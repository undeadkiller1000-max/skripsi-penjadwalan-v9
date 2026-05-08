# -*- coding: utf-8 -*-
"""
DSS Penjadwalan Produksi Job Shop — Garmen | v6.0
Dual-Engine Optimizer: Simulated Annealing + MILP (PuLP/CBC)
Dual Benchmark: EDD + FCFS

PERBAIKAN dari v5.0:
  - [NEW] Toggle tampilan Gantt: Default (warna per order) ↔ Status (merah/hijau)
          tersedia di semua tab Gantt (Pemenang, EDD, FCFS), tombol di bawah chart
  - [NEW] Tab "🆕 Order Baru" terpisah, muncul setelah optimasi awal selesai
  - [FIX] Re-optimasi SA penuh untuk order baru + locked jobs:
          - Locked jobs di-pin dengan constraint start-time exact (±0 toleransi) di SA
          - Urutan existing locked jobs dijamin identik dengan jadwal asal
          - Order baru dioptimasi bebas di sela-sela jadwal yang tersisa
"""

import streamlit as st
import pandas as pd
import pulp
import math
import random
import re
import io
from datetime import datetime, timedelta
import plotly.express as px
import plotly.graph_objects as go

# ============================================================
# 1. KONFIGURASI HALAMAN
# ============================================================
st.set_page_config(page_title="DSS Penjadwalan Job Shop", layout="wide", page_icon="🏭")

st.markdown("""
<style>
.main-header{font-size:2.2rem;font-weight:700;color:#1E3A8A;margin-bottom:0}
.sub-header{font-size:1.05rem;color:#64748B;margin-bottom:16px}
.metric-winner{background:#14532D;padding:14px;border-radius:10px;color:#FFFFFF;line-height:1.6}
.metric-loser{background:#7F1D1D;padding:14px;border-radius:10px;color:#FFFFFF;line-height:1.6}
.metric-neutral{background:#1E3A8A;padding:14px;border-radius:10px;color:#FFFFFF;line-height:1.6}
</style>
""", unsafe_allow_html=True)

st.markdown('<p class="main-header">🏭 DSS: Optimasi Penjadwalan Produksi</p>', unsafe_allow_html=True)
st.markdown('<p class="sub-header">Sistem Penjadwalan Cerdas — Routing Dinamis (OPC) · Dual-Engine Optimizer (SA + MILP) · Analisis Sensitivitas</p>', unsafe_allow_html=True)
st.divider()

# ============================================================
# 2. KONSTANTA GLOBAL
# ============================================================
STATIONS = [
    '1. Potong',
    '2. Jahit_KaosPolo',
    '3. Jahit_KemejaJaket',
    '4. Sablon',
    '5. DTF',
    '6. Bordir',
    '7. Pasang_Kancing',
    '8. Buang_Benang',
    '9. Lipat',
    '10. Packing',
]

REQUIRED_COLUMNS = [
    'id pesanan', 'jenis produk', 'qty', 'due date (tanggal)',
    'furing', 'sablon', 'dtf', 'bordir', 'pasang kancing',
]
BINARY_COLUMNS = ['furing', 'sablon', 'dtf', 'bordir', 'pasang kancing']

MENIT_PER_HARI  = 450
MENIT_ISTIRAHAT = 90

# Palet warna untuk mode Default (per order) — 20 warna berbeda
PALETTE_ORDER = [
    '#2563EB','#16A34A','#DC2626','#D97706','#7C3AED',
    '#0891B2','#DB2777','#65A30D','#EA580C','#0D9488',
    '#4F46E5','#B45309','#BE185D','#15803D','#1D4ED8',
    '#92400E','#6D28D9','#047857','#B91C1C','#0369A1',
]


# ============================================================
# 3. LOAD & VALIDASI DATA
# ============================================================
def load_order_file(uploaded_file):
    fn = uploaded_file.name.lower()
    if fn.endswith('.csv'):
        df = pd.read_csv(uploaded_file)
    elif fn.endswith(('.xlsx', '.xls')):
        df = pd.read_excel(uploaded_file)
    else:
        raise ValueError("Format tidak didukung. Gunakan CSV atau Excel (.xlsx/.xls).")

    df.columns = df.columns.str.lower().str.strip()
    missing = [c for c in REQUIRED_COLUMNS if c not in df.columns]
    if missing:
        raise ValueError(f"Kolom wajib tidak ditemukan: {missing}")

    df = df[REQUIRED_COLUMNS].copy()
    df['id pesanan']   = df['id pesanan'].astype(str).str.strip()
    df['jenis produk'] = df['jenis produk'].astype(str).str.strip().str.lower()

    mapping = {'kaos': 'kaos', 'polo': 'polo', 'kemeja': 'kemeja', 'jaket': 'jaket'}
    df['jenis produk'] = df['jenis produk'].replace(mapping)
    unknown = sorted(set(df['jenis produk']) - set(mapping))
    if unknown:
        raise ValueError(f"Jenis produk tidak dikenali: {unknown}")

    df['qty'] = pd.to_numeric(df['qty'], errors='coerce')
    for col in BINARY_COLUMNS:
        df[col] = pd.to_numeric(df[col], errors='coerce')

    df['due date (tanggal)'] = pd.to_datetime(df['due date (tanggal)'], errors='coerce', dayfirst=True)

    null_mask = df[['qty', 'due date (tanggal)'] + BINARY_COLUMNS].isnull().any(axis=1)
    if null_mask.any():
        raise ValueError(f"Data kosong/invalid di baris: {df.index[null_mask].tolist()}.")
    if (df['qty'] <= 0).any():
        raise ValueError(f"qty <= 0 pada order: {df.loc[df['qty']<=0,'id pesanan'].tolist()}")
    for col in BINARY_COLUMNS:
        inv = df.loc[~df[col].isin([0, 1]), col].unique().tolist()
        if inv:
            raise ValueError(f"Kolom '{col}' hanya boleh 0 atau 1. Nilai: {inv}")

    return df


# ============================================================
# 4. WAKTU PROSES (OPC)
# ============================================================
def hitung_waktu_proses(row, resources, setup_time):
    qty    = row['qty']
    jenis  = str(row['jenis produk']).lower()
    furing = row['furing']
    P      = {m: 0.0 for m in STATIONS}

    cap_potong = 1000
    if jenis in ('kemeja', 'jaket'):
        cap_potong = 125 if furing == 1 else 250
    P['1. Potong'] = (qty / (cap_potong * resources['1. Potong'])) * MENIT_PER_HARI

    if jenis in ('kaos', 'polo'):
        cap_j = 112.5 if jenis == 'kaos' else 55
        P['2. Jahit_KaosPolo'] = (qty / (cap_j * resources['2. Jahit_KaosPolo'])) * MENIT_PER_HARI
    elif jenis in ('kemeja', 'jaket'):
        base = 13.5 if jenis == 'kemeja' else 11.0
        if furing == 1:
            base *= 2/3
        P['3. Jahit_KemejaJaket'] = (qty / (base * resources['3. Jahit_KemejaJaket'])) * MENIT_PER_HARI

    if row['sablon'] == 1:
        P['4. Sablon'] = (qty / (700  * resources['4. Sablon'])) * MENIT_PER_HARI
    if row['dtf']    == 1:
        P['5. DTF']    = (qty / (750  * resources['5. DTF']))    * MENIT_PER_HARI
    if row['bordir'] == 1:
        P['6. Bordir'] = (qty / (442.5* resources['6. Bordir'])) * MENIT_PER_HARI

    if row['pasang kancing'] == 1 and jenis != 'kaos':
        cap_k = 400 if jenis == 'polo' else 125
        P['7. Pasang_Kancing'] = (qty / (cap_k * resources['7. Pasang_Kancing'])) * MENIT_PER_HARI

    cap_benang = 166.67 if furing == 1 else 500
    P['8. Buang_Benang'] = (qty / (cap_benang * resources['8. Buang_Benang'])) * MENIT_PER_HARI
    P['9. Lipat']        = (qty / (500 * resources['9. Lipat']))               * MENIT_PER_HARI
    P['10. Packing']     = (qty / (500 * resources['10. Packing']))            * MENIT_PER_HARI

    for m in STATIONS:
        if P[m] > 0:
            P[m] += setup_time

    return P


# ============================================================
# 5. KONVERSI WAKTU
# ============================================================
def konversi_ke_jam_dinding(menit_efektif, start_date):
    hari_ke = int(menit_efektif // MENIT_PER_HARI)
    sisa    = menit_efektif % MENIT_PER_HARI

    current       = start_date
    hari_ditambah = 0
    while hari_ditambah < hari_ke:
        current += timedelta(days=1)
        if current.weekday() != 6:
            hari_ditambah += 1

    if current.weekday() == 6:
        current += timedelta(days=1)

    base = current.replace(hour=8, minute=30, second=0, microsecond=0)
    if sisa <= 180:
        return base + timedelta(minutes=sisa)
    else:
        return base + timedelta(minutes=sisa + MENIT_ISTIRAHAT)


def hitung_target_menit(target_dt, start_dt):
    if target_dt <= start_dt:
        return 0
    total   = 0
    current = start_dt
    while current.date() < target_dt.date():
        if current.weekday() != 6:
            total += MENIT_PER_HARI
        current += timedelta(days=1)
    if target_dt.weekday() != 6:
        jam_mulai_hari = current.replace(hour=8, minute=30, second=0, microsecond=0)
        delta_kal      = (target_dt - jam_mulai_hari).total_seconds() / 60
        if delta_kal <= 0:
            mnt_hari_ini = 0
        elif delta_kal <= 180:
            mnt_hari_ini = delta_kal
        elif delta_kal <= 180 + MENIT_ISTIRAHAT:
            mnt_hari_ini = 180
        else:
            mnt_hari_ini = delta_kal - MENIT_ISTIRAHAT
        total += mnt_hari_ini
    return total


def pecah_balok_gantt(start_efektif, durasi, start_date):
    blocks      = []
    tersisa     = durasi
    cur_efektif = start_efektif
    while tersisa > 0.01:
        mnt_di_hari = cur_efektif % MENIT_PER_HARI
        if mnt_di_hari < 180:
            chunk = min(tersisa, 180 - mnt_di_hari)
        else:
            chunk = min(tersisa, MENIT_PER_HARI - mnt_di_hari)
        if chunk < 0.01:
            cur_efektif += 0.01
            continue
        blocks.append({
            'start_nyata'    : konversi_ke_jam_dinding(cur_efektif, start_date),
            'end_nyata'      : konversi_ke_jam_dinding(cur_efektif + chunk, start_date),
            'durasi_potongan': chunk,
        })
        cur_efektif += chunk
        tersisa     -= chunk
    return blocks


# ============================================================
# 6. EVAL + SA + BENCHMARK
# ============================================================
def eval_sequence(seq, P_dict, D_dict, W_dict):
    m_avail    = {m: 0.0 for m in STATIONS}
    j_avail    = {j: 0.0 for j in seq}
    total_tard = 0
    sched      = []
    for j in seq:
        rute = [m for m in STATIONS if P_dict[j][m] > 0]
        for m in rute:
            dur   = P_dict[j][m]
            start = max(m_avail[m], j_avail[j])
            end   = start + dur
            m_avail[m] = end
            j_avail[j] = end
            sched.append({'job': j, 'm': m, 'start': start, 'dur': dur})
        total_tard += max(0, j_avail[j] - D_dict[j]) * W_dict[j]
    return total_tard, sched, j_avail


def eval_sequence_with_pins(seq, P_dict, D_dict, W_dict, pinned_starts):
    """
    Evaluasi urutan dengan constraint: job yang di-pin harus mulai tepat sesuai
    pinned_starts[job][mesin]. Slot mesin diisi terlebih dahulu oleh pinned jobs
    sebelum free jobs diselipkan.

    pinned_starts: dict[job_id] -> dict[mesin] -> float (start_efektif)
    """
    # Bangun busy-list dari pinned jobs terlebih dahulu
    m_busy    = {m: [] for m in STATIONS}   # list of (start, end)
    j_end_pin = {}                           # waktu selesai tiap stasiun per pinned job

    for j, pin_m in pinned_starts.items():
        for m, s in pin_m.items():
            dur = P_dict[j][m]
            m_busy[m].append((s, s + dur))
        # Waktu selesai job = akhir stasiun terakhir
        rute_j = [m for m in STATIONS if P_dict[j][m] > 0]
        j_end_pin[j] = max((pin_m.get(m, 0) + P_dict[j][m]) for m in rute_j if m in pin_m)

    for m in STATIONS:
        m_busy[m].sort(key=lambda x: x[0])

    def earliest_free_slot(m, not_before, dur):
        t = not_before
        for s, e in m_busy[m]:
            if t + dur <= s + 1e-6:
                break
            if t < e:
                t = e
        return t

    total_tard = 0
    sched      = []

    # Tambahkan jadwal pinned jobs ke sched
    for j, pin_m in pinned_starts.items():
        rute_j = [m for m in STATIONS if P_dict[j][m] > 0]
        for m in rute_j:
            s = pin_m.get(m, 0)
            sched.append({'job': j, 'm': m, 'start': s, 'dur': P_dict[j][m]})
        total_tard += max(0, j_end_pin[j] - D_dict[j]) * W_dict[j]

    # Proses free jobs dalam urutan seq (hanya yang tidak pinned)
    for j in seq:
        if j in pinned_starts:
            continue
        rute = [m for m in STATIONS if P_dict[j][m] > 0]
        j_avail = 0.0
        for m in rute:
            dur     = P_dict[j][m]
            t_start = earliest_free_slot(m, j_avail, dur)
            t_end   = t_start + dur
            m_busy[m].append((t_start, t_end))
            m_busy[m].sort(key=lambda x: x[0])
            j_avail = t_end
            sched.append({'job': j, 'm': m, 'start': t_start, 'dur': dur})
        total_tard += max(0, j_avail - D_dict[j]) * W_dict[j]

    # Buat dict end time semua job
    j_end_all = {}
    for entry in sched:
        je = entry['start'] + entry['dur']
        if entry['job'] not in j_end_all or je > j_end_all[entry['job']]:
            j_end_all[entry['job']] = je

    return total_tard, sched, j_end_all


def run_simulated_annealing(jobs, P_dict, D_dict, W_dict,
                             pinned_starts=None, n_iter=8000):
    """
    SA standar. Jika pinned_starts diberikan, pinned jobs tidak digeser
    dan free jobs dioptimasi di sela-selanya.
    """
    if pinned_starts is None:
        pinned_starts = {}

    free_jobs = [j for j in jobs if j not in pinned_starts]

    def evaluate(seq):
        if pinned_starts:
            return eval_sequence_with_pins(seq, P_dict, D_dict, W_dict, pinned_starts)
        else:
            return eval_sequence(seq, P_dict, D_dict, W_dict)

    def swap(seq):
        s = seq.copy()
        if len(s) < 2:
            return s
        a, b = random.sample(range(len(s)), 2)
        s[a], s[b] = s[b], s[a]
        return s

    def insert(seq):
        s = seq.copy()
        if len(s) < 2:
            return s
        a   = random.randrange(len(s))
        job = s.pop(a)
        b   = random.randrange(len(s) + 1)
        s.insert(b, job)
        return s

    # Inisialisasi dengan EDD pada free jobs
    cur_seq    = sorted(free_jobs, key=lambda x: D_dict[x])
    cur_score, _, _ = evaluate(cur_seq)
    best_seq   = cur_seq.copy()
    best_score = cur_score

    T_sa    = 500.0
    cooling = 0.997

    for _ in range(n_iter):
        new_seq             = swap(cur_seq) if random.random() < 0.7 else insert(cur_seq)
        new_score, _, _     = evaluate(new_seq)
        delta               = new_score - cur_score
        if delta < 0 or (T_sa > 1e-10 and random.random() < math.exp(-delta / T_sa)):
            cur_seq   = new_seq
            cur_score = new_score
            if new_score < best_score:
                best_seq   = new_seq.copy()
                best_score = new_score
        T_sa *= cooling

    _, final_sched, final_end = evaluate(best_seq)
    return best_score, final_sched, final_end


def run_edd(jobs, P_dict, D_dict, W_dict):
    seq = sorted(jobs, key=lambda x: D_dict[x])
    return eval_sequence(seq, P_dict, D_dict, W_dict)


def run_fcfs(jobs_ordered, P_dict, D_dict, W_dict):
    return eval_sequence(jobs_ordered, P_dict, D_dict, W_dict)


# ============================================================
# 7. HELPER: PULP SAFE NAME
# ============================================================
def safe_var_name(s):
    return re.sub(r'[^A-Za-z0-9_]', '_', str(s))


# ============================================================
# 8. BUILD GANTT DATAFRAME
# ============================================================
def build_gantt_df(sched_list, df_pool, start_date, waktu_selesai_dict=None, D_dict=None):
    rows = []
    for t in sched_list:
        match = df_pool[df_pool['id pesanan'].astype(str) == t['job']]
        qty_val   = match['qty'].iloc[0] if not match.empty else 0
        terlambat = False
        if waktu_selesai_dict and D_dict:
            terlambat = waktu_selesai_dict.get(t['job'], 0) > D_dict.get(t['job'], float('inf'))
        for blk in pecah_balok_gantt(t['start'], t['dur'], start_date):
            rows.append({
                'Stasiun Kerja' : t['m'],
                'ID Pesanan'    : t['job'],
                'Qty'           : qty_val,
                'Mulai'         : blk['start_nyata'],
                'Selesai'       : blk['end_nyata'],
                'Durasi (Menit)': round(blk['durasi_potongan'], 2),
                'Status'        : '🔴 Terlambat' if terlambat else '🟢 Tepat Waktu',
            })
    return pd.DataFrame(rows)


# ============================================================
# 9. RENDER GANTT — DUAL MODE (toggle di bawah chart)
# ============================================================
def render_gantt_dual(df_gantt, title, chart_key, height=520):
    """
    Render Gantt chart dengan dua mode tampilan:
    - Default   : setiap ID Pesanan punya warna unik + legend per order
    - Status    : hijau = tepat waktu, merah = terlambat + legend status

    Tombol toggle ditampilkan DI BAWAH chart.
    State mode disimpan di st.session_state[chart_key].
    """
    if df_gantt.empty:
        st.warning("Tidak ada data jadwal untuk ditampilkan.")
        return

    # Inisialisasi mode
    if chart_key not in st.session_state:
        st.session_state[chart_key] = "default"

    mode = st.session_state[chart_key]

    if mode == "default":
        # Warna unik per ID Pesanan
        unique_ids  = sorted(df_gantt['ID Pesanan'].unique())
        color_map   = {jid: PALETTE_ORDER[i % len(PALETTE_ORDER)] for i, jid in enumerate(unique_ids)}
        fig = px.timeline(
            df_gantt,
            x_start="Mulai", x_end="Selesai",
            y="Stasiun Kerja",
            color="ID Pesanan",
            color_discrete_map=color_map,
            hover_data=["ID Pesanan", "Durasi (Menit)", "Qty", "Status"],
            title=title,
        )
        fig.update_traces(
            text=df_gantt['ID Pesanan'],
            textposition='inside',
            insidetextanchor='middle',
        )
    else:
        # Warna berdasarkan status
        color_map = {'🔴 Terlambat': '#EF4444', '🟢 Tepat Waktu': '#22C55E'}
        fig = px.timeline(
            df_gantt,
            x_start="Mulai", x_end="Selesai",
            y="Stasiun Kerja",
            color="Status",
            color_discrete_map=color_map,
            hover_data=["ID Pesanan", "Durasi (Menit)", "Qty"],
            title=title,
        )
        fig.update_traces(
            text=df_gantt['ID Pesanan'],
            textposition='inside',
            insidetextanchor='middle',
        )
        fig.update_layout(legend_title_text='Status Ketepatan')

    fig.update_yaxes(categoryorder="array", categoryarray=STATIONS[::-1])
    fig.update_layout(
        height=height,
        plot_bgcolor='rgba(0,0,0,0)',
        paper_bgcolor='rgba(0,0,0,0)',
    )
    st.plotly_chart(fig, use_container_width=True, key=f"plot_{chart_key}_{mode}")

    # ── Toggle tombol DI BAWAH chart ──────────────────────────────
    btn_col1, btn_col2, _ = st.columns([1.4, 1.4, 5])
    active_default = mode == "default"
    active_status  = mode == "status"

    if btn_col1.button(
        "🎨 Default (per Order)",
        key=f"btn_default_{chart_key}",
        type="primary" if active_default else "secondary",
        use_container_width=True,
    ):
        st.session_state[chart_key] = "default"
        st.rerun()

    if btn_col2.button(
        "🔴 Status (Tepat/Terlambat)",
        key=f"btn_status_{chart_key}",
        type="primary" if active_status else "secondary",
        use_container_width=True,
    ):
        st.session_state[chart_key] = "status"
        st.rerun()


# ============================================================
# 10. SANITY CHECK
# ============================================================
def jalankan_sanity_check(jadwal_final, df_pool, P_dict, start_date):
    log = ["=" * 60, "🔍 SANITY CHECK — VERIFIKASI LOGIKA JADWAL", "=" * 60]
    err_overlap   = False
    err_presedens = False

    log.append("\n[1/3] Memeriksa Overlap Kapasitas Mesin...")
    for st_name in STATIONS:
        tasks = sorted([t for t in jadwal_final if t['m'] == st_name], key=lambda x: x['start'])
        for i in range(1, len(tasks)):
            prev, curr = tasks[i-1], tasks[i]
            if curr['start'] - (prev['start'] + prev['dur']) < -0.01:
                log.append(f"  ❌ OVERLAP di {st_name}: {prev['job']} & {curr['job']}")
                err_overlap = True
    if not err_overlap:
        log.append("  ✔️ LULUS: Tidak ada tumpang tindih.")

    log.append("\n[2/3] Memeriksa Presedensi...")
    for job in set(t['job'] for t in jadwal_final):
        tasks_j = sorted([t for t in jadwal_final if t['job'] == job], key=lambda x: x['start'])
        for i in range(1, len(tasks_j)):
            prev, curr = tasks_j[i-1], tasks_j[i]
            if curr['start'] - (prev['start'] + prev['dur']) < -0.01:
                log.append(f"  ❌ ERROR Order {job}: {curr['m']} mulai sebelum {prev['m']} selesai!")
                err_presedens = True
    if not err_presedens:
        log.append("  ✔️ LULUS: Semua urutan stasiun benar.")

    log.append("\n[3/3] Memeriksa Jadwal di Hari Minggu...")
    minggu_rows = []
    for t in jadwal_final:
        for blk in pecah_balok_gantt(t['start'], t['dur'], start_date):
            if blk['start_nyata'].weekday() == 6:
                minggu_rows.append({
                    'ID Pesanan': t['job'], 'Stasiun': t['m'],
                    'Mulai'     : blk['start_nyata'].strftime('%d-%b-%y %H:%M'),
                    'Selesai'   : blk['end_nyata'].strftime('%d-%b-%y %H:%M'),
                })
    log.append("  ✔️ LULUS: Tidak ada jadwal di Hari Minggu." if not minggu_rows
               else f"  ❌ {len(minggu_rows)} tugas di Hari Minggu!")

    log.append("\n" + "=" * 60)
    log.append("🚨 SANITY CHECK GAGAL!" if (err_overlap or err_presedens or minggu_rows)
               else "✅ SANITY CHECK PASSED!")
    log.append("=" * 60)

    all_jobs      = list(set(t['job'] for t in jadwal_final))
    sample_job_id = random.choice(all_jobs)
    sample_row_df = df_pool[df_pool['id pesanan'].astype(str) == sample_job_id]
    sample_sched  = sorted([t for t in jadwal_final if t['job'] == sample_job_id], key=lambda x: x['start'])

    return {
        'log_text'     : "\n".join(log),
        'err_overlap'  : err_overlap,
        'err_presedens': err_presedens,
        'sample_job_id': sample_job_id,
        'sample_row'   : sample_row_df.iloc[0].to_dict() if not sample_row_df.empty else {},
        'sample_sched' : sample_sched,
        'sample_rute'  : [t['m'] for t in sample_sched],
        'tabel_minggu' : pd.DataFrame(minggu_rows) if minggu_rows else pd.DataFrame(),
    }


# ============================================================
# 11. SIDEBAR
# ============================================================
with st.sidebar:
    st.image("https://cdn-icons-png.flaticon.com/512/2043/2043236.png", width=60)
    st.header("⚙️ Konfigurasi Sistem")

    with st.expander("📥 Template Data"):
        tpl = pd.DataFrame({
            'id pesanan'        : ['ORD-01', 'ORD-02'],
            'jenis produk'      : ['Kaos', 'Kemeja'],
            'qty'               : [100, 50],
            'due date (tanggal)': ['15/05/2026', '20/05/2026'],
            'furing'            : [0, 1],
            'sablon'            : [1, 0],
            'dtf'               : [0, 0],
            'bordir'            : [0, 1],
            'pasang kancing'    : [0, 1],
        })
        st.download_button(
            "⬇️ Download Template.csv",
            tpl.to_csv(index=False).encode('utf-8'),
            "Template_Order_Pabrik.csv", "text/csv",
        )

    uploaded_file    = st.file_uploader("1. Upload Data Order", type=['csv', 'xlsx', 'xls'])
    start_date_input = st.date_input("2. Tanggal Mulai Produksi", datetime.today())
    start_date       = datetime.combine(start_date_input, datetime.min.time()).replace(hour=8, minute=30)

    st.subheader("🛠️ Analisis Sensitivitas")
    use_custom = st.checkbox("Ubah Kapasitas/Resource Default",
                             help="Simulasikan operator sakit atau mesin rusak.")

    res = {m: 1 for m in STATIONS}
    res['3. Jahit_KemejaJaket'] = 3
    res['8. Buang_Benang']      = 2
    setup_time_val = 0.0

    if use_custom:
        with st.container(border=True):
            setup_time_val              = st.number_input("Setup Antar Order (menit)", 0.0, 60.0, 0.0, 5.0)
            res['1. Potong']            = st.number_input("Operator Potong",           1, 10, 1)
            res['2. Jahit_KaosPolo']    = st.number_input("Tim Jahit Kaos/Polo",       1, 10, 1)
            res['3. Jahit_KemejaJaket'] = st.number_input("Tim Jahit Kemeja/Jaket",    1, 10, 3)
            res['4. Sablon']            = st.number_input("Mesin Sablon",              1, 10, 1)
            res['5. DTF']               = st.number_input("Mesin DTF",                 1, 10, 1)
            res['6. Bordir']            = st.number_input("Mesin Bordir",              1, 10, 1)
            res['7. Pasang_Kancing']    = st.number_input("Operator Pasang Kancing",   1, 10, 1)
            res['8. Buang_Benang']      = st.number_input("Operator Buang Benang",     1, 10, 2)
            res['9. Lipat']             = st.number_input("Operator Lipat",            1, 10, 1)
            res['10. Packing']          = st.number_input("Operator Packing",          1, 10, 1)

    milp_time_limit = st.slider(
        "⏱️ Batas Waktu MILP (detik)",
        min_value=60, max_value=600, value=300, step=30,
    )
    run_button = st.button("🚀 JALANKAN OPTIMASI", type="primary", use_container_width=True)


# ============================================================
# 12. MAIN AREA
# ============================================================
if uploaded_file is None:
    st.info("👈 Silakan unggah file CSV / Excel di panel kiri untuk memulai.")
else:
    try:
        df = load_order_file(uploaded_file)
        df['_orig_order'] = range(len(df))
        df['Bulan-Tahun'] = df['due date (tanggal)'].dt.strftime('%B %Y')

        with st.container(border=True):
            c1, c2 = st.columns(2)
            bulan_pilih = c1.selectbox("Filter Bulan Due Date:", ["Semua"] + list(df['Bulan-Tahun'].unique()))
            sortir      = c2.selectbox(
                "Urutkan:",
                ["Default (sesuai file)", "Due Date Terdekat", "Due Date Terjauh"],
                index=0,
            )

        df_disp = df.copy() if bulan_pilih == "Semua" else df[df['Bulan-Tahun'] == bulan_pilih].copy()
        if sortir == "Due Date Terdekat":
            df_disp = df_disp.sort_values('due date (tanggal)', ascending=True)
        elif sortir == "Due Date Terjauh":
            df_disp = df_disp.sort_values('due date (tanggal)', ascending=False)
        else:
            df_disp = df_disp.sort_values('_orig_order')

        for col, default in [("Pilih", False), ("Priority", False), ("Terkunci", False)]:
            if col not in df_disp.columns:
                pos = {"Pilih": 0, "Priority": 1, "Terkunci": 2}[col]
                df_disp.insert(pos, col, default)

        st.subheader("📋 Pemilihan & Prioritisasi Order")
        st.info(
            "💡 Centang **Pilih** untuk memasukkan order ke optimasi. "
            "Centang **Priority** untuk bobot penalti lebih tinggi (order VIP). "
            "Centang **🔒 Terkunci** untuk order yang sudah/sedang dikerjakan — "
            "posisi jadwalnya tidak akan diubah sama sekali saat ada order baru masuk."
        )

        display_cols = [c for c in df_disp.columns if c not in ['Bulan-Tahun', '_orig_order']]
        df_disp_show = df_disp[display_cols].copy()

        if ("df_editor_state" not in st.session_state or
                set(st.session_state["df_editor_state"].columns) != set(df_disp_show.columns)):
            st.session_state["df_editor_state"] = df_disp_show.copy()

        current_ids = df_disp["id pesanan"].astype(str).tolist()
        stored_ids  = st.session_state["df_editor_state"]["id pesanan"].astype(str).tolist()
        if current_ids != stored_ids:
            st.session_state["df_editor_state"] = df_disp_show.copy()

        col_sel1, col_sel2, _ = st.columns([1, 1, 4])
        if col_sel1.button("☑️ Pilih Semua", use_container_width=True):
            st.session_state["df_editor_state"]["Pilih"] = True
            st.rerun()
        if col_sel2.button("⬜ Batal Semua", use_container_width=True):
            st.session_state["df_editor_state"]["Pilih"] = False
            st.rerun()

        edited_df = st.data_editor(
            st.session_state["df_editor_state"],
            key="order_editor",
            hide_index=True,
            use_container_width=True,
            column_config={
                "Pilih"    : st.column_config.CheckboxColumn("Pilih",        default=False),
                "Priority" : st.column_config.CheckboxColumn("Priority",     default=False),
                "Terkunci" : st.column_config.CheckboxColumn("🔒 Terkunci",  default=False,
                    help="Order sudah/sedang dikerjakan — posisi tidak berubah saat re-optimasi order baru"),
            },
        )
        st.session_state["df_editor_state"] = edited_df.copy()

        df_pool = edited_df[edited_df["Pilih"] == True].copy()
        df_pool = df_pool.merge(df[['id pesanan', '_orig_order']], on='id pesanan', how='left')

        # ============================================================
        # 13. ENGINE OPTIMASI AWAL
        # ============================================================
        if run_button:
            if len(df_pool) == 0:
                st.warning("⚠️ Centang minimal 1 pesanan untuk dioptimasi.")
                st.stop()

            if len(df_pool) == 1:
                st.warning("⚠️ Hanya 1 order dipilih — SA dijalankan, MILP dilewati.")

            pb = st.progress(0, text="Memulai optimasi…")

            # ── Preprocessing ──
            pb.progress(5, "1/5 Kalkulasi routing & waktu proses…")
            df_pool = df_pool.copy()
            df_pool['target_dt']    = df_pool['due date (tanggal)'].apply(
                lambda x: x.replace(hour=17, minute=30, second=0, microsecond=0))
            df_pool['target_menit'] = df_pool['target_dt'].apply(
                lambda x: hitung_target_menit(x, start_date))

            jobs_raw       = df_pool.to_dict('records')
            jobs_raw_fcfs  = sorted(jobs_raw, key=lambda x: x['_orig_order'])
            job_ids        = [str(j['id pesanan']) for j in jobs_raw]
            job_ids_fcfs   = [str(j['id pesanan']) for j in jobs_raw_fcfs]

            P = {str(j['id pesanan']): hitung_waktu_proses(j, res, setup_time_val) for j in jobs_raw}
            D = {str(j['id pesanan']): j['target_menit']                           for j in jobs_raw}
            W = {str(j['id pesanan']): 10_000 if j['Priority'] else 1              for j in jobs_raw}

            # ── SA ──
            pb.progress(15, "2/5 Simulated Annealing (8.000 iterasi)…")
            sa_score, sa_sched, sa_end = run_simulated_annealing(job_ids, P, D, W)

            # ── MILP ──
            pb.progress(35, f"3/5 MILP/CBC (maks {milp_time_limit} detik)…")
            milp_score    = float('inf')
            milp_feasible = False
            milp_status   = "Not Run"
            milp_sched    = []
            milp_end      = {}
            bigm_info     = {}

            if len(job_ids) >= 2:
                prob     = pulp.LpProblem("JobShop_Garment", pulp.LpMinimize)
                S        = pulp.LpVariable.dicts("S",    (job_ids, STATIONS), lowBound=0, cat='Continuous')
                Tard_var = pulp.LpVariable.dicts("Tard", job_ids,             lowBound=0, cat='Continuous')

                BigM_per_mesin = {}
                for m in STATIONS:
                    total_dur = sum(P[i][m] for i in job_ids if P[i][m] > 0)
                    BigM_per_mesin[m] = max(total_dur, 1.0)
                    bigm_info[m]      = round(BigM_per_mesin[m], 1)

                Y = {}
                for m in STATIONS:
                    aktif = [i for i in job_ids if P[i][m] > 0]
                    for a in range(len(aktif)):
                        for b in range(a + 1, len(aktif)):
                            i, j = aktif[a], aktif[b]
                            Y[(i, j, m)] = pulp.LpVariable(
                                f"Y_{safe_var_name(i)}_{safe_var_name(j)}_{safe_var_name(m)}", cat='Binary')

                prob += pulp.lpSum(W[i] * Tard_var[i] for i in job_ids)

                for i in job_ids:
                    rute = [m for m in STATIONS if P[i][m] > 0]
                    for k in range(1, len(rute)):
                        prob += S[i][rute[k]] >= S[i][rute[k-1]] + P[i][rute[k-1]]
                    if rute:
                        prob += Tard_var[i] >= (S[i][rute[-1]] + P[i][rute[-1]]) - D[i]

                for (i, j, m), y_var in Y.items():
                    bm = BigM_per_mesin[m]
                    prob += S[j][m] >= S[i][m] + P[i][m] - bm * y_var
                    prob += S[i][m] >= S[j][m] + P[j][m] - bm * (1 - y_var)

                sa_start_map = {(e['job'], e['m']): e['start'] for e in sa_sched}
                for i in job_ids:
                    for m in STATIONS:
                        val = sa_start_map.get((i, m))
                        if val is not None:
                            S[i][m].setInitialValue(val)
                for (i, j, m), y_var in Y.items():
                    si = sa_start_map.get((i, m))
                    sj = sa_start_map.get((j, m))
                    if si is not None and sj is not None:
                        try:
                            y_var.setInitialValue(1 if sj < si else 0)
                        except Exception:
                            pass

                prob.solve(pulp.PULP_CBC_CMD(timeLimit=milp_time_limit, msg=0, warmStart=True))
                milp_status   = pulp.LpStatus[prob.status]
                obj_val       = pulp.value(prob.objective)
                milp_feasible = milp_status in ('Optimal', 'Feasible') and obj_val is not None
                milp_score    = float(obj_val) if milp_feasible else float('inf')

                if milp_feasible:
                    for i in job_ids:
                        rute = [m for m in STATIONS if P[i][m] > 0]
                        milp_end[i] = (S[i][rute[-1]].varValue or 0) + P[i][rute[-1]] if rute else 0
                        for m in rute:
                            milp_sched.append({'job': i, 'm': m,
                                               'start': round(S[i][m].varValue or 0, 2), 'dur': P[i][m]})

            # ── Benchmark EDD & FCFS ──
            pb.progress(80, "4/5 Menjalankan benchmark EDD & FCFS…")
            edd_score,  edd_sched,  edd_end  = run_edd(job_ids, P, D, W)
            fcfs_score, fcfs_sched, fcfs_end = run_fcfs(job_ids_fcfs, P, D, W)

            # ── Showdown ──
            pb.progress(90, "5/5 Membandingkan & memfinalisasi…")
            if milp_feasible and milp_score <= sa_score:
                pemenang           = f"MILP ({milp_status})"
                label_pemenang     = "MILP"
                jadwal_final       = milp_sched
                waktu_selesai_dict = milp_end
                score_pemenang     = milp_score
            else:
                alasan             = "SA lebih baik" if milp_feasible else f"MILP tidak feasible ({milp_status})"
                pemenang           = f"Simulated Annealing ({alasan})"
                label_pemenang     = "Simulated Annealing"
                jadwal_final       = sa_sched
                waktu_selesai_dict = sa_end
                score_pemenang     = sa_score

            sc = jalankan_sanity_check(jadwal_final, df_pool, P, start_date)
            pb.progress(100, "✅ Selesai!")

            # ── Post-processing ──
            laporan_order  = []
            jadwal_op_rows = []
            pesanan_telat  = 0

            for i in job_ids:
                target_nyata  = df_pool[df_pool['id pesanan'].astype(str) == i]['target_dt'].iloc[0]
                selesai_nyata = konversi_ke_jam_dinding(waktu_selesai_dict[i], start_date)
                selisih_mnt   = (selesai_nyata - target_nyata).total_seconds() / 60
                status_ord    = 'Telat' if selisih_mnt > 0 else 'Tepat Waktu'
                if selisih_mnt > 0:
                    pesanan_telat += 1
                laporan_order.append({
                    'ID Pesanan'      : i,
                    'Prioritas'       : "⭐ Ya" if W[i] > 1 else "Tidak",
                    'Target Selesai'  : target_nyata.strftime('%d-%b-%y %H:%M'),
                    'Estimasi Selesai': selesai_nyata.strftime('%d-%b-%y %H:%M'),
                    'Status'          : status_ord,
                    'Telat (Hari)'    : math.ceil(max(0, selisih_mnt) / MENIT_PER_HARI),
                })

            for t in jadwal_final:
                match = df_pool[df_pool['id pesanan'].astype(str) == t['job']]
                qty_row = match['qty'].iloc[0] if not match.empty else 0
                jadwal_op_rows.append({
                    'Stasiun Kerja': t['m'],
                    'ID Pesanan'   : t['job'],
                    'Qty'          : qty_row,
                    'Mulai'        : konversi_ke_jam_dinding(t['start'], start_date).strftime('%d-%b-%y %H:%M'),
                    'Selesai'      : konversi_ke_jam_dinding(t['start']+t['dur'], start_date).strftime('%d-%b-%y %H:%M'),
                })

            df_gantt      = build_gantt_df(jadwal_final, df_pool, start_date, waktu_selesai_dict, D)
            df_laporan    = pd.DataFrame(laporan_order).sort_values(['Status','Estimasi Selesai'], ascending=[False,True])
            df_op         = pd.DataFrame(jadwal_op_rows)
            df_gantt_edd  = build_gantt_df(edd_sched,  df_pool, start_date, edd_end,  D)
            df_gantt_fcfs = build_gantt_df(fcfs_sched, df_pool, start_date, fcfs_end, D)

            # ── Simpan ke session_state agar tab Order Baru bisa mengakses ──
            st.session_state['hasil_optimasi'] = {
                'jadwal_final'      : jadwal_final,
                'waktu_selesai_dict': waktu_selesai_dict,
                'P'                 : P,
                'D'                 : D,
                'W'                 : W,
                'job_ids'           : job_ids,
                'df_pool'           : df_pool,
                'start_date'        : start_date,
                'res'               : res,
                'setup_time_val'    : setup_time_val,
            }

            # ============================================================
            # 14. DASHBOARD — RINGKASAN METRIK
            # ============================================================
            st.divider()
            m1, m2, m3, m4, m5 = st.columns(5)
            m1.metric("📦 Total Order",    len(job_ids))
            m2.metric("✅ Tepat Waktu",    len(job_ids) - pesanan_telat)
            m3.metric("🚨 Terlambat",      pesanan_telat, delta_color="inverse")
            m4.metric("🏆 Pemenang",       label_pemenang)
            m5.metric("📉 Skor Penalti",   f"{score_pemenang:,.1f}")

            edd_telat  = sum(1 for i in job_ids if edd_end.get(i, 0)  > D.get(i, 0))
            fcfs_telat = sum(1 for i in job_ids if fcfs_end.get(i, 0) > D.get(i, 0))

            with st.container(border=True):
                cc1, cc2, cc3 = st.columns(3)
                cc1.markdown(
                    f'<div class="metric-winner"><b>🏆 {label_pemenang}</b><br>'
                    f'Skor Penalti: <b>{score_pemenang:,.2f}</b><br>'
                    f'MILP Status: {milp_status}</div>', unsafe_allow_html=True)
                cc2.markdown(
                    f'<div class="metric-loser"><b>📊 EDD (Benchmark)</b><br>'
                    f'Skor Penalti: <b>{edd_score:,.2f}</b><br>'
                    f'Tepat: {len(job_ids)-edd_telat} | Terlambat: {edd_telat}</div>', unsafe_allow_html=True)
                cc3.markdown(
                    f'<div class="metric-loser"><b>📊 FCFS (Benchmark)</b><br>'
                    f'Skor Penalti: <b>{fcfs_score:,.2f}</b><br>'
                    f'Tepat: {len(job_ids)-fcfs_telat} | Terlambat: {fcfs_telat}</div>', unsafe_allow_html=True)

            if bigm_info:
                bigm_aktif = {k: v for k, v in bigm_info.items() if v > 1.0}
                bigm_str   = " · ".join(f"{k.split('. ',1)[-1]}={v:.0f}" for k, v in bigm_aktif.items())
                st.caption(f"🔧 BigM per-mesin (v6): {bigm_str} · SA: 8.000 iter, T₀=500, α=0.997 · Warm-start: ✅")
            else:
                st.caption("SA: 8.000 iter, T₀=500, α=0.997")

            # ============================================================
            # 15. TAB DASHBOARD
            # ============================================================
            tab1, tab2, tab3, tab4, tab5, tab6, tab7 = st.tabs([
                "📊 Gantt — Pemenang",
                "📊 Gantt — EDD",
                "📊 Gantt — FCFS",
                "📑 Laporan Manajemen",
                "👨‍🔧 Lembar Kerja Operator",
                "🔎 Audit & Sanity Check",
                "🆕 Penjadwalan Order Baru",
            ])

            # ── TAB 1: Gantt Pemenang ─────────────────────────────────
            with tab1:
                st.markdown(f"**Jadwal Akhir Produksi** — dihasilkan oleh: *{pemenang}*")
                render_gantt_dual(df_gantt,
                                  title=f"Gantt Chart: {label_pemenang} (Skor: {score_pemenang:,.2f})",
                                  chart_key="gantt_pemenang")
                with st.expander("📋 Detail Status Order — Pemenang"):
                    rows_st = []
                    for i in job_ids:
                        tgt  = df_pool[df_pool['id pesanan'].astype(str) == i]['target_dt'].iloc[0]
                        sel  = konversi_ke_jam_dinding(waktu_selesai_dict.get(i, 0), start_date)
                        tel  = (sel - tgt).total_seconds() / 60
                        rows_st.append({'ID Pesanan': i, 'Target': tgt.strftime('%d-%b-%y %H:%M'),
                                        'Estimasi Selesai': sel.strftime('%d-%b-%y %H:%M'),
                                        'Status': '🔴 Terlambat' if tel > 0 else '🟢 Tepat Waktu',
                                        'Selisih (Hari)': math.ceil(max(0, tel) / MENIT_PER_HARI)})
                    st.dataframe(pd.DataFrame(rows_st), hide_index=True, use_container_width=True)

            # ── TAB 2: Gantt EDD ──────────────────────────────────────
            with tab2:
                st.markdown("**Benchmark EDD** — Earliest Due Date")
                render_gantt_dual(df_gantt_edd,
                                  title=f"Gantt Chart EDD (Skor: {edd_score:,.2f})",
                                  chart_key="gantt_edd")
                with st.expander("📋 Detail Status Order — EDD"):
                    rows_edd = []
                    for i in job_ids:
                        tgt  = df_pool[df_pool['id pesanan'].astype(str) == i]['target_dt'].iloc[0]
                        sel  = konversi_ke_jam_dinding(edd_end.get(i, 0), start_date)
                        tel  = (sel - tgt).total_seconds() / 60
                        rows_edd.append({'ID Pesanan': i, 'Target': tgt.strftime('%d-%b-%y %H:%M'),
                                         'Estimasi Selesai': sel.strftime('%d-%b-%y %H:%M'),
                                         'Status': '🔴 Terlambat' if tel > 0 else '🟢 Tepat Waktu',
                                         'Selisih (Hari)': math.ceil(max(0, tel) / MENIT_PER_HARI)})
                    st.dataframe(pd.DataFrame(rows_edd), hide_index=True, use_container_width=True)

            # ── TAB 3: Gantt FCFS ─────────────────────────────────────
            with tab3:
                st.markdown("**Benchmark FCFS** — First Come First Served (urutan masuk order sesuai file)")
                render_gantt_dual(df_gantt_fcfs,
                                  title=f"Gantt Chart FCFS (Skor: {fcfs_score:,.2f})",
                                  chart_key="gantt_fcfs")
                with st.expander("📋 Detail Status Order — FCFS"):
                    rows_fcfs = []
                    for i in job_ids_fcfs:
                        tgt  = df_pool[df_pool['id pesanan'].astype(str) == i]['target_dt'].iloc[0]
                        sel  = konversi_ke_jam_dinding(fcfs_end.get(i, 0), start_date)
                        tel  = (sel - tgt).total_seconds() / 60
                        rows_fcfs.append({'ID Pesanan': i, 'Target': tgt.strftime('%d-%b-%y %H:%M'),
                                          'Estimasi Selesai': sel.strftime('%d-%b-%y %H:%M'),
                                          'Status': '🔴 Terlambat' if tel > 0 else '🟢 Tepat Waktu',
                                          'Selisih (Hari)': math.ceil(max(0, tel) / MENIT_PER_HARI)})
                    st.dataframe(pd.DataFrame(rows_fcfs), hide_index=True, use_container_width=True)

            # ── TAB 4: Laporan Manajemen ──────────────────────────────
            with tab4:
                st.markdown("**Status Penyelesaian Order per Tenggat Waktu**")
                def color_status(val):
                    return 'background-color:#DC2626;color:white' if val == 'Telat' \
                           else 'background-color:#16A34A;color:white'
                st.dataframe(df_laporan.style.map(color_status, subset=['Status']),
                             use_container_width=True, height=420)

            # ── TAB 5: Lembar Kerja Operator ──────────────────────────
            with tab5:
                st.markdown("**Instruksi Kerja (Work Order) per Stasiun Kerja**")
                for stasiun in STATIONS:
                    df_st = df_op[df_op['Stasiun Kerja'] == stasiun]
                    if df_st.empty:
                        continue
                    with st.expander(f"📁 {stasiun} — {len(df_st)} order"):
                        st.dataframe(df_st.drop(columns=['Stasiun Kerja']),
                                     hide_index=True, use_container_width=True)

            # ── TAB 6: Audit & Sanity Check ───────────────────────────
            with tab6:
                st.markdown("### 🔎 Audit Otomatis — Verifikasi Logika Jadwal")
                if sc['err_overlap'] or sc['err_presedens'] or not sc['tabel_minggu'].empty:
                    st.error("🚨 **Sanity Check GAGAL** — ditemukan pelanggaran.")
                else:
                    st.success("✅ **Sanity Check PASSED** — Jadwal valid.")

                with st.expander("📄 Lihat Log Teks Lengkap", expanded=False):
                    st.code(sc['log_text'], language="text")
                st.divider()

                st.markdown("#### [1] Pemeriksaan Overlap Mesin")
                if sc['err_overlap']:
                    st.error("❌ Ditemukan overlap! Lihat log teks di atas.")
                else:
                    st.success("✔️ Tidak ada overlap.")
                st.divider()

                st.markdown("#### [2] Verifikasi Presedensi")
                all_job_ids = list(set(t['job'] for t in jadwal_final))
                if ("selected_job_presedensi" not in st.session_state or
                        st.session_state["selected_job_presedensi"] not in all_job_ids):
                    st.session_state["selected_job_presedensi"] = sc["sample_job_id"]

                selected_job = st.selectbox(
                    "🔍 Pilih Order untuk diperiksa:",
                    options=all_job_ids,
                    index=all_job_ids.index(st.session_state["selected_job_presedensi"]),
                    key="selected_job_presedensi",
                )

                selected_row_df = df_pool[df_pool["id pesanan"].astype(str) == selected_job]
                sr   = selected_row_df.iloc[0].to_dict() if not selected_row_df.empty else {}
                rute = [t["m"] for t in sorted(
                    [t for t in jadwal_final if t["job"] == selected_job], key=lambda x: x["start"])]

                if sr:
                    col_spec1, col_spec2 = st.columns(2)
                    with col_spec1:
                        st.markdown("**Spesifikasi Order:**")
                        spec_data = {
                            'Atribut': ['ID Pesanan','Jenis Produk','Qty','Due Date',
                                        'Furing','Sablon','DTF','Bordir','Pasang Kancing'],
                            'Nilai'  : [
                                str(sr.get('id pesanan','-')),
                                str(sr.get('jenis produk','-')).capitalize(),
                                str(int(sr.get('qty',0))),
                                pd.Timestamp(sr.get('due date (tanggal)','')).strftime('%d-%b-%Y')
                                    if sr.get('due date (tanggal)') else '-',
                                '✅ Ya' if sr.get('furing',0)==1 else '❌ Tidak',
                                '✅ Ya' if sr.get('sablon',0)==1 else '❌ Tidak',
                                '✅ Ya' if sr.get('dtf',0)==1    else '❌ Tidak',
                                '✅ Ya' if sr.get('bordir',0)==1 else '❌ Tidak',
                                '✅ Ya' if sr.get('pasang kancing',0)==1 else '❌ Tidak',
                            ]
                        }
                        st.dataframe(pd.DataFrame(spec_data), hide_index=True, use_container_width=True)
                    with col_spec2:
                        st.markdown("**Routing Aktif (OPC):**")
                        p_sample = P.get(selected_job, {})
                        opc_rows = [{'Urutan': idx+1, 'Stasiun': m,
                                     'Durasi (mnt)': round(p_sample.get(m, 0), 2)}
                                    for idx, m in enumerate(rute)]
                        st.dataframe(pd.DataFrame(opc_rows), hide_index=True, use_container_width=True)

                if rute:
                    st.markdown("**Operation Process Chart (OPC) — Flow Stasiun:**")
                    p_sample = P.get(selected_job, {})
                    opc_fig  = go.Figure()
                    n    = len(rute)
                    durs = [round(p_sample.get(m, 0), 2) for m in rute]
                    for xi, (m, d) in enumerate(zip(rute, durs)):
                        short_m = m.split('. ', 1)[-1].replace('_', ' ')
                        opc_fig.add_trace(go.Scatter(
                            x=[xi], y=[0.35], mode='markers+text',
                            marker=dict(size=48, color='#1E3A8A', symbol='square'),
                            text=[f"<b>{xi+1}</b>"],
                            textposition='middle center',
                            textfont=dict(color='white', size=16),
                            hovertemplate=f"<b>{m}</b><br>Durasi: {d:.1f} mnt<extra></extra>",
                            showlegend=False,
                        ))
                        opc_fig.add_annotation(
                            x=xi, y=-0.35,
                            text=f"<b>{short_m}</b><br>{d:.1f} mnt",
                            showarrow=False,
                            font=dict(size=13, color='#1E293B'),
                            align='center',
                            bgcolor='#F1F5F9',
                            borderpad=5, bordercolor='#1E3A8A', borderwidth=2, opacity=1.0,
                        )
                        if xi < n - 1:
                            opc_fig.add_annotation(
                                ax=xi+0.1, ay=0.35, axref='x', ayref='y',
                                x=xi+0.9,  y=0.35, xref='x',  yref='y',
                                showarrow=True, arrowhead=2, arrowsize=1.5,
                                arrowwidth=2, arrowcolor='#64748B',
                            )
                    opc_fig.update_layout(
                        height=260, margin=dict(l=20, r=20, t=10, b=10),
                        xaxis=dict(visible=False, range=[-0.7, n-0.3]),
                        yaxis=dict(visible=False, range=[-0.85, 0.85]),
                        plot_bgcolor='rgba(0,0,0,0)', paper_bgcolor='rgba(0,0,0,0)',
                    )
                    st.plotly_chart(opc_fig, use_container_width=True)

                st.markdown(f"**Gantt Chart Order `{selected_job}` dalam Jadwal Final:**")
                sched_sample = sorted([t for t in jadwal_final if t['job'] == selected_job],
                                      key=lambda x: x['start'])
                if sched_sample:
                    rows_s = []
                    for t in sched_sample:
                        for blk in pecah_balok_gantt(t['start'], t['dur'], start_date):
                            rows_s.append({'Stasiun': t['m'], 'Mulai': blk['start_nyata'],
                                           'Selesai': blk['end_nyata'],
                                           'Durasi (Menit)': round(blk['durasi_potongan'], 2)})
                    df_sg = pd.DataFrame(rows_s)
                    fig_sg = px.timeline(df_sg, x_start="Mulai", x_end="Selesai",
                                         y="Stasiun", color="Stasiun",
                                         hover_data=["Durasi (Menit)"],
                                         title=f"Alur Proses Order {selected_job}",
                                         color_discrete_sequence=px.colors.qualitative.Set2)
                    fig_sg.update_yaxes(categoryorder="array", categoryarray=rute[::-1])
                    fig_sg.update_layout(height=max(250, len(rute)*45), showlegend=False,
                                         plot_bgcolor='rgba(0,0,0,0)', paper_bgcolor='rgba(0,0,0,0)')
                    st.plotly_chart(fig_sg, use_container_width=True)

                st.divider()
                st.markdown("#### [3] Verifikasi Hari Libur (Minggu)")
                if sc['tabel_minggu'].empty:
                    st.success("✔️ Tidak ada jadwal di Hari Minggu.")
                    st.dataframe(pd.DataFrame(columns=['ID Pesanan','Stasiun','Mulai','Selesai']),
                                 use_container_width=True, hide_index=True)
                    st.caption("↑ Tabel kosong — tidak ada aktivitas produksi di Hari Minggu.")
                else:
                    st.error(f"❌ {len(sc['tabel_minggu'])} slot dijadwalkan di Hari Minggu!")
                    st.dataframe(sc['tabel_minggu'], hide_index=True, use_container_width=True)

            # ============================================================
            # ── TAB 7: PENJADWALAN ORDER BARU ─────────────────────────
            # ============================================================
            with tab7:
                st.markdown("### 🆕 Penjadwalan Order Baru")
                st.info(
                    "Masukkan spesifikasi order baru. Sistem akan menjalankan **re-optimasi SA** "
                    "dengan order baru ditambahkan ke jadwal yang sudah ada. "
                    "Order yang ditandai **🔒 Terkunci** di tabel atas akan di-*pin* secara tepat — "
                    "posisi jadwalnya **tidak akan berubah sama sekali**. "
                    "Order lainnya bebas dioptimasi ulang bersama order baru."
                )

                st.subheader("📥 Spesifikasi Order Baru")
                nb_col1, nb_col2, nb_col3 = st.columns(3)
                nb_id    = nb_col1.text_input("ID Order Baru", value="NEW-001",
                                              key="nb_id_input",
                                              help="ID unik, tidak boleh sama dengan order yang sudah ada")
                nb_jenis = nb_col2.selectbox("Jenis Produk", ['kaos', 'polo', 'kemeja', 'jaket'],
                                             key="nb_jenis")
                nb_qty   = nb_col3.number_input("Qty", min_value=1, max_value=10000, value=100,
                                                key="nb_qty")

                nb_col4, nb_col5, nb_col6 = st.columns(3)
                nb_furing  = 1 if nb_col4.checkbox("Furing",          key="nb_furing")  else 0
                nb_sablon  = 1 if nb_col4.checkbox("Sablon",          key="nb_sablon")  else 0
                nb_dtf     = 1 if nb_col5.checkbox("DTF",             key="nb_dtf")     else 0
                nb_bordir  = 1 if nb_col5.checkbox("Bordir",          key="nb_bordir")  else 0
                nb_kancing = 1 if nb_col6.checkbox("Pasang Kancing",  key="nb_kancing") else 0

                nb_due_input = nb_col1.date_input(
                    "Due Date Order Baru (opsional — untuk dipantau ketepatan waktunya)",
                    value=None,
                    key="nb_due",
                )

                st.divider()

                # Tampilkan daftar order terkunci saat ini
                locked_set = set()
                if 'Terkunci' in edited_df.columns:
                    locked_set = set(
                        edited_df[edited_df['Terkunci'] == True]['id pesanan'].astype(str).tolist()
                    )

                if locked_set:
                    st.success(f"🔒 Order yang akan di-pin (tidak berubah): **{', '.join(sorted(locked_set))}**")
                else:
                    st.warning(
                        "⚠️ Belum ada order yang ditandai **🔒 Terkunci**. "
                        "Semua order existing (+ order baru) akan dioptimasi ulang bersama-sama. "
                        "Jika ada order yang sudah dikerjakan, tandai 🔒 Terkunci di tabel atas lalu "
                        "tekan **JALANKAN OPTIMASI** kembali sebelum masuk ke tab ini."
                    )

                btn_reopt = st.button("⚡ Jalankan Re-Optimasi dengan Order Baru",
                                      type="primary", key="btn_reopt")

                if btn_reopt:
                    nb_id_clean = nb_id.strip()

                    if nb_id_clean == "":
                        st.error("❌ ID Order Baru tidak boleh kosong.")
                    elif nb_id_clean in job_ids:
                        st.error(f"❌ ID '{nb_id_clean}' sudah ada di jadwal. Gunakan ID yang berbeda.")
                    else:
                        # ── Bangun data order baru ──
                        nb_row = {
                            'qty'           : nb_qty,
                            'jenis produk'  : nb_jenis,
                            'furing'        : nb_furing,
                            'sablon'        : nb_sablon,
                            'dtf'           : nb_dtf,
                            'bordir'        : nb_bordir,
                            'pasang kancing': nb_kancing,
                        }
                        P_new_single = hitung_waktu_proses(nb_row, res, setup_time_val)

                        # Due date order baru
                        if nb_due_input:
                            nb_target_dt  = datetime.combine(nb_due_input,
                                            datetime.min.time()).replace(hour=17, minute=30)
                            nb_target_mnt = hitung_target_menit(nb_target_dt, start_date)
                        else:
                            # Tanpa due date → set sangat jauh (tidak ada penalti tardiness)
                            nb_target_mnt = 99999.0

                        # ── Gabungkan semua job (existing + baru) ──
                        all_jobs_new  = job_ids + [nb_id_clean]
                        P_all         = {**P, nb_id_clean: P_new_single}
                        D_all         = {**D, nb_id_clean: nb_target_mnt}
                        W_all         = {**W, nb_id_clean: 1}   # order baru tidak priority by default

                        # ── Bangun pinned_starts dari jadwal_final untuk locked jobs ──
                        # Setiap locked job dipetakan: {mesin: start_time} tepat seperti jadwal asal
                        pinned_starts = {}
                        for jid in locked_set:
                            if jid in job_ids:   # pastikan job ini memang ada
                                pin_m = {}
                                for entry in jadwal_final:
                                    if entry['job'] == jid:
                                        pin_m[entry['m']] = entry['start']
                                if pin_m:
                                    pinned_starts[jid] = pin_m

                        pb_new = st.progress(0, text="Re-optimasi dimulai…")
                        pb_new.progress(20, "Membangun jadwal dengan pin locked jobs…")

                        # ── Re-optimasi SA dengan pinned jobs ──
                        sa_new_score, sa_new_sched, sa_new_end = run_simulated_annealing(
                            all_jobs_new, P_all, D_all, W_all,
                            pinned_starts=pinned_starts,
                            n_iter=8000,
                        )
                        pb_new.progress(100, "✅ Re-optimasi selesai!")

                        # ── Verifikasi locked jobs tidak bergerak ──
                        locked_aman   = True
                        locked_issues = []
                        for jid in locked_set:
                            if jid not in pinned_starts:
                                continue
                            for entry in sa_new_sched:
                                if entry['job'] == jid:
                                    orig_start = pinned_starts[jid].get(entry['m'])
                                    if orig_start is not None and abs(entry['start'] - orig_start) > 0.1:
                                        locked_issues.append(
                                            f"{jid} @ {entry['m']}: asal={orig_start:.1f}, baru={entry['start']:.1f}"
                                        )
                                        locked_aman = False

                        if locked_aman:
                            st.success("✅ Semua order terkunci tetap persis pada posisi jadwal asalnya.")
                        else:
                            st.error(
                                f"⚠️ Ada inkonsistensi kecil pada locked jobs (kemungkinan floating-point): "
                                f"{'; '.join(locked_issues)}"
                            )

                        # ── Bangun DataFrame untuk display ──
                        # Tambahkan order baru ke df_pool sementara untuk build_gantt_df
                        nb_df_row = pd.DataFrame([{
                            'id pesanan': nb_id_clean,
                            'qty'       : nb_qty,
                        }])
                        df_pool_augmented = pd.concat(
                            [df_pool[['id pesanan', 'qty']], nb_df_row], ignore_index=True
                        )

                        waktu_selesai_new = sa_new_end
                        df_gantt_new = build_gantt_df(
                            sa_new_sched, df_pool_augmented, start_date,
                            waktu_selesai_new, D_all
                        )

                        # ── Metrik ringkasan ──
                        pesanan_telat_new = sum(
                            1 for i in all_jobs_new if sa_new_end.get(i, 0) > D_all.get(i, 0)
                        )
                        new_col1, new_col2, new_col3 = st.columns(3)
                        new_col1.metric("📦 Total Order (+ baru)", len(all_jobs_new))
                        new_col2.metric("✅ Tepat Waktu", len(all_jobs_new) - pesanan_telat_new)
                        new_col3.metric("🚨 Terlambat", pesanan_telat_new, delta_color="inverse")

                        # Estimasi selesai order baru
                        selesai_baru_dt = konversi_ke_jam_dinding(sa_new_end.get(nb_id_clean, 0), start_date)
                        if nb_due_input:
                            terlambat_baru = sa_new_end.get(nb_id_clean, 0) > nb_target_mnt
                            status_baru    = "🔴 Terlambat" if terlambat_baru else "🟢 Tepat Waktu"
                        else:
                            status_baru    = "ℹ️ Due date tidak diisi"

                        with st.container(border=True):
                            st.markdown(
                                f"### 📦 Order Baru: `{nb_id_clean}`\n"
                                f"- **Estimasi Selesai:** {selesai_baru_dt.strftime('%A, %d %B %Y pukul %H:%M')}\n"
                                f"- **Status:** {status_baru}"
                            )
                            if nb_due_input:
                                # Rekomendasi due date dengan buffer 1 hari kerja
                                buf_dt = konversi_ke_jam_dinding(
                                    sa_new_end.get(nb_id_clean, 0) + MENIT_PER_HARI, start_date)
                                st.caption(
                                    f"💡 Rekomendasi due date untuk order ini: "
                                    f"**{buf_dt.strftime('%d %B %Y')}** (+1 hari kerja buffer)"
                                )

                        # ── Tabel perbandingan status semua order ──
                        st.markdown("#### 📋 Status Semua Order Setelah Re-Optimasi")
                        rows_cmp = []
                        for i in all_jobs_new:
                            d_mnt    = D_all.get(i, 99999)
                            sel_mnt  = sa_new_end.get(i, 0)
                            sel_dt   = konversi_ke_jam_dinding(sel_mnt, start_date)
                            tgt_str  = konversi_ke_jam_dinding(d_mnt, start_date).strftime('%d-%b-%y %H:%M') \
                                       if d_mnt < 99999 else "—"
                            telat    = sel_mnt > d_mnt
                            selisih  = math.ceil(max(0, sel_mnt - d_mnt) / MENIT_PER_HARI)
                            rows_cmp.append({
                                'ID Pesanan'        : i,
                                'Jenis'             : '🆕 Order Baru' if i == nb_id_clean else
                                                      ('🔒 Terkunci' if i in locked_set else '📋 Existing'),
                                'Target Selesai'    : tgt_str,
                                'Estimasi Selesai'  : sel_dt.strftime('%d-%b-%y %H:%M'),
                                'Status'            : '🔴 Terlambat' if telat else '🟢 Tepat Waktu',
                                'Selisih (Hari)'    : selisih,
                            })
                        st.dataframe(pd.DataFrame(rows_cmp), hide_index=True, use_container_width=True)

                        # ── Gantt gabungan dengan toggle ──
                        st.markdown("#### 📊 Gantt Chart Jadwal Gabungan (Existing + Order Baru)")
                        render_gantt_dual(
                            df_gantt_new,
                            title=f"Re-Optimasi SA: {len(all_jobs_new)} Order (incl. {nb_id_clean})",
                            chart_key="gantt_reopt",
                            height=560,
                        )

            # ============================================================
            # 16. DOWNLOAD EXCEL
            # ============================================================
            st.divider()
            st.subheader("📥 Unduh Rekap Excel")

            buf = io.BytesIO()
            with pd.ExcelWriter(buf, engine='openpyxl') as writer:
                df_laporan.to_excel(writer, sheet_name='Laporan Manajemen',  index=False)
                df_op.to_excel(writer,      sheet_name='Jadwal per Stasiun', index=False)
                df_gantt_edd.drop(columns=['Status'], errors='ignore').to_excel(
                    writer, sheet_name='Benchmark EDD',  index=False)
                df_gantt_fcfs.drop(columns=['Status'], errors='ignore').to_excel(
                    writer, sheet_name='Benchmark FCFS', index=False)

            st.download_button(
                "⬇️ Download Laporan .xlsx",
                data=buf.getvalue(),
                file_name=f"Jadwal_Pabrik_{datetime.now().strftime('%d%b%Y_%H%M')}.xlsx",
                mime="application/vnd.ms-excel",
                type="secondary",
            )

    except Exception as e:
        st.error(f"🚨 Terjadi kesalahan: {e}")
        import traceback
        st.code(traceback.format_exc(), language="text")
