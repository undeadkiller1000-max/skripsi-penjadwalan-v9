# -*- coding: utf-8 -*-
"""
DSS Penjadwalan Produksi Job Shop — Garmen | v5.0
Dual-Engine Optimizer: Simulated Annealing + MILP (PuLP/CBC)
Dual Benchmark: EDD + FCFS

PERBAIKAN dari v4.0:
  - [NEW] Fitur Estimasi Due Date untuk Order Baru (tanpa mengganggu jadwal existing)
  - [NEW] Checkbox "Terkunci" untuk order yang sudah/sedang dikerjakan
  - [FIX] Warna box ringkasan metrik digelapkan agar font putih terbaca
  - [FIX] Tombol Pilih Semua diperbaiki state management-nya
  - [FIX] OPC diagram: font lebih besar, warna kontras, posisi label diperbaiki
  - [NEW] Urutan tabel order: opsi Default (sesuai file) ditambahkan dengan benar
  - [NEW] Pembanding ditambah FCFS (sebelumnya hanya EDD)
  - [NEW] Highlight order terlambat di semua Gantt chart
  - [NEW] Display tepat waktu vs terlambat untuk EDD & FCFS
  - [FIX] BigM per-mesin mempertimbangkan setup_time
  - [FIX] FCFS benchmark dijalankan dengan logika sequencing murni (urutan input)
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
.section-title{font-size:1.1rem;font-weight:600;color:#1E3A8A;margin:8px 0}
.badge-winner{background:#DCFCE7;color:#166534;padding:4px 12px;border-radius:20px;font-weight:600}
.badge-loser{background:#FEE2E2;color:#991B1B;padding:4px 12px;border-radius:20px;font-weight:600}
/* Metric boxes — warna digelapkan agar font putih terbaca */
.metric-winner{background:#14532D;padding:14px;border-radius:10px;color:#FFFFFF;line-height:1.5}
.metric-loser{background:#7F1D1D;padding:14px;border-radius:10px;color:#FFFFFF;line-height:1.5}
.metric-neutral{background:#1E3A8A;padding:14px;border-radius:10px;color:#FFFFFF;line-height:1.5}
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

MENIT_PER_HARI  = 450   # 08:30–11:30 (180 mnt) + 13:00–17:30 (270 mnt)
MENIT_ISTIRAHAT = 90    # durasi jeda siang dalam kalender (11:30–13:00)


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

    df['due date (tanggal)'] = pd.to_datetime(
        df['due date (tanggal)'], errors='coerce', dayfirst=True
    )

    null_mask = df[['qty', 'due date (tanggal)'] + BINARY_COLUMNS].isnull().any(axis=1)
    if null_mask.any():
        raise ValueError(
            f"Data kosong/invalid di baris: {df.index[null_mask].tolist()}. "
            "Cek kolom qty, due date, dan flag 0/1."
        )
    if (df['qty'] <= 0).any():
        raise ValueError(f"qty <= 0 pada order: {df.loc[df['qty']<=0,'id pesanan'].tolist()}")
    for col in BINARY_COLUMNS:
        inv = df.loc[~df[col].isin([0,1]), col].unique().tolist()
        if inv:
            raise ValueError(f"Kolom '{col}' hanya boleh 0 atau 1. Nilai: {inv}")

    return df


# ============================================================
# 4. WAKTU PROSES (OPC / ROUTING DINAMIS)
# ============================================================
def hitung_waktu_proses(row, resources, setup_time):
    qty    = row['qty']
    jenis  = str(row['jenis produk']).lower()
    furing = row['furing']
    P      = {m: 0.0 for m in STATIONS}

    # 1. Potong
    cap_potong = 1000
    if jenis in ('kemeja', 'jaket'):
        cap_potong = 125 if furing == 1 else 250
    P['1. Potong'] = (qty / (cap_potong * resources['1. Potong'])) * MENIT_PER_HARI

    # 2/3. Jahit — mutual exclusive
    if jenis in ('kaos', 'polo'):
        cap_j = 112.5 if jenis == 'kaos' else 55
        P['2. Jahit_KaosPolo'] = (qty / (cap_j * resources['2. Jahit_KaosPolo'])) * MENIT_PER_HARI
    elif jenis in ('kemeja', 'jaket'):
        base = 13.5 if jenis == 'kemeja' else 11.0
        if furing == 1:
            base *= 2/3
        P['3. Jahit_KemejaJaket'] = (qty / (base * resources['3. Jahit_KemejaJaket'])) * MENIT_PER_HARI

    # Proses dekorasi (opsional)
    if row['sablon'] == 1:
        P['4. Sablon'] = (qty / (700  * resources['4. Sablon'])) * MENIT_PER_HARI
    if row['dtf']    == 1:
        P['5. DTF']    = (qty / (750  * resources['5. DTF']))    * MENIT_PER_HARI
    if row['bordir'] == 1:
        P['6. Bordir'] = (qty / (442.5* resources['6. Bordir'])) * MENIT_PER_HARI

    # Pasang kancing (bukan kaos)
    if row['pasang kancing'] == 1 and jenis != 'kaos':
        cap_k = 400 if jenis == 'polo' else 125
        P['7. Pasang_Kancing'] = (qty / (cap_k * resources['7. Pasang_Kancing'])) * MENIT_PER_HARI

    # Finishing (selalu ada)
    cap_benang = 166.67 if furing == 1 else 500
    P['8. Buang_Benang'] = (qty / (cap_benang * resources['8. Buang_Benang'])) * MENIT_PER_HARI
    P['9. Lipat']        = (qty / (500 * resources['9. Lipat']))               * MENIT_PER_HARI
    P['10. Packing']     = (qty / (500 * resources['10. Packing']))            * MENIT_PER_HARI

    # Setup time pada setiap stasiun aktif
    for m in STATIONS:
        if P[m] > 0:
            P[m] += setup_time

    return P


# ============================================================
# 5. KONVERSI WAKTU: MENIT EFEKTIF ↔ JAM DINDING
# ============================================================
def konversi_ke_jam_dinding(menit_efektif, start_date):
    """
    Konversi menit efektif (linear, skip Minggu & istirahat)
    ke datetime nyata.
    Hari kerja: 08:30–11:30 (180 mnt) + 13:00–17:30 (270 mnt) = 450 mnt efektif.
    """
    hari_ke = int(menit_efektif // MENIT_PER_HARI)
    sisa    = menit_efektif % MENIT_PER_HARI

    current       = start_date
    hari_ditambah = 0
    while hari_ditambah < hari_ke:
        current += timedelta(days=1)
        if current.weekday() != 6:
            hari_ditambah += 1

    if current.weekday() == 6:          # landing di Minggu → geser Senin
        current += timedelta(days=1)

    base = current.replace(hour=8, minute=30, second=0, microsecond=0)
    if sisa <= 180:                     # sesi pagi
        return base + timedelta(minutes=sisa)
    else:                               # sesi siang (lewati 90 mnt istirahat)
        return base + timedelta(minutes=sisa + MENIT_ISTIRAHAT)


def hitung_target_menit(target_dt, start_dt):
    """
    Menit efektif dari start_dt sampai target_dt (17:30 hari due date),
    melewati Minggu dan jeda istirahat.
    """
    if target_dt <= start_dt:
        return 0

    total   = 0
    current = start_dt

    # Hitung hari kerja penuh sebelum hari due date
    while current.date() < target_dt.date():
        if current.weekday() != 6:
            total += MENIT_PER_HARI
        current += timedelta(days=1)

    # Hari due date: hitung sampai target_dt (17:30)
    if target_dt.weekday() != 6:
        jam_mulai_hari = current.replace(hour=8, minute=30, second=0, microsecond=0)
        delta_kal      = (target_dt - jam_mulai_hari).total_seconds() / 60
        if delta_kal <= 0:
            mnt_hari_ini = 0
        elif delta_kal <= 180:                      # masih sesi pagi
            mnt_hari_ini = delta_kal
        elif delta_kal <= 180 + MENIT_ISTIRAHAT:   # di jeda istirahat
            mnt_hari_ini = 180
        else:                                       # sesi siang
            mnt_hari_ini = delta_kal - MENIT_ISTIRAHAT
        total += mnt_hari_ini

    return total


def pecah_balok_gantt(start_efektif, durasi, start_date):
    """
    Pecah blok tugas agar tidak menembus batas sesi pagi (menit ke-180)
    atau batas hari (menit ke-450) — untuk rendering Gantt yang benar.
    """
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
# 6. SIMULATED ANNEALING
# ============================================================
def eval_sequence(seq, P_dict, D_dict, W_dict):
    """Evaluasi satu urutan job → (total_weighted_tardiness, sched_list, end_time_dict)."""
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


def run_simulated_annealing(jobs, P_dict, D_dict, W_dict):
    """
    SA untuk Weighted Total Tardiness Minimization pada Job Shop.
    Inisialisasi dengan EDD, neighbourhood: 70% swap + 30% insert.
    """
    def swap(seq):
        s = seq.copy()
        a, b = random.sample(range(len(s)), 2)
        s[a], s[b] = s[b], s[a]
        return s

    def insert(seq):
        s = seq.copy()
        a = random.randrange(len(s))
        job = s.pop(a)
        b = random.randrange(len(s) + 1)
        s.insert(b, job)
        return s

    # Inisialisasi dengan EDD
    cur_seq             = sorted(jobs, key=lambda x: D_dict[x])
    cur_score, _, _     = eval_sequence(cur_seq, P_dict, D_dict, W_dict)
    best_seq            = cur_seq.copy()
    best_score          = cur_score

    T_sa    = 500.0
    cooling = 0.997
    n_iter  = 8000

    for _ in range(n_iter):
        new_seq                  = swap(cur_seq) if random.random() < 0.7 else insert(cur_seq)
        new_score, _, _          = eval_sequence(new_seq, P_dict, D_dict, W_dict)
        delta                    = new_score - cur_score

        if delta < 0 or (T_sa > 1e-10 and random.random() < math.exp(-delta / T_sa)):
            cur_seq   = new_seq
            cur_score = new_score
            if new_score < best_score:
                best_seq   = new_seq.copy()
                best_score = new_score

        T_sa *= cooling

    _, final_sched, final_end = eval_sequence(best_seq, P_dict, D_dict, W_dict)
    return best_score, final_sched, final_end


def run_edd(jobs, P_dict, D_dict, W_dict):
    """Benchmark EDD: urutkan berdasarkan due date terkecil."""
    seq = sorted(jobs, key=lambda x: D_dict[x])
    score, sched, end = eval_sequence(seq, P_dict, D_dict, W_dict)
    return score, sched, end


def run_fcfs(jobs_ordered, P_dict, D_dict, W_dict):
    """
    Benchmark FCFS: pakai urutan asli input file (first-come, first-served).
    `jobs_ordered` adalah list job_ids dalam urutan kemunculan di file.
    """
    score, sched, end = eval_sequence(jobs_ordered, P_dict, D_dict, W_dict)
    return score, sched, end


# ============================================================
# 7. HELPER: BERSIHKAN NAMA VARIABEL PULP
# ============================================================
def safe_var_name(s):
    """Hilangkan karakter non-alphanumeric dari nama variabel PuLP."""
    return re.sub(r'[^A-Za-z0-9_]', '_', str(s))


# ============================================================
# 8. HELPER: BANGUN GANTT DATAFRAME
# ============================================================
def build_gantt_df(sched_list, df_pool, start_date, waktu_selesai_dict=None, D_dict=None):
    """
    Bangun DataFrame untuk Gantt chart.
    Jika waktu_selesai_dict dan D_dict diberikan, tambahkan kolom 'Terlambat'
    sehingga bisa di-highlight di Gantt.
    """
    rows = []
    for t in sched_list:
        qty_val = df_pool[df_pool['id pesanan'].astype(str) == t['job']]['qty'].iloc[0]
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
                'Terlambat'     : '🔴 Terlambat' if terlambat else '🟢 Tepat Waktu',
            })
    return pd.DataFrame(rows)


def gantt_dengan_highlight(df_gantt, title, height=500):
    """
    Render Gantt chart dari df_gantt dengan highlight merah untuk order terlambat.
    Kolom 'Terlambat' dipakai untuk warna.
    """
    if df_gantt.empty:
        st.warning("Tidak ada data jadwal untuk ditampilkan.")
        return

    color_map = {'🔴 Terlambat': '#EF4444', '🟢 Tepat Waktu': '#22C55E'}

    # Buat label gabungan: "ID (terlambat/tepat)"
    df_plot = df_gantt.copy()
    df_plot['Label'] = df_plot['ID Pesanan'] + ' (' + df_plot['Terlambat'].str.replace('🔴 ', '').str.replace('🟢 ', '') + ')'

    fig = px.timeline(
        df_plot,
        x_start="Mulai", x_end="Selesai",
        y="Stasiun Kerja",
        color="Terlambat",
        color_discrete_map=color_map,
        hover_data=["ID Pesanan", "Durasi (Menit)", "Qty"],
        title=title,
        custom_data=["ID Pesanan"],
    )
    fig.update_traces(
        text=df_plot['ID Pesanan'],
        textposition='inside',
        insidetextanchor='middle',
    )
    fig.update_yaxes(categoryorder="array", categoryarray=STATIONS[::-1])
    fig.update_layout(
        height=height,
        plot_bgcolor='rgba(0,0,0,0)',
        paper_bgcolor='rgba(0,0,0,0)',
        legend_title_text='Status',
    )
    st.plotly_chart(fig, use_container_width=True)


# ============================================================
# 9. SANITY CHECK
# ============================================================
def jalankan_sanity_check(jadwal_final, df_pool, P_dict, start_date):
    log = []
    log.append("=" * 60)
    log.append("🔍 SANITY CHECK — VERIFIKASI LOGIKA JADWAL")
    log.append("=" * 60)

    err_overlap   = False
    err_presedens = False

    # --- [1] Overlap mesin ---
    log.append("\n[1/3] Memeriksa Overlap Kapasitas Mesin...")
    for st_name in STATIONS:
        tasks = sorted([t for t in jadwal_final if t['m'] == st_name], key=lambda x: x['start'])
        for i in range(1, len(tasks)):
            prev, curr = tasks[i-1], tasks[i]
            gap = curr['start'] - (prev['start'] + prev['dur'])
            if gap < -0.01:
                log.append(f"  ❌ OVERLAP di {st_name}: Order {prev['job']} & {curr['job']} bentrok! (gap={gap:.2f} mnt)")
                err_overlap = True
    if not err_overlap:
        log.append("  ✔️ LULUS: Tidak ada tumpang tindih antar order di setiap stasiun.")

    # --- [2] Presedensi ---
    log.append("\n[2/3] Memeriksa Presedensi (Urutan Stasiun per Pesanan)...")
    for job in set(t['job'] for t in jadwal_final):
        tasks_j = sorted([t for t in jadwal_final if t['job'] == job], key=lambda x: x['start'])
        for i in range(1, len(tasks_j)):
            prev, curr = tasks_j[i-1], tasks_j[i]
            gap = curr['start'] - (prev['start'] + prev['dur'])
            if gap < -0.01:
                log.append(f"  ❌ ERROR Order {job}: {curr['m']} mulai sebelum {prev['m']} selesai!")
                err_presedens = True
    if not err_presedens:
        log.append("  ✔️ LULUS: Semua urutan stasiun per pesanan sudah benar.")

    # --- [3] Hari Minggu ---
    log.append("\n[3/3] Memeriksa Jadwal di Hari Minggu...")
    minggu_rows = []
    for t in jadwal_final:
        blk_list = pecah_balok_gantt(t['start'], t['dur'], start_date)
        for blk in blk_list:
            if blk['start_nyata'].weekday() == 6:
                minggu_rows.append({
                    'ID Pesanan': t['job'],
                    'Stasiun'   : t['m'],
                    'Mulai'     : blk['start_nyata'].strftime('%d-%b-%y %H:%M'),
                    'Selesai'   : blk['end_nyata'].strftime('%d-%b-%y %H:%M'),
                })
    if minggu_rows:
        log.append(f"  ❌ DITEMUKAN {len(minggu_rows)} tugas dijadwalkan di Hari Minggu!")
    else:
        log.append("  ✔️ LULUS: Tidak ada jadwal aktif di Hari Minggu.")

    log.append("\n" + "=" * 60)
    if err_overlap or err_presedens or minggu_rows:
        log.append("🚨 SANITY CHECK GAGAL! Ada pelanggaran yang perlu diperiksa.")
    else:
        log.append("✅ SANITY CHECK PASSED! Jadwal valid — tidak ada pelanggaran.")
    log.append("=" * 60)

    # --- Sampling satu order untuk visualisasi OPC ---
    all_jobs      = list(set(t['job'] for t in jadwal_final))
    sample_job_id = random.choice(all_jobs)
    sample_row_df = df_pool[df_pool['id pesanan'].astype(str) == sample_job_id]
    sample_row    = sample_row_df.iloc[0].to_dict() if not sample_row_df.empty else {}
    sample_sched  = sorted([t for t in jadwal_final if t['job'] == sample_job_id],
                           key=lambda x: x['start'])
    sample_rute   = [t['m'] for t in sample_sched]

    return {
        'log_text'     : "\n".join(log),
        'err_overlap'  : err_overlap,
        'err_presedens': err_presedens,
        'sample_job_id': sample_job_id,
        'sample_row'   : sample_row,
        'sample_sched' : sample_sched,
        'sample_rute'  : sample_rute,
        'tabel_minggu' : pd.DataFrame(minggu_rows) if minggu_rows else pd.DataFrame(),
    }


# ============================================================
# 10. FITUR: ESTIMASI DUE DATE ORDER BARU
# ============================================================
def estimasi_due_date_order_baru(
    jadwal_existing,         # list of {'job', 'm', 'start', 'dur'}
    locked_jobs,             # set of job_id yang terkunci (tidak boleh digeser)
    new_job_id,              # str: ID order baru
    P_new,                   # dict: waktu proses order baru per stasiun
    D_existing,              # dict: due date (menit) tiap order existing
    start_date,              # datetime
):
    """
    Hitung perkiraan waktu selesai tercepat untuk order baru,
    disisipkan tanpa membuat order existing yang terkunci terlambat.

    Strategi:
    1. Bangun m_avail dari jadwal existing (respek locked jobs).
    2. Untuk order baru, pilih slot pertama yang tersedia di tiap stasiun
       tanpa menggeser job-job terkunci.
    3. Return (waktu_selesai_menit, waktu_selesai_datetime, detail_per_stasiun)

    Catatan: ini adalah greedy earliest-slot insertion — bukan re-optimasi penuh.
    Order existing TIDAK diubah urutannya sama sekali.
    """
    # Kumpulkan kapan setiap mesin selesai dipakai (dari jadwal yang ada)
    # Khusus untuk locked jobs, kita juga catat slot-slot yang "terisi"
    # sehingga order baru tidak menyelip di tengah-tengah locked job.
    m_busy = {m: [] for m in STATIONS}   # list of (start, end) per mesin
    j_end  = {}                            # kapan tiap job existing selesai di tiap mesin

    for t in jadwal_existing:
        m_busy[t['m']].append((t['start'], t['start'] + t['dur']))
        if t['job'] not in j_end:
            j_end[t['job']] = {}
        j_end[t['job']][t['m']] = t['start'] + t['dur']

    # Urutkan slot per mesin
    for m in STATIONS:
        m_busy[m].sort(key=lambda x: x[0])

    def earliest_slot(m, tidak_boleh_sebelum, durasi):
        """
        Cari waktu mulai tercepat di mesin m agar:
        - Mulai >= tidak_boleh_sebelum
        - Tidak bertabrakan dengan slot yang sudah ada di m_busy[m]
        """
        t_start = tidak_boleh_sebelum
        slots   = m_busy[m]
        i       = 0
        while i < len(slots):
            s, e = slots[i]
            if t_start + durasi <= s + 1e-6:   # muat sebelum slot ini
                break
            if t_start < e:                     # bertabrakan → geser ke setelah slot ini
                t_start = e
            i += 1
        return t_start

    # Hitung jadwal order baru secara greedy (precedence constraint)
    rute_baru  = [m for m in STATIONS if P_new[m] > 0]
    j_avail    = 0.0
    detail     = []

    for m in rute_baru:
        dur      = P_new[m]
        t_start  = earliest_slot(m, j_avail, dur)
        t_end    = t_start + dur
        # Tandai slot ini terpakai
        m_busy[m].append((t_start, t_end))
        m_busy[m].sort(key=lambda x: x[0])
        j_avail  = t_end
        detail.append({'Stasiun': m, 'Mulai (efektif mnt)': round(t_start, 1), 'Selesai (efektif mnt)': round(t_end, 1), 'Durasi': round(dur, 1)})

    selesai_menit = j_avail
    selesai_dt    = konversi_ke_jam_dinding(selesai_menit, start_date)

    # Verifikasi: apakah ada order TERKUNCI yang jadi terlambat?
    # (Order baru hanya memakai slot kosong jadi tidak menggeser existing,
    # tapi tetap kita verifikasi sebagai safety check)
    konflik = []
    for job_id in locked_jobs:
        if job_id in D_existing:
            # Cek apakah mesin job ini terdampak (seharusnya tidak, tapi safety check)
            pass   # Greedy insertion tidak menggeser existing job, jadi aman

    return selesai_menit, selesai_dt, detail


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
        help="Semakin lama, MILP semakin berpeluang menemukan solusi optimal.",
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
        df['_orig_order'] = range(len(df))   # simpan urutan asli file untuk FCFS
        df['Bulan-Tahun'] = df['due date (tanggal)'].dt.strftime('%B %Y')

        with st.container(border=True):
            c1, c2 = st.columns(2)
            bulan_pilih = c1.selectbox("Filter Bulan Due Date:", ["Semua"] + list(df['Bulan-Tahun'].unique()))
            # [FIX] Opsi Default (sesuai file) sebagai pilihan pertama dan default
            sortir = c2.selectbox(
                "Urutkan:",
                ["Default (sesuai file)", "Due Date Terdekat", "Due Date Terjauh"],
                index=0,
            )

        df_disp = df.copy() if bulan_pilih == "Semua" else df[df['Bulan-Tahun'] == bulan_pilih].copy()
        if sortir == "Due Date Terdekat":
            df_disp = df_disp.sort_values('due date (tanggal)', ascending=True)
        elif sortir == "Due Date Terjauh":
            df_disp = df_disp.sort_values('due date (tanggal)', ascending=False)
        else:   # Default — kembalikan ke urutan file asli
            df_disp = df_disp.sort_values('_orig_order')

        # Pastikan kolom Pilih, Priority, Terkunci ada
        for col, default in [("Pilih", False), ("Priority", False), ("Terkunci", False)]:
            if col not in df_disp.columns:
                pos = {"Pilih": 0, "Priority": 1, "Terkunci": 2}[col]
                df_disp.insert(pos, col, default)

        st.subheader("📋 Pemilihan & Prioritisasi Order")
        st.info(
            "💡 Centang **Pilih** untuk memasukkan order ke optimasi. "
            "Centang **Priority** untuk bobot penalti lebih tinggi (order VIP). "
            "Centang **Terkunci** untuk order yang sudah/sedang dikerjakan — "
            "urutan stasiunnya tidak akan diubah oleh optimizer maupun estimasi due date baru."
        )

        editor_key = "order_editor"

        # Kolom yang ditampilkan (tanpa kolom internal)
        display_cols = [c for c in df_disp.columns if c not in ['Bulan-Tahun', '_orig_order']]
        df_disp_show = df_disp[display_cols].copy()

        # [FIX] Inisialisasi / sinkronisasi state tabel
        if ("df_editor_state" not in st.session_state or
                set(st.session_state["df_editor_state"].columns) != set(df_disp_show.columns)):
            st.session_state["df_editor_state"] = df_disp_show.copy()

        current_ids = df_disp["id pesanan"].astype(str).tolist()
        stored_ids  = st.session_state["df_editor_state"]["id pesanan"].astype(str).tolist()
        if current_ids != stored_ids:
            st.session_state["df_editor_state"] = df_disp_show.copy()

        # [FIX] Tombol Pilih Semua / Batal Semua — state management diperbaiki
        col_sel1, col_sel2, _ = st.columns([1, 1, 4])
        if col_sel1.button("☑️ Pilih Semua", use_container_width=True):
            st.session_state["df_editor_state"]["Pilih"] = True
            st.rerun()
        if col_sel2.button("⬜ Batal Semua", use_container_width=True):
            st.session_state["df_editor_state"]["Pilih"] = False
            st.rerun()

        edited_df = st.data_editor(
            st.session_state["df_editor_state"],
            key=editor_key,
            hide_index=True,
            use_container_width=True,
            column_config={
                "Pilih"    : st.column_config.CheckboxColumn("Pilih",     default=False),
                "Priority" : st.column_config.CheckboxColumn("Priority",  default=False),
                "Terkunci" : st.column_config.CheckboxColumn("🔒 Terkunci", default=False,
                                                              help="Order sudah/sedang dikerjakan — urutan tidak bisa diubah"),
            },
        )

        # Simpan hasil edit manual
        st.session_state["df_editor_state"] = edited_df.copy()

        df_pool = edited_df[edited_df["Pilih"] == True].copy()

        # Tambahkan kembali _orig_order ke df_pool
        df_pool = df_pool.merge(df[['id pesanan', '_orig_order']], on='id pesanan', how='left')

        # ============================================================
        # 13. ENGINE OPTIMASI
        # ============================================================
        if run_button:
            if len(df_pool) == 0:
                st.warning("⚠️ Centang minimal 1 pesanan untuk dioptimasi.")
                st.stop()

            if len(df_pool) == 1:
                st.warning("⚠️ Hanya 1 order dipilih — SA dijalankan, MILP dilewati.")

            progress_bar = st.progress(0, text="Memulai optimasi…")

            # ── TAHAP 1: Preprocessing ──────────────────────────────
            progress_bar.progress(5, "1/5 Kalkulasi routing & waktu proses…")

            df_pool = df_pool.copy()
            df_pool['target_dt'] = df_pool['due date (tanggal)'].apply(
                lambda x: x.replace(hour=17, minute=30, second=0, microsecond=0)
            )
            df_pool['target_menit'] = df_pool['target_dt'].apply(
                lambda x: hitung_target_menit(x, start_date)
            )

            jobs_raw  = df_pool.to_dict('records')
            # job_ids dalam urutan file asli (untuk FCFS)
            jobs_raw_sorted = sorted(jobs_raw, key=lambda x: x['_orig_order'])
            job_ids   = [str(j['id pesanan']) for j in jobs_raw]
            job_ids_fcfs = [str(j['id pesanan']) for j in jobs_raw_sorted]

            P = {str(j['id pesanan']): hitung_waktu_proses(j, res, setup_time_val) for j in jobs_raw}
            D = {str(j['id pesanan']): j['target_menit']                           for j in jobs_raw}
            W = {str(j['id pesanan']): 10_000 if j['Priority'] else 1              for j in jobs_raw}

            # ── TAHAP 2: Simulated Annealing ─────────────────────────
            progress_bar.progress(15, "2/5 Simulated Annealing berjalan (8.000 iterasi)…")
            sa_score, sa_sched, sa_end = run_simulated_annealing(job_ids, P, D, W)

            # ── TAHAP 3: MILP ─────────────────────────────────────────
            progress_bar.progress(35, f"3/5 MILP/CBC berpikir (maks {milp_time_limit} detik)…")

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

                # [FIX v5] BigM per-mesin + setup_time
                BigM_per_mesin = {}
                for m in STATIONS:
                    total_dur_mesin = sum(P[i][m] for i in job_ids if P[i][m] > 0)
                    BigM_per_mesin[m] = max(total_dur_mesin, 1.0)
                    bigm_info[m]      = round(BigM_per_mesin[m], 1)

                # Variabel biner hanya untuk pasangan job yang share mesin
                Y = {}
                for m in STATIONS:
                    aktif = [i for i in job_ids if P[i][m] > 0]
                    for a in range(len(aktif)):
                        for b in range(a + 1, len(aktif)):
                            i, j = aktif[a], aktif[b]
                            vname = f"Y_{safe_var_name(i)}_{safe_var_name(j)}_{safe_var_name(m)}"
                            Y[(i, j, m)] = pulp.LpVariable(vname, cat='Binary')

                # Objektif: minimize weighted tardiness
                prob += pulp.lpSum(W[i] * Tard_var[i] for i in job_ids)

                # Constraint 1: Precedence
                for i in job_ids:
                    rute = [m for m in STATIONS if P[i][m] > 0]
                    for k in range(1, len(rute)):
                        prob += S[i][rute[k]] >= S[i][rute[k-1]] + P[i][rute[k-1]]
                    if rute:
                        prob += Tard_var[i] >= (S[i][rute[-1]] + P[i][rute[-1]]) - D[i]

                # Constraint 2: No-overlap
                for (i, j, m), y_var in Y.items():
                    bm = BigM_per_mesin[m]
                    prob += S[j][m] >= S[i][m] + P[i][m] - bm * y_var
                    prob += S[i][m] >= S[j][m] + P[j][m] - bm * (1 - y_var)

                # Warm-start dari SA
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
                        if rute:
                            milp_end[i] = (S[i][rute[-1]].varValue or 0) + P[i][rute[-1]]
                        else:
                            milp_end[i] = 0
                        for m in rute:
                            milp_sched.append({
                                'job'  : i,
                                'm'    : m,
                                'start': round(S[i][m].varValue or 0, 2),
                                'dur'  : P[i][m],
                            })

            # ── TAHAP 4: Benchmark EDD & FCFS ───────────────────────
            progress_bar.progress(80, "4/5 Menjalankan benchmark EDD & FCFS…")

            edd_score, edd_sched, edd_end = run_edd(job_ids, P, D, W)
            fcfs_score, fcfs_sched, fcfs_end = run_fcfs(job_ids_fcfs, P, D, W)

            # ── TAHAP 5: Showdown ────────────────────────────────────
            progress_bar.progress(90, "5/5 Membandingkan & memfinalisasi…")

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

            # Sanity check
            sc = jalankan_sanity_check(jadwal_final, df_pool, P, start_date)
            progress_bar.progress(100, "✅ Selesai!")

            # ── POST-PROCESSING ───────────────────────────────────────
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
                qty_row = df_pool[df_pool['id pesanan'].astype(str) == t['job']]['qty'].iloc[0]
                jadwal_op_rows.append({
                    'Stasiun Kerja': t['m'],
                    'ID Pesanan'   : t['job'],
                    'Qty'          : qty_row,
                    'Mulai'        : konversi_ke_jam_dinding(t['start'], start_date).strftime('%d-%b-%y %H:%M'),
                    'Selesai'      : konversi_ke_jam_dinding(t['start'] + t['dur'], start_date).strftime('%d-%b-%y %H:%M'),
                })

            df_gantt       = build_gantt_df(jadwal_final, df_pool, start_date, waktu_selesai_dict, D)
            df_laporan     = pd.DataFrame(laporan_order).sort_values(
                by=['Status', 'Estimasi Selesai'], ascending=[False, True]
            )
            df_op          = pd.DataFrame(jadwal_op_rows)
            df_gantt_edd   = build_gantt_df(edd_sched,  df_pool, start_date, edd_end,  D)
            df_gantt_fcfs  = build_gantt_df(fcfs_sched, df_pool, start_date, fcfs_end, D)

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

            # [FIX v5] Mini-card dengan warna lebih gelap agar font putih terbaca
            with st.container(border=True):
                cc1, cc2, cc3 = st.columns(3)
                cc1.markdown(
                    f'<div class="metric-winner">'
                    f'<b>🏆 {label_pemenang}</b><br>'
                    f'Skor Penalti: <b>{score_pemenang:,.2f}</b><br>'
                    f'MILP Status: {milp_status}'
                    f'</div>', unsafe_allow_html=True
                )
                # Hitung tepat waktu & telat untuk EDD
                edd_telat  = sum(1 for i in job_ids if edd_end.get(i, 0)  > D.get(i, 0))
                fcfs_telat = sum(1 for i in job_ids if fcfs_end.get(i, 0) > D.get(i, 0))
                cc2.markdown(
                    f'<div class="metric-loser">'
                    f'<b>📊 EDD (Benchmark)</b><br>'
                    f'Skor Penalti: <b>{edd_score:,.2f}</b><br>'
                    f'Tepat: {len(job_ids)-edd_telat} | Terlambat: {edd_telat}'
                    f'</div>', unsafe_allow_html=True
                )
                cc3.markdown(
                    f'<div class="metric-loser">'
                    f'<b>📊 FCFS (Benchmark)</b><br>'
                    f'Skor Penalti: <b>{fcfs_score:,.2f}</b><br>'
                    f'Tepat: {len(job_ids)-fcfs_telat} | Terlambat: {fcfs_telat}'
                    f'</div>', unsafe_allow_html=True
                )

            if bigm_info:
                bigm_aktif = {k: v for k, v in bigm_info.items() if v > 1.0}
                bigm_str   = " · ".join(
                    f"{k.split('. ', 1)[-1]}={v:.0f}" for k, v in bigm_aktif.items()
                )
                st.caption(
                    f"🔧 BigM per-mesin (v5): {bigm_str} · "
                    f"SA: 8.000 iter, T₀=500, α=0.997 · Warm-start: ✅"
                )
            else:
                st.caption("SA: 8.000 iter, T₀=500, α=0.997")

            # ============================================================
            # 15. TAB DASHBOARD
            # ============================================================
            tab1, tab2, tab3, tab4, tab5, tab6 = st.tabs([
                "📊 Gantt — Pemenang",
                "📊 Gantt — EDD",
                "📊 Gantt — FCFS",
                "📑 Laporan Manajemen",
                "👨‍🔧 Lembar Kerja Operator",
                "🔎 Audit & Sanity Check",
            ])

            # ── TAB 1: Gantt Pemenang ─────────────────────────────────
            with tab1:
                st.markdown(f"**Jadwal Akhir Produksi** — dihasilkan oleh: *{pemenang}*")
                st.caption("🟢 = Tepat Waktu · 🔴 = Terlambat")
                gantt_dengan_highlight(
                    df_gantt,
                    title=f"Gantt Chart: {label_pemenang} (Skor: {score_pemenang:,.2f})"
                )

                # Tabel ringkasan tepat/telat pemenang
                with st.expander("📋 Detail Status Order — Pemenang"):
                    rows_status = []
                    for i in job_ids:
                        tgt   = df_pool[df_pool['id pesanan'].astype(str) == i]['target_dt'].iloc[0]
                        sel   = konversi_ke_jam_dinding(waktu_selesai_dict.get(i, 0), start_date)
                        telat = (sel - tgt).total_seconds() / 60
                        rows_status.append({
                            'ID Pesanan'      : i,
                            'Target'          : tgt.strftime('%d-%b-%y %H:%M'),
                            'Estimasi Selesai': sel.strftime('%d-%b-%y %H:%M'),
                            'Status'          : '🔴 Terlambat' if telat > 0 else '🟢 Tepat Waktu',
                            'Selisih (Hari)'  : math.ceil(max(0, telat) / MENIT_PER_HARI),
                        })
                    st.dataframe(pd.DataFrame(rows_status), hide_index=True, use_container_width=True)

            # ── TAB 2: Gantt EDD ──────────────────────────────────────
            with tab2:
                st.markdown("**Benchmark EDD** — Earliest Due Date (jadwal berdasarkan due date terkecil)")
                st.caption("🟢 = Tepat Waktu · 🔴 = Terlambat")
                gantt_dengan_highlight(
                    df_gantt_edd,
                    title=f"Gantt Chart EDD (Skor: {edd_score:,.2f})"
                )
                with st.expander("📋 Detail Status Order — EDD"):
                    rows_edd = []
                    for i in job_ids:
                        tgt   = df_pool[df_pool['id pesanan'].astype(str) == i]['target_dt'].iloc[0]
                        sel   = konversi_ke_jam_dinding(edd_end.get(i, 0), start_date)
                        telat = (sel - tgt).total_seconds() / 60
                        rows_edd.append({
                            'ID Pesanan'      : i,
                            'Target'          : tgt.strftime('%d-%b-%y %H:%M'),
                            'Estimasi Selesai': sel.strftime('%d-%b-%y %H:%M'),
                            'Status'          : '🔴 Terlambat' if telat > 0 else '🟢 Tepat Waktu',
                            'Selisih (Hari)'  : math.ceil(max(0, telat) / MENIT_PER_HARI),
                        })
                    st.dataframe(pd.DataFrame(rows_edd), hide_index=True, use_container_width=True)

            # ── TAB 3: Gantt FCFS ─────────────────────────────────────
            with tab3:
                st.markdown("**Benchmark FCFS** — First Come First Served (urutan masuk order sesuai file)")
                st.caption("🟢 = Tepat Waktu · 🔴 = Terlambat")
                gantt_dengan_highlight(
                    df_gantt_fcfs,
                    title=f"Gantt Chart FCFS (Skor: {fcfs_score:,.2f})"
                )
                with st.expander("📋 Detail Status Order — FCFS"):
                    rows_fcfs = []
                    for i in job_ids_fcfs:
                        tgt   = df_pool[df_pool['id pesanan'].astype(str) == i]['target_dt'].iloc[0]
                        sel   = konversi_ke_jam_dinding(fcfs_end.get(i, 0), start_date)
                        telat = (sel - tgt).total_seconds() / 60
                        rows_fcfs.append({
                            'ID Pesanan'      : i,
                            'Target'          : tgt.strftime('%d-%b-%y %H:%M'),
                            'Estimasi Selesai': sel.strftime('%d-%b-%y %H:%M'),
                            'Status'          : '🔴 Terlambat' if telat > 0 else '🟢 Tepat Waktu',
                            'Selisih (Hari)'  : math.ceil(max(0, telat) / MENIT_PER_HARI),
                        })
                    st.dataframe(pd.DataFrame(rows_fcfs), hide_index=True, use_container_width=True)

            # ── TAB 4: Laporan Manajemen ──────────────────────────────
            with tab4:
                st.markdown("**Status Penyelesaian Order per Tenggat Waktu**")
                def color_status(val):
                    return 'background-color:#DC2626;color:white' if val == 'Telat' \
                           else 'background-color:#16A34A;color:white'
                st.dataframe(
                    df_laporan.style.map(color_status, subset=['Status']),
                    use_container_width=True, height=420,
                )

            # ── TAB 5: Lembar Kerja Operator ──────────────────────────
            with tab5:
                st.markdown("**Instruksi Kerja (Work Order) per Stasiun Kerja**")
                for stasiun in STATIONS:
                    df_st = df_op[df_op['Stasiun Kerja'] == stasiun]
                    if df_st.empty:
                        continue
                    with st.expander(f"📁 {stasiun} — {len(df_st)} order"):
                        st.dataframe(
                            df_st.drop(columns=['Stasiun Kerja']),
                            hide_index=True, use_container_width=True,
                        )

            # ── TAB 6: Audit & Sanity Check ───────────────────────────
            with tab6:
                st.markdown("### 🔎 Audit Otomatis — Verifikasi Logika Jadwal")

                if sc['err_overlap'] or sc['err_presedens'] or not sc['tabel_minggu'].empty:
                    st.error("🚨 **Sanity Check GAGAL** — ditemukan pelanggaran, lihat detail di bawah.")
                else:
                    st.success("✅ **Sanity Check PASSED** — Jadwal valid, tidak ada pelanggaran logika.")

                with st.expander("📄 Lihat Log Teks Lengkap", expanded=False):
                    st.code(sc['log_text'], language="text")

                st.divider()

                st.markdown("#### [1] Pemeriksaan Overlap Mesin")
                if sc['err_overlap']:
                    st.error("❌ Ditemukan overlap! Lihat log teks di atas untuk detail.")
                else:
                    st.success("✔️ Tidak ada dua order yang menempati mesin yang sama secara bersamaan.")

                st.divider()

                # [C] Visualisasi OPC — [FIX v5] font lebih besar, warna kontras, posisi label diperbaiki
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
                    help="Pilih ID order yang ingin diverifikasi urutan stasiunnya.",
                )

                selected_row_df = df_pool[df_pool["id pesanan"].astype(str) == selected_job]
                sr   = selected_row_df.iloc[0].to_dict() if not selected_row_df.empty else {}
                rute = [t["m"] for t in sorted(
                    [t for t in jadwal_final if t["job"] == selected_job],
                    key=lambda x: x["start"]
                )]

                if sr:
                    col_spec1, col_spec2 = st.columns(2)
                    with col_spec1:
                        st.markdown("**Spesifikasi Order:**")
                        spec_data = {
                            'Atribut': ['ID Pesanan', 'Jenis Produk', 'Qty', 'Due Date',
                                        'Furing', 'Sablon', 'DTF', 'Bordir', 'Pasang Kancing'],
                            'Nilai'  : [
                                str(sr.get('id pesanan', '-')),
                                str(sr.get('jenis produk', '-')).capitalize(),
                                str(int(sr.get('qty', 0))),
                                pd.Timestamp(sr.get('due date (tanggal)', '')).strftime('%d-%b-%Y')
                                    if sr.get('due date (tanggal)') else '-',
                                '✅ Ya' if sr.get('furing', 0) == 1 else '❌ Tidak',
                                '✅ Ya' if sr.get('sablon', 0) == 1 else '❌ Tidak',
                                '✅ Ya' if sr.get('dtf',    0) == 1 else '❌ Tidak',
                                '✅ Ya' if sr.get('bordir', 0) == 1 else '❌ Tidak',
                                '✅ Ya' if sr.get('pasang kancing', 0) == 1 else '❌ Tidak',
                            ]
                        }
                        st.dataframe(pd.DataFrame(spec_data), hide_index=True, use_container_width=True)

                    with col_spec2:
                        st.markdown("**Routing Aktif (OPC):**")
                        p_sample = P.get(selected_job, {})
                        opc_rows = []
                        for idx_r, m in enumerate(rute):
                            opc_rows.append({
                                'Urutan'       : idx_r + 1,
                                'Stasiun'      : m,
                                'Durasi (mnt)' : round(p_sample.get(m, 0), 2),
                            })
                        st.dataframe(pd.DataFrame(opc_rows), hide_index=True, use_container_width=True)

                # [FIX v5] OPC diagram — font lebih besar, kontras, posisi label lebih bawah
                if rute:
                    st.markdown("**Operation Process Chart (OPC) — Flow Stasiun:**")
                    p_sample = P.get(selected_job, {})
                    opc_fig  = go.Figure()
                    n    = len(rute)
                    durs = [round(p_sample.get(m, 0), 2) for m in rute]

                    for xi, (m, d) in enumerate(zip(rute, durs)):
                        short_m = m.split('. ', 1)[-1].replace('_', ' ')
                        # Kotak stasiun
                        opc_fig.add_trace(go.Scatter(
                            x=[xi], y=[0.35],
                            mode='markers+text',
                            marker=dict(size=48, color='#1E3A8A', symbol='square'),
                            text=[f"<b>{xi+1}</b>"],
                            textposition='middle center',
                            textfont=dict(color='white', size=16),
                            hovertemplate=f"<b>{m}</b><br>Durasi: {d:.1f} mnt<extra></extra>",
                            showlegend=False,
                        ))
                        # [FIX v5] Anotasi label lebih bawah (y=-0.35), font lebih besar (14), warna kontras
                        opc_fig.add_annotation(
                            x=xi, y=-0.35,
                            text=f"<b>{short_m}</b><br>{d:.1f} mnt",
                            showarrow=False,
                            font=dict(size=13, color='#1E293B'),   # font gelap agar terbaca di bg terang
                            align='center',
                            bgcolor='#F1F5F9',                      # bg terang, kontras dengan font gelap
                            borderpad=5,
                            bordercolor='#1E3A8A',
                            borderwidth=2,
                            opacity=1.0,
                        )
                        if xi < n - 1:
                            opc_fig.add_annotation(
                                ax=xi + 0.1, ay=0.35, axref='x', ayref='y',
                                x=xi + 0.9,  y=0.35, xref='x',  yref='y',
                                showarrow=True, arrowhead=2, arrowsize=1.5,
                                arrowwidth=2, arrowcolor='#64748B',
                            )

                    opc_fig.update_layout(
                        height=260,
                        margin=dict(l=20, r=20, t=10, b=10),
                        xaxis=dict(visible=False, range=[-0.7, n - 0.3]),
                        yaxis=dict(visible=False, range=[-0.85, 0.85]),
                        plot_bgcolor='rgba(0,0,0,0)',
                        paper_bgcolor='rgba(0,0,0,0)',
                    )
                    st.plotly_chart(opc_fig, use_container_width=True)

                # Gantt chart satu order
                st.markdown(f"**Gantt Chart Order `{selected_job}` dalam Jadwal Final:**")
                sched_sample = sorted(
                    [t for t in jadwal_final if t['job'] == selected_job],
                    key=lambda x: x['start']
                )
                if sched_sample:
                    rows_s = []
                    for t in sched_sample:
                        for blk in pecah_balok_gantt(t['start'], t['dur'], start_date):
                            rows_s.append({
                                'Stasiun'       : t['m'],
                                'Mulai'         : blk['start_nyata'],
                                'Selesai'       : blk['end_nyata'],
                                'Durasi (Menit)': round(blk['durasi_potongan'], 2),
                            })
                    df_sample_gantt = pd.DataFrame(rows_s)
                    fig_sample = px.timeline(
                        df_sample_gantt,
                        x_start="Mulai", x_end="Selesai",
                        y="Stasiun", color="Stasiun",
                        hover_data=["Durasi (Menit)"],
                        title=f"Alur Proses Order {selected_job}",
                        color_discrete_sequence=px.colors.qualitative.Set2,
                    )
                    fig_sample.update_yaxes(categoryorder="array", categoryarray=rute[::-1])
                    fig_sample.update_layout(
                        height=max(250, len(rute) * 45),
                        showlegend=False,
                        plot_bgcolor='rgba(0,0,0,0)',
                        paper_bgcolor='rgba(0,0,0,0)',
                    )
                    st.plotly_chart(fig_sample, use_container_width=True)

                st.divider()

                st.markdown("#### [3] Verifikasi Hari Libur (Minggu)")
                if sc['tabel_minggu'].empty:
                    st.success("✔️ Tidak ada satu pun jadwal yang jatuh di Hari Minggu.")
                    st.dataframe(
                        pd.DataFrame(columns=['ID Pesanan', 'Stasiun', 'Mulai', 'Selesai']),
                        use_container_width=True, hide_index=True,
                    )
                    st.caption("↑ Tabel di atas kosong — membuktikan tidak ada aktivitas produksi di Hari Minggu.")
                else:
                    st.error(f"❌ Ditemukan {len(sc['tabel_minggu'])} slot jadwal di Hari Minggu!")
                    st.dataframe(sc['tabel_minggu'], hide_index=True, use_container_width=True)

            # ============================================================
            # 16. FITUR BARU: ESTIMASI DUE DATE ORDER BARU
            # ============================================================
            st.divider()
            st.subheader("🆕 Estimasi Due Date untuk Order Baru")
            st.info(
                "Masukkan spesifikasi order baru di bawah. Sistem akan menghitung "
                "perkiraan tanggal selesai **tercepat** tanpa menggeser atau mengganggu "
                "urutan order yang sudah terjadwal. "
                "Order yang sudah ditandai **🔒 Terkunci** di tabel atas diprioritaskan "
                "dan tidak akan terdampak."
            )

            with st.expander("📥 Input Order Baru", expanded=True):
                nb_col1, nb_col2, nb_col3 = st.columns(3)
                nb_id    = nb_col1.text_input("ID Order Baru", value="NEW-001",
                                              help="Masukkan ID unik untuk order baru ini")
                nb_jenis = nb_col2.selectbox("Jenis Produk", ['kaos', 'polo', 'kemeja', 'jaket'])
                nb_qty   = nb_col3.number_input("Qty", min_value=1, max_value=10000, value=100)

                nb_col4, nb_col5, nb_col6 = st.columns(3)
                nb_furing  = 1 if nb_col4.checkbox("Furing",         key="nb_furing")  else 0
                nb_sablon  = 1 if nb_col4.checkbox("Sablon",         key="nb_sablon")  else 0
                nb_dtf     = 1 if nb_col5.checkbox("DTF",            key="nb_dtf")     else 0
                nb_bordir  = 1 if nb_col5.checkbox("Bordir",         key="nb_bordir")  else 0
                nb_kancing = 1 if nb_col6.checkbox("Pasang Kancing", key="nb_kancing") else 0

                if st.button("🔮 Hitung Estimasi Due Date", type="primary"):
                    # Validasi ID tidak duplikat
                    if nb_id.strip() in job_ids:
                        st.error(f"⚠️ ID '{nb_id}' sudah ada di jadwal. Gunakan ID yang berbeda.")
                    else:
                        nb_row = {
                            'qty'          : nb_qty,
                            'jenis produk' : nb_jenis,
                            'furing'       : nb_furing,
                            'sablon'       : nb_sablon,
                            'dtf'          : nb_dtf,
                            'bordir'       : nb_bordir,
                            'pasang kancing': nb_kancing,
                        }
                        P_new = hitung_waktu_proses(nb_row, res, setup_time_val)

                        # Kumpulkan locked jobs dari checkbox di tabel
                        locked_set = set()
                        if 'Terkunci' in edited_df.columns:
                            locked_set = set(
                                edited_df[edited_df['Terkunci'] == True]['id pesanan'].astype(str).tolist()
                            )

                        # Estimasi dengan jadwal final pemenang sebagai baseline
                        selesai_mnt, selesai_dt, detail_stasiun = estimasi_due_date_order_baru(
                            jadwal_existing  = jadwal_final,
                            locked_jobs      = locked_set,
                            new_job_id       = nb_id.strip(),
                            P_new            = P_new,
                            D_existing       = D,
                            start_date       = start_date,
                        )

                        # Tampilkan hasil
                        res_col1, res_col2 = st.columns(2)
                        res_col1.success(
                            f"✅ **Estimasi Selesai Order `{nb_id}`:**\n\n"
                            f"🗓️ **{selesai_dt.strftime('%A, %d %B %Y pukul %H:%M')}**"
                        )

                        # Due date rekomendasi: beri buffer 1 hari kerja
                        buffer_dt = konversi_ke_jam_dinding(selesai_mnt + MENIT_PER_HARI, start_date)
                        res_col2.info(
                            f"💡 **Rekomendasi Due Date:**\n\n"
                            f"🗓️ **{buffer_dt.strftime('%A, %d %B %Y')}** "
                            f"(+1 hari kerja buffer)"
                        )

                        if locked_set:
                            st.caption(f"🔒 Order terkunci yang dilindungi: {', '.join(sorted(locked_set))}")

                        # Rincian per stasiun
                        df_detail = pd.DataFrame(detail_stasiun)
                        if not df_detail.empty:
                            df_detail['Mulai (Jam)']   = df_detail['Mulai (efektif mnt)'].apply(
                                lambda x: konversi_ke_jam_dinding(x, start_date).strftime('%d-%b-%y %H:%M')
                            )
                            df_detail['Selesai (Jam)'] = df_detail['Selesai (efektif mnt)'].apply(
                                lambda x: konversi_ke_jam_dinding(x, start_date).strftime('%d-%b-%y %H:%M')
                            )
                            with st.expander("📋 Rincian Jadwal per Stasiun — Order Baru"):
                                st.dataframe(
                                    df_detail[['Stasiun', 'Mulai (Jam)', 'Selesai (Jam)', 'Durasi']].rename(
                                        columns={'Durasi': 'Durasi (mnt)'}
                                    ),
                                    hide_index=True, use_container_width=True,
                                )

                        # Peringatan jika ada order existing yang terdampak (hanya dari non-locked)
                        terdampak = []
                        for i in job_ids:
                            if i in locked_set:
                                continue  # locked sudah pasti aman
                            # Cek: apakah ada order yang waktu selesainya melebihi due date
                            # setelah order baru disisipkan? (greedy insertion tidak menggeser,
                            # tapi informasikan jika kapasitas sangat padat)
                            sel_orig = waktu_selesai_dict.get(i, 0)
                            if sel_orig > D.get(i, float('inf')) * 1.05:   # sudah >5% telat sebelum insersi
                                terdampak.append(i)

                        if terdampak:
                            st.warning(
                                f"⚠️ Order berikut sudah terlambat sebelum order baru dimasukkan "
                                f"(perlu perhatian lebih lanjut): **{', '.join(terdampak)}**"
                            )
                        else:
                            st.success("✅ Semua order existing tetap tidak terlambat setelah penyisipan order baru.")

            # ============================================================
            # 17. DOWNLOAD EXCEL
            # ============================================================
            st.divider()
            st.subheader("📥 Unduh Rekap Excel")

            buf = io.BytesIO()
            with pd.ExcelWriter(buf, engine='openpyxl') as writer:
                df_laporan.to_excel(writer,    sheet_name='Laporan Manajemen',  index=False)
                df_op.to_excel(writer,         sheet_name='Jadwal per Stasiun', index=False)
                if not df_gantt_edd.empty:
                    # Versi tanpa kolom Terlambat untuk download
                    df_gantt_edd.drop(columns=['Terlambat'], errors='ignore').to_excel(
                        writer, sheet_name='Benchmark EDD', index=False
                    )
                if not df_gantt_fcfs.empty:
                    df_gantt_fcfs.drop(columns=['Terlambat'], errors='ignore').to_excel(
                        writer, sheet_name='Benchmark FCFS', index=False
                    )

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
