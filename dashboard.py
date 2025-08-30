import os, json, pickle, math, io, threading, time, hashlib
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from tkinter import font as tkfont
from datetime import datetime, timedelta

from oauth2client.service_account import ServiceAccountCredentials

import gspread
import pandas as pd
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

from reportlab.lib.pagesizes import A4
from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Image, Spacer
from reportlab.lib.styles import getSampleStyleSheet
from reportlab.lib import colors

import ttkbootstrap as tb
from ttkbootstrap.constants import *
from ttkbootstrap.style import Bootstyle

try:
    from gspread_formatting import cellFormat, numberFormat, format_cell_range
    HAS_GSFMT = True
except Exception:
    HAS_GSFMT = False

# ============= CONFIG =============
CONFIG = {
    'credentials_file': 'credentials.json',
    'backup_folder': 'backups',
    'backup_interval': 3600,
    'auto_save_interval': 300,
    'auto_refresh_seconds': 5,       # << realtime polling interval
    'date_format': '%d/%m/%Y %H:%M:%S',
    'backup_limit': 30,
    'audit_file': 'audit.log',
    'idr_decimals': 0,
    'min_balance_thresholds': {
        "BCA": 100_000, "Mandiri": 100_000, "BNI": 100_000, "BRI": 100_000,
        "Cimb Niaga": 100_000, "BTN": 100_000, "Danamon": 100_000,
        "DANA": 50_000, "OVO": 50_000, "GOPAY": 50_000, "LINK AJA": 50_000
    },
    'anomaly_std_multiplier': 3.0
}

BANK_LIST = [
    "BCA", "Mandiri", "BNI", "BRI", "Cimb Niaga", "BTN", "Danamon",
    "DANA", "OVO", "GOPAY", "LINK AJA"
]

HEADERS = [
    "No.", "Tanggal", "User ID", "Bank/EWallet", "Keterangan",
    "Credit", "Debit", "Saldo Akhir"
] + BANK_LIST

NEW_STYLE_BANK_COLS = {f"Saldo Akhir {b}": b for b in BANK_LIST}

MONEY_COLS = ["Credit", "Debit", "Saldo Akhir"] + BANK_LIST
NON_MONEY_COLS = ["No.", "Tanggal", "User ID", "Bank/EWallet", "Keterangan"]

FONT_BOLD = ("Helvetica", 10, "bold")
FONT_LARGE_BOLD = ("Helvetica", 14, "bold")
FONT_XL_BOLD = ("Helvetica", 18, "bold")
FONT_XXL_BOLD = ("Helvetica", 22, "bold")

# ============= UTILS =============
def ensure_dirs():
    if not os.path.exists(CONFIG['backup_folder']):
        os.makedirs(CONFIG['backup_folder'])

def audit_log(action, details=""):
    ensure_dirs()
    path = os.path.join(CONFIG['backup_folder'], CONFIG['audit_file'])
    ts = datetime.now().strftime(CONFIG['date_format'])
    with open(path, "a", encoding="utf-8") as f:
        f.write(f"[{ts}] {action}: {details}\n")

def read_audit_lines(limit=500):
    path = os.path.join(CONFIG['backup_folder'], CONFIG['audit_file'])
    if not os.path.exists(path):
        return []
    with open(path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    return lines[-limit:]

def _only_digits(s: str) -> str:
    return "".join(ch for ch in s if ch.isdigit() or ch in ",.-()")

def parse_amount_idr(s: str) -> float:
    if s is None:
        return 0.0
    if isinstance(s, (int, float)):
        val = float(s)
        return float(int(round(val))) if CONFIG['idr_decimals'] == 0 else round(val, CONFIG['idr_decimals'])
    s = str(s).strip()
    if s == "":
        return 0.0
    for token in ["Rp", "rp", "IDR", "idr", " "]:
        s = s.replace(token, "")
    s = _only_digits(s)
    neg = False
    if s.startswith("(") and s.endswith(")"):
        neg = True
        s = s[1:-1]
    if "," in s and "." in s:
        if s.rfind(",") > s.rfind("."):
            s = s.replace(".", "").replace(",", ".")
        else:
            s = s.replace(",", "")
    else:
        if "," in s and "." not in s:
            parts = s.split(",")
            if len(parts) == 2 and parts[1].isdigit():
                s = s.replace(".", "").replace(",", ".")
            else:
                s = s.replace(",", "")
        elif "." in s and "," not in s:
            parts = s.split(".")
            if len(parts) > 1 and all(len(p) == 3 for p in parts[1:]):
                s = s.replace(".", "")
    try:
        val = float(s)
    except Exception:
        val = 0.0
    if neg:
        val = -val
    return float(int(round(val))) if CONFIG['idr_decimals'] == 0 else round(val, CONFIG['idr_decimals'])

def fmt_idr(val: float) -> str:
    if val is None or (isinstance(val, float) and np.isnan(val)):
        val = 0
    if CONFIG['idr_decimals'] == 0:
        try:
            i = int(round(float(val)))
        except Exception:
            i = 0
        return f"Rp{format(i, ',').replace(',', '.')} IDR"
    s = f"{float(val):,.2f}"
    s = s.replace(",", "X").replace(".", ",").replace("X", ".")
    return f"Rp{s} IDR"

# ============= GOOGLE SHEETS =============
class GoogleSheetsManager:
    def __init__(self):
        self.scope = [
            "https://spreadsheets.google.com/feeds",
            "https://www.googleapis.com/auth/spreadsheets",
            "https://www.googleapis.com/auth/drive"
        ]
        self.creds = None
        self.client = None
        self.spreadsheet = None
        self.sheet = None
        self.last_sync = None
        self.connected = False
        self.sheet_id = None
        self.sheet_name = "Money Manager Pro"
        self.last_checksum = None  # checksum isi sheet terakhir

    def connect(self):
        try:
            if not os.path.exists(CONFIG['credentials_file']):
                raise FileNotFoundError(f"File {CONFIG['credentials_file']} tidak ditemukan")
            self.creds = ServiceAccountCredentials.from_json_keyfile_name(
                CONFIG['credentials_file'], self.scope)
            self.client = gspread.authorize(self.creds)
            self.connected = True
            audit_log("GSheets Connect", "Berhasil")
            return True
        except Exception as e:
            print("Error connect:", e)
            self.connected = False
            audit_log("GSheets Connect Failed", str(e))
            return False

    def open_sheet(self, sheet_id=None, sheet_name=None):
        try:
            if sheet_id:
                self.spreadsheet = self.client.open_by_key(sheet_id)
            else:
                try:
                    self.spreadsheet = self.client.open(sheet_name or self.sheet_name)
                except gspread.SpreadsheetNotFound:
                    self.spreadsheet = self.client.create(sheet_name or self.sheet_name)
            self.sheet = self.spreadsheet.sheet1
            self.sheet_id = self.spreadsheet.id
            self.ensure_headers()
            self.last_sync = datetime.now()
            audit_log("Open Sheet", self.sheet.title)
            return True
        except Exception as e:
            print("Error open sheet:", e)
            audit_log("Open Sheet Failed", str(e))
            return False

    def _apply_currency_format(self):
        if not HAS_GSFMT:
            return
        try:
            last_col_idx = 8 + len(BANK_LIST)
            start_col = 6
            rng = f"{self._col_letter(start_col)}2:{self._col_letter(last_col_idx)}10000"
            fmt = cellFormat(numberFormat=numberFormat(type="NUMBER", pattern='[$Rp-421] #,##0'))
            format_cell_range(self.sheet, rng, fmt)
        except Exception as e:
            print("Format gagal:", e)

    def _col_letter(self, n):
        s = ""
        while n > 0:
            n, r = divmod(n-1, 26)
            s = chr(65+r) + s
        return s

    def ensure_headers(self):
        headers = self.sheet.row_values(1)
        if headers != HEADERS:
            if headers:
                try:
                    self.sheet.delete_rows(1)
                except AttributeError:
                    self.sheet.delete_row(1)
            self.sheet.insert_row(HEADERS, 1)
            self._apply_currency_format()
        records = self.sheet.get_all_records()
        if len(records) == 0:
            zeros = [0] * len(BANK_LIST)
            first = [1, datetime.now().strftime(CONFIG['date_format']), "SYSTEM",
                     "SALDO AWAL", "Inisialisasi", 0, 0, 0] + zeros
            self.sheet.append_row(first, value_input_option="RAW")
            self._apply_currency_format()
            audit_log("Init Headers & Row", "Saldo Awal 0")

    # ======== NEW: low-level fetch with UNFORMATTED values (true source of truth)
    def _get_all_values_unformatted(self):
        return self.sheet.get_all_values(
            value_render_option='UNFORMATTED_VALUE',
            date_time_render_option='FORMATTED_STRING'
        )

    def _compute_checksum(self, values_2d):
        # Compact but stable checksum for change detection
        packed = json.dumps(values_2d, ensure_ascii=False, separators=(",", ":"))
        return hashlib.sha1(packed.encode("utf-8")).hexdigest()

    def get_sheet_checksum(self):
        try:
            vals = self._get_all_values_unformatted()
            return self._compute_checksum(vals)
        except Exception as e:
            print("Checksum error:", e)
            return None

    def get_all_data(self) -> pd.DataFrame:
        """
        Read the entire sheet using UNFORMATTED_VALUE so numbers stay numeric.
        Recompute running balances locally so UI == API every time.
        """
        try:
            vals = self._get_all_values_unformatted()
            if not vals or len(vals) < 2:
                self.last_checksum = self._compute_checksum(vals if vals else [])
                return pd.DataFrame(columns=HEADERS)

            header = vals[0]
            rows = vals[1:]

            # Map header names to index
            idx = {h: i for i, h in enumerate(header)}

            def get_cell(r, name, default=""):
                if name in idx and idx[name] < len(r):
                    return r[idx[name]]
                # accept "Saldo Akhir BCA" -> "BCA"
                if name in BANK_LIST:
                    alt = f"Saldo Akhir {name}"
                    if alt in idx and idx[alt] < len(r):
                        return r[idx[alt]]
                return default

            # Build normalized dict rows
            norm = []
            for r in rows:
                item = {}
                for h in HEADERS:
                    v = get_cell(r, h, "")
                    if h in MONEY_COLS:
                        item[h] = parse_amount_idr(v)
                    else:
                        item[h] = v
                # coerce No.
                try:
                    item["No."] = int(item.get("No.", 0) or 0)
                except Exception:
                    item["No."] = 0
                norm.append(item)

            df = pd.DataFrame(norm, columns=HEADERS)
            if df.empty:
                self.last_checksum = self._compute_checksum(vals)
                return df

            # Always recompute balances from the sheet order
            df = recompute_all_balances(df)
            df = df[HEADERS].copy()
            df["No."] = range(1, len(df)+1)

            # Save checksum for realtime watcher
            self.last_checksum = self._compute_checksum(vals)
            self.last_sync = datetime.now()
            return df
        except Exception as e:
            print("Error get_all_data:", e)
            return pd.DataFrame(columns=HEADERS)

    def append_data(self, row_list):
        try:
            row_clean = []
            for i, v in enumerate(row_list):
                col = HEADERS[i]
                if col in MONEY_COLS:
                    try:
                        row_clean.append(float(v))
                    except Exception:
                        row_clean.append(parse_amount_idr(str(v)))
                else:
                    row_clean.append(v)
            self.sheet.append_row(row_clean, value_input_option="RAW")
            self.last_sync = datetime.now()
            audit_log("Append Row", str(row_clean[:8]) + " ...")
            return True
        except Exception as e:
            print("Append error:", e)
            audit_log("Append Failed", str(e))
            return False

# ============= RECOMPUTE CORE =============
def recompute_all_balances(df: pd.DataFrame) -> pd.DataFrame:
    for b in BANK_LIST:
        if b not in df.columns:
            df[b] = 0.0
    running = {b: 0.0 for b in BANK_LIST}
    out_rows = []
    for _, r in df.iterrows():
        r = r.copy()
        bank = str(r.get("Bank/EWallet", "")).strip()
        user = str(r.get("User ID", "")).strip().upper()
        credit = float(r.get("Credit", 0) or 0)
        debit = float(r.get("Debit", 0) or 0)
        is_system_init = (user == "SYSTEM" and bank.upper() == "SALDO AWAL")
        if is_system_init:
            for b in BANK_LIST:
                val = r.get(b)
                running[b] = float(val) if pd.notna(val) else 0.0
        else:
            if bank in BANK_LIST:
                running[bank] += (credit - debit)
        for b in BANK_LIST:
            r[b] = running[b]
        r["Saldo Akhir"] = sum(running.values())
        out_rows.append(r)
    return pd.DataFrame(out_rows)

# ============= APP =============
class MoneyManagerPro(tb.Window):
    def __init__(self):
        super().__init__(themename="litera")
        self.title("Money Manager Pro")
        self.geometry("1600x980")

        self.font_families = ["Inter", "Poppins", "Arial", "Calibri", "Segoe UI", "Helvetica", "Times New Roman"]
        self.font_family_var = tk.StringVar(value=self._pick_available_family(self.font_families))
        self.super_bold_var = tk.BooleanVar(value=True)

        self._init_fonts()
        self.style.configure('.', font=FONT_BOLD)

        self.gsheets = GoogleSheetsManager()
        self.backup = BackupManager()
        self.data = pd.DataFrame(columns=HEADERS)
        self.filtered_data = self.data.copy()
        self.current_page = 0
        self.rows_per_page = 25
        self.user_settings = {'default_user':'','default_bank':'','auto_save':True,'theme':'litera'}

        self.only_anomaly_var = tk.BooleanVar(value=False)
        self.parity_state = tk.StringVar(value="Unknown")
        self.parity_details_last = ""
        self._last_sheet_checksum = None  # for realtime watcher

        self._build_menu()
        self._build_statusbar()

        self.tabs = ttk.Notebook(self); self.tabs.pack(fill=tk.BOTH, expand=True, padx=10, pady=(5, 5))
        self.tab_transaksi = ttk.Frame(self.tabs); self.tabs.add(self.tab_transaksi, text="Transaksi")
        self.tab_user = ttk.Frame(self.tabs); self.tabs.add(self.tab_user, text="Ringkasan User")
        self.tab_audit = ttk.Frame(self.tabs); self.tabs.add(self.tab_audit, text="Audit Trail")

        self._build_header(self.tab_transaksi)
        self._build_summary_cards(self.tab_transaksi)
        self._build_input_panel(self.tab_transaksi)
        self._build_filter_panel(self.tab_transaksi)
        self._build_table(self.tab_transaksi)
        self._build_charts(self.tab_transaksi)
        self._build_user_summary(self.tab_user)
        self._build_audit_panel(self.tab_audit)

        self.connect_to_gsheets()

    # ====== Typography helpers ======
    def _pick_available_family(self, preferred):
        available = set(tkfont.families())
        for fam in preferred:
            if fam in available:
                return fam
        return "Helvetica"

    def _init_fonts(self):
        global FONT_BOLD, FONT_LARGE_BOLD, FONT_XL_BOLD, FONT_XXL_BOLD
        base_family = self.font_family_var.get()
        bump = 2 if self.super_bold_var.get() else 0
        FONT_BOLD = tkfont.Font(family=base_family, size=10 + bump, weight="bold")
        FONT_LARGE_BOLD = tkfont.Font(family=base_family, size=14 + bump, weight="bold")
        FONT_XL_BOLD = tkfont.Font(family=base_family, size=18 + bump, weight="bold")
        FONT_XXL_BOLD = tkfont.Font(family=base_family, size=22 + bump, weight="bold")

    def _apply_font_family(self, family):
        for f in (FONT_BOLD, FONT_LARGE_BOLD, FONT_XL_BOLD, FONT_XXL_BOLD):
            f.configure(family=family)

    def _apply_super_bold(self, enabled):
        bump = 2 if enabled else 0
        FONT_BOLD.configure(size=10 + bump)
        FONT_LARGE_BOLD.configure(size=14 + bump)
        FONT_XL_BOLD.configure(size=18 + bump)
        FONT_XXL_BOLD.configure(size=22 + bump)

    # ---------- UI ----------
    def _build_menu(self):
        m = tk.Menu(self)
        file_menu = tk.Menu(m, tearoff=0)
        file_menu.add_command(label="Export Excel", command=self.export_excel)
        file_menu.add_command(label="Export CSV", command=self.export_csv)
        file_menu.add_command(label="Export PDF", command=self.export_pdf)
        file_menu.add_separator()
        file_menu.add_command(label="Keluar", command=self.destroy)
        m.add_cascade(label="File", menu=file_menu)

        actions_menu = tk.Menu(m, tearoff=0)
        actions_menu.add_command(label="Transfer Antar Bank", command=self.open_transfer_dialog)
        actions_menu.add_separator()
        actions_menu.add_command(label="Reload dari Google Sheets", command=self.load_data)
        actions_menu.add_command(label="Cek Kesesuaian (Dashboard ↔ API)", command=self.check_parity_against_api)
        m.add_cascade(label="Aksi", menu=actions_menu)

        view_menu = tk.Menu(m, tearoff=0)
        view_menu.add_command(label="Toggle Dark/Light Theme", command=self.toggle_theme)
        type_sub = tk.Menu(view_menu, tearoff=0)
        for fam in self.font_families:
            type_sub.add_radiobutton(label=fam, variable=self.font_family_var, value=fam,
                                     command=lambda f=fam: self._apply_font_family(f))
        view_menu.add_cascade(label="Font Family", menu=type_sub)
        view_menu.add_checkbutton(label="Very Bold Mode (tebal maksimal)", variable=self.super_bold_var,
                                  command=lambda: self._apply_super_bold(self.super_bold_var.get()))
        m.add_cascade(label="View", menu=view_menu)
        self.config(menu=m)

    def _build_statusbar(self):
        self.status_var = tk.StringVar(value="Status: Offline | Last Sync: -")
        status_label = ttk.Label(self, textvariable=self.status_var, anchor="w", font=FONT_BOLD)
        status_label.pack(side=tk.BOTTOM, fill=tk.X)

    def update_status(self, msg=None):
        last = self.gsheets.last_sync.strftime(CONFIG['date_format']) if self.gsheets.last_sync else "-"
        conn = "Online" if self.gsheets.connected else "Offline"
        base = f"Status: {conn} | Last Sync: {last}"
        warnings = self.check_min_balance(self.data)
        if warnings:
            base += " | ⚠ " + "; ".join(warnings)
        base += f" | Parity: {self.parity_state.get()}"
        if msg:
            base += f" | {msg}"
        self.status_var.set(base)

    def _build_header(self, parent):
        f = ttk.Frame(parent); f.pack(fill=tk.X, pady=(0,10))
        title = ttk.Label(f, text="💰 Money Manager Pro - Dashboard Keuangan", font=FONT_XXL_BOLD)
        title.pack(side=tk.LEFT)
        self.connect_label = ttk.Label(f, text="Status: Offline", font=FONT_BOLD)
        self.connect_label.pack(side=tk.RIGHT)

    def _build_summary_cards(self, parent):
        cards = ttk.Frame(parent); cards.pack(fill=tk.X, pady=(0,10))
        card_style = { "font": FONT_LARGE_BOLD, "width": 22, "anchor": "center", "padding": 10 }
        self.card_income = tb.Label(cards, text="Pemasukan\nRp0 IDR", bootstyle="success, inverse", **card_style)
        self.card_expense = tb.Label(cards, text="Pengeluaran\nRp0 IDR", bootstyle="danger, inverse", **card_style)
        self.card_balance = tb.Label(cards, text="Saldo Akhir\nRp0 IDR", bootstyle="info, inverse", **card_style)
        self.card_today = tb.Label(cards, text="Transaksi Hari Ini\n0", bootstyle="primary, inverse", **card_style)
        for w in [self.card_income,self.card_expense,self.card_balance,self.card_today]:
            w.pack(side=tk.LEFT, expand=True, padx=6)
        self.bank_badges = ttk.Label(parent, text="", font=FONT_BOLD, foreground="#37474F")
        self.bank_badges.pack(fill=tk.X, padx=4, pady=(0,6))

    def _build_input_panel(self, parent):
        fr = ttk.LabelFrame(parent, text="Input Transaksi", padding=10); fr.pack(fill=tk.X, pady=(0,10))
        label_style = {"font": FONT_BOLD}
        ttk.Label(fr, text="User ID:", **label_style).grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        self.user_entry = ttk.Entry(fr, width=25, font=FONT_BOLD); self.user_entry.grid(row=0, column=1, padx=5, pady=2)

        ttk.Label(fr, text="Bank/EWallet:", **label_style).grid(row=0, column=2, sticky=tk.W, padx=5, pady=2)
        self.bank_combo = ttk.Combobox(fr, values=BANK_LIST, state="readonly", width=25, font=FONT_BOLD); self.bank_combo.grid(row=0, column=3, padx=5, pady=2)

        ttk.Label(fr, text="Tipe:", **label_style).grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        self.type_combo = ttk.Combobox(fr, values=["Pemasukan","Pengeluaran"], state="readonly", width=25, font=FONT_BOLD); self.type_combo.grid(row=1, column=1, padx=5, pady=2); self.type_combo.current(0)

        ttk.Label(fr, text="Jumlah (IDR):", **label_style).grid(row=1, column=2, sticky=tk.W, padx=5, pady=2)
        self.amount_entry = ttk.Entry(fr, width=25, font=FONT_BOLD); self.amount_entry.grid(row=1, column=3, padx=5, pady=2)
        self.amount_preview = ttk.Label(fr, text="Terbaca: Rp0 IDR", font=FONT_BOLD, foreground="#00695C"); self.amount_preview.grid(row=1, column=4, sticky=tk.W, padx=10)
        def _on_amount_change(_evt=None):
            val = parse_amount_idr(self.amount_entry.get())
            self.amount_preview.config(text=f"Terbaca: {fmt_idr(val)}")
        self.amount_entry.bind("<KeyRelease>", _on_amount_change); self.amount_entry.bind("<FocusOut>", _on_amount_change)

        ttk.Label(fr, text="Keterangan:", **label_style).grid(row=2, column=0, sticky=tk.W, padx=5, pady=2)
        self.desc_entry = ttk.Entry(fr, width=80, font=FONT_BOLD); self.desc_entry.grid(row=2, column=1, columnspan=3, padx=5, pady=2, sticky=tk.W)

        btn = ttk.Frame(fr); btn.grid(row=3, column=0, columnspan=5, pady=(6,0))
        tb.Button(btn, text="Simpan (Ctrl+S)", bootstyle="success", command=self.save_transaction, width=15).pack(side=tk.LEFT, padx=5)
        tb.Button(btn, text="Bersihkan", bootstyle="outline-secondary", command=self.clear_inputs, width=12).pack(side=tk.LEFT, padx=5)
        tb.Button(btn, text="Set Saldo Awal", bootstyle="outline-warning", command=self.set_initial_balance, width=15).pack(side=tk.LEFT, padx=5)
        tb.Button(btn, text="Transfer Antar Bank", bootstyle="outline-info", command=self.open_transfer_dialog, width=18).pack(side=tk.LEFT, padx=5)
        self.bind("<Control-s>", lambda e: self.save_transaction())

    def _build_filter_panel(self, parent):
        fr = ttk.LabelFrame(parent, text="Filter & Pencarian", padding=10); fr.pack(fill=tk.X, pady=(0,10))
        label_style = {"font": FONT_BOLD}
        ttk.Label(fr, text="User ID:", **label_style).grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        self.user_filter = ttk.Entry(fr, width=20, font=FONT_BOLD); self.user_filter.grid(row=0, column=1, padx=5, pady=2)
        ttk.Label(fr, text="Bank:", **label_style).grid(row=0, column=2, sticky=tk.W, padx=5, pady=2)
        self.bank_filter = ttk.Combobox(fr, values=["Semua"] + BANK_LIST, state="readonly", width=20, font=FONT_BOLD); self.bank_filter.grid(row=0, column=3, padx=5, pady=2); self.bank_filter.current(0)
        ttk.Label(fr, text="Tipe:", **label_style).grid(row=0, column=4, sticky=tk.W, padx=5, pady=2)
        self.type_filter = ttk.Combobox(fr, values=["Semua","Pemasukan","Pengeluaran"], state="readonly", width=20, font=FONT_BOLD); self.type_filter.grid(row=0, column=5, padx=5, pady=2); self.type_filter.current(0)
        ttk.Label(fr, text="Dari (dd/mm/yyyy):", **label_style).grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        self.date_from = ttk.Entry(fr, width=20, font=FONT_BOLD); self.date_from.grid(row=1, column=1, padx=5, pady=2)
        ttk.Label(fr, text="Sampai (dd/mm/yyyy):", **label_style).grid(row=1, column=2, sticky=tk.W, padx=5, pady=2)
        self.date_to = ttk.Entry(fr, width=20, font=FONT_BOLD); self.date_to.grid(row=1, column=3, padx=5, pady=2)
        presets = ttk.Frame(fr); presets.grid(row=1, column=4, columnspan=2, padx=5, pady=2, sticky=tk.W)
        tb.Button(presets, text="Hari Ini", bootstyle="secondary", command=self.filter_today, width=10).pack(side=tk.LEFT, padx=4)
        tb.Button(presets, text="Minggu Ini", bootstyle="secondary", command=self.filter_this_week, width=12).pack(side=tk.LEFT, padx=4)
        tb.Button(presets, text="Bulan Ini", bootstyle="secondary", command=self.filter_this_month, width=12).pack(side=tk.LEFT, padx=4)
        bf = ttk.Frame(fr); bf.grid(row=2, column=0, columnspan=6, padx=5, pady=2, sticky=tk.W)
        tb.Button(bf, text="Terapkan Filter", bootstyle="info", command=self.apply_filters, width=15).pack(side=tk.LEFT, padx=4)
        tb.Button(bf, text="Reset", bootstyle="outline-danger", command=self.reset_filters, width=10).pack(side=tk.LEFT, padx=4)
        ttk.Checkbutton(bf, text="Hanya Anomali", variable=self.only_anomaly_var, command=self.apply_filters).pack(side=tk.LEFT, padx=8)

    def _build_table(self, parent):
        display = ttk.Frame(parent); display.pack(fill=tk.BOTH, expand=True)
        tf = ttk.Frame(display); tf.pack(fill=tk.BOTH, expand=True)
        style = ttk.Style(); style.configure("Treeview.Heading", font=FONT_BOLD); style.configure("Treeview", font=("Helvetica", 9))
        self.tree = ttk.Treeview(tf, columns=HEADERS, show="headings", selectmode="extended")
        vsb = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        hsb = ttk.Scrollbar(tf, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        self.tree.grid(row=0, column=0, sticky="nsew"); vsb.grid(row=0, column=1, sticky="ns"); hsb.grid(row=1, column=0, sticky="ew")
        tf.grid_columnconfigure(0, weight=1); tf.grid_rowconfigure(0, weight=1)
        for col in HEADERS:
            self.tree.heading(col, text=col, anchor="center")
            if col in MONEY_COLS:
                self.tree.column(col, width=140, anchor="e")
            elif col in ["Keterangan"]:
                self.tree.column(col, width=260, anchor="w")
            elif col in ["User ID", "Bank/EWallet"]:
                self.tree.column(col, width=140, anchor="center")
            elif col in ["Tanggal"]:
                self.tree.column(col, width=160, anchor="center")
            else:
                self.tree.column(col, width=70 if col == "No." else 110, anchor="center")
        self.tree.tag_configure("income", background="#e8f5e9")
        self.tree.tag_configure("expense", background="#ffebee")
        self.tree.tag_configure("anomaly", background="#ffcccc")
        pg = ttk.Frame(display); pg.pack(fill=tk.X, pady=(5,0))
        self.prev_btn = tb.Button(pg, text="◀ Sebelumnya", bootstyle="outline-primary", command=self.prev_page); self.prev_btn.pack(side=tk.LEFT, padx=5)
        self.page_label = ttk.Label(pg, text="Halaman 1/1", font=FONT_BOLD); self.page_label.pack(side=tk.LEFT, padx=5)
        self.next_btn = tb.Button(pg, text="Selanjutnya ▶", bootstyle="outline-primary", command=self.next_page); self.next_btn.pack(side=tk.LEFT, padx=5)
        summary = ttk.Frame(display); summary.pack(fill=tk.X, pady=(5,0))
        self.summary_label = ttk.Label(summary, text="Total: 0 | Pemasukan: Rp0 IDR | Pengeluaran: Rp0 IDR | Saldo: Rp0 IDR", font=FONT_BOLD); self.summary_label.pack(side=tk.LEFT)

    def _build_charts(self, parent):
        chart = ttk.Frame(parent); chart.pack(fill=tk.BOTH, expand=True, pady=(10,0))
        plt.rcParams.update({'font.size': 10, 'font.weight': 'bold','axes.titlesize': 12, 'axes.titleweight': 'bold', 'axes.labelweight': 'bold'})
        bal_frame = ttk.LabelFrame(chart, text="Grafik Saldo (Prediksi 7 hari)", padding=10); bal_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,5))
        self.fig_balance, self.ax_balance = plt.subplots(figsize=(8,3), dpi=100); self.balance_embed = FigureCanvasTkAgg(self.fig_balance, master=bal_frame); self.balance_embed.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        type_frame = ttk.LabelFrame(chart, text="Distribusi Transaksi", padding=10); type_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5,5))
        self.fig_type, self.ax_type = plt.subplots(figsize=(4,3), dpi=100); self.type_embed = FigureCanvasTkAgg(self.fig_type, master=type_frame); self.type_embed.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        month_frame = ttk.LabelFrame(chart, text="Perbandingan Bulanan (Income vs Expense)", padding=10); month_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(5,0))
        self.fig_month, self.ax_month = plt.subplots(figsize=(6,3), dpi=100); self.month_embed = FigureCanvasTkAgg(self.fig_month, master=month_frame); self.month_embed.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def _build_user_summary(self, parent):
        top = ttk.Frame(parent); top.pack(fill=tk.X, pady=8, padx=8)
        ttk.Label(top, text="Ringkasan per User", font=FONT_XL_BOLD).pack(side=tk.LEFT)
        tb.Button(top, text="Refresh", bootstyle="secondary", command=self.refresh_user_summary).pack(side=tk.RIGHT)
        frame = ttk.Frame(parent); frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0,8))
        style = ttk.Style(); style.configure("User.Treeview.Heading", font=FONT_BOLD)
        self.tree_user = ttk.Treeview(frame, columns=["User ID","Total Pemasukan","Total Pengeluaran","Saldo Net"], show="headings", style="User.Treeview")
        for i,c in enumerate(["User ID","Total Pemasukan","Total Pengeluaran","Saldo Net"]):
            self.tree_user.heading(c, text=c, anchor="center")
            self.tree_user.column(c, anchor="e" if i>0 else "center", width=200 if i==0 else 160)
        vsb = ttk.Scrollbar(frame, orient="vertical", command=self.tree_user.yview)
        self.tree_user.configure(yscrollcommand=vsb.set)
        self.tree_user.grid(row=0, column=0, sticky="nsew"); vsb.grid(row=0, column=1, sticky="ns")
        frame.grid_columnconfigure(0, weight=1); frame.grid_rowconfigure(0, weight=1)

    def _build_audit_panel(self, parent):
        top = ttk.Frame(parent); top.pack(fill=tk.X, pady=8, padx=8)
        ttk.Label(top, text="Audit Trail", font=FONT_XL_BOLD).pack(side=tk.LEFT)
        tb.Button(top, text="Refresh", bootstyle="secondary", command=self.refresh_audit_view).pack(side=tk.RIGHT)
        body = ttk.Frame(parent); body.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0,8))
        self.audit_text = tk.Text(body, wrap="none", font=("Consolas", 9))
        vsb = ttk.Scrollbar(body, orient="vertical", command=self.audit_text.yview)
        self.audit_text.configure(yscrollcommand=vsb.set)
        self.audit_text.grid(row=0, column=0, sticky="nsew"); vsb.grid(row=0, column=1, sticky="ns")
        body.grid_columnconfigure(0, weight=1); body.grid_rowconfigure(0, weight=1)
        self.refresh_audit_view()

    # ---------- Logic ----------
    def toggle_theme(self):
        theme = self.style.theme.name
        self.style.theme_use('darkly' if theme != 'darkly' else 'litera')

    def connect_to_gsheets(self):
        def t():
            if self.gsheets.connect() and self.gsheets.open_sheet():
                self.load_data()
                self.connect_label.config(text="Status: Terhubung ke Google Sheets", font=FONT_BOLD)
                self.start_realtime_sync()  # << start realtime watcher setelah konek
            else:
                self.connect_label.config(text="Status: Gagal koneksi", font=FONT_BOLD)
            self.update_status()
        threading.Thread(target=t, daemon=True).start()

    def load_data(self):
        df = self.gsheets.get_all_data()
        self._last_sheet_checksum = self.gsheets.last_checksum
        self.data = df.copy() if not df.empty else pd.DataFrame(columns=HEADERS)
        self.filtered_data = self.data.copy()
        self.refresh_table()
        self.update_summary()
        self.update_charts()
        self.refresh_user_summary()
        self.backup.create_backup(self.data)
        self.update_bank_badges()
        self.update_status("Data loaded")
        self.check_parity_against_api(silent=True)

    # ---------- realtime watcher ----------
    def start_realtime_sync(self):
        def watcher():
            while True:
                try:
                    time.sleep(CONFIG['auto_refresh_seconds'])
                    cs = self.gsheets.get_sheet_checksum()
                    if cs and cs != self._last_sheet_checksum:
                        self._last_sheet_checksum = cs
                        # reload on UI thread
                        self.after(0, self.load_data)
                except Exception:
                    pass
        threading.Thread(target=watcher, daemon=True).start()

    # ---------- Filters & Table ----------
    def _format_row_for_display(self, row_dict: dict):
        display_vals = []
        for col in HEADERS:
            v = row_dict.get(col, "")
            if col in MONEY_COLS:
                try:
                    display_vals.append(fmt_idr(float(v)))
                except Exception:
                    display_vals.append(fmt_idr(0))
            else:
                display_vals.append(v)
        return display_vals

    def _get_anomaly_mask(self, df):
        if df.empty:
            return pd.Series([], dtype=bool)
        amt = np.maximum(df['Credit'].astype(float).values, df['Debit'].astype(float).values)
        s = pd.Series(amt)
        mean = s.mean()
        std = s.std(ddof=0)
        if std == 0:
            return pd.Series([False]*len(df))
        thresh = mean + CONFIG['anomaly_std_multiplier']*std
        return s > thresh

    def refresh_table(self):
        for i in self.tree.get_children():
            self.tree.delete(i)
        start = self.current_page * self.rows_per_page
        page = self.filtered_data.iloc[start:start+self.rows_per_page] if not self.filtered_data.empty else pd.DataFrame(columns=HEADERS)
        anomaly_mask_page = self._get_anomaly_mask(page) if not page.empty else pd.Series([], dtype=bool)
        for idx, row in page.iterrows():
            row_dict = {c: row.get(c, "") for c in HEADERS}
            vals = self._format_row_for_display(row_dict)
            tag = ""
            if float(row.get("Credit",0))>0:
                tag = "income"
            elif float(row.get("Debit",0))>0:
                tag = "expense"
            if not page.empty and len(anomaly_mask_page)>0:
                if anomaly_mask_page.iloc[list(page.index).index(idx)]:
                    tag = "anomaly"
            self.tree.insert("", "end", values=vals, tags=(tag,))
        total_pages = max(1, math.ceil(len(self.filtered_data)/self.rows_per_page))
        self.page_label.config(text=f"Halaman {self.current_page+1}/{total_pages}")
        self.prev_btn.config(state="normal" if self.current_page>0 else "disabled")
        self.next_btn.config(state="normal" if self.current_page<total_pages-1 else "disabled")

    def prev_page(self):
        if self.current_page>0:
            self.current_page-=1; self.refresh_table()

    def next_page(self):
        if (self.current_page+1)*self.rows_per_page < len(self.filtered_data):
            self.current_page+=1; self.refresh_table()

    def apply_filters(self):
        try:
            f = self.data.copy()
            u = self.user_filter.get().strip().lower()
            if u:
                f = f[f['User ID'].astype(str).str.lower().str.contains(u)]
            b = self.bank_filter.get()
            if b and b!="Semua":
                f = f[f['Bank/EWallet']==b]
            t = self.type_filter.get()
            if t=="Pemasukan":
                f = f[f['Credit']>0]
            elif t=="Pengeluaran":
                f = f[f['Debit']>0]
            dfm = self.date_from.get().strip(); dt = self.date_to.get().strip()
            if dfm or dt:
                f['_tgl'] = pd.to_datetime(f['Tanggal'], format=CONFIG['date_format'], errors='coerce')
                if dfm:
                    f = f[f['_tgl'] >= datetime.strptime(dfm, '%d/%m/%Y')]
                if dt:
                    f = f[f['_tgl'] < (datetime.strptime(dt, '%d/%m/%Y') + timedelta(days=1))]
                f.drop(columns=['_tgl'], inplace=True, errors="ignore")
            if self.only_anomaly_var.get() and not f.empty:
                mask = self._get_anomaly_mask(f)
                f = f[mask]
            self.filtered_data = f
            self.current_page=0
            self.refresh_table(); self.update_summary(); self.update_charts()
        except Exception as e:
            messagebox.showerror("Error", f"Gagal filter: {e}")

    def reset_filters(self):
        self.user_filter.delete(0, tk.END)
        self.bank_filter.current(0)
        self.type_filter.current(0)
        self.date_from.delete(0, tk.END)
        self.date_to.delete(0, tk.END)
        self.only_anomaly_var.set(False)
        self.filtered_data = self.data.copy()
        self.current_page = 0
        self.refresh_table(); self.update_summary(); self.update_charts()

    def filter_today(self):
        today = datetime.now().strftime('%d/%m/%Y')
        self.date_from.delete(0, tk.END); self.date_from.insert(0, today)
        self.date_to.delete(0, tk.END); self.date_to.insert(0, today)
        self.apply_filters()

    def filter_this_week(self):
        now = datetime.now()
        start = (now - timedelta(days=now.weekday())).strftime('%d/%m/%Y')
        end = (now + timedelta(days=(6-now.weekday()))).strftime('%d/%m/%Y')
        self.date_from.delete(0, tk.END); self.date_from.insert(0, start)
        self.date_to.delete(0, tk.END); self.date_to.insert(0, end)
        self.apply_filters()

    def filter_this_month(self):
        now = datetime.now()
        start = now.replace(day=1).strftime('%d/%m/%Y')
        next_month = (now.replace(day=28) + timedelta(days=4)).replace(day=1)
        end_date = (next_month - timedelta(days=1)).strftime('%d/%m/%Y')
        self.date_from.delete(0, tk.END); self.date_from.insert(0, start)
        self.date_to.delete(0, tk.END); self.date_to.insert(0, end_date)
        self.apply_filters()

    # ---------- Summary & Charts ----------
    def update_summary(self):
        if self.filtered_data.empty:
            self.summary_label.config(text="Total: 0 | Pemasukan: Rp0 IDR | Pengeluaran: Rp0 IDR | Saldo: Rp0 IDR")
            self.card_income.config(text="Pemasukan\nRp0 IDR")
            self.card_expense.config(text="Pengeluaran\nRp0 IDR")
            self.card_balance.config(text="Saldo Akhir\nRp0 IDR")
            self.card_today.config(text="Transaksi Hari Ini\n0")
            self.update_bank_badges()
            return
        income = float(self.filtered_data['Credit'].sum())
        expense = float(self.filtered_data['Debit'].sum())
        balance = float(self.filtered_data['Saldo Akhir'].iloc[-1]) if not self.filtered_data.empty else 0.0
        today = datetime.now().strftime("%d/%m/%Y")
        trx_today = (pd.to_datetime(self.filtered_data['Tanggal'], format=CONFIG['date_format'], errors='coerce').dt.strftime("%d/%m/%Y").eq(today)).sum()
        self.summary_label.config(text=f"Total: {len(self.filtered_data)} | Pemasukan: {fmt_idr(income)} | Pengeluaran: {fmt_idr(expense)} | Saldo: {fmt_idr(balance)}")
        self.card_income.config(text=f"Pemasukan\n{fmt_idr(income)}")
        self.card_expense.config(text=f"Pengeluaran\n{fmt_idr(expense)}")
        self.card_balance.config(text=f"Saldo Akhir\n{fmt_idr(balance)}")
        self.card_today.config(text=f"Transaksi Hari Ini\n{trx_today}")
        self.update_bank_badges()

    def update_bank_badges(self):
        if self.data.empty:
            self.bank_badges.config(text="")
            return
        last = self.data.iloc[-1]
        chips = []
        for b in BANK_LIST:
            try:
                v = float(last[b])
            except Exception:
                v = 0.0
            low = v < CONFIG['min_balance_thresholds'].get(b, 0)
            chip = f"{b}: {int(v):,}".replace(",", ".")
            chips.append(("❗ " + chip) if low else chip)
        self.bank_badges.config(text=" | ".join(chips))

    def _forecast(self, balances):
        n = len(balances)
        if n < 2:
            return np.array([])
        x = np.arange(n); y = np.array(balances, dtype=float)
        a, b = np.polyfit(x, y, 1)
        xf = np.arange(n, n+7)
        return a*xf + b

    def update_charts(self):
        self.ax_balance.clear()
        if not self.filtered_data.empty:
            try:
                d = pd.to_datetime(self.filtered_data['Tanggal'], format=CONFIG['date_format'], errors='coerce')
                bal = self.filtered_data['Saldo Akhir'].astype(float).to_numpy()
                self.ax_balance.plot(d, bal, marker='o', linestyle='-', label='Total', linewidth=2)
                pred = self._forecast(bal)
                if pred.size>0:
                    last = pd.to_datetime(self.filtered_data['Tanggal'].iloc[-1], format=CONFIG['date_format'], errors='coerce')
                    future = [last + timedelta(days=i+1) for i in range(len(pred))]
                    self.ax_balance.plot(future, pred, linestyle='--', label='Prediksi 7 hari', linewidth=2)
                self.ax_balance.set_title('Perkembangan Saldo', fontweight='bold')
                self.ax_balance.set_xlabel('Tanggal', fontweight='bold')
                self.ax_balance.set_ylabel('Saldo (IDR)', fontweight='bold')
                self.ax_balance.grid(True, alpha=0.3)
                self.ax_balance.legend()
                for lab in self.ax_balance.get_xticklabels():
                    lab.set_rotation(45); lab.set_ha('right')
            except Exception as e:
                print("Chart error:", e)
                self.ax_balance.text(0.5,0.5,'No data',ha='center',va='center',transform=self.ax_balance.transAxes, fontweight='bold')
        else:
            self.ax_balance.text(0.5,0.5,'No data',ha='center',va='center',transform=self.ax_balance.transAxes, fontweight='bold')
        self.fig_balance.tight_layout(); self.balance_embed.draw()

        self.ax_type.clear()
        if not self.filtered_data.empty:
            inc = int((self.filtered_data['Credit']>0).sum())
            exp = int((self.filtered_data['Debit']>0).sum())
            if inc or exp:
                self.ax_type.pie([inc,exp], labels=['Pemasukan','Pengeluaran'], autopct='%1.1f%%', startangle=90, textprops={'fontweight': 'bold'})
                self.ax_type.set_title('Distribusi Transaksi', fontweight='bold')
            else:
                self.ax_type.text(0.5,0.5,'No data',ha='center',va='center',transform=self.ax_type.transAxes, fontweight='bold')
        else:
            self.ax_type.text(0.5,0.5,'No data',ha='center',va='center',transform=self.ax_type.transAxes, fontweight='bold')
        self.fig_type.tight_layout(); self.type_embed.draw()

        self.ax_month.clear()
        if not self.data.empty:
            try:
                tmp = self.data.copy()
                tmp['_tgl'] = pd.to_datetime(tmp['Tanggal'], format=CONFIG['date_format'], errors='coerce')
                tmp['YM'] = tmp['_tgl'].dt.to_period('M').astype(str)
                g = tmp.groupby('YM').agg(Income=('Credit','sum'), Expense=('Debit','sum')).reset_index()
                x = np.arange(len(g)); width = 0.35
                self.ax_month.bar(x - width/2, g['Income'].values, width, label='Income')
                self.ax_month.bar(x + width/2, g['Expense'].values, width, label='Expense')
                self.ax_month.set_xticks(x); self.ax_month.set_xticklabels(g['YM'].tolist(), rotation=45, ha='right')
                self.ax_month.set_title('Income vs Expense per Bulan', fontweight='bold')
                self.ax_month.set_ylabel('IDR', fontweight='bold')
                self.ax_month.grid(True, axis='y', alpha=0.3)
                self.ax_month.legend()
            except Exception as e:
                print("Monthly chart error:", e)
                self.ax_month.text(0.5,0.5,'No data',ha='center',va='center',transform=self.ax_month.transAxes, fontweight='bold')
        else:
            self.ax_month.text(0.5,0.5,'No data',ha='center',va='center',transform=self.ax_month.transAxes, fontweight='bold')
        self.fig_month.tight_layout(); self.month_embed.draw()

    def refresh_user_summary(self):
        for it in self.tree_user.get_children():
            self.tree_user.delete(it)
        if self.data.empty:
            return
        g = self.data.groupby("User ID", dropna=False).agg(Total_Pemasukan=("Credit","sum"), Total_Pengeluaran=("Debit","sum")).reset_index()
        g["Saldo_Net"] = g["Total_Pemasukan"] - g["Total_Pengeluaran"]
        for _, r in g.iterrows():
            self.tree_user.insert("", "end", values=[r["User ID"], fmt_idr(r["Total_Pemasukan"]), fmt_idr(r["Total_Pengeluaran"]), fmt_idr(r["Saldo_Net"])])

    def refresh_audit_view(self):
        self.audit_text.delete("1.0", tk.END)
        for line in read_audit_lines():
            self.audit_text.insert(tk.END, line)

    # ---------- Parity Check ----------
    def check_parity_against_api(self, silent=False):
        try:
            vals = self.gsheets._get_all_values_unformatted()
            if not vals or len(vals) < 2:
                self.parity_state.set("Unknown")
                if not silent: messagebox.showwarning("Parity", "Sheet kosong / tidak terbaca")
                self.update_status(); return
            header = vals[0]; rows = vals[1:]
            idx = {h: i for i, h in enumerate(header)}
            df_raw = []
            for r in rows:
                item = {}
                for h in HEADERS:
                    if h in idx and idx[h] < len(r):
                        v = r[idx[h]]
                    elif h in BANK_LIST and f"Saldo Akhir {h}" in idx and idx[f"Saldo Akhir {h}"] < len(r):
                        v = r[idx[f"Saldo Akhir {h}"]]
                    else:
                        v = ""
                    item[h] = parse_amount_idr(v) if h in MONEY_COLS else v
                try:
                    item["No."] = int(item.get("No.", 0) or 0)
                except:
                    item["No."] = 0
                df_raw.append(item)
            df_raw = pd.DataFrame(df_raw, columns=HEADERS)
            if df_raw.empty:
                self.parity_state.set("Unknown")
                if not silent: messagebox.showwarning("Parity", "Data raw kosong")
                self.update_status(); return
            df_raw = recompute_all_balances(df_raw); df_raw = df_raw[HEADERS].copy(); df_raw["No."] = range(1, len(df_raw)+1)
            diffs = []
            if len(df_raw) != len(self.data):
                diffs.append(f"Jumlah baris berbeda → API:{len(df_raw)} vs Dashboard:{len(self.data)}")
            if not df_raw.empty and not self.data.empty:
                last_api = df_raw.iloc[-1]; last_ui = self.data.iloc[-1]
                if abs(float(df_raw["Credit"].sum()) - float(self.data["Credit"].sum())) > 1e-6:
                    diffs.append("Total Credit berbeda")
                if abs(float(df_raw["Debit"].sum()) - float(self.data["Debit"].sum())) > 1e-6:
                    diffs.append("Total Debit berbeda")
                if abs(float(last_api["Saldo Akhir"]) - float(last_ui["Saldo Akhir"])) > 1e-6:
                    diffs.append(f"Saldo Akhir terakhir berbeda ({int(last_api['Saldo Akhir'])} vs {int(last_ui['Saldo Akhir'])})")
                for b in BANK_LIST:
                    if abs(float(last_api[b]) - float(last_ui[b])) > 1e-6:
                        diffs.append(f"{b} terakhir berbeda ({int(last_api[b])} vs {int(last_ui[b])})")
            if diffs:
                self.parity_state.set("Drift"); self.parity_details_last = "\n".join(diffs)
                if not silent: messagebox.showwarning("Parity: DRIFT terdeteksi", self.parity_details_last)
            else:
                self.parity_state.set("OK"); self.parity_details_last = "Semua cocok (Dashboard = API)."
                if not silent: messagebox.showinfo("Parity: OK", "Dashboard sama dengan Google Sheets API.")
        except Exception as e:
            self.parity_state.set("Unknown"); self.parity_details_last = f"Gagal cek parity: {e}"
            if not silent: messagebox.showerror("Parity Error", str(e))
        finally:
            self.update_status()

    # ---------- Transactions ----------
    def save_transaction(self):
        user_id = (self.user_entry.get() or "").strip()
        bank = (self.bank_combo.get() or "").strip()
        ttype = (self.type_combo.get() or "").strip()
        amt_str = (self.amount_entry.get() or "").strip()
        desc = (self.desc_entry.get() or "").strip()

        if not user_id or not bank or not amt_str:
            messagebox.showerror("Error", "User ID, Bank/EWallet, dan Jumlah wajib diisi"); return
        amount = parse_amount_idr(amt_str)
        if amount <= 0:
            messagebox.showerror("Error", "Jumlah harus > 0"); return

        credit = amount if ttype == "Pemasukan" else 0.0
        debit = amount if ttype == "Pengeluaran" else 0.0

        # Ambil saldo per bank dari baris terakhir UI (hanya untuk kalkulasi kolom bank),
        # tapi kebenaran final tetap diserahkan ke API saat reload.
        if not self.data.empty:
            last = self.data.iloc[-1]; per_bank = {b: float(last[b]) for b in BANK_LIST}
        else:
            per_bank = {b: 0.0 for b in BANK_LIST}
        if bank in BANK_LIST:
            per_bank[bank] += (credit - debit)
        new_total = sum(per_bank.values())
        now = datetime.now().strftime(CONFIG['date_format'])
        new_no = int(self.data["No."].iloc[-1]) + 1 if (not self.data.empty and "No." in self.data.columns) else 1
        new_row = [new_no, now, user_id, bank, str(desc), credit, debit, new_total] + [per_bank[b] for b in BANK_LIST]

        if self.gsheets.append_data(new_row):
            audit_log("Save Transaction", f"{user_id} {ttype} {amount}")
            self.clear_inputs()
            # Penting: langsung reload dari API agar state = Google Sheets (realtime, no drift)
            self.load_data()
            messagebox.showinfo("Sukses", "Transaksi disimpan")
        else:
            messagebox.showerror("Error", "Gagal simpan ke Google Sheets")
        self.update_status()

    def open_transfer_dialog(self):
        dlg = tb.Toplevel(self); dlg.title("Transfer Antar Bank"); dlg.geometry("420x240")
        label_style = {"font": FONT_BOLD}
        ttk.Label(dlg, text="Dari Bank:", **label_style).grid(row=0, column=0, padx=8, pady=6, sticky=tk.E)
        src = ttk.Combobox(dlg, values=BANK_LIST, state="readonly", width=24, font=FONT_BOLD); src.grid(row=0, column=1, padx=8, pady=6)
        ttk.Label(dlg, text="Ke Bank:", **label_style).grid(row=1, column=0, padx=8, pady=6, sticky=tk.E)
        dst = ttk.Combobox(dlg, values=BANK_LIST, state="readonly", width=24, font=FONT_BOLD); dst.grid(row=1, column=1, padx=8, pady=6)
        ttk.Label(dlg, text="Jumlah (IDR):", **label_style).grid(row=2, column=0, padx=8, pady=6, sticky=tk.E)
        amt = ttk.Entry(dlg, width=26, font=FONT_BOLD); amt.grid(row=2, column=1, padx=8, pady=6)
        ttk.Label(dlg, text="Keterangan:", **label_style).grid(row=3, column=0, padx=8, pady=6, sticky=tk.E)
        desc = ttk.Entry(dlg, width=26, font=FONT_BOLD); desc.grid(row=3, column=1, padx=8, pady=6)

        def do_transfer():
            try:
                s = src.get().strip(); d = dst.get().strip(); a = parse_amount_idr(amt.get())
                if not s or not d or s == d or a <= 0:
                    messagebox.showerror("Error", "Pilih bank berbeda dan isi jumlah > 0"); return
                note = desc.get().strip() or f"Transfer {s} → {d}"
                # buat dua baris transaksi
                self._append_transaction_row("SYSTEM", s, 0.0, a, note)
                self._append_transaction_row("SYSTEM", d, a, 0.0, note)
                self.load_data()  # reload dari API
                messagebox.showinfo("Sukses", "Transfer berhasil dicatat")
                dlg.destroy()
            except Exception as e:
                messagebox.showerror("Error", f"Gagal transfer: {e}")

        tb.Button(dlg, text="Proses", bootstyle="success", command=do_transfer, width=14).grid(row=4, column=0, columnspan=2, pady=12)

    def _append_transaction_row(self, user_id, bank, credit, debit, desc):
        if not self.data.empty:
            last = self.data.iloc[-1]; per_bank = {b: float(last[b]) for b in BANK_LIST}
        else:
            per_bank = {b: 0.0 for b in BANK_LIST}
        if bank in BANK_LIST:
            per_bank[bank] += (float(credit) - float(debit))
        new_total = sum(per_bank.values())
        now = datetime.now().strftime(CONFIG['date_format'])
        new_no = int(self.data["No."].iloc[-1]) + 1 if (not self.data.empty and "No." in self.data.columns) else 1
        row = [new_no, now, user_id, bank, str(desc), float(credit), float(debit), new_total] + [per_bank[b] for b in BANK_LIST]
        if self.gsheets.append_data(row):
            audit_log("Transfer Row", f"{user_id} {bank} +{credit} -{debit}")

    def set_initial_balance(self):
        dialog = tb.Toplevel(self); dialog.title("Set Saldo Awal Bank"); dialog.geometry("420x560")
        entries = {}
        for i, b in enumerate(BANK_LIST):
            ttk.Label(dialog, text=f"{b}:", font=FONT_BOLD).grid(row=i, column=0, padx=6, pady=4, sticky=tk.E)
            e = ttk.Entry(dialog, width=22, font=FONT_BOLD); e.grid(row=i, column=1, padx=6, pady=4)
            if not self.data.empty and b in self.data.columns:
                try: e.insert(0, str(int(float(self.data[b].iloc[-1]))))
                except Exception: e.insert(0, "0")
            entries[b] = e

        def save_bal():
            try:
                per_bank = {b: parse_amount_idr(entries[b].get()) for b in BANK_LIST}
                total = sum(per_bank.values())
                now = datetime.now().strftime(CONFIG['date_format'])
                new_no = int(self.data["No."].iloc[-1]) + 1 if (not self.data.empty and "No." in self.data.columns) else 1
                row = [new_no, now, "SYSTEM", "SALDO AWAL", "Penyesuaian saldo awal", 0, 0, total] + [per_bank[b] for b in BANK_LIST]
                if self.gsheets.append_data(row):
                    self.load_data()   # reload dari API
                    messagebox.showinfo("Sukses", "Saldo awal disimpan"); dialog.destroy()
                else:
                    messagebox.showerror("Error", "Gagal menyimpan saldo awal")
            except Exception as e:
                messagebox.showerror("Error", f"Input tidak valid: {e}")

        tb.Button(dialog, text="Simpan Saldo Awal", bootstyle="success", command=save_bal).grid(row=len(BANK_LIST), column=0, columnspan=2, pady=12)

    def clear_inputs(self):
        self.user_entry.delete(0, tk.END)
        self.bank_combo.set('')
        self.type_combo.current(0)
        self.amount_entry.delete(0, tk.END)
        self.desc_entry.delete(0, tk.END)
        self.amount_preview.config(text="Terbaca: Rp0 IDR")

    # ---------- Export ----------
    def _get_relevant_columns(self): return HEADERS

    def export_excel(self):
        if self.filtered_data.empty:
            return messagebox.showinfo("Info","Tidak ada data")
        path = filedialog.asksaveasfilename(defaultextension=".xlsx", filetypes=[("Excel","*.xlsx")])
        if not path: return
        try:
            self.filtered_data[self._get_relevant_columns()].to_excel(path, index=False)
            audit_log("Export Excel", path); messagebox.showinfo("Sukses", f"Tersimpan ke {path}")
        except Exception as e:
            messagebox.showerror("Error", f"Gagal export: {e}")

    def export_csv(self):
        if self.filtered_data.empty:
            return messagebox.showinfo("Info","Tidak ada data")
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV","*.csv")])
        if not path: return
        try:
            self.filtered_data[self._get_relevant_columns()].to_csv(path, index=False, encoding='utf-8-sig')
            audit_log("Export CSV", path); messagebox.showinfo("Sukses", f"Tersimpan ke {path}")
        except Exception as e:
            messagebox.showerror("Error", f"Gagal export: {e}")

    def _render_charts_to_images(self):
        buf_bal = io.BytesIO(); self.fig_balance.savefig(buf_bal, format='png', bbox_inches='tight', dpi=160); buf_bal.seek(0)
        buf_type = io.BytesIO(); self.fig_type.savefig(buf_type, format='png', bbox_inches='tight', dpi=160); buf_type.seek(0)
        buf_month = io.BytesIO(); self.fig_month.savefig(buf_month, format='png', bbox_inches='tight', dpi=160); buf_month.seek(0)
        return buf_bal, buf_type, buf_month

    def export_pdf(self):
        if self.filtered_data.empty:
            return messagebox.showinfo("Info","Tidak ada data")
        path = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF","*.pdf")])
        if not path: return
        try:
            doc = SimpleDocTemplate(path, pagesize=A4, rightMargin=24, leftMargin=24, topMargin=24, bottomMargin=24)
            el = []; styles = getSampleStyleSheet()
            el.append(Paragraph("Laporan Transaksi Money Manager Pro", styles['Title']))
            el.append(Paragraph(f"Generated: {datetime.now().strftime('%d/%m/%Y %H:%M:%S')}", styles['Normal'])); el.append(Spacer(1,10))
            income = self.filtered_data['Credit'].sum(); expense = self.filtered_data['Debit'].sum(); balance = self.filtered_data['Saldo Akhir'].iloc[-1]
            el.append(Paragraph(f"<b>Ringkasan:</b><br/>Total Transaksi: {len(self.filtered_data)}<br/>Total Pemasukan: {fmt_idr(income)}<br/>Total Pengeluaran: {fmt_idr(expense)}<br/>Saldo Akhir: {fmt_idr(balance)}", styles['Normal'])); el.append(Spacer(1,8))
            cols = self._get_relevant_columns(); table_rows = []
            for _, row in self.filtered_data.iterrows():
                rd = {c: row.get(c, "") for c in cols}; disp = []
                for c in cols:
                    if c in MONEY_COLS:
                        try: disp.append(fmt_idr(float(rd[c])))
                        except Exception: disp.append(fmt_idr(0))
                    else: disp.append(rd[c])
                table_rows.append(disp)
            table_data = [cols] + table_rows
            tbl = Table(table_data, repeatRows=1)
            tbl.setStyle(TableStyle([('BACKGROUND', (0,0), (-1,0), colors.HexColor("#607D8B")),
                                     ('TEXTCOLOR', (0,0), (-1,0), colors.whitesmoke),
                                     ('ALIGN', (0,0), (-1,-1), 'CENTER'),
                                     ('FONTNAME', (0,0), (-1,0), 'Helvetica-Bold'),
                                     ('FONTSIZE', (0,0), (-1,0), 9),
                                     ('BOTTOMPADDING', (0,0), (-1,0), 8),
                                     ('BACKGROUND', (0,1), (-1,-1), colors.whitesmoke),
                                     ('GRID', (0,0), (-1,-1), 0.25, colors.grey)]))
            el.append(tbl); el.append(Spacer(1,12))
            bal_png, type_png, month_png = self._render_charts_to_images()
            el.append(Paragraph("<b>Grafik Saldo</b>", styles['Heading3'])); el.append(Image(bal_png, width=500, height=220)); el.append(Spacer(1,8))
            el.append(Paragraph("<b>Distribusi Transaksi</b>", styles['Heading3'])); el.append(Image(type_png, width=350, height=220)); el.append(Spacer(1,8))
            el.append(Paragraph("<b>Perbandingan Bulanan (Income vs Expense)</b>", styles['Heading3'])); el.append(Image(month_png, width=500, height=220))
            doc.build(el); audit_log("Export PDF", path); messagebox.showinfo("Sukses", f"PDF tersimpan ke {path}")
        except Exception as e:
            messagebox.showerror("Error", f"Gagal export: {e}")

    # ---------- Background ----------
    def start_background_tasks(self):
        def auto_bak():
            while True:
                try:
                    if not self.data.empty:
                        self.backup.create_backup(self.data)
                        self.check_parity_against_api(silent=True)
                except:
                    pass
                time.sleep(CONFIG['auto_save_interval'])
        threading.Thread(target=auto_bak, daemon=True).start()

    # ---------- New helpers ----------
    def check_min_balance(self, df: pd.DataFrame):
        warnings = []
        if df.empty:
            return warnings
        latest = df.iloc[-1]
        for b, th in CONFIG['min_balance_thresholds'].items():
            try:
                if float(latest[b]) < float(th):
                    warnings.append(f"{b} rendah: {fmt_idr(latest[b])}")
            except Exception:
                continue
        return warnings

# ============= BACKUP =============
class BackupManager:
    def __init__(self):
        ensure_dirs()
    def create_backup(self, data, filename=None):
        try:
            if filename is None:
                filename = f"backup_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pkl"
            path = os.path.join(CONFIG['backup_folder'], filename)
            with open(path, "wb") as f:
                pickle.dump(data, f)
            audit_log("Backup Created", filename)
            self.cleanup_old()
            return True
        except Exception as e:
            print("Backup error:", e)
            audit_log("Backup Failed", str(e))
            return False
    def cleanup_old(self):
        try:
            files = sorted([f for f in os.listdir(CONFIG['backup_folder']) if f.startswith("backup_")], reverse=True)
            for f in files[CONFIG['backup_limit']:]:
                os.remove(os.path.join(CONFIG['backup_folder'], f))
        except Exception as e:
            print("Cleanup error:", e)

# ============= MAIN =============
if __name__ == "__main__":
    app = MoneyManagerPro()
    app.start_background_tasks()
    app.mainloop()
