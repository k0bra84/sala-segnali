#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Sala segnali
============
Segnali crypto "long" (solo acquisti, come su Revolut X) su candele a 4 ore.

- I prezzi arrivano da piu' exchange (Kraken, Binance, Coinbase) e vengono confrontati:
  un segnale e' valido solo se almeno due fonti indipendenti concordano.
- Tutti gli indicatori sono calcolati qui, sui prezzi grezzi (nessun punteggio di terzi).
- Le regole sono scritte in chiaro nella sezione STRAT e restano fisse: il "test in avanti"
  parte dal primo avvio e conta solo i segnali nati dopo quel momento.

Uso:
    python3 signalroom.py            # aggiornamento normale (dati reali, scrive docs/index.html)
    python3 signalroom.py --demo     # dati inventati per vedere la pagina (non tocca state.json)

Solo libreria standard di Python, nessuna installazione.
Questo programma non e' una consulenza finanziaria e non garantisce guadagni.
"""
from __future__ import annotations

import base64
import html as _html
import json
import math
import os
import random
import statistics
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

VERSION = "v1"
HERE = Path(__file__).resolve().parent
STATE_FILE = HERE / "state.json"
OUT_DIR = HERE / "docs"

BAR_S = 4 * 3600
BAR_MS = BAR_S * 1000

# ----------------------------------------------------------------------------
# IMPOSTAZIONI (le uniche da toccare sono costi e capitale)
# ----------------------------------------------------------------------------
CAPITAL_EUR = 1000          # capitale usato nelle notifiche Telegram
NOTIFY_PROFILE = "medio"    # profilo di rischio usato nelle notifiche
FEE_PER_SIDE = 0.0010       # commissione per ogni operazione (0,10%): controlla quella reale su Revolut X
SLIP_PER_SIDE = 0.0010      # scostamento tra prezzo visto e prezzo ottenuto, per operazione
HISTORY_DAYS = 365          # storico per il backtest (se la fonte lo permette)
MIN_BARS = 260              # candele minime per calcolare gli indicatori
VERIFY_BARS = 240           # candele usate per il confronto tra fonti

# Le monete della watchlist su Revolut. Alcune hanno cambiato sigla sugli exchange.
COINS = [
    ("BTC", "Bitcoin"), ("ETH", "Ether"), ("XRP", "XRP"), ("BNB", "BNB"),
    ("DOGE", "Dogecoin"), ("TRX", "Tron"), ("LINK", "Chainlink"), ("BCH", "Bitcoin Cash"),
    ("ETC", "Ethereum Classic"), ("ATOM", "Cosmos"), ("NEAR", "NEAR"), ("TON", "Toncoin"),
    ("ARB", "Arbitrum"), ("OP", "Optimism"), ("IMX", "Immutable"), ("SEI", "SEI"),
    ("TAO", "Bittensor"), ("FET", "Fetch.ai"), ("RNDR", "Render"), ("FIL", "Filecoin"),
    ("GRT", "The Graph"), ("ENA", "Ethena"), ("CELO", "Celo"), ("ANKR", "Ankr"),
    ("MATIC", "Polygon"), ("FTM", "Fantom / Sonic"), ("MEW", "cat in a dogs world"),
    ("GST", "Green Satoshi Token"),
]
ALIASES = {"FTM": ["S", "FTM"], "MATIC": ["POL", "MATIC"], "RNDR": ["RENDER", "RNDR"]}

# Regole della strategia (fisse dalla versione v1).
STRAT = dict(
    ema_fast=50, ema_slow=200,
    rsi_len=14, rsi_pullback=40, rsi_resume=45, pb_lookback=8,
    adx_len=14, adx_min=20,
    atr_len=14, vol_len=20, vol_ratio=1.0,
    sl_atr=2.0,          # stop loss a 2 ATR sotto l'entrata
    tp_atr=4.0,          # take profit a 4 ATR sopra l'entrata
    be_trigger=1.5,      # a +1,5 ATR lo stop va al pareggio
    trail_trigger=2.5,   # a +2,5 ATR lo stop sale a +1 ATR
    trail_lock=1.0,
    max_hold=42,         # uscita a tempo dopo 42 candele (7 giorni)
    cooldown=6,          # candele di pausa dopo la chiusura di un trade sulla stessa moneta
    max_risk=0.20,       # niente segnali se lo stop e' oltre il 20% di distanza
    warmup=210,
)

# Spia dei volumi: solo informativa, non cambia i segnali.
# Si accende se in una delle ultime `recent` candele il volume e' almeno `ratio` volte
# la mediana dei volumi delle `base` candele precedenti.
FLAG = dict(ratio=3.0, base=20, recent=3)

# Fase di mercato letta su Bitcoin: solo informativa. L'unico filtro sui segnali resta
# "Bitcoin sopra la sua media a 200 candele" (prima condizione).
PHASE = dict(adx_strong=20, vol_window=180, vol_min_hist=60, vol_pct=0.80)
PHASE_NAMES = {
    "rialzo_forte": "Rialzo con forza", "rialzo_debole": "Rialzo debole", "transizione": "Fase di transizione",
    "ribasso_debole": "Ribasso debole", "ribasso_forte": "Ribasso con forza",
}

# Finestra d'ingresso: finche' un segnale si puo' ancora usare per entrare. Solo informativa:
# il simulatore segue comunque tutti i segnali all'entrata originale.
# Valido per `max_bars` candele (12 ore), con il prezzo tra -`down_atr` e +`up_atr` ATR dall'entrata.
ENTRY = dict(max_bars=3, up_atr=0.5, down_atr=1.0)

# Quanto rischiare per trade e quante posizioni tenere insieme.
PROFILES = {
    "basso": dict(risk=0.005, max_pos=3, max_size=0.15),
    "medio": dict(risk=0.010, max_pos=5, max_size=0.25),
    "alto": dict(risk=0.020, max_pos=8, max_size=0.35),
}

# Confronto tra fonti: scostamento mediano e dell'ultima chiusura.
XCHECK_MEDIAN = 0.006
XCHECK_LAST = 0.010

UA = "sala-segnali/1.0"

# Icona 180x180 per la schermata Home del telefono (PNG, scritta in docs/icon.png a ogni aggiornamento).
ICON_B64 = "iVBORw0KGgoAAAANSUhEUgAAALQAAAC0CAIAAACyr5FlAAADYUlEQVR42u3dMWsTYRjA8X4Gh0KxKdcm1raWKlTaRQIdhCJZ6lZcipBNzCBSCi42mxSyiUtBcKu4OWQX/AR+gn4CP4KPBKVo7sh7BhrvfvDfejnoPb/c3fLmnbsxf1Ma25xLIDgEh+AQHIJDcAgOwSE4BIcEh+AQHIJDcAgOwSE4BIfgkOAQHIJDcAgOwSE49HfZ3m5ecNS0+eWV7ePD/WG/8+VNQTunRwub63DUS8beh5fFLH4XgBo79+CoS3E/mFDGqIefXsFRi+IxkSRjVKvThqP6xZhL4Lj77DEc1S/GDIfgEByCQ3DAAQcccMABBxxwwAEHHHDAITgEh+AQHHDAAQcccMABBxxwwAHH/1OWLb7urnx9u/r983pe8dfuQQZH7WQUs7ja+UkLjho1PJtUxqhBrwlHLXrUXkqSMSpuNnBUv3jVKIEjSMEBBxxwwCE44IADDjjggAMOOOCAAw444IADDjjggAMOwQEHHHDAAQcccMABBxxwwAEHHHDMWt2D7GP/1vBsNa9Br7m10YCjXjgmX4l0ebFWsFINjgrimHyNWsE44Zir5NMkdZzxiIGjFjjiPaPEROGoBY7U1a1wwAEHHHDAAQcccMABBxxwwAEHHHDAAQcccMABBxxwwAEHHHDAAQcccMABBxxwwAEHHHBcd3FlYyQF5S0jgKPKOLJsccK5xmFj9zSBo5o4knbLGu2plucDjqrhKDGG+AgctcCRuoCxYJkaHFXDUWIGcMABBxxwwAEHHHDAAQcccMABBxxwwAEHHHDAAQcccMABBxxwwAEHHHDAAQcccMABBxxwwAEHHHDAAQccv/r2/va0cMzmZjzZ3i4cJTs/aaXOID4y9lRT3MZra6OReqrLi7W8/3F/2E/FsbC5DsfPtbJxWZNmULCWelobAEaDXjPpVC+eLOed6s7TTpKM7ePD6x3KDK2yf3B/acKHSxwWB09lWXbx1qGpd7W85bsl3jx2To+ufSKz9fscMdT45hVsExzFAQX3jD+eL/+46fDVXw0JIlM5VTwp4pbQfvc8r2ARLyizMA7blQsOwSE4BIfgEByCQ3AIDsEhwSE4BIfgEByCQ3AIDsEhOCQ4BIfgEByCQ3AIDsEhOASHBIfgEByCQ3AIDsEhOASH4BAcEhxK6AdlYCmqPDxUzQAAAABJRU5ErkJggg=="


def log(*a):
    print(*a, file=sys.stderr, flush=True)


# ----------------------------------------------------------------------------
# INDICATORI (formule standard, calcolate sui prezzi grezzi)
# ----------------------------------------------------------------------------
def ema(vals, n):
    out = [None] * len(vals)
    if len(vals) < n:
        return out
    k = 2.0 / (n + 1)
    s = sum(vals[:n]) / n
    out[n - 1] = s
    for i in range(n, len(vals)):
        s = vals[i] * k + s * (1 - k)
        out[i] = s
    return out


def sma(vals, n):
    out = [None] * len(vals)
    if len(vals) < n:
        return out
    s = sum(vals[:n])
    out[n - 1] = s / n
    for i in range(n, len(vals)):
        s += vals[i] - vals[i - n]
        out[i] = s / n
    return out


def rsi(closes, n=14):
    """RSI di Wilder."""
    out = [None] * len(closes)
    if len(closes) <= n:
        return out
    g = l = 0.0
    for i in range(1, n + 1):
        d = closes[i] - closes[i - 1]
        g += max(d, 0.0)
        l += max(-d, 0.0)
    ag, al = g / n, l / n

    def val(ag, al):
        if al == 0:
            return 50.0 if ag == 0 else 100.0
        return 100.0 - 100.0 / (1.0 + ag / al)

    out[n] = val(ag, al)
    for i in range(n + 1, len(closes)):
        d = closes[i] - closes[i - 1]
        ag = (ag * (n - 1) + max(d, 0.0)) / n
        al = (al * (n - 1) + max(-d, 0.0)) / n
        out[i] = val(ag, al)
    return out


def true_range(h, l, c):
    tr = [h[0] - l[0]]
    for i in range(1, len(c)):
        tr.append(max(h[i] - l[i], abs(h[i] - c[i - 1]), abs(l[i] - c[i - 1])))
    return tr


def atr(h, l, c, n=14):
    """ATR di Wilder: la volatilita' tipica di una candela, in unita' di prezzo."""
    out = [None] * len(c)
    if len(c) <= n:
        return out
    tr = true_range(h, l, c)
    a = sum(tr[1:n + 1]) / n
    out[n] = a
    for i in range(n + 1, len(c)):
        a = (a * (n - 1) + tr[i]) / n
        out[i] = a
    return out


def adx(h, l, c, n=14):
    """ADX di Wilder con +DI e -DI. Ritorna (adx, pdi, mdi)."""
    N = len(c)
    adx_o, pdi_o, mdi_o = [None] * N, [None] * N, [None] * N
    if N < 2 * n + 1:
        return adx_o, pdi_o, mdi_o
    tr = true_range(h, l, c)
    pdm, mdm = [0.0] * N, [0.0] * N
    for i in range(1, N):
        up, dn = h[i] - h[i - 1], l[i - 1] - l[i]
        pdm[i] = up if (up > dn and up > 0) else 0.0
        mdm[i] = dn if (dn > up and dn > 0) else 0.0
    s_tr = sum(tr[1:n + 1])
    s_p = sum(pdm[1:n + 1])
    s_m = sum(mdm[1:n + 1])
    dx = [None] * N

    def di(sp, sm, st):
        if st == 0:
            return 0.0, 0.0, 0.0
        p, m = 100.0 * sp / st, 100.0 * sm / st
        d = 0.0 if (p + m) == 0 else 100.0 * abs(p - m) / (p + m)
        return p, m, d

    p, m, d = di(s_p, s_m, s_tr)
    pdi_o[n], mdi_o[n], dx[n] = p, m, d
    for i in range(n + 1, N):
        s_tr = s_tr - s_tr / n + tr[i]
        s_p = s_p - s_p / n + pdm[i]
        s_m = s_m - s_m / n + mdm[i]
        p, m, d = di(s_p, s_m, s_tr)
        pdi_o[i], mdi_o[i], dx[i] = p, m, d
    a = sum(dx[n:2 * n]) / n
    adx_o[2 * n - 1] = a
    for i in range(2 * n, N):
        a = (a * (n - 1) + dx[i]) / n
        adx_o[i] = a
    return adx_o, pdi_o, mdi_o


def volume_flag(v, i):
    """Spia dei volumi sulla candela chiusa i. Ritorna (acceso, rapporto_massimo) oppure None.
    Il rapporto e' volume / mediana delle `base` candele precedenti (la mediana non si lascia
    spostare da un vecchio picco). Candele con mediana zero (moneta senza scambi) sono saltate."""
    F = FLAG
    best = None
    for j in range(i - F["recent"] + 1, i + 1):
        if j - F["base"] < 0:
            return None
        med = statistics.median(v[j - F["base"]:j])
        if med <= 0:
            continue
        r = v[j] / med
        best = r if best is None else max(best, r)
    if best is None:
        return None
    return best >= F["ratio"], best


def phase_series(cols, ind):
    """Fase di mercato per ogni candela, calcolata sulle candele di Bitcoin.
    Direzione: rialzo se prezzo e media a 50 sono sopra la media a 200, ribasso se sono sotto,
    altrimenti transizione. Forza: ADX. Volatilita' alta: ATR in % del prezzo nel 20% piu' alto
    degli ultimi `vol_window` valori. Ritorna {inizio_candela_ms: (etichetta, volatilita_alta)}."""
    P = PHASE
    c, t = cols["c"], cols["t"]
    natr = [None if ind["atr"][i] is None else ind["atr"][i] / c[i] for i in range(len(c))]
    out = {}
    for i in range(len(c)):
        e_f, e_s, ad = ind["ema_f"][i], ind["ema_s"][i], ind["adx"][i]
        if None in (e_f, e_s, ad):
            continue
        strong = ad >= P["adx_strong"]
        if c[i] > e_s and e_f > e_s:
            label = "rialzo_forte" if strong else "rialzo_debole"
        elif c[i] < e_s and e_f < e_s:
            label = "ribasso_forte" if strong else "ribasso_debole"
        else:
            label = "transizione"
        past = [x for x in natr[max(0, i - P["vol_window"]):i] if x is not None]
        hv = (natr[i] is not None and len(past) >= P["vol_min_hist"]
              and sum(1 for x in past if x < natr[i]) / len(past) >= P["vol_pct"])
        out[t[i]] = (label, bool(hv))
    return out


def indicators(cols):
    S = STRAT
    c, h, l, v = cols["c"], cols["h"], cols["l"], cols["v"]
    a, p, m = adx(h, l, c, S["adx_len"])
    return dict(
        ema_f=ema(c, S["ema_fast"]), ema_s=ema(c, S["ema_slow"]),
        rsi=rsi(c, S["rsi_len"]), atr=atr(h, l, c, S["atr_len"]),
        adx=a, pdi=p, mdi=m, vsma=sma(v, S["vol_len"]),
    )


# ----------------------------------------------------------------------------
# REGOLE DEL SEGNALE
# ----------------------------------------------------------------------------
CHECKS = ("regime", "trend", "strong", "resume", "vol")


def conditions(ind, cols, i, regime_ok):
    """Valuta le 5 condizioni sulla candela chiusa i. None se mancano dati."""
    S = STRAT
    c, v = cols["c"], cols["v"]
    e_f, e_s = ind["ema_f"][i], ind["ema_s"][i]
    ad, pd, md = ind["adx"][i], ind["pdi"][i], ind["mdi"][i]
    r, r1 = ind["rsi"][i], ind["rsi"][i - 1]
    at, vs = ind["atr"][i], ind["vsma"][i]
    win = ind["rsi"][i - S["pb_lookback"]:i]
    if None in (e_f, e_s, ad, pd, md, r, r1, at, vs) or any(x is None for x in win):
        return None
    volr = v[i] / vs if vs else 0.0
    vf = volume_flag(v, i)
    return dict(
        regime=bool(regime_ok),
        trend=(e_f > e_s and c[i] > e_s),
        strong=(ad >= S["adx_min"] and pd > md),
        resume=(min(win) <= S["rsi_pullback"] and r > S["rsi_resume"] and r1 <= S["rsi_resume"]),
        vol=(volr >= S["vol_ratio"]),
        adx=ad, rsi=r, volr=volr, atr=at, e_f=e_f, e_s=e_s,
        spike=bool(vf and vf[0]), spike_ratio=(vf[1] if vf else None),
    )


def why_text(cd):
    return [
        "Mercato in regime rialzista: Bitcoin sopra la sua media a 200 candele",
        "Trend rialzista: media a 50 sopra la media a 200 e prezzo sopra la media a 200",
        "Trend con forza: ADX %.0f (soglia %d), compratori in vantaggio" % (cd["adx"], STRAT["adx_min"]),
        "Ripartenza dopo un calo: RSI risalito a %.0f dopo essere sceso sotto %d" % (cd["rsi"], STRAT["rsi_pullback"]),
        "Volume %s volte la media recente" % it_num(cd["volr"], 1),
    ]


def cost_side():
    return FEE_PER_SIDE + SLIP_PER_SIDE


def be_level(entry):
    c = cost_side()
    return entry * (1 + c) / (1 - c)


def new_trade(sym, i, t_close, close, atr_v, why, vol=None, phase=None):
    S, c = STRAT, cost_side()
    sl = close - S["sl_atr"] * atr_v
    if sl <= 0:
        return None
    tp = close + S["tp_atr"] * atr_v
    risk = 1.0 - sl * (1 - c) / (close * (1 + c))
    if risk <= 0 or risk > S["max_risk"]:
        return None
    return dict(sym=sym, e_idx=i, t_in=t_close, entry=close, atr=atr_v, sl0=sl, sl=sl, tp=tp,
                stage=0, events=[], risk=risk, why=why, status="open",
                spike=bool(vol and vol[0]), spike_ratio=(vol[1] if vol else None),
                phase=(phase[0] if phase else None), phase_hv=bool(phase and phase[1]))


def step_trade(T, i, t_close, o, h, l, c):
    """Applica la candela i al trade T. Ritorna True se il trade si chiude.
    Se nella stessa candela scattano stop e target, vale lo stop (ipotesi prudente).
    Gli spostamenti dello stop valgono dalla candela successiva."""
    S, cs = STRAT, cost_side()
    hold = i - T["e_idx"]
    px = reason = None
    if l <= T["sl"]:
        px = o if o < T["sl"] else T["sl"]
        reason = ("stop", "pareggio", "trailing")[T["stage"]]
    elif h >= T["tp"]:
        px = o if o > T["tp"] else T["tp"]
        reason = "target"
    elif hold >= S["max_hold"]:
        px, reason = c, "tempo"
    if px is not None:
        T.update(status="closed", t_out=t_close, p_out=px, reason=reason, bars=hold)
        T["ret"] = px * (1 - cs) / (T["entry"] * (1 + cs)) - 1.0
        T["r"] = T["ret"] / T["risk"]
        return True
    a = T["atr"]
    if T["stage"] < 2 and h >= T["entry"] + S["trail_trigger"] * a:
        T["sl"] = max(T["sl"], T["entry"] + S["trail_lock"] * a)
        T["stage"] = 2
        T["events"].append([t_close, "trail", T["sl"]])
    elif T["stage"] < 1 and h >= T["entry"] + S["be_trigger"] * a:
        T["sl"] = max(T["sl"], be_level(T["entry"]))
        T["stage"] = 1
        T["events"].append([t_close, "be", T["sl"]])
    return False


def simulate_coin(sym, cols, ind, regime, phases=None):
    """Rigioca tutta la storia di una moneta. regime: dict {inizio_candela_ms: bool}.
    Ritorna la lista dei trade (l'ultimo puo' essere ancora aperto)."""
    S = STRAT
    n = len(cols["c"])
    trades, cur, pause = [], None, -1
    for i in range(S["warmup"], n):
        t_close = cols["t"][i] + BAR_MS
        if cur is not None:
            if step_trade(cur, i, t_close, cols["o"][i], cols["h"][i], cols["l"][i], cols["c"][i]):
                trades.append(cur)
                cur, pause = None, i + S["cooldown"]
                continue
        if cur is None and i > pause:
            cd = conditions(ind, cols, i, regime.get(cols["t"][i], False))
            if cd and all(cd[k] for k in CHECKS):
                cur = new_trade(sym, i, t_close, cols["c"][i], cd["atr"], why_text(cd),
                                vol=(cd["spike"], cd["spike_ratio"]),
                                phase=(phases or {}).get(cols["t"][i]))
    if cur is not None:
        trades.append(cur)
    return trades


# ----------------------------------------------------------------------------
# PORTAFOGLIO, STATISTICHE
# ----------------------------------------------------------------------------
def size_pct(profile, risk):
    P = PROFILES[profile]
    return min(P["risk"] / risk, P["max_size"]) if risk > 0 else 0.0


def signal_stats(trades):
    """Qualita' dei segnali, indipendente da quanto si investe."""
    n = len(trades)
    if n == 0:
        return dict(n=0)
    wins = [t for t in trades if t["ret"] > 0]
    gp = sum(t["ret"] for t in wins)
    gl = -sum(t["ret"] for t in trades if t["ret"] <= 0)
    return dict(n=n, win_rate=len(wins) / n, avg_r=sum(t["r"] for t in trades) / n,
                avg_ret=sum(t["ret"] for t in trades) / n,
                pf=(gp / gl) if gl > 0 else None, avg_bars=sum(t["bars"] for t in trades) / n)


def portfolio(trades, profile):
    """Simula il capitale (partendo da 1,0) seguendo tutti i segnali con le regole del profilo."""
    P = PROFILES[profile]
    ev = []
    for i, t in enumerate(trades):
        ev.append((t["t_in"], 1, i))
        ev.append((t["t_out"], 0, i))
    ev.sort()
    E, open_amt, curve, taken, skipped = 1.0, {}, [], [], 0
    if ev:
        curve.append([ev[0][0], 1.0])
    for tm, kind, i in ev:
        t = trades[i]
        if kind == 1:
            if len(open_amt) >= P["max_pos"]:
                skipped += 1
                continue
            alloc = size_pct(profile, t["risk"]) * E
            avail = E - sum(open_amt.values())
            alloc = min(alloc, avail)
            if alloc < 0.05 * E:
                skipped += 1
                continue
            open_amt[i] = alloc
        elif i in open_amt:
            a = open_amt.pop(i)
            E += a * t["ret"]
            curve.append([tm, E])
            taken.append((a, a * t["ret"]))
    peak, mdd = 1.0, 0.0
    for _, e in curve:
        peak = max(peak, e)
        mdd = max(mdd, 1 - e / peak)
    pos = sum(p for _, p in taken if p > 0)
    neg = -sum(p for _, p in taken if p <= 0)
    return dict(equity=curve, final=E, n=len(taken), skipped=skipped, mdd=mdd,
                wins=sum(1 for _, p in taken if p > 0),
                pf=(pos / neg) if neg > 0 else None,
                avg_size=(sum(a for a, _ in taken) / len(taken)) if taken else 0.0)


# ----------------------------------------------------------------------------
# DATI: download da piu' fonti
# ----------------------------------------------------------------------------
class NoSymbol(Exception):
    pass


def http_get(url, params=None, timeout=25, tries=3):
    if params:
        url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    last = None
    for k in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "application/json"})
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return json.loads(r.read().decode("utf-8"))
        except urllib.error.HTTPError as e:
            last = e
            if e.code in (400, 403, 404, 451):
                break
            time.sleep(2 + 3 * k if e.code == 429 else 1 + k)
        except Exception as e:  # rete, timeout, JSON
            last = e
            time.sleep(1 + k)
    raise last


def aliases(sym):
    return ALIASES.get(sym, [sym])


def clean_rows(rows, now_ms):
    """Ordina, toglie i doppioni e le candele non ancora chiuse. None se vuoto o vecchio."""
    if not rows:
        return None
    d = {r[0]: r for r in rows}
    out = [d[k] for k in sorted(d) if k + BAR_MS <= now_ms]
    if not out or out[-1][0] < now_ms - 3 * BAR_MS:
        return None
    return out


def to_cols(rows):
    return dict(t=[r[0] for r in rows], o=[r[1] for r in rows], h=[r[2] for r in rows],
                l=[r[3] for r in rows], c=[r[4] for r in rows], v=[r[5] for r in rows])


class Kraken:
    name = "kraken"
    delay = 1.1

    def __init__(self):
        self.pairs = {}

    def load(self):
        j = http_get("https://api.kraken.com/0/public/AssetPairs")
        for key, p in j.get("result", {}).items():
            ws = p.get("wsname") or ""
            if "/" not in ws or key.endswith(".d"):
                continue
            base, quote = ws.split("/")
            if quote == "USD":
                self.pairs[{"XBT": "BTC", "XDG": "DOGE"}.get(base, base)] = key

    def candles(self, sym):
        for al in aliases(sym):
            key = self.pairs.get(al)
            if not key:
                continue
            j = http_get("https://api.kraken.com/0/public/OHLC", {"pair": key, "interval": 240})
            res = j.get("result", {})
            for k, v in res.items():
                if k != "last" and v:
                    return [(int(r[0]) * 1000, float(r[1]), float(r[2]), float(r[3]), float(r[4]), float(r[6]))
                            for r in v]
        return None


class Binance:
    name = "binance"
    delay = 0.1
    BASES = ["https://data-api.binance.vision", "https://api.binance.com"]

    def _get(self, params):
        err = None
        for b in self.BASES:
            try:
                return http_get(b + "/api/v3/klines", params, tries=2)
            except urllib.error.HTTPError as e:
                if e.code == 400:
                    raise NoSymbol()
                err = e
            except Exception as e:
                err = e
        raise err

    def candles(self, sym, bars):
        for al in aliases(sym):
            out, end = [], None
            try:
                while len(out) < bars:
                    params = {"symbol": al + "USDT", "interval": "4h", "limit": 1000}
                    if end:
                        params["endTime"] = end
                    j = self._get(params)
                    if not j:
                        break
                    rows = [(int(k[0]), float(k[1]), float(k[2]), float(k[3]), float(k[4]), float(k[5])) for k in j]
                    out = rows + out
                    end = rows[0][0] - 1
                    if len(j) < 1000:
                        break
                    time.sleep(self.delay)
            except NoSymbol:
                continue
            if out:
                return out
        return None


class Coinbase:
    name = "coinbase"
    delay = 0.15

    @staticmethod
    def _iso(ts):
        return datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    def candles(self, sym, bars4h):
        hours = bars4h * 4
        for al in aliases(sym):
            prod = "%s-USD" % al
            raw, end, need = [], int(time.time()), hours
            try:
                while need > 0:
                    span = min(300, need)
                    start = end - span * 3600
                    j = http_get("https://api.exchange.coinbase.com/products/%s/candles" % prod,
                                 {"granularity": 3600, "start": self._iso(start), "end": self._iso(end)})
                    raw += j
                    end, need = start, need - span
                    time.sleep(self.delay)
            except urllib.error.HTTPError as e:
                if e.code == 404:
                    continue
                raise
            rows = self.aggregate(raw)
            if rows:
                return rows
        return None

    @staticmethod
    def aggregate(raw):
        """Candele orarie [tempo, minimo, massimo, apertura, chiusura, volume] -> 4 ore allineate UTC."""
        buckets = {}
        for r in sorted(raw, key=lambda x: x[0]):
            b = (int(r[0]) // BAR_S) * BAR_S
            buckets.setdefault(b, []).append(r)
        out = []
        for b, rs in sorted(buckets.items()):
            if len(rs) < 2:
                continue
            out.append((b * 1000, float(rs[0][3]), max(float(x[2]) for x in rs), min(float(x[1]) for x in rs),
                        float(rs[-1][4]), sum(float(x[5]) for x in rs)))
        return out


def get_fx():
    """Dollari per 1 euro. None se nessuna fonte risponde."""
    for url, params in (("https://api.frankfurter.dev/v1/latest", {"base": "EUR", "symbols": "USD"}),
                        ("https://api.frankfurter.app/latest", {"from": "EUR", "to": "USD"})):
        try:
            return float(http_get(url, params, tries=2)["rates"]["USD"])
        except Exception:
            pass
    try:
        j = http_get("https://api.kraken.com/0/public/Ticker", {"pair": "EURUSD"}, tries=2)
        return float(next(iter(j["result"].values()))["c"][0])
    except Exception:
        return None


def collect(now_ms):
    """Scarica tutte le monete. Ritorna ({sym: {fonte: righe}}, stato_fonti)."""
    kr, bn, cb = Kraken(), Binance(), Coinbase()
    status = {k: dict(ok=0, fail=0, note="") for k in ("kraken", "binance", "coinbase")}
    try:
        kr.load()
    except Exception as e:
        status["kraken"]["note"] = "elenco coppie non raggiunto"
        log("Kraken: elenco coppie non raggiunto:", e)
    bars = HISTORY_DAYS * 6
    jobs = (("kraken", lambda s: kr.candles(s), kr.delay),
            ("binance", lambda s: bn.candles(s, bars), bn.delay),
            ("coinbase", lambda s: cb.candles(s, VERIFY_BARS), cb.delay))
    out = {}
    for sym, _ in COINS:
        out[sym] = {}
        for name, fn, delay in jobs:
            if name == "kraken" and not kr.pairs:
                continue
            try:
                rows = clean_rows(fn(sym), now_ms)
            except Exception as e:
                rows = None
                log("%s %s: %s" % (name, sym, e))
            if rows:
                out[sym][name] = rows
                status[name]["ok"] += 1
            else:
                status[name]["fail"] += 1
            time.sleep(delay)
        log("%-5s fonti: %s" % (sym, ", ".join("%s=%d" % (k, len(v)) for k, v in out[sym].items()) or "nessuna"))
    for name, st in status.items():
        if st["ok"] == 0 and not st["note"]:
            st["note"] = "nessuna risposta"
    return out, status


# ----------------------------------------------------------------------------
# CONFRONTO TRA FONTI
# ----------------------------------------------------------------------------
def compare_sources(primary_rows, other_rows):
    """Confronta le chiusure sulle candele in comune. None se sono troppo poche."""
    a = {r[0]: r[4] for r in primary_rows}
    b = {r[0]: r[4] for r in other_rows}
    common = sorted(set(a) & set(b))[-60:]
    if len(common) < 30:
        return None
    devs = [abs(a[t] / b[t] - 1.0) for t in common]
    med, last = statistics.median(devs), devs[-1]
    return dict(median=med, last=last, n=len(common), ok=(med <= XCHECK_MEDIAN and last <= XCHECK_LAST))


def evaluate_sources(srcs):
    """Sceglie la fonte con piu' storico e la confronta con le altre.
    Ritorna (nome_fonte_principale, righe, verdetto, dettagli)."""
    good = {k: v for k, v in srcs.items() if v}
    if not good:
        return None, None, "nodata", {}
    prim = max(good, key=lambda k: len(good[k]))
    if len(good[prim]) < MIN_BARS:
        return prim, good[prim], "short", {}
    det = {}
    for k, rows in good.items():
        if k != prim:
            det[k] = compare_sources(good[prim], rows)
    checked = [d for d in det.values() if d]
    if not checked:
        verdict = "single"
    elif all(d["ok"] for d in checked):
        verdict = "ok"
    else:
        verdict = "discordant"
    return prim, good[prim], verdict, det


# ----------------------------------------------------------------------------
# ANALISI COMPLETA
# ----------------------------------------------------------------------------
STATUS_TEXT = {
    "regime": "In attesa: Bitcoin sotto la sua media a 200 candele (mercato non rialzista)",
    "trend": "In attesa: la moneta non è in trend rialzista",
    "strong": "In attesa: trend troppo debole (ADX basso)",
    "resume": "In attesa: serve un calo seguito da una ripartenza",
    "vol": "In attesa: volume sotto la media",
}
VERDICT_TEXT = {
    "nodata": "Dati non disponibili da nessuna fonte",
    "short": "Storico troppo corto per calcolare gli indicatori",
    "single": "Una sola fonte: solo osservazione, nessun segnale",
    "discordant": "Le fonti non concordano sul prezzo: segnali bloccati",
}


def by_key(trs, key):
    """Statistiche dei segnali raggruppate per un campo del trade (per esempio la fase di mercato)."""
    groups = {}
    for t in trs:
        if t.get(key):
            groups.setdefault(t[key], []).append(t)
    return {k: signal_stats(v) for k, v in groups.items()}


def analyze(raw, src_status, now_ms, state, fx):
    """raw: {sym: {fonte: righe}}. Aggiorna state['forward'] e ritorna il payload per la pagina."""
    coins = {}
    for sym, name in COINS:
        prim, rows, verdict, det = evaluate_sources(raw.get(sym, {}))
        coins[sym] = dict(sym=sym, name=name, prim=prim, rows=rows, verdict=verdict, det=det,
                          srcs=sorted(k for k, v in raw.get(sym, {}).items() if v))
    # regime di mercato: Bitcoin sopra la sua EMA 200 (a 4 ore)
    regime, btc_ok_now, phases, btc_info = {}, None, {}, {}
    b = coins.get("BTC")
    if b and b["rows"] and b["verdict"] == "ok":
        bc = to_cols(b["rows"])
        e = ema(bc["c"], STRAT["ema_slow"])
        for i, t in enumerate(bc["t"]):
            regime[t] = e[i] is not None and bc["c"][i] > e[i]
        btc_ok_now = regime.get(bc["t"][-1])
        bind = indicators(bc)
        phases = phase_series(bc, bind)
        cur = phases.get(bc["t"][-1])
        if cur:
            j = len(bc["c"]) - 1
            btc_info = dict(phase=cur[0], phase_hv=cur[1], btc_adx=bind["adx"][j],
                            btc_dist=bc["c"][j] / bind["ema_s"][j] - 1.0, btc_atr_pct=bind["atr"][j] / bc["c"][j])
    sims, rows_out, n_up = {}, [], 0
    for sym, name in COINS:
        co = coins[sym]
        base = dict(sym=sym, name=name, verdict=co["verdict"], srcs=co["srcs"], prim=co["prim"])
        if co["verdict"] in ("nodata", "short"):
            base.update(status=VERDICT_TEXT[co["verdict"]], kind="nodata")
            rows_out.append(base)
            continue
        cols = to_cols(co["rows"])
        ind = indicators(cols)
        i = len(cols["c"]) - 1
        cd = conditions(ind, cols, i, regime.get(cols["t"][i], False))
        vf = volume_flag(cols["v"], i)
        base.update(spike=bool(vf and vf[0]), spike_ratio=(vf[1] if vf else None),
                    price=cols["c"][i], chg=cols["c"][i] / cols["c"][max(0, i - 6)] - 1.0,
                    bars=len(cols["c"]), t_last=cols["t"][i] + BAR_MS,
                    rsi=(ind["rsi"][i]), adx=(ind["adx"][i]),
                    trend=bool(cd and cd["trend"]))
        n_up += 1 if base["trend"] else 0
        if co["verdict"] in ("single", "discordant"):
            base.update(status=VERDICT_TEXT[co["verdict"]], kind="warn")
        elif cd is None:
            base.update(status="Indicatori non ancora calcolabili", kind="nodata")
        else:
            if co["verdict"] == "ok":
                sims[sym] = (cols, simulate_coin(sym, cols, ind, regime, phases))
            first_fail = next((k for k in CHECKS if not cd[k]), None)
            base.update(status=STATUS_TEXT[first_fail] if first_fail else "Condizioni soddisfatte ora", kind="wait" if first_fail else "signal")
            if first_fail == "resume":
                base["status"] += " (RSI %.0f)" % cd["rsi"]
        rows_out.append(base)

    all_trades = [t for _, (cols, trs) in sims.items() for t in trs]
    closed = [t for t in all_trades if t["status"] == "closed"]
    # --- test in avanti: aggiorna lo storico persistente ---
    fw = state["forward"]
    for sym, (cols, trs) in sims.items():
        for t in trs:
            if t["t_in"] < state["forward_start"]:
                continue
            tid = "%s|%d" % (sym, t["t_in"])
            if tid in fw:
                keep = fw[tid].get("notified", [])
                fw[tid] = dict(t, id=tid, notified=keep, first_seen=fw[tid].get("first_seen", now_ms))
            else:
                fw[tid] = dict(t, id=tid, notified=[], first_seen=now_ms)
    fw_all = sorted(fw.values(), key=lambda t: t["t_in"])
    fw_closed = [t for t in fw_all if t["status"] == "closed"]
    fw_open = [t for t in fw_all if t["status"] == "open"]
    # prezzi correnti per i trade aperti
    last_px = {s: c["rows"][-1][4] for s, c in coins.items() if c["rows"]}
    for t in fw_open:
        t["last"] = last_px.get(t["sym"], t["entry"])
    # segnali ora: trade aperti del test in avanti nati nelle ultime 3 candele
    last_bar_close = max([r["t_last"] for r in rows_out if r.get("t_last")] or [now_ms])
    signals = [t for t in fw_open if last_bar_close - t["t_in"] <= 2 * BAR_MS]

    def pack(trs):
        return [[t["sym"], t["t_in"], t["entry"], t["t_out"], t["p_out"], t["reason"], t["ret"], t["r"], t["risk"],
                 bool(t.get("spike"))] for t in trs]

    def block(trs):
        return dict(stats=signal_stats(trs), profiles={p: portfolio(trs, p) for p in PROFILES}, trades=pack(trs[-40:]),
                    spike=dict(on=signal_stats([t for t in trs if t.get("spike")]),
                               off=signal_stats([t for t in trs if not t.get("spike")])),
                    phase=by_key(trs, "phase"),
                    phase_hv=dict(on=signal_stats([t for t in trs if t.get("phase_hv")]),
                                  off=signal_stats([t for t in trs if t.get("phase") and not t.get("phase_hv")])))

    hist = [len(c["rows"]) / 6.0 for c in coins.values() if c["rows"]]
    payload = dict(
        generated=now_ms, forward_start=state["forward_start"], version=VERSION, fx=fx,
        capital_eur=CAPITAL_EUR, costs=dict(fee=FEE_PER_SIDE, slip=SLIP_PER_SIDE),
        strat=STRAT, profiles=PROFILES,
        market=dict(btc_ok=btc_ok_now, n_up=n_up, n_total=len(COINS), n_checked=len(sims), **btc_info),
        sources=src_status, history_days=dict(min=min(hist) if hist else 0, max=max(hist) if hist else 0),
        flag=FLAG, phase_names=PHASE_NAMES, phase_cfg=PHASE, entry_cfg=ENTRY, coins=rows_out,
        signals=[open_view(t, last_bar_close) for t in signals],
        open=[open_view(t, last_bar_close) for t in fw_open],
        backtest=block(sorted(closed, key=lambda t: t["t_out"])),
        forward=block(sorted(fw_closed, key=lambda t: t["t_out"])),
        forward_open_n=len(fw_open),
    )
    return payload


def entry_status(t, now_close):
    """Un segnale si puo' ancora usare per entrare? Ritorna (si, motivo).
    Motivo: ok, tempo, salito (inseguire il prezzo), sceso (segnale che si indebolisce), stop_spostato."""
    E = ENTRY
    if t.get("stage", 0) > 0:
        return False, "stop_spostato"
    if now_close - t["t_in"] > E["max_bars"] * BAR_MS:
        return False, "tempo"
    move = (t.get("last", t["entry"]) - t["entry"]) / t["atr"]
    if move > E["up_atr"]:
        return False, "salito"
    if move < -E["down_atr"]:
        return False, "sceso"
    return True, "ok"


def open_view(t, now_close=None):
    a = t["atr"]
    ok, why_not = entry_status(t, t["t_in"] if now_close is None else now_close)
    return dict(id=t["id"], sym=t["sym"], t_in=t["t_in"], entry=t["entry"], sl=t["sl"], sl0=t["sl0"], tp=t["tp"],
                stage=t["stage"], risk=t["risk"], last=t.get("last", t["entry"]), why=t["why"],
                spike=bool(t.get("spike")), spike_ratio=t.get("spike_ratio"), phase=t.get("phase"),
                be_at=t["entry"] + STRAT["be_trigger"] * a, trail_at=t["entry"] + STRAT["trail_trigger"] * a,
                trail_to=t["entry"] + STRAT["trail_lock"] * a, be_to=be_level(t["entry"]),
                enter_ok=ok, enter_why=why_not, enter_lo=t["entry"] - ENTRY["down_atr"] * a,
                enter_hi=t["entry"] + ENTRY["up_atr"] * a, enter_until=t["t_in"] + ENTRY["max_bars"] * BAR_MS)


# ----------------------------------------------------------------------------
# STATO E NOTIFICHE TELEGRAM
# ----------------------------------------------------------------------------
def load_state(now_ms):
    st = {}
    if STATE_FILE.exists():
        try:
            st = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        except Exception:
            st = {}
    if st.get("version") != VERSION or "forward_start" not in st:
        # prima esecuzione (o regole cambiate): il test in avanti riparte da qui
        st = dict(version=VERSION, forward_start=(now_ms // BAR_MS) * BAR_MS, forward={},
                  telegram_chat_id=st.get("telegram_chat_id"))
    st.setdefault("forward", {})
    st.setdefault("telegram_chat_id", None)
    return st


def it_num(x, dec=2):
    s = "{:,.{d}f}".format(x, d=dec)
    return s.replace(",", "§").replace(".", ",").replace("§", ".")


def money(usd, fx):
    if fx:
        return "€" + it_num(usd / fx, price_dec(usd / fx))
    return "$" + it_num(usd, price_dec(usd))


def price_dec(p):
    return 0 if p >= 1000 else 2 if p >= 10 else 3 if p >= 1 else 4 if p >= 0.1 else 5 if p >= 0.01 else 6


def local_time(ms):
    try:
        from zoneinfo import ZoneInfo
        return datetime.fromtimestamp(ms / 1000, ZoneInfo("Europe/Rome")).strftime("%d/%m %H:%M")
    except Exception:
        return datetime.fromtimestamp(ms / 1000, timezone.utc).strftime("%d/%m %H:%M UTC")


def compose(t, event, fx):
    sym = _html.escape(t["sym"])
    e, tp = t["entry"], t["tp"]
    sl = next((x[2] for x in t["events"] if x[1] == event), t["sl"])
    if event == "open":
        sp = size_pct(NOTIFY_PROFILE, t["risk"])
        amt = CAPITAL_EUR * sp
        lines = ["<b>Segnale di acquisto: %s</b>" % sym,
                 "Entra ora a circa %s" % money(e, fx),
                 "Stop loss: %s (%s%%)" % (money(t["sl0"], fx), it_num(-(t["sl0"] / e - 1) * 100, 1)),
                 "Take profit: %s (+%s%%)" % (money(tp, fx), it_num((tp / e - 1) * 100, 1)),
                 "Quota consigliata: %s%% del capitale (circa €%s su €%s)" % (
                     it_num(sp * 100, 0), it_num(amt, 0), it_num(CAPITAL_EUR, 0)),
                 "Se dopo 7 giorni non ha toccato né lo stop né il take profit, chiudi la posizione.",
                 "", "Perché:"] + ["- " + _html.escape(w) for w in t["why"]]
        if t.get("phase"):
            lines.insert(5, "Fase di mercato: %s" % PHASE_NAMES.get(t["phase"], t["phase"]))
        if t.get("spike"):
            lines.insert(1, "\u26a0 Volume anomalo: %s volte il normale. Segnale da guardare con pi\u00f9 attenzione." % it_num(t["spike_ratio"], 1))
        return "\n".join(lines)
    if event == "be":
        return ("<b>%s: sposta lo stop al pareggio</b>\nIl prezzo è salito abbastanza.\n"
                "Nuovo stop loss: %s (entrata %s). Il take profit resta a %s.") % (
            sym, money(sl, fx), money(e, fx), money(tp, fx))
    if event == "trail":
        return ("<b>%s: sposta lo stop in guadagno</b>\nNuovo stop loss: %s (sopra l'entrata di %s).\n"
                "Il take profit resta a %s.") % (sym, money(sl, fx), money(e, fx), money(tp, fx))
    # close
    why = {"stop": "stop loss raggiunto", "pareggio": "uscito a pareggio", "trailing": "uscito con stop in guadagno",
           "target": "take profit raggiunto", "tempo": "chiuso per tempo (7 giorni)"}[t["reason"]]
    return "<b>%s: trade chiuso</b> (%s)\nRisultato stimato: %s%% al netto dei costi.\nSe non è già chiusa da stop o take profit, chiudi la posizione." % (
        sym, why, ("+" if t["ret"] > 0 else "") + it_num(t["ret"] * 100, 1))


def pending_events(t, now_ms):
    """Quali messaggi mandare per questo trade. Ritorna (da_inviare, da_segnare_in_silenzio)."""
    n = set(t.get("notified", []))
    evs = [e[1] for e in t["events"]]
    if t["status"] == "closed":
        if "open" not in n:
            return [], ["open", "be", "trail", "close"]   # trade mai comunicato: non serve avvisare
        return ([] if "close" in n else ["close"]), []
    out = []
    if "open" not in n:
        if now_ms - t["t_in"] <= 3 * BAR_MS:
            out.append("open")
        else:                                             # segnale ormai vecchio: non lo comunico
            return [], ["open"] + evs
    out += [e for e in evs if e not in n]
    return out, []


def tg_post(token, chat_id, text):
    data = urllib.parse.urlencode({"chat_id": chat_id, "text": text, "parse_mode": "HTML",
                                   "disable_web_page_preview": "true"}).encode()
    req = urllib.request.Request("https://api.telegram.org/bot%s/sendMessage" % token, data=data,
                                 headers={"User-Agent": UA})
    urllib.request.urlopen(req, timeout=20).read()


def tg_find_chat(token):
    j = http_get("https://api.telegram.org/bot%s/getUpdates" % token, tries=2)
    for u in reversed(j.get("result", [])):
        m = u.get("message") or {}
        ch = m.get("chat") or {}
        if ch.get("type") == "private" and ch.get("id"):
            return ch["id"]
    return None


def notify(state, fx, now_ms, send=tg_post, find_chat=tg_find_chat):
    token = os.environ.get("TELEGRAM_BOT_TOKEN", "").strip()
    if not token:
        log("Telegram: nessun token impostato, salto le notifiche.")
        return 0
    chat = state.get("telegram_chat_id") or os.environ.get("TELEGRAM_CHAT_ID", "").strip() or None
    if not chat:
        try:
            chat = find_chat(token)
        except Exception as e:
            log("Telegram: impossibile leggere i messaggi:", e)
        if not chat:
            log("Telegram: scrivi un messaggio al tuo bot e riesegui.")
            return 0
        state["telegram_chat_id"] = chat
        try:
            send(token, chat, "Sala segnali collegata. Ti scrivo quando c'è un segnale o devi spostare uno stop.")
        except Exception as e:
            log("Telegram: messaggio di benvenuto non inviato:", e)
    sent = 0
    for t in sorted(state["forward"].values(), key=lambda x: x["t_in"]):
        todo, silent = pending_events(t, now_ms)
        t.setdefault("notified", [])
        for ev in silent:
            if ev not in t["notified"]:
                t["notified"].append(ev)
        for ev in todo:
            try:
                send(token, chat, compose(t, ev, fx))
            except Exception as e:
                log("Telegram: invio non riuscito (riprovo al prossimo giro):", e)
                break
            t["notified"].append(ev)
            sent += 1
            time.sleep(0.4)
    return sent


# ----------------------------------------------------------------------------
# PAGINA
# ----------------------------------------------------------------------------
PAGE = r'''<!doctype html>
<html lang="it">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>Sala segnali</title>
<link rel="icon" href="icon.png">
<link rel="apple-touch-icon" href="icon.png">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="Sala segnali">
<meta name="theme-color" content="#f3f4f5" media="(prefers-color-scheme: light)">
<meta name="theme-color" content="#0f1317" media="(prefers-color-scheme: dark)">
<style>
/* Strumento da sala operativa: grafite neutro, ambra per cio' che richiede attenzione, verde/rosso solo per esito. */
:root{
  --bg:#f3f4f5; --panel:#ffffff; --panel2:#eceef0; --line:#d9dde2; --fg:#12161b; --muted:#566170;
  --accent:#a76500; --accent-bg:#fbf0d9; --pos:#157347; --pos-bg:#dff3e8; --neg:#b3321f; --neg-bg:#f8e0dc;
  --warn:#8a5a00; --warn-bg:#f7ecd0; --chart:#12161b; --chart-fill:rgba(18,22,27,.07);
  --font:system-ui,-apple-system,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
}
@media (prefers-color-scheme: dark){
  :root{
    --bg:#0f1317; --panel:#171c22; --panel2:#1f252c; --line:#2a313a; --fg:#e8ebef; --muted:#97a1ae;
    --accent:#f0b429; --accent-bg:#2c2412; --pos:#4cc38a; --pos-bg:#14301f; --neg:#ef7a69; --neg-bg:#35191a;
    --warn:#e9b44c; --warn-bg:#2c2412; --chart:#e8ebef; --chart-fill:rgba(232,235,239,.08);
    color-scheme:dark;
  }
}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.5 var(--font);padding-inline:16px;padding-block:20px 56px}
.wrap{max-width:720px;margin:0 auto;display:flex;flex-direction:column;gap:28px}
h1{font-size:26px;line-height:1.15;margin:0;letter-spacing:-.01em;font-weight:700}
h2{font-size:12px;line-height:1.2;margin:0 0 12px;letter-spacing:.12em;text-transform:uppercase;color:var(--muted);font-weight:650;font-family:var(--mono)}
h3{font-size:15px;margin:0;font-weight:650}
p{margin:0}
.muted{color:var(--muted)}
.small{font-size:13px}
.num{font-variant-numeric:tabular-nums}
.pos{color:var(--pos)} .neg{color:var(--neg)}
button,input,select{font:inherit;color:inherit}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px}

.head{display:flex;flex-direction:column;gap:6px}
.demo{background:var(--neg-bg);color:var(--neg);border:1px solid var(--neg);padding:8px 12px;border-radius:6px;font-size:13px;font-weight:600}
.market{display:flex;flex-wrap:wrap;gap:8px 14px;align-items:center;margin-top:6px}
.pill{display:inline-block;padding:2px 9px;border-radius:999px;font-size:12px;font-weight:650;border:1px solid transparent;white-space:nowrap}
.pill.signal{background:var(--pos-bg);color:var(--pos)}
.pill.wait{background:var(--panel2);color:var(--muted)}
.pill.warn{background:var(--warn-bg);color:var(--warn)}
.pill.nodata{background:var(--neg-bg);color:var(--neg)}
.pill.accent{background:var(--accent-bg);color:var(--accent)}

.controls{display:grid;grid-template-columns:repeat(auto-fit,minmax(140px,1fr));gap:12px;background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:14px}
.field{display:flex;flex-direction:column;gap:5px;min-width:0}
.field label,.field .lab{font-size:12px;color:var(--muted);font-family:var(--mono);letter-spacing:.04em;text-transform:uppercase}
.field input,.field select{background:var(--bg);border:1px solid var(--line);border-radius:6px;padding:8px 10px;min-height:40px;width:100%}
.seg{display:flex;border:1px solid var(--line);border-radius:6px;overflow:hidden;background:var(--bg)}
.seg button{flex:1;background:none;border:0;padding:8px 10px;min-height:40px;cursor:pointer;color:var(--muted);font-weight:600}
.seg button[aria-pressed="true"]{background:var(--fg);color:var(--bg)}

.cards{display:flex;flex-direction:column;gap:12px}
.card{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:14px;display:flex;flex-direction:column;gap:12px;min-width:0}
.card.fresh{border-color:var(--accent)}
.card-top{display:flex;justify-content:space-between;gap:10px;align-items:flex-start;flex-wrap:wrap}
.sym{font-size:20px;font-weight:700;letter-spacing:-.01em}
.grid2{display:grid;grid-template-columns:1fr 1fr;gap:10px 14px}
.kv{display:flex;flex-direction:column;gap:1px;min-width:0}
.kv .k{font-size:12px;color:var(--muted)}
.kv .v{font-size:17px;font-weight:650;overflow-wrap:anywhere}
.step{background:var(--panel2);border-radius:6px;padding:9px 11px;font-size:13.5px}
details{border-top:1px solid var(--line);padding-top:10px}
details summary{cursor:pointer;font-weight:600;font-size:14px}
details ul{margin:8px 0 0;padding-left:18px;display:flex;flex-direction:column;gap:4px}
.warnbox{background:var(--accent-bg);color:var(--accent)}
.phase{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:14px;display:flex;flex-direction:column;gap:12px}
.phase .top{display:flex;gap:6px 12px;align-items:center;flex-wrap:wrap}
.phase .name{font-size:19px;font-weight:700}
.phase .tiles{margin:0}
.empty{background:var(--panel);border:1px dashed var(--line);border-radius:10px;padding:16px;display:flex;flex-direction:column;gap:6px}
.groups{display:flex;flex-direction:column;gap:22px}
.sub{font-size:15px;font-weight:700;margin:0 0 4px;display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.sub + .small{margin-bottom:10px}
.btn{min-height:44px;padding:8px 16px;border-radius:8px;border:1px solid var(--fg);background:var(--fg);color:var(--bg);font-weight:650;cursor:pointer;align-self:flex-start}
.btn.ghost{background:none;color:var(--fg);border-color:var(--line);font-weight:600}
.btn.sm{min-height:38px;padding:6px 12px;font-size:13.5px}
details.late{border-top:0;padding-top:0}
details.late summary{padding:6px 0}
details.late .list{margin-top:8px}

.tabs{display:flex;gap:6px;margin-bottom:12px;flex-wrap:wrap}
.tabs button{background:var(--panel);border:1px solid var(--line);border-radius:999px;padding:7px 14px;cursor:pointer;font-weight:600;color:var(--muted);min-height:38px}
.tabs button[aria-pressed="true"]{background:var(--fg);color:var(--bg);border-color:var(--fg)}
.tiles{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px;margin-bottom:12px}
.tile{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:12px;display:flex;flex-direction:column;gap:2px;min-width:0}
.tile .k{font-size:12px;color:var(--muted)}
.tile .v{font-size:21px;font-weight:700;overflow-wrap:anywhere}
.tile .s{font-size:12.5px;color:var(--muted)}
.chart{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:8px 6px 2px;margin-bottom:12px}
.chart svg{display:block;width:100%;height:auto}
.axis{fill:var(--muted);font-size:11px;font-family:var(--mono)}
.gridl{stroke:var(--line);stroke-width:1}
.base{stroke:var(--muted);stroke-width:1;stroke-dasharray:3 3}
.line{fill:none;stroke:var(--chart);stroke-width:2;stroke-linejoin:round}
.area{fill:var(--chart-fill);stroke:none}
.dot{fill:var(--accent);stroke:var(--panel);stroke-width:2}
.bar{height:8px;background:var(--panel2);border-radius:999px;overflow:hidden;margin:6px 0}
.bar i{display:block;height:100%;background:var(--accent)}

.scroll{overflow-x:auto;background:var(--panel);border:1px solid var(--line);border-radius:10px}
table{border-collapse:collapse;width:100%;min-width:520px;font-size:13.5px}
th,td{padding:8px 10px;text-align:left;border-bottom:1px solid var(--line);white-space:nowrap}
th{font-size:11.5px;color:var(--muted);font-weight:600;font-family:var(--mono);letter-spacing:.04em;text-transform:uppercase}
td.r,th.r{text-align:right}
table.compact{min-width:0;font-size:13px}
table.compact th,table.compact td{white-space:normal;padding:8px 7px;vertical-align:top}
table.compact th{font-size:10.5px;letter-spacing:.02em}
tr:last-child td{border-bottom:0}

.list{display:flex;flex-direction:column;background:var(--panel);border:1px solid var(--line);border-radius:10px}
.row{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:2px 12px;padding:10px 14px;border-bottom:1px solid var(--line)}
.row:last-child{border-bottom:0}
.row .l{min-width:0}
.row .rt{text-align:right}
.row .st{grid-column:1/-1;display:flex;gap:8px;align-items:flex-start;font-size:13px;color:var(--muted)}
.row .st .pill{flex:none}

.guide{display:flex;flex-direction:column;gap:10px}
.guide details{background:var(--panel);border:1px solid var(--line);border-radius:10px;padding:12px 14px}
.guide details[open]{padding-bottom:14px}
.guide .body{margin-top:10px;display:flex;flex-direction:column;gap:8px}
.guide dt{font-weight:650;margin-top:6px}
.guide dd{margin:0;color:var(--muted)}
.foot{font-size:12.5px;color:var(--muted);display:flex;flex-direction:column;gap:4px}
</style>
</head>
<body>
<div class="wrap">
  <header class="head">
    <h1>Sala segnali</h1>
    <div class="muted small" id="meta"></div>
    <div id="demo"></div>
    <div class="market" id="market"></div>
  </header>

  <div class="controls" aria-label="Impostazioni">
    <div class="field"><span class="lab">Valuta</span>
      <div class="seg" role="group" aria-label="Valuta">
        <button type="button" data-cur="EUR" aria-pressed="false">Euro</button>
        <button type="button" data-cur="USD" aria-pressed="false">Dollari</button>
      </div>
    </div>
    <div class="field"><label for="cap">Capitale</label><input id="cap" type="number" inputmode="decimal" min="0" step="50" value="1000"></div>
    <div class="field"><label for="prof">Rischio</label>
      <select id="prof">
        <option value="basso">Basso</option>
        <option value="medio">Medio</option>
        <option value="alto">Alto</option>
      </select>
    </div>
  </div>

  <main id="app"></main>
</div>

<script>
const D = /*__DATA__*/null;

(function () {
  "use strict";
  const $ = (s, r) => (r || document).querySelector(s);
  const esc = s => String(s).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  if (!D) { $("#app").innerHTML = '<div class="empty"><h3>Nessun dato</h3><p class="muted">Il programma non ha ancora prodotto dati. Eseguilo almeno una volta.</p></div>'; return; }

  const BAR = 4 * 3600 * 1000;
  const S = { cur: D.fx ? "EUR" : "USD", cap: D.capital_eur || 1000, prof: "medio", view: "forward", mine: [] };
  try { Object.assign(S, JSON.parse(localStorage.getItem("sala-segnali-v1") || "{}")); } catch (e) {}
  if (!D.fx) S.cur = "USD";
  if (!D.profiles[S.prof]) S.prof = "medio";
  if (S.view !== "forward" && S.view !== "backtest") S.view = "forward";
  if (!Array.isArray(S.mine)) S.mine = [];
  const save = () => { try { localStorage.setItem("sala-segnali-v1", JSON.stringify(S)); } catch (e) {} };
  // toglie le operazioni segnate che i dati non conoscono piu' (chiuse da molto tempo)
  (function pruneMine() {
    const known = {};
    (D.open || []).forEach(t => { known[t.id] = 1; });
    ((D.forward && D.forward.trades) || []).forEach(t => { known[t[0] + "|" + t[1]] = 1; });
    const keep = S.mine.filter(id => known[id]);
    if (keep.length !== S.mine.length) { S.mine = keep; save(); }
  })();

  const nf = (x, d) => x.toLocaleString("it-IT", { minimumFractionDigits: d, maximumFractionDigits: d });
  const sgn = (x, d) => (x > 0 ? "+" : x < 0 ? "−" : "") + nf(Math.abs(x), d);
  const pct = (x, d) => sgn(x * 100, d === undefined ? 1 : d) + "%";
  const sym = () => (S.cur === "EUR" ? "€" : "$");
  const conv = usd => (S.cur === "EUR" && D.fx ? usd / D.fx : usd);
  const pdec = p => (p >= 1000 ? 0 : p >= 10 ? 2 : p >= 1 ? 3 : p >= 0.1 ? 4 : p >= 0.01 ? 5 : 6);
  const price = usd => { const v = conv(usd); return sym() + nf(v, pdec(v)); };
  const cash = (v, d) => sym() + nf(v, d === undefined ? 0 : d);
  const dt = ms => new Date(ms).toLocaleString("it-IT", { timeZone: "Europe/Rome", day: "2-digit", month: "2-digit", hour: "2-digit", minute: "2-digit" });
  const dday = ms => new Date(ms).toLocaleDateString("it-IT", { timeZone: "Europe/Rome", day: "2-digit", month: "short" });
  const REASON = { stop: "Stop loss", pareggio: "Pareggio", trailing: "Stop in guadagno", target: "Take profit", tempo: "Scaduto" };
  const SRC = { kraken: "Kraken", binance: "Binance", coinbase: "Coinbase" };
  const cs = (D.costs.fee + D.costs.slip) * 2;

  // ---------- intestazione ----------
  function head() {
    $("#meta").textContent = "Aggiornato " + dt(D.generated) + " · candele a 4 ore · regole " + D.version;
    if (D.demo) $("#demo").innerHTML = '<div class="demo">DATI DI PROVA. I numeri sono inventati e servono solo a mostrare come appare la pagina.</div>';
    const m = D.market;
    const regime = m.btc_ok === null || m.btc_ok === undefined
      ? '<span class="pill nodata">Mercato: Bitcoin non verificabile</span>'
      : m.btc_ok ? '<span class="pill signal">Mercato rialzista</span>' : '<span class="pill warn">Mercato non rialzista</span>';
    $("#market").innerHTML = regime +
      '<span class="small muted">' + (m.btc_ok === false ? "Bitcoin è sotto la sua media a 200 candele: nessun segnale. " : "") +
      m.n_up + " monete su " + m.n_total + " in trend rialzista</span>";
    const sp = D.coins.filter(c => c.spike);
    if (sp.length) $("#market").innerHTML += '<span class="pill accent">Volume anomalo: ' + sp.map(c => esc(c.sym)).join(", ") + "</span>";
  }

  // ---------- operazioni in corso ----------
  const E = D.entry_cfg || { max_bars: 3, up_atr: 0.5, down_atr: 1 };
  const nowMs = () => (D.demo ? D.generated : Date.now());
  const WHY = {
    tempo: "Sono passate più di " + E.max_bars * 4 + " ore dal segnale.",
    salito: "Il prezzo è già salito sopra la fascia: inseguirlo peggiora il rapporto tra rischio e guadagno.",
    sceso: "Il prezzo è sceso sotto la fascia: il segnale si sta indebolendo.",
    stop_spostato: "Il prezzo ha già raggiunto il livello in cui si sposta lo stop: è tardi per entrare."
  };
  // si puo' ancora entrare? Il controllo sul tempo si rifa qui, cosi' resta giusto anche se l'aggiornamento e' in ritardo.
  function enterState(t) {
    if (!t.enter_ok) return [false, t.enter_why || "tempo"];
    if (nowMs() > t.enter_until) return [false, "tempo"];
    return [true, "ok"];
  }
  const coinName = s => (D.coins.find(c => c.sym === s) || {}).name || "";

  function openCard(t, mine) {
    const P = D.profiles[S.prof];
    const size = Math.min(P.risk / t.risk, P.max_size);
    const amt = S.cap * size, loss = amt * t.risk;
    const now = t.last / t.entry - 1;
    let next;
    if (t.stage === 0) next = "Se il prezzo sale a <b>" + price(t.be_at) + "</b>, sposta lo stop al pareggio (" + price(t.be_to) + ").";
    else if (t.stage === 1) next = "Stop già al pareggio (" + price(t.sl) + "). Se il prezzo sale a <b>" + price(t.trail_at) + "</b>, sposta lo stop a " + price(t.trail_to) + ".";
    else next = "Stop in guadagno a " + price(t.sl) + ". Ora resta solo il take profit.";
    const expire = t.t_in + D.strat.max_hold * BAR;
    const windowStep = mine ? "" :
      '<div class="step"><b>Entra solo se il prezzo è tra ' + price(t.enter_lo) + " e " + price(t.enter_hi) + "</b>, ed entro le " + dt(t.enter_until) +
      ". Fuori da questa fascia il segnale non vale più. Stop loss e take profit restano a questi prezzi anche se entri un po' sopra o sotto.</div>";
    const button = mine
      ? '<button type="button" class="btn ghost sm" data-unmine="' + esc(t.id) + '">Non sono entrato</button>'
      : '<button type="button" class="btn" data-mine="' + esc(t.id) + '">Sono entrato</button>';
    return '<article class="card' + (mine ? "" : " fresh") + '">' +
      '<div class="card-top"><div><div class="sym">' + esc(t.sym) + '</div><div class="muted small">' + esc(coinName(t.sym)) + '</div></div>' +
      '<span class="pill ' + (mine ? "wait" : "accent") + '">' + (mine ? "In corso" : "Da valutare") + "</span></div>" +
      '<div class="grid2">' +
      kv("Entrata", price(t.entry)) +
      kv("Ora", price(t.last) + ' <span class="small ' + (now >= 0 ? "pos" : "neg") + '">' + pct(now) + "</span>") +
      kv("Stop loss", price(t.stage ? t.sl : t.sl0) + ' <span class="small muted">' + pct(((t.stage ? t.sl : t.sl0) / t.entry) - 1) + "</span>") +
      kv("Take profit", price(t.tp) + ' <span class="small muted">' + pct(t.tp / t.entry - 1) + "</span>") +
      kv("Quota consigliata", nf(size * 100, 0) + "% = " + cash(amt)) +
      kv("Perdita massima", "≈ " + cash(loss, loss < 10 ? 1 : 0)) +
      "</div>" + windowStep +
      '<div class="step">' + next + "</div>" +
      (t.spike ? '<div class="step warnbox"><b>Volume anomalo</b> al momento del segnale: ' + nf(t.spike_ratio, 1) + " volte il normale. Segnale da guardare con più attenzione.</div>" : "") +
      "<details><summary>Perché questo segnale</summary><ul>" + t.why.map(w => "<li>" + esc(w) + "</li>").join("") + "</ul></details>" +
      '<div class="small muted">Candela chiusa il ' + dt(t.t_in) + ". Se entro il " + dt(expire) + " non ha toccato stop o take profit, chiudi la posizione." + (t.phase ? " Fase di mercato al segnale: " + esc((D.phase_names || {})[t.phase] || t.phase) + "." : "") + "</div>" +
      button + "</article>";
  }
  const kv = (k, v) => '<div class="kv"><span class="k">' + k + '</span><span class="v num">' + v + "</span></div>";

  // segnale non piu' entrabile: riga compatta
  function lateRow(t) {
    const why = enterState(t)[1];
    const now = t.last / t.entry - 1;
    return '<div class="row"><div class="l"><b>' + esc(t.sym) + '</b> <span class="muted small">' + esc(coinName(t.sym)) + "</span>" +
      '<div class="small muted num">Segnale del ' + dt(t.t_in) + " a " + price(t.entry) + " · ora " + price(t.last) + " (" + pct(now) + ")</div></div>" +
      '<div class="rt"><button type="button" class="btn ghost sm" data-mine="' + esc(t.id) + '">Sono entrato</button></div>' +
      '<div class="st"><span class="pill wait">Non entrabile</span><span>' + (WHY[why] || "") + "</span></div></div>";
  }

  // operazione segnata da me, gia' chiusa: mostra l'esito
  function closedRow(t) {
    const id = t[0] + "|" + t[1], good = t[6] >= 0;
    const act = t[5] === "tempo" ? "Il tempo massimo è scaduto: chiudi la posizione se è ancora aperta." :
      t[5] === "target" ? "Take profit raggiunto: controlla che la tua posizione sia chiusa." :
      "Stop raggiunto: controlla che la tua posizione sia chiusa.";
    return '<div class="row"><div class="l"><b>' + esc(t[0]) + '</b> <span class="muted small">' + esc(coinName(t[0])) + "</span>" +
      '<div class="small muted num">Entrata ' + dt(t[1]) + " a " + price(t[2]) + " · uscita " + dt(t[3]) + " a " + price(t[4]) + "</div></div>" +
      '<div class="rt"><div class="num ' + (good ? "pos" : "neg") + '"><b>' + pct(t[6]) + '</b></div><button type="button" class="btn ghost sm" data-unmine="' + esc(id) + '">Rimuovi</button></div>' +
      '<div class="st"><span class="pill ' + (good ? "signal" : "nodata") + '">' + (REASON[t[5]] || esc(t[5])) + "</span><span>" + act + "</span></div></div>";
  }

  function openSection() {
    const mineSet = {};
    S.mine.forEach(id => { mineSet[id] = 1; });
    const open = D.open.slice().sort((a, b) => b.t_in - a.t_in);
    const fresh = [], late = [], mineOpen = [];
    open.forEach(t => { if (mineSet[t.id]) mineOpen.push(t); else if (enterState(t)[0]) fresh.push(t); else late.push(t); });
    const mineClosed = ((D.forward && D.forward.trades) || []).filter(t => mineSet[t[0] + "|" + t[1]]).reverse();

    let g1;
    if (fresh.length) {
      g1 = '<div><h3 class="sub">Da valutare ora <span class="pill accent">' + fresh.length + '</span></h3><p class="small muted">Segnali ancora entrabili. Se entri, tocca «Sono entrato».</p><div class="cards">' + fresh.map(t => openCard(t, false)).join("") + "</div></div>";
    } else {
      const why = D.market.btc_ok === false ? "Bitcoin è sotto la sua media a 200 candele, quindi con queste regole non si compra nulla." :
        "Servono insieme: trend rialzista, trend con forza, una ripartenza dopo un calo e volume sopra la media.";
      g1 = '<div class="empty"><h3>Nessun segnale da valutare adesso</h3><p class="muted">' + why +
        (late.length ? " Gli ultimi segnali non sono più entrabili: li trovi in fondo a questa sezione." : "") +
        " Aspettare fa parte delle regole: la pagina si aggiorna da sola ogni 4 ore.</p></div>";
    }
    let g2 = "";
    if (mineOpen.length || mineClosed.length) {
      g2 = '<div><h3 class="sub">Le mie operazioni <span class="pill wait">' + (mineOpen.length + mineClosed.length) + '</span></h3><p class="small muted">Quelle che hai segnato con «Sono entrato». Restano salvate solo su questo telefono.</p>' +
        (mineOpen.length ? '<div class="cards">' + mineOpen.map(t => openCard(t, true)).join("") + "</div>" : "") +
        (mineClosed.length ? '<div class="list" style="margin-top:12px">' + mineClosed.map(closedRow).join("") + "</div>" : "") + "</div>";
    }
    let g3 = "";
    if (late.length) {
      g3 = '<details class="late"><summary>Non più entrabili (' + late.length + ')</summary><p class="small muted" style="margin-top:6px">Segnali passati: non conviene più entrare. Se eri già dentro, tocca «Sono entrato».</p><div class="list">' + late.map(lateRow).join("") + "</div></details>";
    }
    return '<section><h2>Segnali e operazioni in corso</h2><div class="groups">' + g1 + g2 + g3 + "</div></section>";
  }

  // ---------- simulatore ----------
  function chart(points) {
    if (!points || points.length < 2) return "";
    const W = 640, H = 230, L = 58, R = 14, T = 14, B = 26;
    const vals = points.map(p => S.cap * p[1]);
    let lo = Math.min.apply(null, vals.concat([S.cap])), hi = Math.max.apply(null, vals.concat([S.cap]));
    if (hi - lo < S.cap * 0.01) { hi += S.cap * 0.01; lo -= S.cap * 0.01; }
    const pad = (hi - lo) * 0.08; lo -= pad; hi += pad;
    const t0 = points[0][0], t1 = points[points.length - 1][0];
    const x = t => L + (W - L - R) * (t1 === t0 ? 0 : (t - t0) / (t1 - t0));
    const y = v => T + (H - T - B) * (1 - (v - lo) / (hi - lo));
    const path = points.map((p, i) => (i ? "L" : "M") + x(p[0]).toFixed(1) + " " + y(S.cap * p[1]).toFixed(1)).join("");
    const area = path + "L" + x(t1).toFixed(1) + " " + (H - B) + "L" + x(t0).toFixed(1) + " " + (H - B) + "Z";
    let g = "";
    for (let k = 0; k < 4; k++) {
      const v = lo + (hi - lo) * k / 3;
      g += '<line class="gridl" x1="' + L + '" x2="' + (W - R) + '" y1="' + y(v).toFixed(1) + '" y2="' + y(v).toFixed(1) + '"/>' +
        '<text class="axis" x="' + (L - 6) + '" y="' + (y(v) + 4).toFixed(1) + '" text-anchor="end">' + sym() + nf(v, 0) + "</text>";
    }
    const last = points[points.length - 1];
    return '<div class="chart"><svg viewBox="0 0 ' + W + " " + H + '" role="img" aria-label="Andamento del capitale simulato">' + g +
      '<line class="base" x1="' + L + '" x2="' + (W - R) + '" y1="' + y(S.cap).toFixed(1) + '" y2="' + y(S.cap).toFixed(1) + '"/>' +
      '<path class="area" d="' + area + '"/><path class="line" d="' + path + '"/>' +
      '<circle class="dot" cx="' + x(last[0]).toFixed(1) + '" cy="' + y(S.cap * last[1]).toFixed(1) + '" r="4.5"/>' +
      '<text class="axis" x="' + L + '" y="' + (H - 7) + '">' + dday(t0) + '</text>' +
      '<text class="axis" x="' + (W - R) + '" y="' + (H - 7) + '" text-anchor="end">' + dday(t1) + "</text></svg></div>";
  }

  function tile(k, v, s, cls) { return '<div class="tile"><span class="k">' + k + '</span><span class="v num ' + (cls || "") + '">' + v + '</span><span class="s">' + (s || "") + "</span></div>"; }

  const PH = {
    rialzo_forte: ["signal", "Bitcoin sale con una direzione chiara. È la fase per cui sono pensate queste regole, che seguono il trend. I segnali sono ammessi."],
    rialzo_debole: ["signal", "Bitcoin è sopra la media a 200 candele ma senza una spinta netta. I segnali sono ammessi."],
    transizione: ["warn", "Le medie di Bitcoin si contraddicono: il mercato sta cambiando direzione oppure è fermo. I segnali sono ammessi solo se Bitcoin è sopra la media a 200 candele."],
    ribasso_debole: ["warn", "Bitcoin è sotto la media a 200 candele ma senza una discesa netta. I segnali sono bloccati."],
    ribasso_forte: ["nodata", "Bitcoin scende con una direzione chiara. I segnali sono bloccati."]
  };
  const PH_ORDER = ["rialzo_forte", "rialzo_debole", "transizione", "ribasso_debole", "ribasso_forte"];

  function phaseSection() {
    const m = D.market, names = D.phase_names || {};
    if (!m.phase) {
      return '<section><h2>Fase di mercato</h2><div class="empty"><h3>Non disponibile</h3><p class="muted">I dati di Bitcoin non sono verificabili da due fonti, quindi la fase non viene valutata e non ci sono segnali.</p></div></section>';
    }
    const info = PH[m.phase] || ["wait", ""];
    return '<section><h2>Fase di mercato</h2><div class="phase"><div class="top"><span class="name">' + esc(names[m.phase] || m.phase) + "</span>" +
      '<span class="pill ' + info[0] + '">' + (m.btc_ok ? "Segnali ammessi" : "Segnali bloccati") + "</span>" +
      (m.phase_hv ? '<span class="pill accent">Volatilità alta</span>' : "") + "</div>" +
      '<p class="small muted">' + info[1] + "</p>" +
      '<div class="tiles">' +
      tile("Bitcoin e media a 200", sgn(m.btc_dist * 100, 1) + "%", "distanza dalla media a 200 candele", m.btc_dist >= 0 ? "pos" : "neg") +
      tile("Forza del trend", nf(m.btc_adx, 0), "ADX di Bitcoin, sopra " + ((D.phase_cfg || {}).adx_strong || 20) + " il trend è chiaro") +
      tile("Volatilità", m.phase_hv ? "Alta" : "Normale", "una candela si muove in media del " + nf(m.btc_atr_pct * 100, 1) + "%") +
      tile("Ampiezza", m.n_up + " su " + m.n_total, "monete in trend rialzista") +
      "</div></div></section>";
  }

  function spikeCompare(B) {
    if (!B.spike || !B.spike.on.n) return "";
    const a = B.spike.on, b = B.spike.off;
    const row = (lab, st) => st.n
      ? "<tr><td>" + lab + '</td><td class="r num">' + st.n + '</td><td class="r num">' + nf(st.win_rate * 100, 0) + '%</td><td class="r num">' + sgn(st.avg_r, 2) + "</td></tr>"
      : "<tr><td>" + lab + '</td><td class="r num">0</td><td class="r">—</td><td class="r">—</td></tr>';
    const few = Math.min(a.n, b.n) < 20 ? " Pochi trade per confrontare: non trarre conclusioni." : "";
    return '<h2 style="margin-top:16px">Spia volume</h2><div class="scroll"><table class="compact"><thead><tr><th>Segnali</th><th class="r">Trade</th><th class="r">Vincenti</th><th class="r">R medio</th></tr></thead><tbody>' +
      row("Con volume anomalo", a) + row("Senza", b) + '</tbody></table></div><p class="small muted" style="margin:8px 0 0">Solo informativo: la spia non cambia i segnali.' + few + "</p>";
  }

  function phaseCompare(B) {
    const ph = B.phase || {}, names = D.phase_names || {};
    const keys = PH_ORDER.filter(k => ph[k] && ph[k].n);
    if (!keys.length) return "";
    const row = (lab, st) => "<tr><td>" + lab + '</td><td class="r num">' + st.n + '</td><td class="r num">' + nf(st.win_rate * 100, 0) + '%</td><td class="r num">' + sgn(st.avg_r, 2) + "</td></tr>";
    let rows = keys.map(k => row(esc(names[k] || k), ph[k])).join("");
    const hv = B.phase_hv;
    if (hv && hv.on.n) rows += row("Volatilità alta", hv.on);
    if (hv && hv.off.n) rows += row("Volatilità normale", hv.off);
    const few = keys.some(k => ph[k].n < 20) ? " Pochi trade in alcune fasi: non trarre conclusioni." : "";
    return '<h2 style="margin-top:16px">Per fase di mercato</h2><div class="scroll"><table class="compact"><thead><tr><th>Al momento del segnale</th><th class="r">Trade</th><th class="r">Vincenti</th><th class="r">R medio</th></tr></thead><tbody>' + rows +
      '</tbody></table></div><p class="small muted" style="margin:8px 0 0">Solo informativo. Con il filtro su Bitcoin non ci sono segnali nelle fasi di ribasso.' + few + "</p>";
  }

  function simSection() {
    const B = D[S.view], pf = B.profiles[S.prof], st = B.stats;
    const tabs = '<div class="tabs" role="group" aria-label="Tipo di prova">' +
      '<button type="button" data-view="forward" aria-pressed="' + (S.view === "forward") + '">Test in avanti</button>' +
      '<button type="button" data-view="backtest" aria-pressed="' + (S.view === "backtest") + '">Backtest sul passato</button></div>';
    let note, body;
    if (S.view === "forward") {
      const need = 50, n = st.n || 0;
      note = "Conta solo i segnali nati dopo il " + dt(D.forward_start) + ", con le regole di oggi, senza ritocchi. È la prova più onesta." +
        (D.forward_open_n ? " Trade ancora aperti: " + D.forward_open_n + "." : "");
      const bar = '<div class="small muted">Trade chiusi: <b>' + n + "</b> su " + need + ' (per fidarsi meglio ne servono 50-100)</div><div class="bar"><i style="width:' + Math.min(100, n / need * 100) + '%"></i></div>';
      body = bar;
    } else {
      note = "Rifa tutti i segnali che le stesse regole avrebbero dato nel periodo coperto dai dati (fino a " + Math.round(D.history_days.max) + " giorni). Mostra com'è andata, non come andrà. I prezzi per il backtest arrivano da una sola fonte.";
      body = "";
    }
    let res;
    if (!pf.n) {
      res = '<div class="empty"><h3>Ancora nessuna operazione chiusa</h3><p class="muted">' +
        (S.view === "forward" ? "Il test in avanti è partito da poco. Quando un trade si chiude, qui compaiono i risultati." : "Con queste regole non ci sono stati segnali nel periodo.") + "</p></div>";
    } else {
      const ret = pf.final - 1;
      res = '<div class="tiles">' +
        tile("Capitale simulato", cash(S.cap * pf.final), pct(ret) + " su " + cash(S.cap), ret >= 0 ? "pos" : "neg") +
        tile("Operazioni", String(pf.n), pf.skipped ? pf.skipped + " saltate (troppe aperte insieme)" : "tutte seguite") +
        tile("Vincenti", nf(pf.wins / pf.n * 100, 0) + "%", pf.wins + " su " + pf.n) +
        tile("Calo massimo", "−" + nf(pf.mdd * 100, 1) + "%", "dal punto più alto", pf.mdd > 0.2 ? "neg" : "") +
        tile("Profit factor", pf.pf === null ? "—" : nf(pf.pf, 2), "guadagni diviso perdite (sopra 1 = in attivo)") +
        tile("Risultato medio", st.avg_r === undefined ? "—" : nf(st.avg_r, 2) + " R", "1 R = la perdita massima prevista") + "</div>" + chart(pf.equity);
      const rows = B.trades.slice(-15).reverse().map(t =>
        "<tr><td><b>" + esc(t[0]) + "</b>" + (t[9] ? ' <span class="pill accent">volume</span>' : "") + "</td><td>" + dt(t[1]) + "</td><td>" + (REASON[t[5]] || esc(t[5])) + " " + dday(t[3]) + '</td><td class="r num ' + (t[6] >= 0 ? "pos" : "neg") + '">' + pct(t[6]) + '</td><td class="r num">' + sgn(t[7], 2) + "</td></tr>").join("");
      res += spikeCompare(B) + phaseCompare(B) + '<h2 style="margin-top:16px">Ultime operazioni</h2><div class="scroll"><table class="compact"><thead><tr><th>Moneta</th><th>Entrata</th><th>Uscita</th><th class="r">Risultato</th><th class="r">R</th></tr></thead><tbody>' + rows + "</tbody></table></div>" +
        '<p class="small muted" style="margin-top:8px">Risultati al netto dei costi (' + nf(cs * 100, 2) + "% tra andata e ritorno). Il capitale simulato conta solo i trade chiusi.</p>";
    }
    return "<section><h2>Simulatore</h2>" + tabs + '<p class="small muted" style="margin-bottom:10px">' + note + "</p>" + body + res + "</section>";
  }

  // ---------- monete ----------
  const KIND_ORDER = { signal: 0, wait: 1, warn: 2, nodata: 3 };
  const KIND_LABEL = { signal: "Segnale", wait: "Attesa", warn: "Fonti", nodata: "Dati" };
  function coinsSection() {
    const cs2 = D.coins.slice().sort((a, b) => (KIND_ORDER[a.kind] - KIND_ORDER[b.kind]) || ((b.spike ? 1 : 0) - (a.spike ? 1 : 0)));
    const rows = cs2.map(c => {
      const right = c.price === undefined ? "" :
        '<div class="num"><b>' + price(c.price) + '</b></div><div class="small num ' + (c.chg >= 0 ? "pos" : "neg") + '">' + pct(c.chg) + " in 24h</div>";
      const srcs = c.srcs.length ? c.srcs.map(s => SRC[s] || s).join(" + ") : "nessuna fonte";
      return '<div class="row"><div class="l"><b>' + esc(c.sym) + '</b> <span class="muted small">' + esc(c.name) + '</span>' + (c.spike ? ' <span class="pill accent">Volume anomalo ' + nf(c.spike_ratio, 1) + '×</span>' : "") + '<div class="small muted">' + srcs + '</div></div><div class="rt">' + right + "</div>" +
        '<div class="st"><span class="pill ' + c.kind + '">' + KIND_LABEL[c.kind] + "</span><span>" + esc(c.status) + "</span></div></div>";
    }).join("");
    return "<section><h2>Monete seguite</h2><div class=\"list\">" + rows + "</div></section>";
  }

  // ---------- guida ----------
  function guide() {
    const s = D.strat, pr = D.profiles, F = D.flag || { ratio: 3, base: 20, recent: 3 }, P = D.phase_cfg || { adx_strong: 20, vol_window: 180, vol_pct: 0.8 };
    return '<section><h2>Come funziona</h2><div class="guide">' +
      "<details><summary>Cosa fa questa pagina</summary><div class=\"body\"><p>Ogni 4 ore, quando si chiude una candela, il programma scarica i prezzi di " + D.market.n_total + " crypto da più exchange, li confronta, calcola gli indicatori e controlla se c'è un'occasione di acquisto. Non compra e non vende nulla al posto tuo: ti dice cosa fare e dove mettere stop loss e take profit.</p><p>Un segnale vale solo se almeno due fonti indipendenti danno lo stesso prezzo. Se discordano, o ce n'è una sola, la moneta resta in sola osservazione.</p></div></details>" +
      "<details><summary>Quando scatta un segnale</summary><div class=\"body\"><p>Devono essere vere tutte e cinque, sull'ultima candela chiusa:</p><ol style=\"margin:0;padding-left:20px;display:flex;flex-direction:column;gap:4px\">" +
      "<li>Bitcoin è sopra la sua media a " + s.ema_slow + " candele (il mercato nel suo insieme sale).</li>" +
      "<li>La moneta è in trend rialzista: media a " + s.ema_fast + " sopra media a " + s.ema_slow + ", e il prezzo sopra la media a " + s.ema_slow + ".</li>" +
      "<li>Il trend ha forza: ADX almeno " + s.adx_min + " e compratori in vantaggio.</li>" +
      "<li>Dopo un calo (RSI sceso a " + s.rsi_pullback + " o meno nelle ultime " + s.pb_lookback + " candele) il prezzo riparte: RSI sale sopra " + s.rsi_resume + ".</li>" +
      "<li>Il volume è almeno nella media recente.</li></ol><p>Si compra solo al rialzo, come su Revolut X: niente vendite allo scoperto.</p></div></details>" +
      "<details><summary>Finestra d'ingresso e tasto «Sono entrato»</summary><div class=\"body\">" +
      "<p>Un segnale vale solo per poco. Nasce alla chiusura di una candela e si può usare per al massimo " + E.max_bars * 4 + " ore. In più il prezzo deve restare in una fascia attorno a quello del segnale: non oltre " + nf(E.up_atr, 1) + " ATR sopra (inseguire un rialzo già partito peggiora il rapporto tra rischio e guadagno) e non oltre " + nf(E.down_atr, 1) + " ATR sotto (il segnale si sta indebolendo).</p>" +
      "<p>Passata la finestra, o uscito dalla fascia, il segnale va tra «Non più entrabili» e non devi fare nulla. Se te ne accorgi tardi non hai perso un'occasione da rincorrere: le regole non prevedono di entrare in ritardo.</p>" +
      "<p>Se entri, tocca «Sono entrato»: il segnale passa in «Le mie operazioni», dove vedi stop, take profit e quando spostare lo stop. Quando il trade si chiude compare l'esito: controlla la tua posizione e premi Rimuovi.</p>" +
      "<p>Le tue operazioni sono salvate solo nel browser di questo telefono. Se aggiungi la pagina alla Home, usa sempre l'icona: aprendo lo stesso link da Safari le operazioni segnate non compaiono.</p>" +
      "<p>I numeri del simulatore non dipendono da cosa tocchi: il test in avanti conta tutti i segnali, come se si entrasse sempre al prezzo di chiusura della candela. Entrare in ritardo, dentro la fascia, dà un risultato un po' diverso.</p></div></details>" +
      "<details><summary>Gli indicatori in parole semplici</summary><div class=\"body\"><dl style=\"margin:0\">" +
      "<dt>Media mobile (EMA)</dt><dd>Il prezzo medio recente, con più peso agli ultimi giorni. Se la media a 50 candele (circa 8 giorni) sta sopra quella a 200 (circa 33 giorni), la moneta sta salendo da un po'.</dd>" +
      "<dt>RSI</dt><dd>Un numero da 0 a 100 che dice se la moneta è scesa o salita troppo in fretta. Dopo un calo, quando risale oltre " + s.rsi_resume + " vuol dire che i compratori sono tornati.</dd>" +
      "<dt>ADX</dt><dd>Misura la forza del trend, non la direzione. Sopra " + s.adx_min + " il movimento ha una direzione chiara; sotto è un mercato confuso.</dd>" +
      "<dt>ATR</dt><dd>Di quanto si muove in media una candela. Serve a mettere stop e take profit alla distanza giusta per ogni moneta: più è nervosa, più sono larghi.</dd>" +
      "<dt>Volume</dt><dd>Quanto si scambia. Un movimento con volumi sopra la media è più credibile.</dd></dl></div></details>" +
      "<details><summary>La spia dei volumi</summary><div class='body'>" +
      "<p>La spia si accende su una moneta quando, in una delle ultime " + F.recent + " candele (" + F.recent * 4 + " ore), il volume è almeno " + nf(F.ratio, 0) + " volte il normale. Il normale è la mediana, cioè il valore di mezzo, dei volumi delle " + F.base + " candele precedenti: così un vecchio picco non falsa il confronto.</p>" +
      "<p>Non è la quinta condizione dei segnali. Quella chiede solo che il volume sia almeno nella media, e lascia passare senza avviso anche un volume dieci volte più alto. La spia serve proprio a vedere i picchi.</p>" +
      "<p>Un picco può voler dire molto interesse reale, una notizia, oppure un rialzo spinto che poi rientra. Da solo non dice quale dei tre. Per questo la spia non blocca nulla: ti avvisa e basta. Nel Simulatore vedi come sono andati i segnali con e senza spia. Se vuoi trasformarla in una regola, conta solo ciò che emerge dal test in avanti, non dal backtest.</p>" +
      "<p>Il volume è quello della fonte principale di ogni moneta, non la somma di più exchange.</p></div></details>" +
      "<details><summary>La fase di mercato</summary><div class='body'>" +
      "<p>Si guarda Bitcoin, che di solito trascina le altre monete. Tre misure: la direzione (prezzo e medie a " + s.ema_fast + " e " + s.ema_slow + " candele), la forza del trend (ADX, chiaro da " + P.adx_strong + " in su) e la volatilità (quanto si muove una candela rispetto agli ultimi " + Math.round(P.vol_window / 6) + " giorni: alta se è tra il " + nf((1 - P.vol_pct) * 100, 0) + "% più alto).</p>" +
      "<p>Ne escono cinque fasi: rialzo con forza, rialzo debole, transizione (le medie si contraddicono), ribasso debole e ribasso con forza. In più la volatilità può essere alta o normale. L'ampiezza dice quante delle " + D.market.n_total + " monete sono in trend rialzista: se Bitcoin sale ma poche altre lo seguono, il movimento è concentrato su poche monete.</p>" +
      "<p>Una parte è già una regola: i segnali scattano solo se Bitcoin è sopra la media a " + s.ema_slow + " candele. Tutto il resto è informativo e non cambia i segnali. Nel Simulatore vedi come sono andati i segnali in ciascuna fase.</p>" +
      "<p>È una lettura approssimativa. L'ADX, per esempio, può dare forza anche a oscillazioni molto regolari.</p></div></details>" +
      "<details><summary>Stop loss, take profit e come spostare lo stop</summary><div class=\"body\">" +
      "<p><b>Stop loss</b>: " + s.sl_atr + " ATR sotto l'entrata. Se il prezzo ci arriva, esci con la perdita prevista.</p>" +
      "<p><b>Take profit</b>: " + s.tp_atr + " ATR sopra l'entrata, cioè il doppio della distanza dello stop.</p>" +
      "<p><b>Se va bene</b>: a +" + nf(s.be_trigger, 1) + " ATR sposta lo stop al pareggio (entrata più i costi). A +" + nf(s.trail_trigger, 1) + " ATR sposta lo stop a +" + nf(s.trail_lock, 0) + " ATR sopra l'entrata. Così un trade che parte bene difficilmente chiude in perdita.</p>" +
      "<p><b>Se non succede nulla</b>: dopo " + s.max_hold / 6 + " giorni chiudi la posizione.</p></div></details>" +
      "<details><summary>Quanto investire per ogni segnale</summary><div class=\"body\"><p>Scegli quanto sei disposto a perdere per operazione: " +
      Object.keys(pr).map(k => k + " " + nf(pr[k].risk * 100, 1) + "% del capitale").join(", ") +
      ". La quota si ricava dividendo quel rischio per la distanza dello stop, con un tetto per ogni posizione (" +
      Object.keys(pr).map(k => k + " " + nf(pr[k].max_size * 100, 0) + "%").join(", ") + ") e un massimo di posizioni aperte insieme (" +
      Object.keys(pr).map(k => pr[k].max_pos).join(" / ") + "). Non si usa mai più del capitale che hai.</p></div></details>" +
      "<details><summary>Limiti da tenere presenti</summary><div class=\"body\">" +
      "<p>Nessuno strumento può garantire guadagni. Il backtest mostra cosa sarebbe successo in passato, il futuro può essere diverso. Questa pagina non è una consulenza finanziaria.</p>" +
      "<p>Le regole sono state fissate prima di vedere i dati e non vengono ritoccate. Se le cambi dopo aver guardato i risultati, il backtest smette di essere una prova: conta solo il test in avanti.</p>" +
      "<p>Costi ipotizzati: " + nf(D.costs.fee * 100, 2) + "% di commissione e " + nf(D.costs.slip * 100, 2) + "% di scostamento di prezzo per ogni operazione (circa " + nf(cs * 100, 2) + "% tra andata e ritorno). Controlla le commissioni reali su Revolut X.</p>" +
      "<p>Si ipotizza l'entrata al prezzo di chiusura della candela. Se nella stessa candela il prezzo tocca sia stop sia take profit, si assume che sia scattato lo stop. I prezzi degli exchange possono differire un po' da quelli di Revolut X.</p></div></details>" +
      "</div></section>";
  }

  function foot() {
    const src = Object.keys(D.sources).map(k => (SRC[k] || k) + " " + D.sources[k].ok + "/" + D.market.n_total + (D.sources[k].note ? " (" + esc(D.sources[k].note) + ")" : "")).join(" · ");
    const h = D.history_days;
    return '<footer class="foot"><div>Fonti raggiunte in questo aggiornamento: ' + src + ".</div>" +
      "<div>Monete con segnali abilitati: " + D.market.n_checked + " su " + D.market.n_total + ". Storico: " + Math.round(h.min) + "-" + Math.round(h.max) + " giorni.</div></footer>";
  }

  function render() {
    $("#app").innerHTML = '<div class="wrap" style="gap:28px">' + openSection() + phaseSection() + simSection() + coinsSection() + guide() + foot() + "</div>";
  }

  function syncControls() {
    document.querySelectorAll("[data-cur]").forEach(b => {
      b.setAttribute("aria-pressed", String(b.dataset.cur === S.cur));
      if (b.dataset.cur === "EUR" && !D.fx) { b.disabled = true; b.title = "Cambio euro/dollaro non disponibile"; }
    });
    $("#cap").value = S.cap;
    $("#prof").value = S.prof;
  }

  document.querySelectorAll("[data-cur]").forEach(b => b.addEventListener("click", () => { if (b.disabled) return; S.cur = b.dataset.cur; save(); syncControls(); render(); }));
  $("#cap").addEventListener("input", e => { const v = parseFloat(String(e.target.value).replace(",", ".")); if (isFinite(v) && v >= 0) { S.cap = v; save(); render(); } });
  $("#prof").addEventListener("change", e => { S.prof = e.target.value; save(); render(); });
  $("#app").addEventListener("click", e => {
    const t = e.target;
    let b = t.closest("[data-view]");
    if (b) { S.view = b.dataset.view; save(); render(); return; }
    b = t.closest("[data-mine]");
    if (b) { const id = b.dataset.mine; if (S.mine.indexOf(id) < 0) S.mine.push(id); save(); render(); return; }
    b = t.closest("[data-unmine]");
    if (b) { const id = b.dataset.unmine; S.mine = S.mine.filter(x => x !== id); save(); render(); }
  });

  head();
  syncControls();
  render();
})();
</script>
</body>
</html>
'''


def render_page(payload):
    page = PAGE if PAGE is not None else (HERE / "page.html").read_text(encoding="utf-8")
    blob = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    return page.replace("/*__DATA__*/null", blob)


# ----------------------------------------------------------------------------
# DATI DI PROVA (solo con --demo)
# ----------------------------------------------------------------------------
def demo_raw(now_ms, seed=7, days=300):
    rng = random.Random(seed)
    n = days * 6
    last_open = (now_ms // BAR_MS) * BAR_MS - BAR_MS
    # fattore di mercato con fasi rialziste e ribassiste
    mkt, drift, m = [], 0.0, 0.0
    for k in range(n):
        if k % 240 == 0:
            drift = rng.choice([0.0012, 0.0008, -0.0006, 0.0003, -0.0010])
        m += drift + rng.gauss(0, 0.006)
        mkt.append(m)
    raw = {}
    for sym, _ in COINS:
        beta = 1.0 if sym == "BTC" else rng.uniform(0.7, 1.6)
        p = rng.uniform(0.05, 800)
        rows = []
        for k in range(n):
            o = p
            if k == 0:
                c = p
            else:
                c = p * math.exp(beta * (mkt[k] - mkt[k - 1]) + rng.gauss(0, 0.004))
            hi = max(o, c) * (1 + abs(rng.gauss(0, 0.004)))
            lo = min(o, c) * (1 - abs(rng.gauss(0, 0.004)))
            vol = rng.uniform(80, 120) * (1 + abs(c / o - 1) * 40)
            rows.append((last_open - (n - 1 - k) * BAR_MS, o, hi, lo, c, vol))
            p = c
        second = [(r[0], r[1] * 1.0004, r[2] * 1.0004, r[3] * 1.0004, r[4] * (1 + rng.gauss(0, 0.0008)), r[5])
                  for r in rows[-VERIFY_BARS:]]
        raw[sym] = {"kraken": rows, "coinbase": second}
    return raw


# ----------------------------------------------------------------------------
def main(argv):
    demo = "--demo" in argv
    now_ms = int(time.time() * 1000)
    if demo:
        raw = demo_raw(now_ms)
        status = {k: dict(ok=len(COINS), fail=0, note="dati di prova") for k in ("kraken", "coinbase")}
        status["binance"] = dict(ok=0, fail=len(COINS), note="dati di prova")
        fx = 1.08
        state = dict(version=VERSION, forward_start=now_ms - 360 * BAR_MS, forward={}, telegram_chat_id=None)
    else:
        raw, status = collect(now_ms)
        fx = get_fx()
        state = load_state(now_ms)
        if not any(raw[s] for s in raw):
            log("Nessuna fonte ha risposto: esco senza modificare nulla.")
            return 1
    payload = analyze(raw, status, now_ms, state, fx)
    payload["demo"] = demo
    out = OUT_DIR if not demo else HERE / "docs-demo"
    out.mkdir(exist_ok=True)
    (out / "index.html").write_text(render_page(payload), encoding="utf-8")
    (out / ".nojekyll").write_text("", encoding="utf-8")
    (out / "icon.png").write_bytes(base64.b64decode(ICON_B64))
    if not demo:
        sent = notify(state, fx, now_ms)
        state["last_run"] = now_ms
        STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, indent=1), encoding="utf-8")
        log("Fatto: %d notifiche inviate." % sent)
    else:
        log("Demo scritta in", out / "index.html")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
