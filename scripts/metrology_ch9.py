#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
metrology_ch9.py — reproducible metrology of TTP Chapters 5 and 9.

The script uses the Python standard library (bytearray sieve, array) plus
optional numpy acceleration for the histogram/CMI kernels.  It reproduces the
numerical protocol of the monograph:

  * Block A — Table 9.1: axial information law and exact U_q^4 tensor check.
  * Block B — honest proper-time diagnostics: universal r_n^(k) via an
                incremental odd mask, full-alphabet CMI_plug, Miller–Madow,
                stratified permutation null, rank ladder and the quadratic
                horizon zero test.
  * Block C — Table 5.1: 0-parameter survival law on T^8 out-of-sample.
  * Block D — Tables 9.3/9.4: IEEE-754 binary64 chord charge and the
                zero-error L_6^Dir projector reconstruction of pi(X).

Run:
    python3 scripts/metrology_ch9.py

Optional (for smoke tests only):
    python3 scripts/metrology_ch9.py --permutations 2 --blocks A,D
"""

from __future__ import annotations

import argparse
import math
import random
import sys
import time
from array import array
from bisect import bisect_right
from collections import Counter
from functools import lru_cache

try:
    import numpy as np
except Exception:  # pragma: no cover - optional acceleration
    np = None

GAMMA = 0.5772156649015329
EXP_NEG_GAMMA = math.exp(-GAMMA)

PRIMES: array
GAPS: array
PI_1E8: int
PI_2E8: int


def primes_upto(n: int) -> array:
    """Odd-only sieve of Eratosthenes. Returns all primes <= n as uint32."""
    size = (n + 1) // 2
    sieve = bytearray(b"\x01") * size
    sieve[0] = 0
    limit = math.isqrt(n)
    for i in range(1, limit // 2 + 1):
        if sieve[i]:
            p = 2 * i + 1
            start = (p * p) // 2
            sieve[start::p] = b"\x00" * (((size - 1 - start) // p) + 1)
    out = array("I", [2])
    out.extend(2 * i + 1 for i in range(1, size) if sieve[i])
    return out


def pi_upto(x: int) -> int:
    return bisect_right(PRIMES, x)


def iroot(n: int, k: int) -> int:
    """Integer k-th root."""
    if k == 1:
        return n
    r = int(round(n ** (1.0 / k)))
    while (r + 1) ** k <= n:
        r += 1
    while r ** k > n:
        r -= 1
    return r


def mobius_small(n: int) -> int:
    if n == 1:
        return 1
    factors = 0
    d = 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            factors += 1
            if n % d == 0:
                return 0
        d += 1
    if n > 1:
        factors += 1
    return -1 if factors % 2 else 1


def J_memory(r: int) -> float:
    """Structural memory kernel J(r), eq. (9.2)."""
    if r == 0:
        return 0.0
    if r == 1:
        return math.log(2.0)
    return math.log((r + 1.0) / r) + (r - 1.0) * math.log((r * r - 1.0) / (r * r))


def build_buchstab(umax: float = 8.0, du: float = 2.0e-4):
    n = int(umax / du)
    w = [0.0] * (n + 1)
    for i in range(n + 1):
        u = i * du
        if u <= 1.0:
            w[i] = 1.0
        elif u <= 2.0:
            w[i] = 1.0 / u
    F = 1.0
    for i in range(int(2.0 / du) + 1, n + 1):
        u = i * du
        x = (u - 1.0) / du
        j = int(x)
        frac = x - j
        wm = w[j] * (1.0 - frac) + w[j + 1] * frac if j + 1 <= n else w[j]
        F += wm * du
        w[i] = F / u
    return w, du


BUCH_TAB, BUCH_DU = build_buchstab()


def omega_buchstab(u: float) -> float:
    if u <= 1.0:
        return 1.0
    if u > 8.0:
        return EXP_NEG_GAMMA
    x = u / BUCH_DU
    i = int(x)
    if i >= len(BUCH_TAB) - 1:
        return BUCH_TAB[-1]
    f = x - i
    return BUCH_TAB[i] * (1.0 - f) + BUCH_TAB[i + 1] * f


# ---------------------------------------------------------------------------
# Block A
# ---------------------------------------------------------------------------
P0_REF = {
    3: 0.434982,
    5: 0.214156,
    7: 0.146284,
    11: 0.090812,
    13: 0.076419,
    17: 0.058104,
    19: 0.051942,
    23: 0.042815,
}


def measure_p0(qs, limit_index: int):
    n_all = [0] * len(qs)
    n_tr = [0] * len(qs)
    c_all = [0] * len(qs)
    c_tr = [0] * len(qs)
    for i in range(limit_index - 1):
        p = PRIMES[i]
        g = GAPS[i]
        tr = g < 60
        for j, q in enumerate(qs):
            if p > q:
                n_all[j] += 1
                if tr:
                    n_tr[j] += 1
                if g % q == 0:
                    c_all[j] += 1
                    if tr:
                        c_tr[j] += 1
    return ([c_all[j] / n_all[j] for j in range(len(qs))],
            [c_tr[j] / n_tr[j] for j in range(len(qs))])


def tensor_cmi(q: int, p0: float):
    """Exact enumeration of all (q-1)^4 trajectories in U_q^4."""
    T = [[0.0] * q for _ in range(q)]
    step = (1.0 - p0) / (q - 2)
    for u in range(1, q):
        T[u][u] += p0
        for v in range(1, q):
            if v != u:
                T[u][v] += step

    p1 = [0.0] * q
    p2 = [0.0] * q
    p12 = [[0.0] * q for _ in range(q)]
    p23 = [[0.0] * q for _ in range(q)]
    p123 = [[[0.0] * q for _ in range(q)] for _ in range(q)]

    w0 = 1.0 / (q - 1)
    for u0 in range(1, q):
        for u1 in range(1, q):
            w1 = w0 * T[u0][u1]
            if w1 == 0.0:
                continue
            a = (u1 - u0) % q
            p1[a] += w1
            for u2 in range(1, q):
                w2 = w1 * T[u1][u2]
                if w2 == 0.0:
                    continue
                b = (u2 - u1) % q
                p2[b] += w2
                p12[a][b] += w2
                for u3 in range(1, q):
                    w3 = w2 * T[u2][u3]
                    if w3 == 0.0:
                        continue
                    c = (u3 - u2) % q
                    p123[a][b][c] += w3
                    p23[b][c] += w3

    I1 = 0.0
    for a in range(q):
        if p1[a] == 0.0:
            continue
        for b in range(q):
            pab = p12[a][b]
            if pab == 0.0:
                continue
            I1 += pab * math.log(pab / (p1[a] * p2[b]))

    CMI = 0.0
    for a in range(q):
        for b in range(q):
            pab = p12[a][b]
            if pab == 0.0:
                continue
            for c in range(q):
                pabc = p123[a][b][c]
                if pabc == 0.0:
                    continue
                pbc = p23[b][c]
                CMI += pabc * math.log(pabc * p2[b] / (pab * pbc))
    return I1, CMI


def analytic_axis(q: int, p0: float):
    J1 = J_memory(q - 2)
    J2 = J_memory(q - 3)
    I1 = (1.0 - p0) ** 2 / (q - 2) * J1
    CMI = p0 * I1 + (q - 3) * (1.0 - p0) ** 3 / (q - 2) ** 2 * J2
    return I1, CMI, J1


def block_a(qs, pi_limit: int):
    print("\n" + "=" * 88)
    print("[A] ТАБЛИЦА 9.1 — осевая память и тензор U_q^4 на [1, 10^8]")
    print("=" * 88)
    t0 = time.perf_counter()
    p0_all, p0_tr = measure_p0(qs, pi_limit)
    print(f"  p0 измерены на {pi_limit} простых (p_n <= 10^8); время {time.perf_counter()-t0:.2f} s")
    print("\n  q    p0(all gaps)   p0(g<60)     p0(Table 9.1)")
    for j, q in enumerate(qs):
        print(f" {q:>3}   {p0_all[j]:.6f}       {p0_tr[j]:.6f}     {P0_REF.get(q, float('nan')):.6f}")

    rows = []
    total_cmi = 0.0
    for j, q in enumerate(qs):
        p0 = p0_all[j]
        I1a, CMIa, J1 = analytic_axis(q, p0)
        I1t, CMIt = tensor_cmi(q, p0)
        rows.append((q, q - 2, J1, p0, I1a, CMIa, abs(I1a - I1t), abs(CMIa - CMIt)))
        total_cmi += CMIa

    print("\n  Эмпирические p0 (все зазоры) и точный перебор U_q^4:")
    print("   q   r=q-2   J(q-2)      p0        I1_analyt    CMI_analyt   |dI1|      |dCMI|     share%")
    for q, r, J1, p0, I1a, CMIa, dI1, dCMI in rows:
        share = 100.0 * CMIa / total_cmi if total_cmi else 0.0
        print(f"  {q:>3}   {r:>3}   {J1:.9f}  {p0:.6f}  {I1a:.9f}  {CMIa:.9f}  {dI1:.2e}  {dCMI:.2e}  {share:6.2f}")
    print(f"  {'SUM':>3}   {'':>3}   {'':>9}  {'':>8}  {sum(r[4] for r in rows):.9f}  {total_cmi:.9f}")

    print("\n  Сверка с опубликованными p0 Таблицы 9.1 (reference check):")
    print("   q   p0_ref     I1_ref      CMI_ref     |dI1|_ref   |dCMI|_ref")
    ref_rows = []
    for q in qs:
        p0 = P0_REF[q]
        I1a, CMIa, _ = analytic_axis(q, p0)
        I1t, CMIt = tensor_cmi(q, p0)
        ref_rows.append((q, p0, I1a, CMIa, abs(I1a - I1t), abs(CMIa - CMIt)))
    ref_total = sum(r[3] for r in ref_rows)
    for q, p0, I1a, CMIa, dI1, dCMI in ref_rows:
        print(f"  {q:>3}  {p0:.6f}  {I1a:.9f}  {CMIa:.9f}  {dI1:.2e}   {dCMI:.2e}")
    print(f"  Сумма CMI_ref = {ref_total:.9f} нат; максимальная невязка = "
          f"{max(max(r[4], r[5]) for r in ref_rows):.2e}")
    print("  Примечание: опубликованные p0 близки к 1/q и не воспроизводятся")
    print("  как доля сырых зазоров, кратных q; поэтому приведены оба набора.")
    print(f"  Время блока A: {time.perf_counter()-t0:.2f} s")


# ---------------------------------------------------------------------------
# Block B
# ---------------------------------------------------------------------------
def make_open_mask(X: int) -> bytearray:
    """Odd-number mask: index i represents 2*i+1.  Index 0 (number 1) closed."""
    mask = bytearray(b"\x01") * ((X + 1) // 2)
    mask[0] = 0
    return mask


def mark_prime(mask: bytearray, p: int) -> None:
    """Close all odd multiples of p starting at p^2 (incremental Eratosthenes)."""
    if p <= 2:
        return
    start = (p * p) // 2
    if start >= len(mask):
        return
    mask[start::p] = b"\x00" * (((len(mask) - 1 - start) // p) + 1)


def make_coprime_prefix(M: int, axes):
    """Small-M prefix helper used by Block D (M6 = 30030)."""
    pat = bytearray(b"\x01") * M
    for q in axes:
        pat[0::q] = b"\x00" * (((M - 1) // q) + 1)
    pref = array("I", [0])
    c = 0
    for x in range(M):
        c += pat[x]
        pref.append(c)
    return pref, c


def proper_times_all(mask: bytearray, start: int, end: int) -> array:
    """r_n^(k) = Phi_k(p_{n+1}) - Phi_k(p_n) - 1.

    For odd p_n and even g_n, the open odd indices strictly inside
    (p_n, p_n+g_n) are [(p_n+1)/2, (p_n+g_n)/2).
    """
    out = array("H")
    append = out.append
    for i in range(start, end + 1):
        p = int(PRIMES[i])
        g = int(GAPS[i])
        append(mask.count(1, (p + 1) // 2, (p + g) // 2))
    return out


def cmi_stats(seq):
    """Plug-in CMI(X;Z|Y) with the full (uncapped) alphabet.

    Returns (CMI, K3D, K2D_XY, K2D_YZ, K1D_Y, N).  With numpy available the
    histogram is built by np.bincount; otherwise flat Python lists are used.
    No tail compression and no alphabet truncation are applied.
    """
    L = len(seq)
    if L < 3:
        return 0.0, 0, 0, 0, 0, 0
    N = L - 2
    if np is not None:
        arr = np.asarray(seq, dtype=np.int64)
        x = arr[:-2]
        y = arr[1:-1]
        z = arr[2:]
        B = int(arr.max()) + 1
        c3 = np.bincount((x * B + y) * B + z, minlength=B ** 3)
        c2xy = np.bincount(x * B + y, minlength=B ** 2)
        c2yz = np.bincount(y * B + z, minlength=B ** 2)
        c1y = np.bincount(y, minlength=B)

        def H(c):
            nz = c[c > 0]
            p = nz / N
            return float(-np.sum(p * np.log(p)))

        cmi = H(c2xy) + H(c2yz) - H(c3) - H(c1y)
        return (cmi, int(np.count_nonzero(c3)), int(np.count_nonzero(c2xy)),
                int(np.count_nonzero(c2yz)), int(np.count_nonzero(c1y)), N)

    # Pure-Python fallback: flat dense arrays plus touched-index lists.
    B = int(max(seq)) + 1
    c3 = [0] * (B ** 3)
    c2xy = [0] * (B ** 2)
    c2yz = [0] * (B ** 2)
    c1y = [0] * B
    t3, t2xy, t2yz, t1 = [], [], [], []
    for i in range(1, L - 1):
        x = int(seq[i - 1])
        y = int(seq[i])
        z = int(seq[i + 1])
        i3 = (x * B + y) * B + z
        if c3[i3] == 0:
            t3.append(i3)
        c3[i3] += 1
        i2a = x * B + y
        if c2xy[i2a] == 0:
            t2xy.append(i2a)
        c2xy[i2a] += 1
        i2b = y * B + z
        if c2yz[i2b] == 0:
            t2yz.append(i2b)
        c2yz[i2b] += 1
        if c1y[y] == 0:
            t1.append(y)
        c1y[y] += 1

    def H(vals, counts):
        s = 0.0
        for idx in vals:
            p = counts[idx] / N
            s -= p * math.log(p)
        return s

    cmi = H(t2xy, c2xy) + H(t2yz, c2yz) - H(t3, c3) - H(t1, c1y)
    return cmi, len(t3), len(t2xy), len(t2yz), len(t1), N


def stratified_permutation(seq, strata: int, rng):
    """Shuffle values inside equal-count density windows (strata)."""
    L = len(seq)
    if np is not None:
        arr = np.asarray(seq, dtype=np.uint16).copy()
        for s in range(strata):
            a = s * L // strata
            b = (s + 1) * L // strata
            rng.shuffle(arr[a:b])
        return arr

    perm = array("H", seq)
    for s in range(strata):
        a = s * L // strata
        b = (s + 1) * L // strata
        sub = list(perm[a:b])
        rng.shuffle(sub)
        perm[a:b] = array("H", sub)
    return perm


def axis_cmi_value(q: int, p0: float) -> float:
    """CMI(q, p0) of eq. (9.4) / (4.21)."""
    J1 = J_memory(q - 2)
    J2 = J_memory(q - 3)
    I1 = (1.0 - p0) ** 2 / (q - 2) * J1
    return p0 * I1 + (q - 3) * (1.0 - p0) ** 3 / (q - 2) ** 2 * J2


def build_tail_table(qmax: int = 100000):
    """Empirical p0(q) for q <= max_gap, p0=0 above; suffix sums of CMI(q)."""
    max_gap = int(max(GAPS[:PI_1E8 - 1]))
    freq = [0] * (max_gap + 1)
    total = 0
    for i in range(PI_1E8 - 1):
        g = int(GAPS[i])
        freq[g] += 1
        total += 1
    primes_q = []
    vals = []
    for p in PRIMES:
        q = int(p)
        if q > qmax:
            break
        if q == 2:
            primes_q.append(q)
            vals.append(0.0)
            continue
        if q <= max_gap:
            p0 = sum(freq[q::q]) / total
        else:
            p0 = 0.0
        primes_q.append(q)
        vals.append(axis_cmi_value(q, p0))
    suffix = [0.0] * (len(vals) + 1)
    for i in range(len(vals) - 1, -1, -1):
        suffix[i] = suffix[i + 1] + vals[i]
    return primes_q, suffix, max_gap


def make_rng(seed: int):
    return np.random.default_rng(seed) if np is not None else random.Random(seed)


def perm_mean(seq, strata: int, n_perm: int, seed: int) -> float:
    rng = make_rng(seed)
    vals = []
    for _ in range(n_perm):
        perm = stratified_permutation(seq, strata, rng)
        vals.append(cmi_stats(perm)[0])
    return sum(vals) / len(vals)


def legacy_proper_times(k: int, start: int, end: int) -> array:
    """Old prefix-based count in (p_n, p_{n+1}] (kept only for B0 verification)."""
    axes = [int(p) for p in PRIMES[:k]]
    M = 1
    phi = 1
    for p in axes:
        M *= p
        phi *= p - 1
    pref, phi2 = make_coprime_prefix(M, axes)
    assert phi == phi2

    def F(x: int) -> int:
        q, r = divmod(x, M)
        return q * phi + pref[r + 1]

    out = array("H")
    append = out.append
    for i in range(start, end + 1):
        p = int(PRIMES[i])
        g = int(GAPS[i])
        append(F(p + g) - F(p))
    return out


def verify_legacy_shift(X: int, ks=(1, 2, 6, 7, 8)):
    print("\n" + "-" * 88)
    print("[B0] Сверка нового r_n^(k) с legacy proper_times: new == old - 1")
    print("-" * 88)
    t0 = time.perf_counter()
    open_mask = make_open_mask(X)
    current_k = 1
    for k in sorted(ks):
        while current_k < k:
            current_k += 1
            mark_prime(open_mask, int(PRIMES[current_k - 1]))
        p_k = int(PRIMES[k - 1])
        start = max(0, bisect_right(PRIMES, p_k))
        end = PI_2E8 - 2
        new = proper_times_all(open_mask, start, end)
        old = legacy_proper_times(k, start, end)
        max_abs = 0
        mismatches = 0
        first_bad = None
        for i, (a, b) in enumerate(zip(new, old)):
            d = abs(int(a) - (int(b) - 1))
            if d:
                mismatches += 1
                max_abs = max(max_abs, d)
                if first_bad is None:
                    first_bad = (start + i, int(a), int(b))
        print(f"  k={k:>2}, p_k={p_k:>2}, gaps={len(new):>8}: "
              f"max|new-(old-1)|={max_abs}, mismatches={mismatches}"
              + ("" if first_bad is None else f", first_bad={first_bad}"))
    print(f"  Время B0: {time.perf_counter()-t0:.2f} s")


def check_density_drift(X: int, n_perm: int, strata_list):
    print("\n" + "-" * 88)
    print("[B1] Дрейф плотности ln p_n: стратификация и перестановочный эталон (k=1)")
    print("-" * 88)
    t0 = time.perf_counter()
    open_mask = make_open_mask(X)
    start = 1  # p_n > p_1 = 2
    seq = proper_times_all(open_mask, start, PI_1E8 - 2)
    plug = cmi_stats(seq)[0]
    print(f"  p_n > 2, [1, 10^8]: {len(seq)} зазоров, {len(seq)-2} троек")
    print(f"  CMI_plug = {plug:.9f} нат")
    print("\n  strata   CMI_perm     CMI_plug - CMI_perm")
    rows = {}
    for strata in strata_list:
        perm = perm_mean(seq, strata, n_perm, 7000 + strata)
        rows[strata] = (perm, plug - perm)
        print(f"  {strata:>6}   {perm:.9f}   {plug-perm:+.9f}")
    first_len = max(1, len(seq) // 20)
    p_lo = int(PRIMES[start])
    p_hi = int(PRIMES[start + first_len - 1])
    artifact = rows[5000][0] - rows[20][0]
    print(f"\n  Первая страта strata=20: p_n in [{p_lo}, {p_hi}], "
          f"ln p_n in [{math.log(p_lo):.3f}, {math.log(p_hi):.3f}]")
    print(f"  Артефакт грубой стратификации: "
          f"(CMI_plug-CMI_perm)_20 - (CMI_plug-CMI_perm)_5000 = "
          f"{rows[20][1]-rows[5000][1]:+.9f} нат")
    print(f"  (CMI_perm_5000 - CMI_perm_20 = {artifact:+.9f} нат)")
    print(f"  Время B1: {time.perf_counter()-t0:.2f} s")


def check_rank_ladder(X: int, ks, n_perm: int, strata: int, tail_primes, tail_suffix):
    print("\n" + "-" * 88)
    print("[B2] Лестница рангов тора: честный CMI без сжатия алфавита")
    print("-" * 88)
    t0 = time.perf_counter()
    open_mask = make_open_mask(X)
    current_k = 1
    r8_all = None
    results = {}
    print(f"  strata={strata}, перестановок={n_perm}, алфавит = max(r)+1 (без cap)")
    print("\n   k  p_k  CMI_plug_cal  dMM_cal   CMI_perm_cal  excess_cal  R_tail    "
          "net_cal  | CMI_plug_oos  dMM_oos   CMI_perm_oos  excess_oos  net_oos")
    for k in sorted(ks):
        tk = time.perf_counter()
        while current_k < k:
            current_k += 1
            mark_prime(open_mask, int(PRIMES[current_k - 1]))
        p_k = int(PRIMES[k - 1])
        r_all = proper_times_all(open_mask, 0, PI_2E8 - 2)

        cal_start = max(0, bisect_right(PRIMES, p_k))
        cal_seq = r_all[cal_start:PI_1E8 - 1]
        oos_seq = r_all[PI_1E8:PI_2E8 - 1]
        if len(cal_seq) < 3 or len(oos_seq) < 3:
            print(f"  {k:>2}  {p_k:>3}  (недостаточно данных)")
            continue

        plug_cal, k3c, k2ac, k2bc, k1c, Nc = cmi_stats(cal_seq)
        dmm_cal = (k3c - k2ac - k2bc + k1c) / (2.0 * Nc)
        plug_oos, k3o, k2ao, k2bo, k1o, No = cmi_stats(oos_seq)
        dmm_oos = (k3o - k2ao - k2bo + k1o) / (2.0 * No)

        perm_cal = perm_mean(cal_seq, strata, n_perm, 8000 + k)
        perm_oos = perm_mean(oos_seq, strata, n_perm, 9000 + k)
        excess_cal = plug_cal - perm_cal
        excess_oos = plug_oos - perm_oos
        net_cal = max(0.0, plug_cal - max(dmm_cal, perm_cal))
        net_oos = max(0.0, plug_oos - max(dmm_oos, perm_oos))
        tail_idx = bisect_right(tail_primes, p_k)
        r_tail = tail_suffix[tail_idx] if tail_idx < len(tail_suffix) else 0.0

        results[k] = {
            "p_k": p_k, "plug_cal": plug_cal, "dmm_cal": dmm_cal,
            "perm_cal": perm_cal, "excess_cal": excess_cal, "net_cal": net_cal,
            "plug_oos": plug_oos, "dmm_oos": dmm_oos, "perm_oos": perm_oos,
            "excess_oos": excess_oos, "net_oos": net_oos, "r_tail": r_tail,
            "n_cal": Nc, "n_oos": No,
        }
        if k == 8:
            r8_all = r_all
        print(f"  {k:>2} {p_k:>3}  {plug_cal:12.9f}  {dmm_cal:.6f}  {perm_cal:12.9f}  "
              f"{excess_cal:+.6f}  {r_tail:.6f}  {net_cal:.6f}  | "
              f"{plug_oos:12.9f}  {dmm_oos:.6f}  {perm_oos:12.9f}  "
              f"{excess_oos:+.6f}  {net_oos:.6f}   ({time.perf_counter()-tk:.1f} s)")
        del r_all
    print(f"  Время B2: {time.perf_counter()-t0:.2f} s")
    return results, r8_all


def check_quadratic_zero(X: int):
    print("\n" + "-" * 88)
    print("[B3] Детерминированный ноль внутри квадратичного горизонта (Теорема 4.6(2))")
    print("-" * 88)
    t0 = time.perf_counter()
    sqrtX = math.isqrt(X)
    K = bisect_right(PRIMES, sqrtX) - 1
    pK = int(PRIMES[K])
    pNext = int(PRIMES[K + 1])
    open_mask = make_open_mask(X)
    for j in range(1, K + 1):
        mark_prime(open_mask, int(PRIMES[j]))
    start = bisect_right(PRIMES, pK)
    end = bisect_right(PRIMES, X) - 2
    vals = proper_times_all(open_mask, start, end)
    max_r = int(max(vals)) if vals else 0
    H = 0.0
    if max_r > 0:
        c = Counter(int(v) for v in vals)
        Nv = len(vals)
        for v in c.values():
            p = v / Nv
            H -= p * math.log(p)
    cmi = cmi_stats(vals)[0] if max_r > 0 else 0.0
    print(f"  K={K}, p_K={pK}, p_(K+1)={pNext}, X={X}")
    print(f"  условие p_(K+1)^2 = {pNext*pNext} > X: {pNext*pNext > X}")
    print(f"  Проверено зазоров: {len(vals)}; max r_n^(K) = {max_r}")
    print(f"  H(r^(K)) = {H:.12f} нат; CMI(r^(K)) = {cmi:.12f} нат")
    print(f"  Время B3: {time.perf_counter()-t0:.2f} s")


def block_b(X: int, ks, n_perm: int, strata: int):
    print("\n" + "=" * 88)
    print("[B] ЧЕСТНАЯ ДИАГНОСТИКА БЛОКА B: собственное время r_n^(k), CMI, перестановки")
    print("=" * 88)
    t0 = time.perf_counter()
    print(f"  X={X}; n_perm={n_perm}; рабочий алфавит — полный max(r)+1 (без сжатия хвоста)")
    verify_legacy_shift(X, (1, 2, 6, 7, 8))
    check_density_drift(X, n_perm, [20, 500, 2000, 5000])
    tail_primes, tail_suffix, max_gap = build_tail_table()
    print(f"\n  Таблица хвоста: max_gap={max_gap}, простых q<=100000: {len(tail_primes)}")
    results, r8_all = check_rank_ladder(X, ks, n_perm, strata, tail_primes, tail_suffix)
    check_quadratic_zero(X)
    print(f"\n  Общее время блока B: {time.perf_counter()-t0:.2f} s")
    return results, r8_all


# ---------------------------------------------------------------------------
# Block C
# ---------------------------------------------------------------------------
def geom_entropy(h: float) -> float:
    if not (0.0 < h < 1.0):
        return float("nan")
    return -math.log(h) - (1.0 - h) / h * math.log(1.0 - h)


def block_c(r8_oos, p_oos):
    print("\n" + "=" * 88)
    print("[C] ТАБЛИЦА 5.1 — 0-параметрический закон выживания на (10^8, 2*10^8]")
    print("=" * 88)
    t0 = time.perf_counter()
    M8, PHI8 = 9699690, 1658880
    R = int(60.0 * PHI8 / M8)
    n = len(r8_oos)
    assert n == len(p_oos)

    emp = emp2 = emp_tr = emp_tr2 = emp80 = emp80_2 = 0.0
    n_tr = n80 = 0
    hc2_var = hc2_var_tr = 0.0
    z_sum = z2_sum = 0.0
    z_tr_sum = z_tr2_sum = 0.0
    hcr_sum = hcr_z_sum = 0.0
    hcr_tr_sum = hcr_z_tr_sum = 0.0
    ll_ttp = ll_cr_gap = 0.0
    r_counts_reg = Counter()
    g_counts_reg = Counter()

    for i in range(n):
        p = p_oos[i]
        g = GAPS[PI_1E8 + i]
        r = r8_oos[i]
        lnp = math.log(p)
        u = lnp / math.log(19.0)
        hc = (M8 / PHI8) / lnp
        h = hc * EXP_NEG_GAMMA / omega_buchstab(u)
        if h >= 1.0:
            h = 0.999999
        var_model = (1.0 - h) / (h * h)
        q = 1.0 - h
        var_tr_model = q / ((1.0 - q) ** 2) - (R * R * q ** R) / ((1.0 - q ** R) ** 2)

        z = (g - (M8 / PHI8) * (r + 1)) / lnp
        v = g / lnp
        emp += v
        emp2 += v * v
        z_sum += z
        z2_sum += z * z
        hc2_var += hc * hc * var_model
        hcr = hc * r
        hcr_sum += hcr
        hcr_z_sum += hcr * z

        Z = 1.0 - q ** R
        prob = (h / Z * q ** r) if r < R else (h * q ** r)
        if prob <= 0.0:
            prob = 1e-300
        ll_ttp -= math.log(prob)
        qc = math.exp(-1.0 / lnp)
        ll_cr_gap -= math.log((1.0 - qc) * qc ** (g - 1))
        if g < 60:
            g_counts_reg[g] += 1
            r_counts_reg[r] += 1
            n_tr += 1
            emp_tr += v
            emp_tr2 += v * v
            z_tr_sum += z
            z_tr2_sum += z * z
            hc2_var_tr += hc * hc * var_tr_model
            hcr_tr = hc * r
            hcr_tr_sum += hcr_tr
            hcr_z_tr_sum += hcr_tr * z
        if g < 80:
            n80 += 1
            emp80 += v
            emp80_2 += v * v

    sig_full = emp2 / n - (emp / n) ** 2
    sig_trunc = emp_tr2 / n_tr - (emp_tr / n_tr) ** 2
    sig80 = emp80_2 / n80 - (emp80 / n80) ** 2
    z_mean = z_sum / n
    z_var = z2_sum / n - z_mean ** 2
    hcr_mean = hcr_sum / n
    cov = hcr_z_sum / n - hcr_mean * z_mean
    pred_full = hc2_var / n + z_var + 2.0 * cov

    z_tr_mean = z_tr_sum / n_tr
    z_tr_var = z_tr2_sum / n_tr - z_tr_mean ** 2
    hcr_tr_mean = hcr_tr_sum / n_tr
    cov_tr = hcr_z_tr_sum / n_tr - hcr_tr_mean * z_tr_mean
    pred_trunc = hc2_var_tr / n_tr + z_tr_var + 2.0 * cov_tr

    n_reg = sum(r_counts_reg.values())
    H_r = 0.0
    for v in r_counts_reg.values():
        pp = v / n_reg
        H_r -= pp * math.log(pp)
    H_g = 0.0
    for v in g_counts_reg.values():
        pp = v / n_reg
        H_g -= pp * math.log(pp)
    mean_r_reg = sum(k * v for k, v in r_counts_reg.items()) / n_reg
    h_cr = 1.0 / (1.0 + mean_r_reg)
    H_cr = geom_entropy(h_cr)

    print(f"  Выборка A2: {n} зазоров; регулярное ядро g<60: {n_reg}")
    print(f"  Эмпирические:  sigma_full^2 = {sig_full:.6f}   sigma_trunc^2 = {sig_trunc:.6f}")
    print(f"  (для справки:  sigma^2 при g<80 = {sig80:.6f}; опубликовано 0.62019)")
    print(f"  TTP-разложение: Var(h_circ*r)_model + Var(z) + 2Cov = "
          f"{hc2_var/n:.6f} + {z_var:.6f} + {2*cov:.6f} = {pred_full:.6f}")
    print(f"  TTP trunc:      {hc2_var_tr/n_tr:.6f} + {z_tr_var:.6f} + {2*cov_tr:.6f} = {pred_trunc:.6f}")
    print(f"  Кросс-энтропия TTP на r (observed): {ll_ttp/n:.6f} нат")
    print(f"  Энтропия H(r8 | g<60):              {H_r:.6f} нат")
    print(f"  Энтропия H(g  | g<60):              {H_g:.6f} нат")
    print(f"  Cramer rank: mean_r={mean_r_reg:.6f}, h={h_cr:.6f}, H_geom={H_cr:.6f} нат")
    print(f"  Кросс-энтропия Cramer по g:         {ll_cr_gap/n:.6f} нат")
    print("\n  Сверка с Таблицей 5.1 (A2):")
    print("   empirical: sigma_full=0.62019  sigma_trunc=0.49453")
    print("   TTP T^8:   sigma_full=0.62032  sigma_trunc=0.49451  log-loss=1.8560")
    print("   Cramer:    sigma_full=1.00000  sigma_trunc=0.64821  log-loss=2.1940")
    print("  Примечание: опубликованные sigma_full/log-loss используют иную")
    print("  нормализацию/усечение; скрипт печатает фактические значения и")
    print("  явно определённые величины, чтобы протокол был воспроизводим.")
    print(f"  Время блока C: {time.perf_counter()-t0:.2f} s")


# ---------------------------------------------------------------------------
# Block D
# ---------------------------------------------------------------------------
def factor_distinct(n: int):
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append(n)
    return factors


def exact_cyclotomic_one(q: int) -> int:
    fs = factor_distinct(q)
    return fs[0] if len(fs) == 1 else 1


def phi_trig(q: int) -> float:
    if q == 2:
        return 2.0
    # Symmetric pairing (r, q-r).  Accumulate in log space: for q = 30030
    # the plain product passes through values below the binary64 underflow
    # threshold before the large-r factors restore it.
    logs = []
    for r in range(1, (q - 1) // 2 + 1):
        if math.gcd(r, q) == 1:
            s = math.sin(math.pi * r / q)
            logs.append(math.log(4.0) + 2.0 * math.log(s))
    return math.exp(math.fsum(logs))


def mobius_upto(n: int):
    mu = [1] * (n + 1)
    is_prime = [True] * (n + 1)
    primes = []
    mu[0] = 0
    for i in range(2, n + 1):
        if is_prime[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            is_prime[i * p] = False
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def sigma_L_formula(X: int, p_k: int = 13, p_next: int = 17) -> float:
    u = int(math.log(X) / math.log(p_next))
    total = 0.0
    for m in range(1, u + 1):
        total += (pi_upto(iroot(X, m)) - pi_upto(p_k)) / m
    return total


def block_d():
    print("\n" + "=" * 88)
    print("[D] ТАБЛИЦЫ 9.3 и 9.4 — калибровка IEEE 754 binary64")
    print("=" * 88)
    t0 = time.perf_counter()

    qs = [2, 3, 4, 6, 8, 9, 12, 17, 27, 30, 105, 997, 30030]
    print("\n  Таблица 9.3: Phi_q^trig(1) vs точное целое Phi_q(1)")
    print("   q       type                 phi(q)  exact   computed              |dPhi|      |dlog|")
    for q in qs:
        fs = factor_distinct(q)
        if len(fs) == 1:
            e = 0
            m = q
            while m % fs[0] == 0:
                m //= fs[0]
                e += 1
            typ = "prime" if e == 1 else f"p^{e}"
        else:
            typ = "mixed"
        exact = exact_cyclotomic_one(q)
        val = phi_trig(q)
        dphi = abs(val - exact)
        dlog = abs(math.log(val) - math.log(exact))
        nphi = sum(1 for r in range(1, q) if math.gcd(r, q) == 1)
        print(f"  {q:>5}   {typ:<20} {nphi:>6}  {exact:>5}   {val:.16f}  {dphi:.2e}  {dlog:.2e}")

    M6 = 30030
    axes6 = [2, 3, 5, 7, 11, 13]
    pref6, phi6 = make_coprime_prefix(M6, axes6)

    def F6(x: int) -> int:
        q, r = divmod(x, M6)
        return q * phi6 + pref6[r + 1]

    maxX = 1_000_000
    spf = array("I", range(maxX + 1))
    for i in range(2, math.isqrt(maxX) + 1):
        if spf[i] == i:
            for j in range(i * i, maxX + 1, i):
                if spf[j] == j:
                    spf[j] = i

    @lru_cache(maxsize=None)
    def divisors(n: int):
        if n == 1:
            return (1,)
        p = spf[n]
        m = n
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        base = divisors(m)
        out = []
        pk = 1
        for _ in range(e + 1):
            for d in base:
                out.append(d * pk)
            pk *= p
        return tuple(out)

    @lru_cache(maxsize=None)
    def ordered_fact(n: int, m: int) -> int:
        if m == 1:
            return 1 if n >= 17 else 0
        total = 0
        low = 17 ** (m - 1)
        for d in divisors(n):
            if d >= 17 and n // d >= low:
                total += ordered_fact(n // d, m - 1)
        return total

    mu = mobius_upto(16)
    horizons = [1000, 10000, 100000, 500000, 1000000]
    print("\n  Таблица 9.4: точная реконструкция pi(X) на T^6 (M6=30030, p6=13)")
    print("   X        floor(u)  open nodes   Sigma_L(direct)   Sigma_L(formula)   pi_CCA-6  pi(X)-6  |dpi|")
    for X in horizons:
        u = int(math.log(X) / math.log(17))
        open_nodes = F6(X) - F6(13)
        sum_direct = 0.0
        for n in range(14, X + 1):
            if math.gcd(n, M6) != 1:
                continue
            L = 0.0
            for m in range(1, u + 1):
                fm = ordered_fact(n, m)
                if fm:
                    L += ((-1) ** (m - 1)) * fm / m
            sum_direct += L
        sum_formula = sigma_L_formula(X)
        pi_cca = 0.0
        for r in range(1, u + 1):
            if mu[r]:
                pi_cca += mu[r] / r * sigma_L_formula(iroot(X, r))
        true_pi = pi_upto(X) - 6
        print(f"  {X:>7}   {u:>5}    {open_nodes:>8}   {sum_direct:>15.9f}   "
              f"{sum_formula:>15.9f}   {pi_cca:>8.0f}  {true_pi:>8}  {abs(pi_cca-true_pi):.2e}")
        if abs(sum_direct - sum_formula) > 1e-9:
            print(f"    [!] direct/formula residual = {sum_direct-sum_formula:.3e}")

    print(f"  Время блока D: {time.perf_counter()-t0:.2f} s")


def main():
    global PRIMES, GAPS, PI_1E8, PI_2E8
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-x", type=int, default=200_000_000)
    ap.add_argument("--permutations", type=int, default=20)
    ap.add_argument("--strata", type=int, default=2000)
    ap.add_argument("--blocks", default="A,B,C,D")
    ap.add_argument("--ks", default="1,2,3,4,6,7,8,10,12,16")
    args = ap.parse_args()
    blocks = {b.strip().upper() for b in args.blocks.split(",") if b.strip()}
    ks = [int(x) for x in args.ks.split(",") if x.strip()]

    t_start = time.perf_counter()
    print("=" * 88)
    print("TTP METROLOGY — CHAPTERS 5 AND 9 (reproducible; numpy-accelerated when available)")
    print("=" * 88)
    print(f"Python {sys.version.split()[0]}; max_x={args.max_x}; "
          f"permutations={args.permutations}; strata={args.strata}")

    t0 = time.perf_counter()
    PRIMES = primes_upto(args.max_x)
    t_sieve = time.perf_counter() - t0
    GAPS = array("H", (PRIMES[i + 1] - PRIMES[i] for i in range(len(PRIMES) - 1)))
    PI_1E8 = pi_upto(100_000_000)
    PI_2E8 = pi_upto(200_000_000)
    print(f"\n[1] Решето Эратосфена до X={args.max_x}")
    print(f"    pi(10^8)  = {PI_1E8}   (эталон 5761455)   "
          f"{'OK' if PI_1E8 == 5761455 else 'MISMATCH'}")
    print(f"    pi(2*10^8)= {PI_2E8}  (эталон 11078937)  "
          f"{'OK' if PI_2E8 == 11078937 else 'MISMATCH'}")
    print(f"    Время решета: {t_sieve:.2f} s; простых: {len(PRIMES)}; зазоров: {len(GAPS)}")
    if args.max_x < 200_000_000:
        print("    [!] ВНИМАНИЕ: max_x < 2*10^8, блоки B/C будут неполными.")

    qs = [3, 5, 7, 11, 13, 17, 19, 23]
    if "A" in blocks:
        block_a(qs, PI_1E8)

    results_b = None
    r8_all = None
    if "B" in blocks:
        results_b, r8_all = block_b(args.max_x, ks, args.permutations, args.strata)

    if "C" in blocks:
        if r8_all is None:
            open_mask = make_open_mask(args.max_x)
            for j in range(1, 8):
                mark_prime(open_mask, int(PRIMES[j]))
            r8_all = proper_times_all(open_mask, 0, PI_2E8 - 2)
        r8_oos = r8_all[PI_1E8:PI_2E8 - 1]
        p_oos = PRIMES[PI_1E8:PI_2E8 - 1]
        block_c(r8_oos, p_oos)

    if "D" in blocks:
        block_d()

    print("\n" + "=" * 88)
    print(f"ОБЩЕЕ ВРЕМЯ РАБОТЫ: {time.perf_counter()-t_start:.2f} s")
    print("=" * 88)


if __name__ == "__main__":
    main()
