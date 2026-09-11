"""Emit dual_kappa_spike/WindowLedger.lean — the certified X_11
windows as a kernel-checked ledger.

Follows the DP6Ledger/DP3M2Ledger/OSCSLedger convention: exact
rationals as (numerator : Int, denominator : Nat), comparisons
cross-multiplied into Int, kernel `decide` on closed integer
arithmetic, no Mathlib, axiom budget {propext, Quot.sound} at most.

What the emitted file makes the KERNEL do (not merely transcribe):

  * assemble T[n,m](s) = poly(s) + sum_cfg W(cfg) N(cfg) s^E(cfg)
    with the assembly weight W and exponent E rederived in Lean from
    the configuration labelling, and the polynomial evaluated at the
    exact rational coupling (evalNum precedent of DP3M2Ledger);
  * assemble the unresolved-mass bound U from the SAME labelling:
    crude rows use the fully-rederived bound W * cN (cN = d_n d_m
    prod_f d_f); CS rows use W * min(cN, r) where the cited r is
    kernel-checked to satisfy r >= 0 and r^2 >= D_a * D_b, and the
    cited partner values (D_a, D_b) are kernel-located in the cited
    diagonal ledger through the D4 action (d4Images);
  * form lo = T - U - tail and hi = T + U + tail and check
    lo > 0 (all three entries) at every grid point, plus the ratio
    certificate lo11 * lo00 > hi01^2 at the CERT grid points —
    i.e. X_11 = log(T11 T00 / T01^2) > 0 in the M -> infinity limit
    at that coupling.

Transcribed literals (provenance-caveated, NOT rederived): the M = 2
census polynomials (dp3_m2_entries.json; the (1,1) final part's
internal consistency is separately banked in DP3M2Ledger), the
landed network values N (rust/haar_contract + su2_cut_eval, gated),
the cited diagonal values (same engines; independently banked with
OS-positivity and CS checks in OSCSLedger), and the tail bounds
(level-3 CS tail + domination levels >= 4 + Lambda-slop at Lambda=8,
computed by computations/su2_cs_tail.py + su2_minf_windows.py and
rounded UP to 10^-60 — still valid upper bounds).

Mathematical inputs licensing the bound structure (prose/gated, not
kernel-checked here): the OS/CS lemma |N| <= sqrt(D_a D_b)
(work_plan §16h; kernel-exercised on all landed values in
OSCSLedger) and D4 value-invariance (gated numerically; the ACTION
is what Lean rederives).

Run:  python scripts/gen_window_lean.py > dual_kappa_spike/WindowLedger.lean
"""
from __future__ import annotations

import json
import math
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from computations.su2_cs_tail import (          # noqa: E402
    canon_key, _key_str, load_diag, _sqrt_upper, level3_tail,
)
from computations.su2_m2_finality import (      # noqa: E402
    load_all, _cfg_key, cs_sharpened_u2,
)
from computations.su2_minf_windows import (     # noqa: E402
    DomTransfer, entry_value_and_unreached, load_m2,
)

Frac = Fraction
LAM = 8
CERT_GRID = [Frac(1, 2), Frac(11, 20), Frac(9, 16), Frac(4, 7),
             Frac(3, 5), Frac(61, 100), Frac(8, 13)]
POS_GRID = [Frac(31, 50), Frac(5, 8)]
ENTRIES = (("0,0", (0, 0)), ("1,1", (1, 1)), ("0,1", (0, 1)))


def q(f: Frac) -> str:
    return f"({f.numerator}, {f.denominator})"


def natlist(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def cfg_lit(c) -> str:
    return (f"⟨{natlist(c['q'])}, {natlist(c['w'])}, "
            f"{natlist(c['top'])}, {natlist(c['bot'])}⟩")


def key_lit(loop, qq, ww, tt) -> str:
    return f"⟨{loop}, {natlist(qq)}, {natlist(ww)}, {natlist(tt)}⟩"


def ceil_to(x: Frac, scale: int) -> Frac:
    """Round x UP to a denominator of 10^scale."""
    num = x * 10 ** scale
    n = num.numerator // num.denominator
    if n * num.denominator < num.numerator:
        n += 1
    out = Frac(n, 10 ** scale)
    assert out >= x
    return out


def wd_of(c) -> int:
    W = 1
    for x in c["q"]:
        W *= (x + 1) ** 2
    for x in c["w"] + c["top"] + c["bot"]:
        W *= (x + 1)
    return W


def cN_of(n, m, c) -> int:
    cN = (n + 1) * (m + 1)
    for x in c["q"]:
        cN *= (x + 1) ** 2
    for x in c["w"] + c["top"] + c["bot"]:
        cN *= (x + 1)
    return cN


def main() -> None:
    d = load_m2()
    vals = load_all()
    diag = load_diag()

    # ---- per-entry data ---------------------------------------------
    entry_data = {}
    cited = {}          # _key_str -> (key tuple, value)
    for key, (n, m) in ENTRIES:
        poly = sorted((int(k), Frac(v[0], v[1]))
                      for k, v in d[key]["poly"].items())
        add_rows, cs_rows, crude_rows = [], [], []
        for cfg in d[key]["unreached"]:
            if "q" not in cfg:
                continue
            ks = _cfg_key(key, cfg)
            if vals.get(ks) is not None:
                v = Frac(int(vals[ks][0]), int(vals[ks][1]))
                add_rows.append((cfg, v))
                continue
            ka = canon_key(n, tuple(cfg["q"]), tuple(cfg["w"]),
                           tuple(cfg["top"]))
            kb = canon_key(m, tuple(cfg["q"]), tuple(cfg["w"]),
                           tuple(cfg["bot"]))
            da, db = diag.get(_key_str(ka)), diag.get(_key_str(kb))
            if da is not None and db is not None:
                r = ceil_to(_sqrt_upper(da * db), 40)
                assert r * r >= da * db and r >= 0
                cs_rows.append((cfg, da, db, r))
                cited[_key_str(ka)] = (ka, da)
                cited[_key_str(kb)] = (kb, db)
            else:
                crude_rows.append(cfg)
        entry_data[key] = (n, m, poly, add_rows, cs_rows, crude_rows)

    # ---- reference U (must equal cs_sharpened_u2's residual) --------
    def u_exact(key, n, m, s):
        u = Frac(0)
        for (cfg, da, db, r) in entry_data[key][4]:
            u += (Frac(wd_of(cfg))
                  * min(Frac(cN_of(n, m, cfg)), r) * s ** cfg["E"])
        for cfg in entry_data[key][5]:
            u += Frac(wd_of(cfg) * cN_of(n, m, cfg)) * s ** cfg["E"]
        return u

    def t_exact(key, n, m, s):
        n_, m_, poly, add_rows, _, _ = entry_data[key]
        t = sum(c * s ** k for k, c in poly)
        for (cfg, v) in add_rows:
            t += Frac(wd_of(cfg)) * v * s ** cfg["E"]
        return t

    # cross-check T against the reference implementation
    for key, (n, m) in ENTRIES:
        for s in (Frac(1, 2), Frac(8, 13)):
            t_ref, _ = entry_value_and_unreached(d, key, n, m, s)
            from computations.su2_m2_finality import (
                resolved_and_residual)
            add_ref, _, _ = resolved_and_residual(key, n, m, s)
            assert t_exact(key, n, m, s) == t_ref + add_ref, (key, s)

    # ---- tails (rounded up) + window soundness pre-check ------------
    def tail_exact(n, m, s):
        lvl3, _, _ = level3_tail(n, m, s, diag)
        dt = DomTransfer(n, m, s, LAM)
        rest = dt.dominated_trace(LAM) - dt.dominated_trace(3)
        assert rest >= 0
        return lvl3 + rest + dt.lam_slop()

    grid_rows = []      # (s, {entry: tail'}, cert_expected)
    for s in CERT_GRID + POS_GRID:
        tails = {}
        lo, hi = {}, {}
        for key, (n, m) in ENTRIES:
            tl = ceil_to(tail_exact(n, m, s), 60)
            tails[key] = tl
            T = t_exact(key, n, m, s)
            U = u_exact(key, n, m, s)
            lo[key] = T - U - tl
            hi[key] = T + U + tl
        assert all(v > 0 for v in lo.values()), f"not positive at {s}"
        cert = s in CERT_GRID
        if cert:
            assert lo["1,1"] * lo["0,0"] > hi["0,1"] ** 2, \
                f"ratio not certified at {s}"
        grid_rows.append((s, tails, cert,
                          float(math.log(float(
                              lo["1,1"] * lo["0,0"] / hi["0,1"] ** 2)))
                          if cert else None))

    cited_rows = sorted(cited.values(), key=lambda t: _key_str(t[0]))

    # ---- emission ---------------------------------------------------
    out = []
    A = out.append
    A("/-")
    A("  WindowLedger.lean — the certified X_11 (M -> infinity)")
    A("  windows, kernel-checked at the ledger level.")
    A("")
    A("  GENERATED FILE: emitted by scripts/gen_window_lean.py from")
    A("  dp3_m2_entries.json + the merged banked value ledgers;")
    A("  upstream engines rust/haar_contract (§16j, gated) and")
    A("  computations/su2_cut_eval.py.  Do not edit — regenerate.")
    A("")
    A("  WHAT THE KERNEL CHECKS (work_plan §16l):")
    A("")
    A("  * T[n,m](s) is ASSEMBLED in-kernel: census polynomial")
    A("    evaluated at the exact rational coupling + resolved-config")
    A("    rows with assembly weight W and exponent E rederived from")
    A("    the labelling (DP3M2Ledger's evalNum precedent, extended).")
    A("  * The unresolved-mass bound U is assembled from the SAME")
    A("    labelling: crude rows use the fully-rederived W * cN; CS")
    A("    rows use W * min(cN, r) with the cited r kernel-checked")
    A("    (r >= 0, r^2 >= D_a * D_b) and the cited partner values")
    A("    kernel-LOCATED in the cited diagonal ledger through the")
    A("    D4 action (`d4Images`), so no citation is trusted.")
    A("  * lo = T - U - tail > 0 at all grid points (all entries),")
    A("    and lo11 * lo00 > hi01^2 at the CERT points — i.e.")
    A("    X_11 = log(T11 T00 / T01^2) > 0, the blocked one-step")
    A("    mass-gap observable exceeds its U(1) mirror value 0.")
    A("")
    A("  TRANSCRIBED (provenance-caveated): census polynomials")
    A("  (dp3_m2_entries), landed N values and cited diagonal values")
    A("  (the exact engines; independently banked in OSCSLedger with")
    A("  OS-positivity + CS checks), tail bounds (level-3 CS tail +")
    A("  domination levels >= 4 + Lambda-slop at Lambda = 8, rounded")
    A("  UP to 10^-60: still valid upper bounds).  Mathematical")
    A("  inputs licensing the bound structure: the OS/CS lemma")
    A("  |N| <= sqrt(D_a D_b) (§16h) and D4 value-invariance (gated;")
    A("  the ACTION is rederived here).")
    A("")
    A("  Axiom budget: {propext, Quot.sound} at most.  No Mathlib.")
    A("-/")
    A("")
    A("set_option maxHeartbeats 16000000")
    A("set_option maxRecDepth 20000")
    A("")
    A("namespace WindowLedger")
    A("")
    A("abbrev Q := Int × Nat")
    A("")
    A("def qDen (a : Q) : Int := Int.ofNat a.2")
    A("")
    A("def qPos (a : Q) : Bool := decide (0 < a.1) && decide (0 < a.2)")
    A("")
    A("def qNonneg (a : Q) : Bool := decide (0 ≤ a.1) && decide (0 < a.2)")
    A("")
    A("def qLe (a b : Q) : Bool := decide (a.1 * qDen b ≤ b.1 * qDen a)")
    A("")
    A("def qLt (a b : Q) : Bool := decide (a.1 * qDen b < b.1 * qDen a)")
    A("")
    A("def qAdd (a b : Q) : Q := (a.1 * qDen b + b.1 * qDen a, a.2 * b.2)")
    A("")
    A("def qSub (a b : Q) : Q := (a.1 * qDen b - b.1 * qDen a, a.2 * b.2)")
    A("")
    A("def qMul (a b : Q) : Q := (a.1 * b.1, a.2 * b.2)")
    A("")
    A("def qSq (a : Q) : Q := qMul a a")
    A("")
    A("def qMulNat (a : Q) (k : Nat) : Q := (a.1 * Int.ofNat k, a.2)")
    A("")
    A("def natQ (k : Nat) : Q := (Int.ofNat k, 1)")
    A("")
    A("def qMin (a b : Q) : Q := if qLe a b then a else b")
    A("")
    A("def qSum : List Q → Q")
    A("  | [] => (0, 1)")
    A("  | a :: rest => qAdd a (qSum rest)")
    A("")
    A("/-- s^e for s = a/b. -/")
    A("def qPow (a b e : Nat) : Q := (Int.ofNat (a ^ e), b ^ e)")
    A("")
    A("def casimir4 (n : Nat) : Nat := n * (n + 2)")
    A("")
    A("def dimOf (n : Nat) : Nat := n + 1")
    A("")
    A("def sumC (l : List Nat) : Nat := l.foldl (fun acc n => acc + casimir4 n) 0")
    A("")
    A("def prodD (l : List Nat) : Nat := l.foldl (fun acc n => acc * dimOf n) 1")
    A("")
    A("def prodDSq (l : List Nat) : Nat :=")
    A("  l.foldl (fun acc n => acc * dimOf n * dimOf n) 1")
    A("")
    A("structure Config where")
    A("  q : List Nat")
    A("  w : List Nat")
    A("  top : List Nat")
    A("  bot : List Nat")
    A("  deriving BEq, DecidableEq")
    A("")
    A("structure Key where")
    A("  loop : Nat")
    A("  q : List Nat")
    A("  w : List Nat")
    A("  t : List Nat")
    A("  deriving BEq, DecidableEq")
    A("")
    A("def rot (r : Nat) (l : List Nat) : List Nat := l.drop r ++ l.take r")
    A("")
    A("def reflAnchored : List Nat → List Nat")
    A("  | [] => []")
    A("  | x :: rest => x :: rest.reverse")
    A("")
    A("def d4Images (k : Key) : List Key :=")
    A("  (List.range 4).flatMap (fun r =>")
    A("    let qq := rot r k.q")
    A("    let ww := rot r k.w")
    A("    let tt := rot r k.t")
    A("    [ ⟨k.loop, qq, ww, tt⟩,")
    A("      ⟨k.loop, reflAnchored qq, ww.reverse, reflAnchored tt⟩ ])")
    A("")
    A("/-- The s-exponent, rederived from the labelling. -/")
    A("def configExp (c : Config) : Nat :=")
    A("  2 * sumC c.q + sumC c.w + sumC c.top + sumC c.bot")
    A("")
    A("/-- The assembly weight W (loop dims excluded), rederived. -/")
    A("def wdOf (c : Config) : Nat :=")
    A("  prodDSq c.q * prodD c.w * prodD c.top * prodD c.bot")
    A("")
    A("/-- The crude |N| bound cN = d_n d_m prod_f d_f, rederived. -/")
    A("def cnOf (n m : Nat) (c : Config) : Nat :=")
    A("  dimOf n * dimOf m * prodDSq c.q * prodD c.w * prodD c.top")
    A("    * prodD c.bot")
    A("")
    A("/-- The cited diagonal values used by the CS rows — the subset")
    A("of OSCSLedger's diagLedger that the U bounds below cite;")
    A(f"{len(cited_rows)} entries, all landed. -/")
    A("def citedDiag : List (Key × Q) :=")
    lits = [f"    ⟨{key_lit(k[0], k[1], k[2], k[3])}, {q(v)}⟩"
            for (k, v) in cited_rows]
    A("  [ " + ",\n".join(lits).lstrip() + " ]")
    A("")
    A(f"theorem cited_count : citedDiag.length = {len(cited_rows)} := by decide")
    A("")
    A("theorem cited_nonneg :")
    A("    citedDiag.all (fun r => qNonneg r.2) = true := by decide")
    A("")
    A("def locates (k : Key) (v : Q) : Bool :=")
    A("  (d4Images k).any (fun img =>")
    A("    citedDiag.any (fun row => row.1 == img && row.2 == v))")
    A("")
    # ---- per-entry emissions ---------------------------------------
    tags = {"0,0": "00", "1,1": "11", "0,1": "01"}
    for key, (n, m) in ENTRIES:
        tg = tags[key]
        n_, m_, poly, add_rows, cs_rows, crude_rows = entry_data[key]
        A(f"/-- The M = 2 census polynomial of T[{key}] "
          f"(dp3_m2_entries). -/")
        A(f"def poly{tg} : List (Nat × Q) :=")
        lits = [f"    ({k}, {q(c)})" for (k, c) in poly]
        A("  [ " + ",\n".join(lits).lstrip() + " ]")
        A("")
        A(f"/-- Resolved configs of T[{key}]: (config, exact N); "
          f"weight and exponent rederived. -/")
        A(f"def addRows{tg} : List (Config × Q) :=")
        if add_rows:
            lits = [f"    ⟨{cfg_lit(c)}, {q(v)}⟩" for (c, v) in add_rows]
            A("  [ " + ",\n".join(lits).lstrip() + " ]")
        else:
            A("  []")
        A("")
        A(f"/-- CS-bounded unresolved configs of T[{key}]: "
          f"(config, D_a, D_b, r). -/")
        A(f"def csRows{tg} : List (Config × Q × Q × Q) :=")
        if cs_rows:
            lits = [f"    ⟨{cfg_lit(c)}, {q(da)}, {q(db)}, {q(r)}⟩"
                    for (c, da, db, r) in cs_rows]
            A("  [ " + ",\n".join(lits).lstrip() + " ]")
        else:
            A("  []")
        A("")
        A(f"/-- Crude-bounded unresolved configs of T[{key}]. -/")
        A(f"def crudeRows{tg} : List Config :=")
        if crude_rows:
            lits = [f"    {cfg_lit(c)}" for c in crude_rows]
            A("  [ " + ",\n".join(lits).lstrip() + " ]")
        else:
            A("  []")
        A("")
        A(f"def tVal{tg} (a b : Nat) : Q :=")
        A(f"  qAdd (qSum (poly{tg}.map (fun t => qMul t.2 (qPow a b t.1))))")
        A(f"       (qSum (addRows{tg}.map (fun r =>")
        A(f"         qMul (qMulNat r.2 (wdOf r.1))")
        A(f"              (qPow a b (configExp r.1)))))")
        A("")
        A(f"def uVal{tg} (a b : Nat) : Q :=")
        A(f"  qAdd (qSum (csRows{tg}.map (fun r =>")
        A(f"         qMul (qMulNat (qMin r.2.2.2 (natQ (cnOf {n} {m} r.1)))")
        A(f"                       (wdOf r.1))")
        A(f"              (qPow a b (configExp r.1)))))")
        A(f"       (qSum (crudeRows{tg}.map (fun c =>")
        A(f"         qMul (natQ (wdOf c * cnOf {n} {m} c))")
        A(f"              (qPow a b (configExp c)))))")
        A("")
        A(f"/-- Every CS citation of T[{key}] is valid: r >= 0,")
        A(f"r^2 >= D_a * D_b, and both cited values are located in")
        A(f"`citedDiag` at a D4 image of the demanded key. -/")
        A(f"theorem cs_valid{tg} :")
        A(f"    csRows{tg}.all (fun r =>")
        A(f"      qNonneg r.2.2.2")
        A(f"      && qLe (qMul r.2.1 r.2.2.1) (qSq r.2.2.2)")
        A(f"      && locates ⟨{n}, r.1.q, r.1.w, r.1.top⟩ r.2.1")
        A(f"      && locates ⟨{m}, r.1.q, r.1.w, r.1.bot⟩ r.2.2.1)")
        A(f"      = true := by decide")
        A("")
    # ---- grids ------------------------------------------------------
    A("/-- lo/hi per entry: T -+ (U + tail). -/")
    A("def lo00 (a b : Nat) (tl : Q) : Q :=")
    A("  qSub (tVal00 a b) (qAdd (uVal00 a b) tl)")
    A("def hi01 (a b : Nat) (tl : Q) : Q :=")
    A("  qAdd (tVal01 a b) (qAdd (uVal01 a b) tl)")
    A("def lo01 (a b : Nat) (tl : Q) : Q :=")
    A("  qSub (tVal01 a b) (qAdd (uVal01 a b) tl)")
    A("def lo11 (a b : Nat) (tl : Q) : Q :=")
    A("  qSub (tVal11 a b) (qAdd (uVal11 a b) tl)")
    A("")
    A("/-- One grid row: (a, b, tail00, tail11, tail01) for s = a/b;")
    A("tails are Lambda = 8 bounds rounded UP to 10^-60. -/")
    A("abbrev Row := Nat × Nat × Q × Q × Q")
    A("")
    A("def posAt (g : Row) : Bool :=")
    A("  qPos (lo00 g.1 g.2.1 g.2.2.1)")
    A("  && qPos (lo11 g.1 g.2.1 g.2.2.2.1)")
    A("  && qPos (lo01 g.1 g.2.1 g.2.2.2.2)")
    A("")
    A("def certAt (g : Row) : Bool :=")
    A("  posAt g")
    A("  && qLt (qSq (hi01 g.1 g.2.1 g.2.2.2.2))")
    A("         (qMul (lo11 g.1 g.2.1 g.2.2.2.1)")
    A("               (lo00 g.1 g.2.1 g.2.2.1))")
    A("")
    cert_lits, pos_lits = [], []
    for (s, tails, cert, x11lo) in grid_rows:
        row = (f"    ({s.numerator}, {s.denominator}, "
               f"{q(tails['0,0'])}, {q(tails['1,1'])}, "
               f"{q(tails['0,1'])})")
        (cert_lits if cert else pos_lits).append(row)
    A("/-- The ratio-certified grid: X_11 > 0 kernel-checked at each")
    A("s = a/b.  Certified X_11 lower bounds (float, for the reader):")
    for (s, _, cert, x11lo) in grid_rows:
        if cert:
            A(f"    s = {s}: X_11 >= {x11lo:+.6f}")
    A("-/")
    A("def certGrid : List Row :=")
    A("  [ " + ",\n".join(cert_lits).lstrip() + " ]")
    A("")
    A("/-- The positivity-only grid (window positive; ratio open). -/")
    A("def posGrid : List Row :=")
    A("  [ " + ",\n".join(pos_lits).lstrip() + " ]")
    A("")
    A(f"theorem cert_grid_count : certGrid.length = {len(cert_lits)}"
      f" := by decide")
    A("")
    A(f"theorem pos_grid_count : posGrid.length = {len(pos_lits)}"
      f" := by decide")
    A("")
    A("theorem grid_tails_nonneg :")
    A("    (certGrid ++ posGrid).all (fun g =>")
    A("      qNonneg g.2.2.1 && qNonneg g.2.2.2.1 && qNonneg g.2.2.2.2)")
    A("      = true := by decide")
    A("")
    A("/-- **The certified windows are positive** at every grid")
    A("point: T - U - tail > 0 entrywise. -/")
    A("theorem windows_positive :")
    A("    (certGrid ++ posGrid).all posAt = true := by decide")
    A("")
    A("/-- **The X_11 ratio certificate**: lo11 * lo00 > hi01^2 at")
    A("every CERT grid point, i.e. the blocked one-step observable")
    A("X_11 = log(T11 T00 / T01^2) is strictly positive in the")
    A("M -> infinity limit — the SU(2) instrument reads a gap where")
    A("its U(1) mirror reads exactly 0 — now with the whole")
    A("assembly's arithmetic replayed by the Lean kernel. -/")
    A("theorem x11_ratio_certified :")
    A("    certGrid.all certAt = true := by decide")
    A("")
    A("end WindowLedger")
    print("\n".join(out))


if __name__ == "__main__":
    main()
