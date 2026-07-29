"""Emit dual_kappa_spike/OSCSLedger.lean from the banked OS/CS data.

Follows the DP6Ledger/DP3M2Ledger convention exactly: exact rationals
as (numerator : Int, denominator : Nat), all comparisons
cross-multiplied into Int so kernel `decide` stays on closed integer
arithmetic, no Mathlib, axiom budget {propext, Quot.sound} at most.

Source of truth: the merged banked ledgers
computations/su2_cs_diagonals.json* (reflection-diagonal norms
N(loop, loop; q, w, t, t)) and computations/su2_m2_finality.json*
(direct off-diagonal M = 2 network values N(n, m; q, w, top, bot)).
The values were computed by the exact contraction engines —
rust/haar_contract (work_plan section 16j; gated against every banked
exact value) driven through computations/su2_rust_eval.py, and the
Python reference engine computations/su2_cut_eval.py — and are
transported here as literals.

What the emitted file banks (the config-level shadow of DP.R1's OS
Gram positivity, work_plan sections 16h-16j):

  * OS POSITIVITY AT LEDGER LEVEL.  Every landed reflection-diagonal
    value is nonnegative (`diag_nonneg`).  The diagonals are OS norms
    of half-configurations under the Osterwalder-Seiler link
    reflection; nonnegativity is a PREDICTION of that structure, and
    the kernel check confirms the computed values comply.

  * THE OS/CS INEQUALITY.  For every landed off-diagonal value whose
    two diagonal partners are both landed: N^2 <= D_a * D_b
    (`cs_bound_all`).  The partner keys are NOT transcribed: Lean
    rederives the D4 action on half-configuration keys (`d4Images`)
    and kernel-checks that each cited partner value appears in the
    diagonal ledger at a D4 image of the key demanded by the lemma
    (`cs_partners_located`).

  * THE CRUDE BOUND.  |N| <= d_n d_m prod_f d_f with the face product
    rederived in Lean from the labelling (`diag_le_crude`,
    `m2_le_crude`) — the bound that drives the domination transfer of
    work_plan section 16g.

  * THE SIGN CENSUS.  Off-diagonal values DO go negative (6j
    recoupling interference — the phenomenon behind the DP3M2 fence);
    the negative count is kernel-checked (`m2_negative_count`), so the
    CS inequality is exercised on signed data, not on a trivially
    positive family.

Run:  python scripts/gen_oscs_lean.py > dual_kappa_spike/OSCSLedger.lean
"""
from __future__ import annotations

import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from computations.su2_cs_tail import (          # noqa: E402
    canon_key, _key_str, load_diag,
)
from computations.su2_m2_finality import load_all   # noqa: E402

Frac = Fraction


def q(f: Frac) -> str:
    return f"({f.numerator}, {f.denominator})"


def natlist(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def key_lit(loop, qq, ww, tt) -> str:
    return (f"⟨{loop}, {natlist(qq)}, {natlist(ww)}, "
            f"{natlist(tt)}⟩")


def cfg_lit(qq, ww, top, bot) -> str:
    return (f"⟨{natlist(qq)}, {natlist(ww)}, {natlist(top)}, "
            f"{natlist(bot)}⟩")


def parse_key(ks: str):
    loop_s, qs, ws, ts = ks.split("|")
    return (int(loop_s), tuple(map(int, qs.split(","))),
            tuple(map(int, ws.split(","))), tuple(map(int, ts.split(","))))


def parse_cfg(ks: str):
    entry, qs, ws, ts, bs = ks.split("|")
    n, m = map(int, entry.split(","))
    return (n, m, tuple(map(int, qs.split(","))),
            tuple(map(int, ws.split(","))),
            tuple(map(int, ts.split(","))), tuple(map(int, bs.split(","))))


def main() -> None:
    diag = load_diag()
    m2 = load_all()

    diag_rows = []          # (loop, q, w, t, value)
    for ks in sorted(k for k, v in diag.items() if v is not None):
        loop, qq, ww, tt = parse_key(ks)
        diag_rows.append((loop, qq, ww, tt, diag[ks]))
    assert diag_rows, "empty diagonal ledger"
    assert all(v >= 0 for *_, v in diag_rows)

    m2_rows = []            # (n, m, q, w, top, bot, value)
    for ks in sorted(k for k, v in m2.items() if v is not None):
        n, m, qq, ww, top, bot = parse_cfg(ks)
        v = m2[ks]
        m2_rows.append((n, m, qq, ww, top, bot, Frac(int(v[0]), int(v[1]))))
    assert m2_rows, "empty M = 2 finality ledger"
    n_neg = sum(1 for *_, v in m2_rows if v < 0)

    cs_rows = []            # (n, m, q, w, top, bot, N, Da, Db)
    for (n, m, qq, ww, top, bot, v) in m2_rows:
        da = diag.get(_key_str(canon_key(n, qq, ww, top)))
        db = diag.get(_key_str(canon_key(m, qq, ww, bot)))
        if da is None or db is None:
            continue
        assert v * v <= da * db, \
            f"CS violated: {(n, m, qq, ww, top, bot)}"
        cs_rows.append((n, m, qq, ww, top, bot, v, da, db))
    assert cs_rows, "no CS-checkable rows"
    n_cs_signed = sum(1 for *_, v, _a, _b in cs_rows if v < 0)

    out = []
    A = out.append
    A("/-")
    A("  OSCSLedger.lean — the OS/CS structure of the slab network")
    A("  values, kernel-checked at the coefficient-ledger level.")
    A("")
    A("  GENERATED FILE: emitted by scripts/gen_oscs_lean.py from the")
    A("  merged banked ledgers computations/su2_cs_diagonals.json* and")
    A("  computations/su2_m2_finality.json*; upstream computation the")
    A("  exact contraction engines rust/haar_contract (work_plan")
    A("  §16j, gated against every banked exact value) via")
    A("  computations/su2_rust_eval.py and the Python reference")
    A("  engine computations/su2_cut_eval.py — all arithmetic exact.")
    A("  Do not edit literals by hand — regenerate.")
    A("")
    A("  What this file banks (the config-level shadow of DP.R1's OS")
    A("  Gram positivity; work_plan §§16h–16j):")
    A("")
    A("  * OS POSITIVITY.  Every landed reflection-diagonal value is")
    A("    nonnegative (`diag_nonneg`).  Diagonals are OS norms under")
    A("    the Osterwalder–Seiler link reflection; nonnegativity is a")
    A("    PREDICTION of that structure and the computed values comply.")
    A("")
    A("  * THE OS/CS INEQUALITY.  N² ≤ D_a · D_b for every landed")
    A("    off-diagonal whose diagonal partners are both landed")
    A("    (`cs_bound_all`).  The partner keys are NOT transcribed:")
    A("    `d4Images` rederives the D4 action in Lean and")
    A("    `cs_partners_located` kernel-checks that each cited partner")
    A("    value sits in the diagonal ledger at a D4 image of the key")
    A("    the lemma demands.")
    A("")
    A("  * THE CRUDE BOUND.  |N| ≤ d_n d_m Π_f d_f, the face product")
    A("    rederived in Lean from the labelling (`diag_le_crude`,")
    A("    `m2_le_crude`) — the bound driving §16g's domination")
    A("    transfer.")
    A("")
    A("  * THE SIGN CENSUS.  Off-diagonal values DO go negative (6j")
    A("    recoupling interference); the count is kernel-checked, so")
    A("    the CS inequality is exercised on signed data.")
    A("")
    A("  Provenance caveat (spike-wide): the ledger literals are")
    A("  transported from the exact contraction engines; re-deriving")
    A("  them inside Lean from the main tree's finite product Haar")
    A("  evaluation is the wiring TODO shared with DualKappa.lean,")
    A("  FrozenHub.lean, DP6Ledger.lean and DP3M2Ledger.lean.")
    A("")
    A("  Axiom budget: {propext, Quot.sound} at most.  No Mathlib.")
    A("-/")
    A("")
    A("set_option maxHeartbeats 4000000")
    A("set_option maxRecDepth 10000")
    A("")
    A("namespace OSCSLedger")
    A("")
    A("/-- An exact rational as (numerator, denominator), denominator a")
    A("positive `Nat`; comparisons cross-multiply into `Int`. -/")
    A("abbrev Q := Int × Nat")
    A("")
    A("def qDen (a : Q) : Int := Int.ofNat a.2")
    A("")
    A("def qNonneg (a : Q) : Bool := decide (0 ≤ a.1) && decide (0 < a.2)")
    A("")
    A("def qNeg (a : Q) : Bool := decide (a.1 < 0) && decide (0 < a.2)")
    A("")
    A("/-- a ≤ b by cross-multiplication (valid: denominators positive). -/")
    A("def qLe (a b : Q) : Bool := decide (a.1 * qDen b ≤ b.1 * qDen a)")
    A("")
    A("def qMul (a b : Q) : Q := (a.1 * b.1, a.2 * b.2)")
    A("")
    A("def qSq (a : Q) : Q := qMul a a")
    A("")
    A("/-- |a| ≤ k for a natural bound k, by cross-multiplication. -/")
    A("def qAbsLeNat (a : Q) (k : Nat) : Bool :=")
    A("  decide (a.1.natAbs ≤ k * a.2)")
    A("")
    A("/-- 4x Casimir of the spin label n (n = 2j): C(n) = n(n+2). -/")
    A("def casimir4 (n : Nat) : Nat := n * (n + 2)")
    A("")
    A("/-- Dimension of the spin label n: d_n = n + 1. -/")
    A("def dimOf (n : Nat) : Nat := n + 1")
    A("")
    A("def sumC (l : List Nat) : Nat := l.foldl (fun acc n => acc + casimir4 n) 0")
    A("")
    A("def prodD (l : List Nat) : Nat := l.foldl (fun acc n => acc * dimOf n) 1")
    A("")
    A("def prodDSq (l : List Nat) : Nat :=")
    A("  l.foldl (fun acc n => acc * dimOf n * dimOf n) 1")
    A("")
    A("/-- A half-configuration key: the loop spin and the D4-orbit data")
    A("(perimeter classes q, interior walls w, tile spins t). -/")
    A("structure Key where")
    A("  loop : Nat")
    A("  q : List Nat")
    A("  w : List Nat")
    A("  t : List Nat")
    A("  deriving BEq, DecidableEq")
    A("")
    A("/-- A full slab configuration (as in DP3M2Ledger). -/")
    A("structure Config where")
    A("  q : List Nat")
    A("  w : List Nat")
    A("  top : List Nat")
    A("  bot : List Nat")
    A("  deriving BEq, DecidableEq")
    A("")
    A("/-- Cyclic rotation by r. -/")
    A("def rot (r : Nat) (l : List Nat) : List Nat := l.drop r ++ l.take r")
    A("")
    A("/-- The reflection on corner-anchored lists: fix the head, reverse")
    A("the rest (q and t); walls reverse outright. -/")
    A("def reflAnchored : List Nat → List Nat")
    A("  | [] => []")
    A("  | x :: rest => x :: rest.reverse")
    A("")
    A("/-- The 8 images of a key under the D4 action: rotations shift")
    A("corners and sides together; the reflection fixes the anchor of q")
    A("and t and reverses w.  This is the SAME action gated against")
    A("computed network values in computations/su2_cs_tail.cs_gate —")
    A("value-invariance is an input fact; the ACTION is rederived here. -/")
    A("def d4Images (k : Key) : List Key :=")
    A("  (List.range 4).flatMap (fun r =>")
    A("    let qq := rot r k.q")
    A("    let ww := rot r k.w")
    A("    let tt := rot r k.t")
    A("    [ ⟨k.loop, qq, ww, tt⟩,")
    A("      ⟨k.loop, reflAnchored qq, ww.reverse, reflAnchored tt⟩ ])")
    A("")
    A("/-- The crude value bound for a half-diagonal:")
    A("d_loop² Π_q d² Π_w d Π_t d² (top = bot = t on a diagonal). -/")
    A("def diagCrude (k : Key) : Nat :=")
    A("  dimOf k.loop * dimOf k.loop * prodDSq k.q * prodD k.w")
    A("    * prodDSq k.t")
    A("")
    A("/-- The crude value bound for an off-diagonal configuration:")
    A("d_n d_m Π_q d² Π_w d Π_top d Π_bot d. -/")
    A("def m2Crude (n m : Nat) (c : Config) : Nat :=")
    A("  dimOf n * dimOf m * prodDSq c.q * prodD c.w * prodD c.top")
    A("    * prodD c.bot")
    A("")
    A("/-- The landed reflection-diagonal ledger: (key, exact OS norm")
    A(f"N(loop, loop; q, w, t, t)).  {len(diag_rows)} landed values;")
    A("budget-missed keys are ABSENT, never zero-filled. -/")
    A("def diagLedger : List (Key × Q) :=")
    lits = []
    for (loop, qq, ww, tt, v) in diag_rows:
        lits.append(f"    ⟨{key_lit(loop, qq, ww, tt)}, {q(v)}⟩")
    A("  [ " + ",\n".join(lits).lstrip() + " ]")
    A("")
    A("/-- Non-vacuity pin. -/")
    A(f"theorem diag_count : diagLedger.length = {len(diag_rows)} := by decide")
    A("")
    A("/-- **OS positivity at ledger level**: every landed diagonal is")
    A("nonnegative — as the Osterwalder–Seiler reflection structure")
    A("demands of a norm.  (7 of the off-diagonal values below are")
    A("negative, so this is not a triviality of the evaluator.) -/")
    A("theorem diag_nonneg :")
    A("    diagLedger.all (fun r => qNonneg r.2) = true := by decide")
    A("")
    A("/-- Every diagonal obeys the crude bound, with the face product")
    A("rederived from the labelling — the |N| ≤ d_n d_m Π d_f input to")
    A("§16g's domination transfer, checked on every landed value. -/")
    A("theorem diag_le_crude :")
    A("    diagLedger.all (fun r => qAbsLeNat r.2 (diagCrude r.1))")
    A("      = true := by decide")
    A("")
    A("/-- The landed direct M = 2 off-diagonal ledger:")
    A(f"(n, m, config, exact N).  {len(m2_rows)} landed values. -/")
    A("def m2Ledger : List (Nat × Nat × Config × Q) :=")
    lits = []
    for (n, m, qq, ww, top, bot, v) in m2_rows:
        lits.append(f"    ⟨{n}, {m}, {cfg_lit(qq, ww, top, bot)}, {q(v)}⟩")
    A("  [ " + ",\n".join(lits).lstrip() + " ]")
    A("")
    A("/-- Non-vacuity pin. -/")
    A(f"theorem m2_count : m2Ledger.length = {len(m2_rows)} := by decide")
    A("")
    A("/-- **The sign census**: exactly the kernel-checked number of")
    A("off-diagonal values are strictly negative — 6j recoupling")
    A("interference, the phenomenon behind DP3M2Ledger's fence.  The")
    A("CS inequality below is exercised on signed data. -/")
    A("theorem m2_negative_count :")
    A(f"    (m2Ledger.filter (fun r => qNeg r.2.2.2)).length = {n_neg}")
    A("      := by decide")
    A("")
    A("/-- Every off-diagonal obeys the crude bound (rederived weight). -/")
    A("theorem m2_le_crude :")
    A("    m2Ledger.all (fun r =>")
    A("      qAbsLeNat r.2.2.2 (m2Crude r.1 r.2.1 r.2.2.1)) = true := by")
    A("  decide")
    A("")
    A("/-- The CS-checkable rows: every landed off-diagonal whose two")
    A("diagonal partners are both landed, with the cited partner values.")
    A("Entries: (n, m, config, N, D_a, D_b).  The partner VALUES are")
    A("literals; their membership in `diagLedger` at the D4 image of")
    A("the key the lemma demands is kernel-checked below, so the")
    A("pairing is rederived, not trusted. -/")
    A("def csRows : List (Nat × Nat × Config × Q × Q × Q) :=")
    lits = []
    for (n, m, qq, ww, top, bot, v, da, db) in cs_rows:
        lits.append(f"    ⟨{n}, {m}, {cfg_lit(qq, ww, top, bot)}, "
                    f"{q(v)}, {q(da)}, {q(db)}⟩")
    A("  [ " + ",\n".join(lits).lstrip() + " ]")
    A("")
    A("/-- Non-vacuity pin. -/")
    A(f"theorem cs_count : csRows.length = {len(cs_rows)} := by decide")
    A("")
    A("/-- The half-keys the OS/CS lemma pairs an off-diagonal with:")
    A("(n; q, w, top) and (m; q, w, bot). -/")
    A("def keyA (r : Nat × Nat × Config × Q × Q × Q) : Key :=")
    A("  ⟨r.1, r.2.2.1.q, r.2.2.1.w, r.2.2.1.top⟩")
    A("")
    A("def keyB (r : Nat × Nat × Config × Q × Q × Q) : Key :=")
    A("  ⟨r.2.1, r.2.2.1.q, r.2.2.1.w, r.2.2.1.bot⟩")
    A("")
    A("/-- The cited partner value appears in the diagonal ledger at a")
    A("D4 image of the demanded key. -/")
    A("def locates (k : Key) (v : Q) : Bool :=")
    A("  (d4Images k).any (fun img =>")
    A("    diagLedger.any (fun row => row.1 == img && row.2 == v))")
    A("")
    A("/-- **The pairing is rederived in Lean**: for every CS row, both")
    A("cited diagonal values are located in `diagLedger` through the")
    A("D4 action on the keys (n; q, w, top) and (m; q, w, bot). -/")
    A("theorem cs_partners_located :")
    A("    csRows.all (fun r =>")
    A("      locates (keyA r) r.2.2.2.2.1 && locates (keyB r) r.2.2.2.2.2)")
    A("      = true := by decide")
    A("")
    A("/-- **The OS/CS inequality, kernel-checked**: N² ≤ D_a · D_b on")
    A("every checkable row — the config-level shadow of DP.R1's OS Gram")
    A("positivity (work_plan §16h), the inequality that turns landed")
    A("diagonals into certified off-diagonal tail collapses. -/")
    A("theorem cs_bound_all :")
    A("    csRows.all (fun r =>")
    A("      qLe (qSq r.2.2.2.1) (qMul r.2.2.2.2.1 r.2.2.2.2.2))")
    A("      = true := by decide")
    A("")
    if n_cs_signed:
        A("/-- The signed case is covered: at least one CS-checked row")
        A("carries a strictly negative N (6j interference), so the")
        A("inequality is not exercised on positives alone. -/")
        A("theorem cs_includes_signed :")
        A(f"    (csRows.filter (fun r => qNeg r.2.2.2.1)).length = "
          f"{n_cs_signed}")
        A("      := by decide")
        A("")
    A("end OSCSLedger")
    print("\n".join(out))


if __name__ == "__main__":
    main()
