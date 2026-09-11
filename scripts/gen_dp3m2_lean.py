"""Emit dual_kappa_spike/DP3M2Ledger.lean from the banked M = 2 data.

Follows the DP6Ledger convention exactly: exact rationals as
(numerator : Int, denominator : Nat), all comparisons cross-multiplied
into Int so kernel `decide` stays on closed integer arithmetic, no
Mathlib, axiom budget {propext, Quot.sound} at most.

Source of truth: computations/dp3_m2_entries.json (exact per-entry
kernels and per-configuration census at activity truncation M = 2).

What the emitted file banks:

  * the E = 76 configuration ledger of T[1,1] — every configuration at
    that exponent, its exact Haar network value N, and its D4
    multiplicity, with BOTH the exponent and the weight rederived
    in-Lean from the labelling (the analogue of DP6Ledger's
    profileExp / profileCoeff rederivation);
  * the refutation of DP.3-(i) at entry granularity: the assembled
    coefficient is -32/3, kernel-checked negative;
  * the refutation at aggregated granularity: the (Bv)_1 coefficient at
    E = 79 is -64/3, with the sibling channels kernel-checked to
    vanish, so no cancellation is available;
  * the eps_slab(1) exponent table against the naive single-face bound;
  * evaluation pins: the final part of T[1,1] is strictly positive at
    exact rational couplings despite the negative coefficient.

Run:  python scripts/gen_dp3m2_lean.py > dual_kappa_spike/DP3M2Ledger.lean
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from computations.dp3_m2_analysis import (          # noqa: E402
    blocked_image, contributions_to, load,
)
from computations.exact_haar_network import casimir4, dim   # noqa: E402

Frac = Fraction
ENTRIES = os.path.join(os.path.dirname(os.path.dirname(
    os.path.abspath(__file__))), "computations", "dp3_m2_entries.json")

EPS_STAR = [((0, 0), 38), ((0, 1), 32), ((0, 2), 32), ((0, 3), 68),
            ((1, 1), 38), ((1, 2), 44), ((1, 3), 56), ((2, 2), 56),
            ((2, 3), 68), ((3, 3), 88)]

DEN = 3             # common denominator of the T[1,1] final part
NEG_E = 76          # the entry-level fence, in T[1,1]
BLOCKED_E = 79      # the aggregated fence, in (Bv)_1


def q(f: Frac) -> str:
    return f"({f.numerator}, {f.denominator})"


def natlist(xs) -> str:
    return "[" + ", ".join(str(x) for x in xs) + "]"


def e76_rows(raw_path):
    """Every configuration of T[1,1] at exponent NEG_E, with N and mult."""
    rec = json.load(open(raw_path))["1,1"]
    rows = []
    for c in rec["negative_configs"]:
        pass  # negatives are a subset; we need the full census below
    # the full census is not stored in the entry file; rebuild the
    # exponent-76 slice from the geometry + cached values instead
    return rows


def main():
    T, UN, W = load(ENTRIES)
    entries = json.load(open(ENTRIES))

    # --- the E = 76 slice of T[1,1], rebuilt from the geometry --------
    sys.path.insert(0, os.path.dirname(os.path.dirname(
        os.path.abspath(__file__))))
    from computations.dp3_fixed_tile import layer_labellings
    from computations.dp3_m2_driver import _classes, wpow
    import glob
    cache = {}
    for f in glob.glob("/home/claude/dp3m2/fx_cache_*.json"):
        for k, v in json.load(open(f)).items():
            if k in cache and cache[k] is not None:
                continue
            cache[k] = None if v is None else Frac(v[0], v[1])

    rows = []
    for rep, members in _classes(2).items():
        qq, ww = rep
        for top in layer_labellings(1, qq, ww, 2):
            for bot in layer_labellings(1, qq, ww, 2):
                E = (wpow(qq, ww) + sum(casimir4(a) for a in top)
                     + sum(casimir4(b) for b in bot))
                if E != NEG_E:
                    continue
                N = cache.get(f"1|1|{qq}|{ww}|{top}|{bot}")
                assert N is not None, (qq, ww, top, bot)
                rows.append((qq, ww, top, bot, len(members), N))
    rows.sort()

    total = Frac(0)
    for qq, ww, top, bot, mult, N in rows:
        wt = mult
        for x in qq:
            wt *= dim(x) ** 2
        for x in ww:
            wt *= dim(x)
        for x in top:
            wt *= dim(x)
        for x in bot:
            wt *= dim(x)
        total += N * wt
    assert total == T[(1, 1)][NEG_E] == Frac(-32, 3), total

    # --- the aggregated fence ----------------------------------------
    B1 = blocked_image(T, 1)
    contribs = contributions_to(T, 1, BLOCKED_E)
    assert B1[BLOCKED_E] == Frac(-64, 3)

    # --- T[1,1] final part -------------------------------------------
    win = entries["1,1"]["exact_below_E"]
    t11 = sorted((e, c) for e, c in T[(1, 1)].items() if e < win)

    out = []
    A = out.append
    A("""/-
  DP3M2Ledger.lean — the DP.3 M = 2 verdict, kernel-checked at the
  coefficient-ledger level.

  GENERATED FILE: emitted by scripts/gen_dp3m2_lean.py from
  computations/dp3_m2_entries.json; upstream computation
  computations/dp3_fixed_tile.py + dp3_m2_driver.py (exact Haar values
  of the pure-character slab networks at activity truncation M = 2, all
  arithmetic Fraction-exact).  Do not edit literals by hand —
  regenerate.

  The verdict this file banks (DP.3-(i) REFUTED at BOTH granularities):

  * ENTRY LEVEL.  The blocked kernel entry T[1,1] carries a NEGATIVE
    coefficient at s^76.  Every configuration at that exponent is
    listed (`e76Configs`), each with its exact network value N and its
    D4 multiplicity; both the exponent and the assembly weight are
    rederived in Lean from the labelling (`configExp`, `configWeight`),
    so the ledger is internally consistent and not merely transcribed.
    `t11_coeff_76_negative` is the Lakatos fence: the cone C_exp of
    coefficientwise-nonnegative dual data is NOT preserved by one
    blocking step at M = 2.

  * AGGREGATED LEVEL.  The DP.6 repair route — "positivity lost at fine
    granularity is restored by aggregation" — is CLOSED here.  The
    blocked image (Bv)_1 at s^79 receives contributions only from
    T[1,1] (via d_1 s^{C(1)}); the sibling channels T[1,0] and T[1,2]
    are exactly zero at the feeding exponents 79 and 71
    (`blocked_79_no_cancellation`), so the sum is -64/3
    (`blocked_79_negative`).  There is nothing to cancel against.

  * WHAT SURVIVES is positivity as a FUNCTION, not coefficientwise.
    Following the DP6Ledger precedent, "positive polynomial on (0,1)"
    is NOT formalized here as a statement about all real s.  What IS
    kernel-checked is evaluation at exact rational couplings
    (`t11_final_positive_at`), which is a partial bridge only: it
    witnesses that the negative coefficient does not make the entry
    negative at those s, and nothing more.

  * eps_slab(1).  The certified truncation exponents E*(n,m,1), each
    far above the naive single-face bound C(2) = 8
    (`eps_star_beats_naive`).  E* itself is produced by exhaustive
    enumeration in computations/eps_slab.py; only the table and its
    comparisons are banked here.

  Rationals are (numerator : Int, denominator : Nat) pairs with
  positive denominators; all comparisons cross-multiply into Int so
  kernel `decide` stays on closed integer arithmetic.

  Provenance caveat (spike-wide): the ledger literals are transported
  from the Python quaternion-Haar machinery; re-deriving them inside
  Lean from the main tree's finite product Haar evaluation is the
  wiring TODO shared with DualKappa.lean, FrozenHub.lean and
  DP6Ledger.lean.

  Axiom budget: {propext, Quot.sound} at most.  No Mathlib.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace DP3M2Ledger

/-- An exact rational as (numerator, denominator), denominator a
positive `Nat`; comparisons cross-multiply into `Int`. -/
abbrev Q := Int × Nat

def qDen (a : Q) : Int := Int.ofNat a.2

def qPos (a : Q) : Bool := decide (0 < a.1) && decide (0 < a.2)

def qNeg (a : Q) : Bool := decide (a.1 < 0) && decide (0 < a.2)

def qZero (a : Q) : Bool := decide (a.1 = 0)

def qEq (a b : Q) : Bool := decide (a.1 * qDen b = b.1 * qDen a)

def qAdd (a b : Q) : Q := (a.1 * qDen b + b.1 * qDen a, a.2 * b.2)

def qMulNat (a : Q) (k : Nat) : Q := (a.1 * Int.ofNat k, a.2)

def qSum : List Q → Q
  | [] => (0, 1)
  | a :: rest => qAdd a (qSum rest)

/-- 4x Casimir of the spin label n (n = 2j): C(n) = n(n+2). -/
def casimir4 (n : Nat) : Nat := n * (n + 2)

/-- Dimension of the spin label n: d_n = n + 1. -/
def dimOf (n : Nat) : Nat := n + 1

def sumC (l : List Nat) : Nat := l.foldl (fun acc n => acc + casimir4 n) 0

def prodD (l : List Nat) : Nat := l.foldl (fun acc n => acc * dimOf n) 1

def prodDSq (l : List Nat) : Nat :=
  l.foldl (fun acc n => acc * dimOf n * dimOf n) 1

/-- A slab configuration: perimeter-wall classes q (two faces each),
interior walls w, and the two layers' tile spins. -/
structure Config where
  q : List Nat
  w : List Nat
  top : List Nat
  bot : List Nat
  deriving DecidableEq

/-- The s-exponent of a configuration, rederived in Lean:
E = 2 Sum C(q) + Sum C(w) + Sum C(top) + Sum C(bot). -/
def configExp (c : Config) : Nat :=
  2 * sumC c.q + sumC c.w + sumC c.top + sumC c.bot

/-- The assembly weight of a configuration, rederived in Lean:
Prod d_q^2 * Prod d_w * Prod d_top * Prod d_bot.  Strictly positive by
construction — which is exactly why a negative kernel coefficient can
only come from a negative network value N. -/
def configWeight (c : Config) : Nat :=
  prodDSq c.q * prodD c.w * prodD c.top * prodD c.bot
""")

    # ---- e76 ledger --------------------------------------------------
    A("")
    A("/-- Every configuration of T[1,1] at the fence exponent 76:")
    A("(configuration, D4 orbit multiplicity, exact Haar network value N).")
    A(f"All {len(rows)} are computed — none unreached — so the assembled")
    A("coefficient below is FINAL. -/")
    A("def e76Configs : List (Config × Nat × Q) :=")
    body = []
    for qq, ww, top, bot, mult, N in rows:
        body.append(
            f"  ⟨⟨{natlist(qq)}, {natlist(ww)}, {natlist(top)}, "
            f"{natlist(bot)}⟩, {mult}, {q(N)}⟩")
    A("  [ " + ",\n    ".join(x.strip() for x in body) + " ]")
    A("")
    A("/-- The contribution of one ledger row: mult * weight * N. -/")
    A("def rowContribution : Config × Nat × Q → Q")
    A("  | (c, mult, n) => qMulNat n (mult * configWeight c)")
    A("")
    A("/-- Every listed configuration really sits at exponent 76 — the")
    A("exponent is recomputed in Lean from the labelling, not trusted. -/")
    A("theorem e76_exponents_are_76 :")
    A("    e76Configs.all (fun t => decide (configExp t.1 = 76)) = true := by")
    A("  decide")
    A("")
    A(f"theorem e76_config_count : e76Configs.length = {len(rows)} := by decide")
    A("")
    A("/-- Every assembly weight is strictly positive.  This is what")
    A("licenses the whole argument: since dimensions, Casimir powers and")
    A("orbit multiplicities are all positive, a negative coefficient in")
    A("T[n,m] can ONLY originate in a negative network value N — i.e. in")
    A("signed 6j recoupling interference, not in bookkeeping. -/")
    A("theorem e76_weights_positive :")
    A("    e76Configs.all (fun t => decide (0 < t.2.1 * configWeight t.1))")
    A("      = true := by decide")
    A("")
    nneg = sum(1 for r in rows if r[5] < 0)
    nzero = sum(1 for r in rows if r[5] == 0)
    A(f"/-- Of the {len(rows)} configurations, {nzero} have vanishing network")
    A(f"value and {nneg} are strictly negative; none is positive.  The")
    A("negativity is 6j interference, not a bookkeeping artefact. -/")
    A("theorem e76_signs :")
    A("    e76Configs.all (fun t => qNeg t.2.2 || qZero t.2.2) = true := by")
    A("  decide")
    A("")
    A("/-- **The entry-level fence** (kernel-checked): the assembled")
    A("coefficient of s^76 in T[1,1] is -32/3, hence strictly negative.")
    A("Claim DP.3-(i) — preservation of the coefficientwise cone C_exp —")
    A("is REFUTED at activity truncation M = 2. -/")
    A("theorem t11_coeff_76_value :")
    A("    qEq (qSum (e76Configs.map rowContribution)) (-32, 3) = true := by")
    A("  decide")
    A("")
    A("theorem t11_coeff_76_negative :")
    A("    qNeg (qSum (e76Configs.map rowContribution)) = true := by decide")
    A("")

    # ---- T[1,1] final part -------------------------------------------
    A(f"/-- The final part of T[1,1] at M = 2: every coefficient of")
    A(f"exponent < {win}, exact regardless of which high-exponent")
    A("configurations exceeded their budget. -/")
    A("def t11Final : List (Nat × Q) :=")
    A("  [ " + ",\n    ".join(f"({e}, {q(c)})" for e, c in t11) + " ]")
    A("")
    A("/-- Exactly one coefficient of the final part is negative, and it")
    A("is the s^76 fence; every other coefficient is strictly positive. -/")
    A("theorem t11_final_unique_negative :")
    A("    (t11Final.filter (fun t => qNeg t.2)).map (fun t => t.1) = [76]")
    A("      := by decide")
    A("")
    A(f"/-- Non-vacuity pin: the final-part ledger is not empty, so the")
    A("`List.all` verdicts above are not trivially true. -/")
    A(f"theorem t11_final_count : t11Final.length = {len(t11)} := by decide")
    A("")
    A("theorem t11_final_others_positive :")
    A("    (t11Final.filter (fun t => t.1 != 76)).all")
    A("      (fun t => qPos t.2) = true := by decide")
    A("")

    # ---- blocked image ------------------------------------------------
    A("/-- The aggregated fence.  For the heat-kernel envelope")
    A("v_m = d_m s^{C(m)}, the coefficient of s^79 in (Bv)_1 collects")
    A("T[1,m] at exponent 79 - C(m), weighted by d_m.  Entries:")
    A("(m, feeding exponent, T[1,m] coefficient there). -/")
    A("def blocked79 : List (Nat × Nat × Q) :=")
    A("  [ " + ",\n    ".join(
        f"({m}, {e}, {q(c)})" for m, e, c, _ in contribs) + " ]")
    A("")
    A("def blockedContribution : Nat × Nat × Q → Q")
    A("  | (m, _, c) => qMulNat c (dimOf m)")
    A("")
    A("/-- Non-vacuity pin. -/")
    A("theorem blocked79_count : blocked79.length = 3 := by decide")
    A("")
    A("/-- The feeding exponents are the arithmetically correct ones:")
    A("79 - C(m) for m = 0, 1, 2. -/")
    A("theorem blocked79_exponents :")
    A("    blocked79.all (fun t => decide (t.2.1 + casimir4 t.1 = 79))")
    A("      = true := by decide")
    A("")
    A("/-- **No cancellation is available.**  Both sibling channels")
    A("vanish identically at their feeding exponents, so the negative")
    A("contribution from T[1,1] stands alone — the DP.6 repair route")
    A("(cancellation across m at fixed output exponent) is CLOSED. -/")
    A("theorem blocked_79_no_cancellation :")
    A("    (blocked79.filter (fun t => t.1 != 1)).all")
    A("      (fun t => qZero t.2.2) = true := by decide")
    A("")
    A("/-- **The aggregated fence** (kernel-checked): the coefficient of")
    A("s^79 in the blocked image (Bv)_1 is -64/3, strictly negative. -/")
    A("theorem blocked_79_value :")
    A("    qEq (qSum (blocked79.map blockedContribution)) (-64, 3) = true := by")
    A("  decide")
    A("")
    A("theorem blocked_79_negative :")
    A("    qNeg (qSum (blocked79.map blockedContribution)) = true := by decide")
    A("")

    # ---- evaluation pins ----------------------------------------------
    A("/-- The final part of T[1,1] with a common denominator cleared:")
    A("(exponent, integer coefficient), where the integer is c_E * den.")
    A("The scaling is not trusted — `t11_scaled_matches` re-checks every")
    A("row against `t11Final` in the kernel. -/")
    A("def t11Scaled : List (Nat × Int) :=")
    A("  [ " + ",\n    ".join(
        f"({e}, {c.numerator * (DEN // c.denominator)})" for e, c in t11)
      + " ]")
    A("")
    A("def scaleDen : Nat := " + str(DEN))
    A("")
    A("/-- Each scaled coefficient really is c_E * scaleDen. -/")
    A("theorem t11_scaled_matches :")
    A("    (t11Final.zip t11Scaled).all (fun p =>")
    A("      decide (p.1.1 = p.2.1) && qEq (qMulNat p.1.2 scaleDen)")
    A("        (p.2.2, 1)) = true := by decide")
    A("")
    A("theorem t11_scaled_length :")
    A("    t11Scaled.length = t11Final.length := by decide")
    A("")
    A("/-- Numerator of the value of the scaled ledger at s = a/b:")
    A("N = Sum_E k_E * a^E * b^(scale - E).  Since b^scale > 0 and")
    A("scaleDen > 0, `0 < N` is equivalent to positivity of the")
    A("polynomial at s = a/b. -/")
    A("def evalNum (l : List (Nat × Int)) (a b scale : Nat) : Int :=")
    A("  l.foldl (fun acc t =>")
    A("    acc + t.2 * Int.ofNat (a ^ t.1) * Int.ofNat (b ^ (scale - t.1))) 0")
    A("")

    # pick evaluation points
    maxE = max(e for e, _ in t11)
    den = DEN
    pins = []
    for (a, b) in [(1, 4), (1, 2), (3, 4)]:
        s = Frac(a, b)
        val = sum(c * s ** e for e, c in t11)
        num = sum(int(c.numerator * (den // c.denominator)) * a ** e
                  * b ** (maxE - e) for e, c in t11)
        assert (num > 0) == (val > 0), (a, b, num, val)
        assert val > 0
        pins.append((a, b, num))
    A(f"/-- Evaluation pins for the final part of T[1,1] (max exponent")
    A(f"{maxE}, common denominator {den}).  Despite the negative")
    A("coefficient at s^76 the entry is strictly positive at each of")
    A("these exact rational couplings.  This is a WITNESS, not a proof")
    A("of positivity on all of (0,1) — that statement is certified by")
    A("Sturm in computations/, and is deliberately not claimed here. -/")
    A("theorem t11_final_positive_at :")
    for i, (a, b, num) in enumerate(pins):
        conn = "    " if i == 0 else "      && "
        A(f"{conn}decide (0 < evalNum t11Scaled {a} {b} {maxE})")
    A("      = true := by decide")
    A("")

    # ---- eps_slab ------------------------------------------------------
    A("/-- eps_slab(1): certified truncation exponents E*(n,m,1) — the")
    A("minimum s-exponent of any admissible slab configuration carrying")
    A("spin 2.  Entries: ((n, m), E*). -/")
    A("def epsStar : List ((Nat × Nat) × Nat) :=")
    A("  [ " + ",\n    ".join(
        f"(({n}, {m}), {e})" for (n, m), e in EPS_STAR) + " ]")
    A("")
    A("/-- The naive single-face bound: one face at spin 2 costs C(2). -/")
    A("def naiveBound : Nat := casimir4 2")
    A("")
    A("theorem naive_bound_is_eight : naiveBound = 8 := by decide")
    A("")
    A("/-- Non-vacuity pin. -/")
    A(f"theorem eps_star_count : epsStar.length = {len(EPS_STAR)} := by decide")
    A("")
    A("/-- **Every certified exponent beats the naive bound**, by at")
    A("least a factor of four: a spin-2 face cannot appear in isolation,")
    A("because the triads at the 4-valent interior edge and at the")
    A("corner-linked perimeter classes force companion faces up with")
    A("it. -/")
    A("theorem eps_star_beats_naive :")
    A("    epsStar.all (fun t => decide (4 * naiveBound <= t.2)) = true := by")
    A("  decide")
    A("")
    A(f"/-- The global truncation exponent is 32. -/")
    A("theorem eps_star_min :")
    A("    (epsStar.all (fun t => decide (32 <= t.2))")
    A("      && epsStar.any (fun t => decide (t.2 = 32))) = true := by decide")
    A("")
    A("end DP3M2Ledger")

    print("\n".join(out))


if __name__ == "__main__":
    main()
