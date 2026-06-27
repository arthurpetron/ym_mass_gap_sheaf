/-
Track B / R2 — CAPSTONE of the dominant-mode margin loop: the SCOPE of the
character-coefficient "gap = 1 − leading character coefficient" margin.

# What this module is — and what it is NOT (read first)

This module does NOT claim a physical Yang–Mills mass gap.  It DELIMITS THE SCOPE of
the dominant-mode character-coefficient margin: it machine-confirms that the margin's
zero-crossing — where the formula `gap = 1 − (leading character coefficient)` turns
NEGATIVE — is the genuine STRONG/WEAK-coupling boundary, NOT an artifact of the `N = 1`
truncation.  It is a small, concrete confirmation built entirely on the already-proved
fusion machinery.

# The character-coefficient margin and its zero-crossing (the conceptual finding)

The diagonal SU(2) heat-kernel character coefficient at spin `s = 1` is
`coeffW w 1 = dimQ 1 · w^{C₄(1)} = 2·w³` — exactly the character coefficient
`2·e^{−3t}` with `w = e^{−t}` (`t` the heat-kernel time, `t → 0` is weak coupling,
`t → ∞` is strong coupling).  The dominant-mode "gap = 1 − leading character
coefficient" margin therefore reads `1 − 2w³`, and the vacuum-normalized fusion form
`physMargin = (1 − c₁)²/(1 + c₁²)` (`c₁ = 2w³`) vanishes EXACTLY at `c₁ = 1`, i.e. at

    w = 2^{−1/3} ≈ 0.794   (the intermediate-coupling "middle").

So the raw excited coefficient `c₁ = 2w³` EXCEEDS the vacuum coefficient `1` for
`w > 2^{−1/3}` (weak coupling, small `t`): the `gap = 1 − leading-coefficient`
formula is positive at strong coupling and NEGATIVE at weak coupling.  It is a
STRONG-COUPLING formula.

# The facts machine-confirmed here (all `decide` on closed concrete rationals)

  * FACT 1 (`raw_excited_exceeds_vacuum`, `raw_excited_below_vacuum_strong`).  At the
    weak-coupling witness `w = 4/5 = 0.8` (just past the `2^{−1/3} ≈ 0.794`
    boundary), `coeffW (4/5) 1 = 2·(4/5)³ = 128/125 > 1`: the raw `s = 1` character
    coefficient exceeds the vacuum, so `1 − coeffW · 1 < 0`.  At the strong-coupling
    witness `w = 1/6`, `coeffW (1/6) 1 = 2/216 < 1`, so the formula stays positive.
    The zero-crossing of `gap = 1 − leading-coefficient` is BRACKETED by these two.

  * FACT 2 (`n2_margin_nonpos_at_witness`, on the GENUINE `fusionProduct 2`).  The
    zero-crossing is NOT an `N = 1` truncation artifact.  At `N = 2` the genuine
    Clebsch–Gordan fusion gives, at the SAME witness `w = 4/5`,

        Z'₂ = fusionProduct 2 (coeffW w)(coeffW w) 0  =  1 + c₁² + c₂²
        E₂  = fusionProduct 2 (coeffW w)(coeffW w) 1  =  2c₁(1 + c₂)

    (selection rule below), with `c₂ = coeffW (4/5) 2 = 3·(4/5)⁸ = 196608/390625 ≈
    0.503`.  The margin numerator `Z'₂ − E₂ = (1 − c₁)² + c₂(c₂ − 2c₁) ≤ 0` here, so
    the normalized excited coefficient `E₂/Z'₂ ≥ 1` and the margin is `≤ 0` at `N = 2`
    too.  Proved directly on the real `fusionProduct 2` by `decide` at the concrete
    rational.

  * The N=2 selection rule (`fusionInd2_*`, `fusionExcited2_eqv_witness`,
    `fusionTrivial2_eqv_witness`).  Each compatible `(a,b)` indicator is `decide`-
    checked: at `s = 1` the surviving pairs are `(0,1),(1,0),(1,2),(2,1)` (giving
    `E₂ ≃ 2c₁ + 2c₁c₂ = 2c₁(1+c₂)` with `c₀ = 1`), and at `s = 0` the surviving pairs
    are the diagonals `(0,0),(1,1),(2,2)` (giving `Z'₂ ≃ 1 + c₁² + c₂²`).  The
    `…_eqv_witness` lemmas record these explicit evaluations (as `Q'` `eqv`, since the
    fusion sum and the explicit value share a rational but not a structural form), at
    the concrete witness.

# THE CONCEPTUAL CONCLUSION for R2(B) (FACT 3, honest)

`coeffW w 1 = 2w³` is the SU(2) heat-kernel character coefficient `2·e^{−3t}`; it
EXCEEDS the vacuum coefficient `1` for `w > 2^{−1/3}` (weak coupling, small `t`).
Hence the dominant-mode "gap = 1 − leading character coefficient" margin is a
STRONG-COUPLING formula: it goes negative at the strong/weak boundary `w ≈ 0.794`
(the intermediate-coupling "middle"), at `N = 1` AND `N = 2` (Facts 1–2), so the
zero-crossing is NOT a truncation artifact.

CONCLUSION:  the physical-gap identification CANNOT be carried by the
character-coefficient margin into the weak-coupling / continuum region.  The genuine
physical transfer-operator spectral gap at weak coupling is a DIFFERENT object than
`1 − (leading character coefficient)`, and the intermediate-coupling region is the
SAME "middle" wall that the continuum problem itself runs into.  This module does NOT
claim a physical gap; it delimits the SCOPE of the dominant-mode margin — it is a
strong-coupling object, and the middle is the genuine wall for Track B.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Every numeric fact is `decide` on a CLOSED concrete-rational proposition (`<`, `≤`,
`eqv` on `Q'`, and `Nat`/`Bool` fusion indicators) — no symbolic-`k` decide, no
`Classical.*`, no `native_decide`, no `sorry`.  `Q'` order/eqv are decidable via
`Int` cross-products, so each `decide` reduces concretely; every load-bearing
declaration is gated with `#print axioms` and depends on no axioms (or only
`propext`/`Quot.sound`).  The fusion objects (`coeffW`, `fusionProduct`,
`fusionInd`) are the genuine ones from the bond-moving construction — NOT re-defined
to fit.
-/

import YMGap.Continuum.NormExcitedDrift

namespace YMGap.Continuum.FusionMarginScope

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.VacuumStability

/-! ## Concrete coupling witnesses (closed rationals)

`wWeak = 4/5 = 0.8` sits just PAST the strong/weak boundary `2^{−1/3} ≈ 0.794`
(weak-coupling side); `wStrong = 1/6` is deep on the strong-coupling side. -/

/-- The weak-coupling witness `w = 4/5 = 0.8` (just past `2^{−1/3} ≈ 0.794`). -/
def wWeak : Q' := Q'.mkPos 4 5 (by decide)

/-- The strong-coupling witness `w = 1/6`. -/
def wStrong : Q' := Q'.mkPos 1 6 (by decide)

/-! ## FACT 1 — the raw `s = 1` character coefficient crosses the vacuum

`coeffW w 1 = 2w³`.  At `w = 4/5` it is `2·64/125 = 128/125 > 1` (weak coupling: the
`gap = 1 − coeffW·1` formula is NEGATIVE); at `w = 1/6` it is `2/216 < 1` (strong
coupling: the formula is positive).  The zero-crossing is bracketed. -/

/-- **FACT 1 (weak side).**  `coeffW (4/5) 1 = 2·(4/5)³ = 128/125 > 1`: past the
strong/weak boundary the raw excited character coefficient EXCEEDS the vacuum, so
`gap = 1 − coeffW·1 < 0`. -/
theorem raw_excited_exceeds_vacuum : (1 : Q') < coeffW wWeak 1 := by decide

/-- **FACT 1 (strong side).**  `coeffW (1/6) 1 = 2/216 < 1`: deep at strong coupling
the raw excited character coefficient is BELOW the vacuum, so `gap = 1 − coeffW·1 > 0`.
Together with `raw_excited_exceeds_vacuum`, the `coeffW·1 = 1` zero-crossing of the
margin is bracketed between `1/6` and `4/5` — it is the strong/weak boundary. -/
theorem raw_excited_below_vacuum_strong : coeffW wStrong 1 < (1 : Q') := by decide

/-! ## The N = 2 fusion selection rule (decide-checked indicators)

At truncation degree `N = 2` (`a, b ∈ {0,1,2}`) the Clebsch–Gordan indicators
`fusionInd a b s` determine which `(a,b)` pairs contribute to channel `s`. -/

/-- `s = 1` channel, surviving off-diagonal pairs `(0,1),(1,0),(1,2),(2,1)`. -/
theorem fusionInd2_s1_01 : fusionInd 0 1 1 = (1 : Q') := by decide
theorem fusionInd2_s1_10 : fusionInd 1 0 1 = (1 : Q') := by decide
theorem fusionInd2_s1_12 : fusionInd 1 2 1 = (1 : Q') := by decide
theorem fusionInd2_s1_21 : fusionInd 2 1 1 = (1 : Q') := by decide
/-- `s = 1` channel, killed pairs (diagonals and `(0,2)`/`(2,0)`). -/
theorem fusionInd2_s1_00 : fusionInd 0 0 1 = (0 : Q') := by decide
theorem fusionInd2_s1_11 : fusionInd 1 1 1 = (0 : Q') := by decide
theorem fusionInd2_s1_22 : fusionInd 2 2 1 = (0 : Q') := by decide
theorem fusionInd2_s1_02 : fusionInd 0 2 1 = (0 : Q') := by decide
theorem fusionInd2_s1_20 : fusionInd 2 0 1 = (0 : Q') := by decide

/-- `s = 0` channel, surviving diagonal pairs `(0,0),(1,1),(2,2)`. -/
theorem fusionInd2_s0_00 : fusionInd 0 0 0 = (1 : Q') := by decide
theorem fusionInd2_s0_11 : fusionInd 1 1 0 = (1 : Q') := by decide
theorem fusionInd2_s0_22 : fusionInd 2 2 0 = (1 : Q') := by decide
/-- `s = 0` channel, killed off-diagonal pairs. -/
theorem fusionInd2_s0_01 : fusionInd 0 1 0 = (0 : Q') := by decide
theorem fusionInd2_s0_02 : fusionInd 0 2 0 = (0 : Q') := by decide
theorem fusionInd2_s0_12 : fusionInd 1 2 0 = (0 : Q') := by decide

/-! ## The N = 2 selection-rule EVALUATIONS at the witness (genuine `fusionProduct 2`)

With `c₀ = coeffW w 0 = 1`, the surviving pairs give the explicit values
`E₂ ≃ 2c₁(1 + c₂)` and `Z'₂ ≃ 1 + c₁² + c₂²`.  We record these as `Q'` `eqv`
between the GENUINE `fusionProduct 2` and the explicit-coefficient form, at the
concrete witness (the fusion sum and the explicit value share a rational value but
not a structural representation, hence `eqv`, decide-checked). -/

/-- **`E₂` evaluation at the witness.**  The genuine fused excited coefficient
`fusionProduct 2 (coeffW w)(coeffW w) 1` equals (as a rational) the explicit value
`2c₁ + (c₁c₂ + c₂c₁) = 2c₁(1 + c₂)`, the sum of the four surviving cross-terms
`(0,1),(1,0),(1,2),(2,1)` with `c₀ = 1`. -/
theorem fusionExcited2_eqv_witness :
    (fusionProduct 2 (coeffW wWeak) (coeffW wWeak) 1).eqv
      ((coeffW wWeak 1 + coeffW wWeak 1)
        + (coeffW wWeak 1 * coeffW wWeak 2 + coeffW wWeak 2 * coeffW wWeak 1)) := by
  decide

/-- **`Z'₂` evaluation at the witness.**  The genuine fused partition function
`fusionProduct 2 (coeffW w)(coeffW w) 0` equals (as a rational) `1 + c₁² + c₂²`, the
sum of the three surviving diagonal terms `(0,0),(1,1),(2,2)` with `c₀ = 1`. -/
theorem fusionTrivial2_eqv_witness :
    (fusionProduct 2 (coeffW wWeak) (coeffW wWeak) 0).eqv
      ((1 + coeffW wWeak 1 * coeffW wWeak 1)
        + coeffW wWeak 2 * coeffW wWeak 2) := by
  decide

/-! ## FACT 2 — the N = 2 margin is NONPOSITIVE at the witness (NOT an N=1 artifact)

The dominant-mode margin at `N = 2` is `1 − E₂/Z'₂`; it is `≤ 0` ⟺ `Z'₂ ≤ E₂`.  At
the SAME witness `w = 4/5` past the boundary, `Z'₂ ≤ E₂` holds on the genuine
`fusionProduct 2`, so the normalized excited coefficient `E₂/Z'₂ ≥ 1` and the margin
is `≤ 0`.  The zero-crossing survives the truncation degree increase. -/

/-- **FACT 2 — the N = 2 explicit-coefficient inequality.**  At `w = 4/5`,
`1 + c₁² + c₂² ≤ 2c₁(1 + c₂)`, i.e. `Z'₂ ≤ E₂` in explicit-coefficient form
(equivalently `(1 − c₁)² + c₂(c₂ − 2c₁) ≤ 0`); `decide`-checked on the concrete
rational. -/
theorem n2_margin_nonpos_explicit :
    (1 + coeffW wWeak 1 * coeffW wWeak 1) + coeffW wWeak 2 * coeffW wWeak 2
      ≤ (coeffW wWeak 1 + coeffW wWeak 1) * (1 + coeffW wWeak 2) := by
  decide

/-- **FACT 2 — on the GENUINE `fusionProduct 2`.**  `Z'₂ ≤ E₂`, i.e.
`fusionProduct 2 (coeffW w)(coeffW w) 0 ≤ fusionProduct 2 (coeffW w)(coeffW w) 1` at
`w = 4/5`.  Hence the N = 2 normalized excited coefficient `E₂/Z'₂ ≥ 1` and the
dominant-mode margin `1 − E₂/Z'₂ ≤ 0`: the zero-crossing is NOT an N = 1 truncation
artifact.  Proved directly on the real fusion object by `decide`. -/
theorem n2_margin_nonpos_at_witness :
    fusionProduct 2 (coeffW wWeak) (coeffW wWeak) 0
      ≤ fusionProduct 2 (coeffW wWeak) (coeffW wWeak) 1 := by
  decide

/-! ## FACT 3 — the conceptual conclusion (English; see the module header)

CONFIRMED (Facts 1–2):  the character-coefficient "gap = 1 − leading coefficient"
margin's zero-crossing at `w ≈ 0.794` is the genuine STRONG/WEAK-coupling boundary
(the intermediate-coupling "middle"), present at BOTH `N = 1` and `N = 2` — NOT a
truncation artifact.  CONCLUSION:  the dominant-mode character-coefficient margin is
a STRONG-COUPLING object; it cannot be carried into the weak-coupling / continuum
region, where the genuine physical transfer-operator spectral gap is a DIFFERENT
object.  The middle is the same wall as the continuum problem.  This module delimits
the SCOPE of the margin; it does NOT claim a physical gap. -/

end YMGap.Continuum.FusionMarginScope

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionMarginScope.raw_excited_exceeds_vacuum
#print axioms YMGap.Continuum.FusionMarginScope.raw_excited_below_vacuum_strong
#print axioms YMGap.Continuum.FusionMarginScope.fusionInd2_s1_01
#print axioms YMGap.Continuum.FusionMarginScope.fusionInd2_s1_12
#print axioms YMGap.Continuum.FusionMarginScope.fusionInd2_s1_11
#print axioms YMGap.Continuum.FusionMarginScope.fusionInd2_s0_00
#print axioms YMGap.Continuum.FusionMarginScope.fusionInd2_s0_22
#print axioms YMGap.Continuum.FusionMarginScope.fusionInd2_s0_01
#print axioms YMGap.Continuum.FusionMarginScope.fusionExcited2_eqv_witness
#print axioms YMGap.Continuum.FusionMarginScope.fusionTrivial2_eqv_witness
#print axioms YMGap.Continuum.FusionMarginScope.n2_margin_nonpos_explicit
#print axioms YMGap.Continuum.FusionMarginScope.n2_margin_nonpos_at_witness
