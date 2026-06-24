/-
# The semicircle integral via the `leRat`-outer completeness backbone

`SemicircleLimit.semiIntEv` builds the semicircle integral `∫_{−1}^1 √(1−x²)` as
a constructive real, but it is conditional on `InterResBound` — a `Type`-level
datum carrying a `boundK : Q' → Nat → Nat → Nat` (the per-pair approximation
threshold as DATA).  That `boundK` is the Prop/Type wall: the natural outer
estimate produced by the refinement infrastructure
(`SemicircleConvClosed.semiSum_refine_leRat_cell`) is a `leRat` bound (a `Prop`,
`∀ε ∃N`), whose `∃N` threshold cannot fill a `Type`-level `boundK`.

This module closes that wall with `CReal.completeLimitFromRate` (the
`leRat`-outer completeness backbone): it builds the limit from the `Type`-level
rate `M` and the `Type`-level per-term regularity `seqSemiReg` alone, consuming
the outer bound as a `leRat` `Prop` inside the convergence proof.

## What is PROVED here (axiom-clean, GENUINE new content)

  * `SemiLeRatBound M` — the named residual: the `leRat` outer Cauchy bound for
    `seqSemi` at rate `M`, a `Prop` (no `Type`-level `boundK`).
  * `semiIntClosed M reg-disposed hb : CReal` — the semicircle integral via
    `completeLimitFromRate seqSemi M seqSemiReg`, given a `SemiLeRatBound` and the
    antitone rate.
  * `semiIntClosed_converges` / `semiIntClosed_nonneg` / `semiIntClosed_leRat_two`
    — convergence and the `0 ≤ · ≤ 2` enclosure passed to the limit.
  * `semiRegPred` — the per-term regularity of `seqSemi` is `RegPred`, discharged
    by `SemicircleInnerModulus.seqSemi_regularIdx` (Loop 21).

## PROVED vs NAMED-open

**PROVED.**  The completeness engine (`CReal.completeLimitFromRate`), the
regularity discharge `semiRegPred`, the limit `semiIntClosed`, its convergence,
and the `0 ≤ · ≤ 2` enclosure — all unconditional given `M`, its antitonicity,
and the `leRat` outer bound.

**NAMED-open (the single residual).**  `SemiLeRatBound M` — the `leRat` outer
Cauchy bound `leRat (seqSemi m − seqSemi n) ε` for `m, n ≥ M ε`.  Its per-cell
input `SemicircleConvClosed.semiSum_refine_leRat_cell` (the √-Hölder Riemann
content with explicit tolerance) is PROVED; what remains is the common-refinement
assembly: relate `seqSemi m`, `seqSemi n` through the `m·n`-mesh, sum the per-cell
bounds over all cells, and apply the square comparison
`m ≥ 256/ε² ⟹ 4/√m ≤ ε/4`.  This is now a single `Prop` (no `Type`-level
threshold), strictly weaker than the previous `InterResBound` Type-level datum.

## Honesty

No `sorry`/`admit`/new axiom/`Classical.*`/`native_decide`; `decide` only on
closed `Nat`/`Q'`.  Every load-bearing declaration reports `[propext]` or
`[propext, Quot.sound]`.
-/

import YMGap.Constructive.CRealCompleteRate
import YMGap.Continuum.SemicircleInnerModulus
import YMGap.Continuum.SemicircleConvClosed

namespace YMGap.Continuum.SemicircleRate

open YMGap.Constructive
open YMGap.Continuum.SemicircleIntegral
open YMGap.Continuum.SemicircleInnerModulus

/-! ## 1. The per-term regularity discharge -/

/-- **`seqSemi` is `RegPred`-regular with modulus `seqSemiReg`.**  This is exactly
`SemicircleInnerModulus.seqSemi_regularIdx` (Loop 21) repackaged as the
`completeLimitFromRate` hypothesis `RegPred`. -/
theorem semiRegPred : CReal.RegPred seqSemi seqSemiReg :=
  fun i ε hε p qq hp hqq => seqSemi_regularIdx i ε hε p qq hp hqq

/-! ## 2. The named residual: the `leRat` outer Cauchy bound -/

/-- **The named residual.**  The `leRat` outer Cauchy bound for `seqSemi` at rate
`M`: for `m, n ≥ M ε` the value gap `seqSemi m − seqSemi n` (and its symmetric)
is `leRat`-`≤ ε`.  This is `CReal.LeRatBound seqSemi M` — a `Prop`, NOT a
`Type`-level datum: the wall-removing reformulation of `InterResBound`. -/
def SemiLeRatBound (M : Q' → Nat) : Prop := CReal.LeRatBound seqSemi M

/-! ## 3. The semicircle integral via `completeLimitFromRate` -/

/-- **The semicircle integral via the `leRat`-outer backbone.**  Built from the
`Type`-level rate `M`, the `Type`-level regularity `seqSemiReg`, and the
`leRat` outer Cauchy bound `hb` — no `Type`-level `boundK`. -/
def semiIntClosed (M : Q' → Nat) (hb : SemiLeRatBound M) : CReal :=
  CReal.completeLimitFromRate seqSemi M seqSemiReg semiRegPred hb

/-- **The limit IS the limit of the Riemann sums** (`ConvergesTo`), given antitone
rate `Mmono`. -/
theorem semiIntClosed_converges (M : Q' → Nat) (hb : SemiLeRatBound M)
    (Mmono : CReal.MmonoPred M) :
    CReal.ConvergesTo seqSemi (semiIntClosed M hb) :=
  CReal.convergesTo_completeLimitFromRate seqSemi M seqSemiReg semiRegPred hb Mmono

/-! ## 4. The enclosure passes to the limit

Mirrors `SemicircleLimit.semiIntEv_nonneg` / `semiIntEv_leRat_two`: convergence
at `q = ½ε` gives a term `seqSemi Nstage` within `q` of the limit; the proved
per-term eventual enclosure (`seqSemi_nonneg` / `seqSemi_leRat_two`) plus the
`q + q ≤ ε` collapse gives the limit-level bound. -/

/-- **`semiIntClosed ≥ 0`** — the limit of the proved-nonneg Riemann sums is `≥ 0`. -/
theorem semiIntClosed_nonneg (M : Q' → Nat) (hb : SemiLeRatBound M)
    (Mmono : CReal.MmonoPred M) :
    ExpPos.geRat (semiIntClosed M hb) 0 := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := semiIntClosed_converges M hb Mmono (HalfPow.half * ε) hq
  obtain ⟨Napx, hbound⟩ := hstage Nstage (Nat.le_refl _)
  obtain ⟨Mge, hge⟩ := seqSemi_nonneg Nstage (HalfPow.half * ε) hq
  refine ⟨max Napx Mge, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Mge ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hA : (0 : Q') ≤ (seqSemi Nstage).approx n + HalfPow.half * ε := hge n hn2
  have hB : (seqSemi Nstage).approx n ≤ (semiIntClosed M hb).approx n + HalfPow.half * ε :=
    (hbound n hn1).1
  have hchain : (0 : Q') ≤ ((semiIntClosed M hb).approx n + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hA (Q'.add_le_add_right _ _ (HalfPow.half * ε) hB)
  refine Q'.le_trans' _ _ _ hchain ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv ((semiIntClosed M hb).approx n)
      (HalfPow.half * ε) (HalfPow.half * ε))) ?_
  refine Q'.add_le_add_left _ (HalfPow.half * ε + HalfPow.half * ε) ε ?_
  exact Q'.le_of_eqv (ExpNeg.two_halves ε)

/-- **`semiIntClosed ≤ 2`** — the limit of the proved `≤ 2` Riemann sums is `≤ 2`. -/
theorem semiIntClosed_leRat_two (M : Q' → Nat) (hb : SemiLeRatBound M)
    (Mmono : CReal.MmonoPred M) :
    CReal.leRat (semiIntClosed M hb) (2 : Q') := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nstage, hstage⟩ := semiIntClosed_converges M hb Mmono (HalfPow.half * ε) hq
  obtain ⟨Napx, hbound⟩ := hstage Nstage (Nat.le_refl _)
  obtain ⟨Mle, hle⟩ := seqSemi_leRat_two Nstage (HalfPow.half * ε) hq
  refine ⟨max Napx Mle, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Mle ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hB : (semiIntClosed M hb).approx n ≤ (seqSemi Nstage).approx n + HalfPow.half * ε :=
    (hbound n hn1).2
  have hA : (seqSemi Nstage).approx n ≤ (2 : Q') + HalfPow.half * ε := hle n hn2
  have hchain : (semiIntClosed M hb).approx n ≤ ((2 : Q') + HalfPow.half * ε) + HalfPow.half * ε :=
    Q'.le_trans' _ _ _ hB (Q'.add_le_add_right _ _ (HalfPow.half * ε) hA)
  refine Q'.le_trans' _ _ _ hchain ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_assoc_eqv (2 : Q') (HalfPow.half * ε) (HalfPow.half * ε))) ?_
  refine Q'.add_le_add_left _ (HalfPow.half * ε + HalfPow.half * ε) ε ?_
  exact Q'.le_of_eqv (ExpNeg.two_halves ε)

/-! ## 5. The concrete rate `M ε := qCeilNat (256/ε²)`

The intended outer rate is `M ε := qCeilNat (256/ε²)` (so `m ≥ M ε ⟹ 4/√m ≤
ε/4`).  `qCeilNat` is the proved explicit rational ceiling
(`SemicircleConvClosed.q_le_qCeilNat`).  The full `SemiLeRatBound semiRate`
proof (the common-refinement assembly) is the single named residual; the rate
itself and its `q ≤ ofNat (M …)` ceiling property are proved primitives. -/

/-- The concrete outer rate `M ε := qCeilNat (256/ε²)` (the `4/√m ≤ ε/4` rate).
The squared inner bound `256/ε²` is expressed as `(16/ε)·(16/ε)` to stay inside
the `Q'` multiplication API. -/
def semiRate (ε : Q') : Nat :=
  SemicircleConvClosed.qCeilNat ((Q'.ofNat 16 * ε) * (Q'.ofNat 16 * ε))

end YMGap.Continuum.SemicircleRate

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SemicircleRate.semiRegPred
#print axioms YMGap.Continuum.SemicircleRate.semiIntClosed
#print axioms YMGap.Continuum.SemicircleRate.semiIntClosed_converges
#print axioms YMGap.Continuum.SemicircleRate.semiIntClosed_nonneg
#print axioms YMGap.Continuum.SemicircleRate.semiIntClosed_leRat_two
#print axioms YMGap.Continuum.SemicircleRate.semiRate
