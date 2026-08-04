/-
`FusionWeightedBoxInterlacing` — a finite-support compiler for the weighted
Clebsch-box Cauchy--Binet inequality.

# The reduction

The open box inequality is usually written with an apparently infinite mode
quantifier:

    boxSum w N s * boxSum w N (s+2) <= boxSum w N (s+1)^2.

But the truncated Clebsch box has support only through mode `2*N`.  Therefore
the second cross factor vanishes as soon as `2*N < s+2`.  This file proves the
corresponding fact directly in the explicit weighted Cauchy--Binet coordinate
`FusionCoreStepRoundB.quadDiff` and compiles a certificate on the finite
triangle

    s + 2 <= 2*N

into the existing all-mode `UniformBoxQuadCertificate`, hence into
`UniformBoxLogConcave` and every fixed-`N` `FusionConvLogConcaveCore`.

This is a strict reduction, not a renamed copy of the open core: every mode
outside the finite triangle is discharged here from the proved support
theorem `BoxSumTailGeneral.boxSum_tail`.  The exact remaining analytic content
is the weighted interlacing inequality `0 <= quadDiff w N s` only on that
finite triangle.  The indicator minors themselves have both signs; no
pointwise TP2 or MLR claim is made.

# Honest scope

The finite-triangle inequalities are not inhabited uniformly in `N` here.
They remain the heat-kernel-specific weighted interlacing/local-CLT input.
This module proves their support reduction and downstream assembly only; it
does not close `FusionConvLogConcaveCore` or any continuum frontier atom.

# Constructive contract

Mathlib-free; pure `Q'`/`Nat`.  No `Classical`, `native_decide`, `sorry`, new
axiom, or noncomputable definition.  Load-bearing declarations are axiom
gated below.
-/

import YMGap.Continuum.BoxSumTailGeneral
import YMGap.Continuum.FusionPathRowLogConcave

namespace YMGap.Continuum.FusionWeightedBoxInterlacing

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.BoxSumTailGeneral
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB

/-! ## 1. Tail modes are automatically nonnegative in Cauchy--Binet form -/

/-- **Outside-support weighted minor positivity.**  If `s+2` is above the
largest Clebsch mode `2*N`, then the second cross factor `boxSum w N (s+2)`
vanishes.  Consequently the box cross-difference is a nonnegative square,
and its explicit weighted Cauchy--Binet representative `quadDiff` is
nonnegative.

This removes every mode outside the finite triangle `s+2 <= 2*N` without any
analytic input beyond coefficient nonnegativity. -/
theorem quadDiff_nonneg_of_two_mul_lt_add_two {w : Q'}
    (hw0 : (0 : Q') ≤ w) (N s : Nat) (hs : 2 * N < s + 2) :
    (0 : Q') ≤ quadDiff w N s := by
  have hz : (boxSum w N (s + 2)).eqv 0 := boxSum_tail w N (s + 2) hs
  have hLHS : (boxSum w N s * boxSum w N (s + 2)).eqv 0 := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) ?_
    exact Q'.mul_zero_eqv _
  have hcross :
      boxSum w N s * boxSum w N (s + 2)
        ≤ boxSum w N (s + 1) * boxSum w N (s + 1) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
    exact Q'.mul_nonneg _ _ (boxSum_nonneg hw0 N (s + 1))
      (boxSum_nonneg hw0 N (s + 1))
  have hdiff : (0 : Q') ≤
      boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)) :=
    Q'.sub_nonneg_of_le hcross
  exact Q'.le_trans' _ _ _ hdiff
    (Q'.le_of_eqv (boxDiff_eq_quadDiff w N s))

/-! ## 2. Compile the finite weighted-interlacing triangle to all modes -/

/-- **Fixed-cutoff finite weighted interlacing suffices.**  At a fixed cutoff
`N`, it is enough to prove the explicit weighted Cauchy--Binet inequality on
the finite triangle `s+2 <= 2*N`.  The complementary modes are supplied by
`quadDiff_nonneg_of_two_mul_lt_add_two`.

The hypothesis is deliberately an explicit function argument rather than a
new opaque structure: it displays the exact residual and does not pretend to
inhabit it. -/
theorem quadDiff_nonneg_of_finite_interlacing {w : Q'}
    (hw0 : (0 : Q') ≤ w) (N : Nat)
    (hfinite : ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s) :
    ∀ s, (0 : Q') ≤ quadDiff w N s := by
  intro s
  by_cases hs : s + 2 ≤ 2 * N
  · exact hfinite s hs
  · exact quadDiff_nonneg_of_two_mul_lt_add_two hw0 N s (by omega)

/-- **All-cutoff compiler.**  A family of finite-triangle weighted
interlacing inequalities produces the existing uniform Cauchy--Binet
certificate.  The only remaining input is

    `forall N s, s+2 <= 2*N -> 0 <= quadDiff w N s`.

The infinitely many tail-mode inequalities of `UniformBoxQuadCertificate`
are proved here rather than assumed. -/
def uniformBoxQuadCertificate_of_finite_interlacing {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (hfinite : ∀ N s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s) :
    UniformBoxQuadCertificate w where
  strongCoupling := hstrong
  quadNonneg := fun N => quadDiff_nonneg_of_finite_interlacing hw0 N (hfinite N)

/-- The finite weighted-interlacing triangle therefore yields uniform box
log-concavity for every cutoff and mode. -/
def uniformBoxLogConcave_of_finite_interlacing {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (hfinite : ∀ N s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s) :
    UniformBoxLogConcave w :=
  uniformOfQuad
    (uniformBoxQuadCertificate_of_finite_interlacing hw0 hstrong hfinite)

/-- **Direct bridge to `FusionConvLogConcaveCore.cauchyBinet`.**  At one
cutoff, finite weighted interlacing plus the existing strong-coupling datum
inhabits the genuine fixed-`N` box core.  The `cauchyBinet` field receives all
tail modes from the support compiler above. -/
def fusionConvLogConcaveCore_of_finite_interlacing {N : Nat} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (hfinite : ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s) :
    FusionConvLogConcaveCore N w hw0 hw1 where
  strongCoupling := hstrong
  cauchyBinet := fun s => by
    have hquad : (0 : Q') ≤ quadDiff w N s :=
      quadDiff_nonneg_of_finite_interlacing hw0 N hfinite s
    have hdiff : (0 : Q') ≤
        boxSum w N (s + 1) * boxSum w N (s + 1)
          + -(boxSum w N s * boxSum w N (s + 2)) :=
      Q'.le_trans' _ _ _ hquad
        (Q'.ge_of_eqv (boxDiff_eq_quadDiff w N s))
    exact Q'.le_of_sub_nonneg hdiff

/-! ## 3. A reflected finite checker (computation-theoretic certificate) -/

/-- The executable checker for the finite weighted-interlacing triangle at
cutoff `N`.  `List.range (2*N-1)` is exactly the set of natural modes
satisfying `s+2 <= 2*N`; each rational inequality is decided by kernel
computation. -/
def finiteInterlacingCheck (w : Q') (N : Nat) : Bool :=
  (List.range (2 * N - 1)).all
    (fun s => decide ((0 : Q') ≤ quadDiff w N s))

/-- **Checker soundness.**  A successful Boolean scan supplies every
finite-triangle inequality required by
`fusionConvLogConcaveCore_of_finite_interlacing`. -/
theorem finiteInterlacingCheck_sound (w : Q') (N : Nat)
    (hcheck : finiteInterlacingCheck w N = true) :
    ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s := by
  intro s hs
  have hmem : s ∈ List.range (2 * N - 1) :=
    List.mem_range.mpr (by omega)
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck s hmem)

/-- **Checker completeness.**  Conversely, a proof of the finite triangle
makes the executable scan return `true`.  Together with soundness this is a
reflection theorem, so fixed cutoffs may be discharged by trusted kernel
evaluation rather than re-expanding the Cauchy--Binet algebra by hand. -/
theorem finiteInterlacingCheck_complete (w : Q') (N : Nat)
    (hfinite : ∀ s, s + 2 ≤ 2 * N → (0 : Q') ≤ quadDiff w N s) :
    finiteInterlacingCheck w N = true := by
  apply List.all_eq_true.mpr
  intro s hmem
  apply decide_eq_true
  exact hfinite s (by
    have hs := List.mem_range.mp hmem
    omega)

/-- **Checked fixed-cutoff core.**  A successful finite Boolean certificate,
plus the separate strong-coupling field, builds the genuine
`FusionConvLogConcaveCore N w`.  No unbounded computation occurs: the scan
contains exactly `2*N-1` candidate modes. -/
def fusionConvLogConcaveCore_of_check {N : Nat} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q'))
    (hcheck : finiteInterlacingCheck w N = true) :
    FusionConvLogConcaveCore N w hw0 hw1 :=
  fusionConvLogConcaveCore_of_finite_interlacing hw0 hw1 hstrong
    (finiteInterlacingCheck_sound w N hcheck)

/-- At cutoff zero the finite triangle is empty, so the checker succeeds
definitionally for every weight. -/
theorem finiteInterlacingCheck_zero (w : Q') :
    finiteInterlacingCheck w 0 = true := rfl

/-! ## 4. Same-parity ballot rows do not supply the weighted cross-parity step -/

/-- Three positive, ordinarily log-concave degree weights.  They are kept as
an explicit finite carrier so the obstruction below is a kernel computation,
not an informal counterexample. -/
def firstThreeDegreeWeight : Nat → Nat
  | 0 | 1 | 2 => 1
  | _ => 0

/-- The ballot transform of the first three fundamental path rows with unit
weights. -/
def firstThreeBallotMix (s : Nat) : Nat :=
  firstThreeDegreeWeight 0 * pathCount 1 0 s +
    firstThreeDegreeWeight 1 * pathCount 1 1 s +
      firstThreeDegreeWeight 2 * pathCount 1 2 s

/-- The three weights are strictly positive and log-concave on their finite
window. -/
theorem firstThreeDegreeWeight_positive_logConcave :
    0 < firstThreeDegreeWeight 0 ∧
      0 < firstThreeDegreeWeight 1 ∧
      0 < firstThreeDegreeWeight 2 ∧
      firstThreeDegreeWeight 0 * firstThreeDegreeWeight 2 ≤
        firstThreeDegreeWeight 1 * firstThreeDegreeWeight 1 := by decide

/-- The corresponding ballot mixture is `(B₀,B₁,B₂) = (2,1,1)`. -/
theorem firstThreeBallotMix_values :
    firstThreeBallotMix 0 = 2 ∧ firstThreeBallotMix 1 = 1 ∧
      firstThreeBallotMix 2 = 1 := by decide

/-- **Rigorous mixed-parity obstruction.**  Positive log-concave degree
weights and support-row log-concavity do not imply the raw neighboring-mode
inequality: this ballot mixture has `B₀*B₂ = 2 > 1 = B₁²`.

The missing input must therefore compare the even- and odd-degree weighted
mixtures themselves.  It cannot be recovered from a theorem about each
fixed-parity row in isolation. -/
theorem firstThreeBallotMix_not_mixedParity_logConcave :
    ¬ (firstThreeBallotMix 0 * firstThreeBallotMix 2 ≤
      firstThreeBallotMix 1 * firstThreeBallotMix 1) := by decide

/-! ## 5. Generic compatibility with already-proved fixed-cutoff cores -/

/-- Every already-proved fixed-cutoff core supplies the finite weighted
interlacing inequalities at that cutoff.  This is a compatibility theorem,
not the general construction: its use is to validate that the finite
triangle has exactly the intended orientation and weights. -/
theorem quadDiff_nonneg_of_core {N : Nat} {w : Q'}
    {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (core : FusionConvLogConcaveCore N w hw0 hw1) (s : Nat) :
    (0 : Q') ≤ quadDiff w N s := by
  have hdiff : (0 : Q') ≤
      boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)) :=
    Q'.sub_nonneg_of_le (core.cauchyBinet s)
  exact Q'.le_trans' _ _ _ hdiff
    (Q'.le_of_eqv (boxDiff_eq_quadDiff w N s))

/-- The existing exact `N=1` strong-coupling core validates the reflected
checker at `N=1`.  This is a regression anchor for the checker orientation;
it does not claim the general cutoff family. -/
theorem finiteInterlacingCheck_one {w : Q'}
    (hw : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (hstrong : coeffW w 1 * coeffW w 1 ≤ (3 : Q')) :
    finiteInterlacingCheck w 1 = true := by
  apply finiteInterlacingCheck_complete
  intro s _hs
  exact quadDiff_nonneg_of_core
    (fusionConvLogConcaveCore_N1 hw hw1 hstrong) s

/-! ## 6. PROVED vs. remaining input

PROVED (axiom-clean):

* `quadDiff_nonneg_of_two_mul_lt_add_two`: every Cauchy--Binet tail mode is
  nonnegative from finite Clebsch support;
* `quadDiff_nonneg_of_finite_interlacing`: a fixed finite triangle compiles
  to all modes;
* `uniformBoxQuadCertificate_of_finite_interlacing` and
  `uniformBoxLogConcave_of_finite_interlacing`: the all-cutoff finite
  triangles compile to the existing uniform certificate/core machinery;
* `fusionConvLogConcaveCore_of_finite_interlacing`: the direct fixed-cutoff
  bridge to `FusionConvLogConcaveCore.cauchyBinet`;
* `finiteInterlacingCheck` with its soundness/completeness reflection
  theorems: a fixed cutoff is a finite kernel-checkable certificate;
* `fusionConvLogConcaveCore_of_check`: a successful scan builds the genuine
  fixed-cutoff core;
* `finiteInterlacingCheck_zero` / `finiteInterlacingCheck_one`: closed
  checker anchors at the first two cutoffs;
* `firstThreeBallotMix_not_mixedParity_logConcave`: an exact counterexample
  showing that positive log-concave degree weights plus support-row ballot
  log-concavity do not supply the mixed-parity inequality;
* `quadDiff_nonneg_of_core`: compatibility with existing small-cutoff cores.

REMAINING (explicit argument, not inhabited here):

* `forall N s, s+2 <= 2*N -> 0 <= quadDiff w N s`, the weighted
  cross-parity box interlacing on the finite support triangle.  This is
  strictly narrower than the old all-mode field: the complementary infinite
  tail is now proved.  It is still the heat-kernel local-CLT content, not an
  indicator-only TP2 fact.
-/

end YMGap.Continuum.FusionWeightedBoxInterlacing

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.quadDiff_nonneg_of_two_mul_lt_add_two
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.quadDiff_nonneg_of_finite_interlacing
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.uniformBoxQuadCertificate_of_finite_interlacing
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.uniformBoxLogConcave_of_finite_interlacing
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.fusionConvLogConcaveCore_of_finite_interlacing
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.finiteInterlacingCheck_sound
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.finiteInterlacingCheck_complete
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.fusionConvLogConcaveCore_of_check
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.finiteInterlacingCheck_zero
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.firstThreeDegreeWeight_positive_logConcave
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.firstThreeBallotMix_values
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.firstThreeBallotMix_not_mixedParity_logConcave
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.quadDiff_nonneg_of_core
#print axioms YMGap.Continuum.FusionWeightedBoxInterlacing.finiteInterlacingCheck_one
