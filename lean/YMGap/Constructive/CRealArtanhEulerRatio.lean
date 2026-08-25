/-
# The universal artanh-ratio Euler inverse frontier

The direct rational logarithm is represented through the coordinate

    y = (m - 1) / (m + 1),      m = (1 + y) / (1 - y).

This module removes the rational mantissa `m`, its logarithm wrapper, and all
Wilson/reconstruction data from the remaining exponential evaluation.  It
packages the one universal analytic statement still required: for a negative
`y` in the direct artanh window, the negative exponential of four times the
artanh partial sum converges to the square of the Mobius ratio
`(1+y)/(1-y)`.

The compiler is deliberately not inhabited here.  The exact inverse
calculation is the next analytic frontier.  What is proved here is the complete
rational algebra needed to compile that future family-independent witness back
to any direct-window rational logarithm.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.CRealExpRationalStreamContinuity
import YMGap.Constructive.CRealLogOddness
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Constructive.CRealArtanhEulerRatio

set_option autoImplicit false

open YMGap.Constructive

/-- For a strictly negative artanh coordinate, the denominator `1-y` of the
inverse Mobius transform is strictly positive. -/
theorem one_sub_pos_of_neg (y : Q') (hy : y < (0 : Q')) :
    (0 : Q') < (1 : Q') + -y :=
  Q'.pos_add_nonneg (by decide)
    (Q'.nonneg_neg_of_nonpos (Q'.le_of_lt hy))

/-- The inverse Mobius transform of the artanh coordinate. -/
def artanhRatio (y : Q') (hy : y < (0 : Q')) : Q' :=
  ((1 : Q') + y) * Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy)

/-- Four times the negative artanh partial sum, written in the same literal
factorization used by the direct logarithm-square exponent. -/
def negativeArtanhSquareExponent (y : Q') (stage : Nat) : Q' :=
  (-(CRealLog.partialSum y stage + CRealLog.partialSum y stage)) *
    ((1 : Q') + 1)

/-- The universal artanh-square exponent is pointwise nonnegative on the
negative branch. -/
theorem negativeArtanhSquareExponent_nonnegative
    (y : Q') (hy : y < (0 : Q')) (stage : Nat) :
    (0 : Q') <= negativeArtanhSquareExponent y stage := by
  have hyNonpositive : y <= (0 : Q') := Q'.le_of_lt hy
  have hpartial : CRealLog.partialSum y stage <= (0 : Q') := by
    have hanti := CRealLog.partialSum_anti_of_nonpos y hyNonpositive 0 stage
    rw [CRealLog.partialSum_zero, Nat.zero_add] at hanti
    exact hanti
  have hsum : CRealLog.partialSum y stage + CRealLog.partialSum y stage <=
      (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.add_le_add hpartial hpartial)
      (Q'.le_of_eqv (by decide : ((0 : Q') + 0).eqv 0))
  exact Q'.mul_nonneg _ _ (Q'.nonneg_neg_of_nonpos hsum) (by decide)

/-- The family-independent analytic evaluation at one negative artanh
coordinate. -/
structure NegativeWindowArtanhSquareEulerEvaluation
    (y : Q') (hy : y < (0 : Q'))
    (_hyb : Q'.abs y <= CRealLog.recipOdd 1) : Type 1 where
  exponentialConverges : CReal.ConvergesTo
    (fun stage => ExpNeg.expNeg
      (negativeArtanhSquareExponent y stage)
      (negativeArtanhSquareExponent_nonnegative y hy stage))
    (CReal.ofQ' (artanhRatio y hy * artanhRatio y hy))

/-- One uniform analytic compiler for the entire negative direct artanh
window.  It contains no logarithm, mantissa, Wilson datum, cutoff family, or
continuum structure. -/
structure NegativeWindowArtanhSquareEulerCompiler : Type 2 where
  evaluate :
    (y : Q') -> (hy : y < (0 : Q')) ->
    (hyb : Q'.abs y <= CRealLog.recipOdd 1) ->
    NegativeWindowArtanhSquareEulerEvaluation y hy hyb

/-! ## A smaller positive-window, one-copy frontier -/

/-- Strict negativity becomes strict positivity after rational negation. -/
theorem neg_pos_of_strict_neg (y : Q') (hy : y < (0 : Q')) :
    (0 : Q') < -y := by
  have hynum : y.num < 0 := by
    have hcross : y.num * (1 : Int) <
        (0 : Int) * (y.den : Int) := hy
    omega
  show (0 : Int) * ((-y).den : Int) < (-y).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  change (0 : Int) < (-y.num)
  omega

/-- Twice the positive artanh partial sum.  This is one copy of the direct
logarithmic exponent, before the square used by the Wilson graph norm. -/
def positiveArtanhExponent (z : Q') (stage : Nat) : Q' :=
  CRealLog.partialSum z stage + CRealLog.partialSum z stage

/-- The one-copy positive artanh exponent is pointwise nonnegative. -/
theorem positiveArtanhExponent_nonnegative
    (z : Q') (hz : (0 : Q') < z) (stage : Nat) :
    (0 : Q') <= positiveArtanhExponent z stage := by
  have hpartial : (0 : Q') <= CRealLog.partialSum z stage := by
    have hmono := CRealLog.partialSum_mono_of_nonneg
      z (Q'.le_of_lt hz) 0 stage
    rw [CRealLog.partialSum_zero, Nat.zero_add] at hmono
    exact hmono
  exact Q'.zero_le_add _ _ hpartial hpartial

/-- On the direct artanh window the one-copy exponent is uniformly at most
one.  The proof sums the literal positive artanh series into the geometric
half bound; no completed logarithm or inverse identity is used. -/
theorem positiveArtanhExponent_le_one
    (z : Q') (hzb : Q'.abs z <= CRealLog.recipOdd 1) (stage : Nat) :
    positiveArtanhExponent z stage <= (1 : Q') := by
  have htermZeroEqv : (CRealLog.termAbs z 0).eqv (Q'.abs z) := by
    show ((Q'.abs z) ^ (2 * 0 + 1) * CRealLog.recipOdd 0).eqv
      (Q'.abs z)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ (Q'.abs z) (CRealLog.recipOdd 0) ?_) ?_
    · show (Q'.abs z * (Q'.abs z) ^ 0).eqv (Q'.abs z)
      exact Q'.mul_one_eqv (Q'.abs z)
    · refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.abs z) _ 1 (by decide)) ?_
      exact Q'.mul_one_eqv (Q'.abs z)
  have hterm : CRealLog.termAbs z 0 <=
      Q'.mkPos 8 9 (by decide) * HalfPow.half :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv htermZeroEqv)
      (Q'.le_trans' _ _ _ hzb (by decide))
  have hrec : CRealLog.termAbs z 0 +
      CRealLog.oneNinth * HalfPow.half <= HalfPow.half :=
    CRealLog.recurrence_from_term z 0 HalfPow.half hterm
  have hblock : CRealLog.blockAbs z 0 stage <= HalfPow.half :=
    CRealLog.blockAbs_le z hzb HalfPow.half 0 HalfPow.half_nonneg hrec stage
  have hpartial : CRealLog.partialSum z stage <= HalfPow.half := by
    have hupper := CRealLog.block_upper z 0 stage
    rw [Nat.zero_add, CRealLog.partialSum_zero] at hupper
    exact Q'.le_trans' _ _ _ hupper
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left 0 (CRealLog.blockAbs z 0 stage)
          HalfPow.half hblock)
        (Q'.le_of_eqv (QPoly.q_zero_add_eqv HalfPow.half)))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add hpartial hpartial)
    (Q'.le_of_eqv (ExpNeg.two_halves 1))

/-- The explicit outer modulus for the doubled positive-artanh exponent. -/
def positiveArtanhExponentModulus (epsilon : Q') : Nat :=
  CRealLog.Martanh (HalfPow.half * epsilon)

/-- The doubled artanh exponent has an explicit Type-level Cauchy modulus.
This exposes the quantitative outer-stage stability needed by the finite
cleared-defect proof rather than hiding it in a `CReal.cauchy` existential. -/
theorem positiveArtanhExponent_cauchy_explicit
    (z : Q') (hzb : Q'.abs z <= CRealLog.recipOdd 1)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    forall m n,
      positiveArtanhExponentModulus epsilon <= m ->
      positiveArtanhExponentModulus epsilon <= n ->
      positiveArtanhExponent z m <= positiveArtanhExponent z n + epsilon /\
        positiveArtanhExponent z n <=
          positiveArtanhExponent z m + epsilon := by
  intro m n hm hn
  let q : Q' := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  have hpartial := CRealLog.artanh_cauchy_explicit z hzb q hq m n hm hn
  have hbudget : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
  have close : forall a b : Q', a <= b + q ->
      a + a <= (b + b) + epsilon := by
    intro a b hab
    have hadd : a + a <= (b + q) + (b + q) :=
      Q'.add_le_add hab hab
    refine Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ ((b + b) + (q + q)) _
      (Q'.add_swap_inner b q b q) ?_
    exact Q'.add_eqv_congr_left (b + b) _ _ hbudget
  exact
    ⟨close (CRealLog.partialSum z m) (CRealLog.partialSum z n) hpartial.1,
      close (CRealLog.partialSum z n) (CRealLog.partialSum z m) hpartial.2⟩

/-- Uniform finite-series response to the outer artanh stage.  Once both
outer stages are past the explicit exponent modulus, every exponential
partial sum, at every inner index, differs by at most three times the outer
tolerance. -/
theorem positiveArtanhExpPartialSum_cauchy_explicit
    (z : Q') (hz : (0 : Q') < z)
    (hzb : Q'.abs z <= CRealLog.recipOdd 1)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (m n : Nat)
    (hm : positiveArtanhExponentModulus epsilon <= m)
    (hn : positiveArtanhExponentModulus epsilon <= n)
    (inner : Nat) :
    Q'.abs
        (ExpNeg.partialSum (positiveArtanhExponent z m) inner +
          -(ExpNeg.partialSum (positiveArtanhExponent z n) inner)) <=
      epsilon * Q'.ofNat 3 := by
  have hclose := positiveArtanhExponent_cauchy_explicit
    z hzb epsilon hepsilon m n hm hn
  have hlipschitz := ExpNeg.partialSumDiff_le
    (positiveArtanhExponent_nonnegative z hz m)
    (positiveArtanhExponent_le_one z hzb m)
    (positiveArtanhExponent_nonnegative z hz n)
    (positiveArtanhExponent_le_one z hzb n)
    (Q'.le_of_lt hepsilon) hclose.1 hclose.2 inner
  exact Q'.le_trans' _ _ _ hlipschitz
    (Q'.mul_le_mul_of_nonneg_left
      (ExpNeg.sumBound inner) (Q'.ofNat 3) epsilon
      (ExpNeg.sumBound_le_three inner) (Q'.le_of_lt hepsilon))

/-- The denominator `1+z` of the positive-window decay ratio is positive. -/
theorem one_add_pos_of_pos (z : Q') (hz : (0 : Q') < z) :
    (0 : Q') < (1 : Q') + z :=
  Q'.add_pos (by decide) hz

/-- The rational decay ratio paired with `2*artanh z`:
`(1-z)/(1+z)`. -/
def positiveArtanhDecayRatio (z : Q') (hz : (0 : Q') < z) : Q' :=
  ((1 : Q') + -z) *
    Q'.recipPos ((1 : Q') + z) (one_add_pos_of_pos z hz)

/-- The smaller family-independent evaluation: `exp(-2*artanh z)` converges
to `(1-z)/(1+z)` on the positive direct window. -/
structure PositiveWindowArtanhEulerEvaluation
    (z : Q') (hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  exponentialConverges : CReal.ConvergesTo
    (fun stage => ExpNeg.expNeg
      (positiveArtanhExponent z stage)
      (positiveArtanhExponent_nonnegative z hz stage))
    (CReal.ofQ' (positiveArtanhDecayRatio z hz))

/-- One uniform inverse compiler on the positive artanh window.  This is the
smallest analytic compiler in the current scalar path: one sign branch, one
copy of the exponent, and an unsquared rational target. -/
structure PositiveWindowArtanhEulerCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerEvaluation z hz hzb

/-- The computed inner exponential-series cutoff used by the pivot
certificate.  The outer stage controls the artanh partial sum; at that fixed
stage, `ExpNeg.Mexp` controls every later exponential approximation. -/
def positiveArtanhEulerPivot
    (z : Q') (stage : Nat) (epsilon : Q') : Nat :=
  ExpNeg.Mexp (positiveArtanhExponent z stage)
    (HalfPow.half * epsilon)

/-- Moving computed exponential pivots are quantitatively stable in the
outer artanh stage.  The comparison passes through the maximum of the two
inner cutoffs: two explicit exponential Cauchy errors surround one uniform
finite-series response error. -/
theorem positiveArtanhEulerMovingPivot_cauchy_explicit
    (z : Q') (hz : (0 : Q') < z)
    (hzb : Q'.abs z <= CRealLog.recipOdd 1)
    (innerTolerance outerTolerance : Q')
    (hinner : (0 : Q') < innerTolerance)
    (houter : (0 : Q') < outerTolerance)
    (m n : Nat)
    (hm : positiveArtanhExponentModulus outerTolerance <= m)
    (hn : positiveArtanhExponentModulus outerTolerance <= n) :
    let exponentM := positiveArtanhExponent z m
    let exponentN := positiveArtanhExponent z n
    let pivotM := ExpNeg.Mexp exponentM innerTolerance
    let pivotN := ExpNeg.Mexp exponentN innerTolerance
    let valueM := ExpNeg.partialSum exponentM pivotM
    let valueN := ExpNeg.partialSum exponentN pivotN
    let response := outerTolerance * Q'.ofNat 3
    valueM <= ((valueN + innerTolerance) + response) + innerTolerance /\
      valueN <= ((valueM + innerTolerance) + response) + innerTolerance := by
  let exponentM : Q' := positiveArtanhExponent z m
  let exponentN : Q' := positiveArtanhExponent z n
  let pivotM : Nat := ExpNeg.Mexp exponentM innerTolerance
  let pivotN : Nat := ExpNeg.Mexp exponentN innerTolerance
  let common : Nat := max pivotM pivotN
  let valueM : Q' := ExpNeg.partialSum exponentM pivotM
  let valueN : Q' := ExpNeg.partialSum exponentN pivotN
  let commonM : Q' := ExpNeg.partialSum exponentM common
  let commonN : Q' := ExpNeg.partialSum exponentN common
  let response : Q' := outerTolerance * Q'.ofNat 3
  have hcauchyM := ExpNeg.expNeg_cauchy_explicit exponentM
    (positiveArtanhExponent_nonnegative z hz m)
    innerTolerance hinner pivotM common
    (Nat.le_refl pivotM) (Nat.le_max_left pivotM pivotN)
  have hcauchyN := ExpNeg.expNeg_cauchy_explicit exponentN
    (positiveArtanhExponent_nonnegative z hz n)
    innerTolerance hinner common pivotN
    (Nat.le_max_right pivotM pivotN) (Nat.le_refl pivotN)
  have hresponseMN := positiveArtanhExpPartialSum_cauchy_explicit
    z hz hzb outerTolerance houter m n hm hn common
  have hresponseNM := positiveArtanhExpPartialSum_cauchy_explicit
    z hz hzb outerTolerance houter n m hn hm common
  have subUpper : forall a b bound : Q',
      Q'.abs (a + -b) <= bound -> a <= b + bound := by
    intro a b bound habs
    have hsub : a + -b <= bound :=
      Q'.le_trans' _ _ _ (Q'.le_abs_self (a + -b)) habs
    have hshift : (a + -b) + b <= bound + b :=
      Q'.add_le_add_right _ _ b hsub
    have hmain : a <= bound + b := by
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hshift
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left a _ _ (Q'.neg_add_self_eqv b)) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' a)
    exact Q'.le_trans' _ _ _ hmain
      (Q'.le_of_eqv (Q'.add_comm_eqv bound b))
  have hcommonMN : commonM <= commonN + response :=
    subUpper commonM commonN response hresponseMN
  have hcommonNM : commonN <= commonM + response :=
    subUpper commonN commonM response hresponseNM
  have forward : valueM <=
      ((valueN + innerTolerance) + response) + innerTolerance :=
    Q'.le_trans' _ _ _ hcauchyM.1
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ innerTolerance hcommonMN)
        (Q'.add_le_add_right _ _ innerTolerance
          (Q'.add_le_add_right _ _ response hcauchyN.1)))
  have backward : valueN <=
      ((valueM + innerTolerance) + response) + innerTolerance :=
    Q'.le_trans' _ _ _ hcauchyN.2
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ innerTolerance hcommonNM)
        (Q'.add_le_add_right _ _ innerTolerance
          (Q'.add_le_add_right _ _ response hcauchyM.2)))
  exact ⟨forward, backward⟩

/-- Inner exponential tolerance used by the single-anchor compiler: one
eighth of the requested final tolerance. -/
def positiveArtanhAnchorInnerTolerance (epsilon : Q') : Q' :=
  HalfPow.half * (HalfPow.half * (HalfPow.half * epsilon))

/-- Outer exponent tolerance used by the single-anchor compiler: one
twenty-fourth of the requested tolerance.  The finite exponential response
constant three turns this exactly into the inner one-eighth budget. -/
def positiveArtanhAnchorOuterTolerance (epsilon : Q') : Q' :=
  Q'.mkPos 1 24 (by decide) * epsilon

theorem positiveArtanhAnchorInnerTolerance_pos
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < positiveArtanhAnchorInnerTolerance epsilon :=
  ExpNeg.half_mul_pos _
    (ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon hepsilon))

theorem positiveArtanhAnchorOuterTolerance_pos
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < positiveArtanhAnchorOuterTolerance epsilon :=
  Q'.mul_pos (by decide) hepsilon

/-- The outer-stage response budget is exactly the inner exponential budget:
`(epsilon/24) * 3 = epsilon/8`. -/
theorem positiveArtanhAnchor_response_eqv_inner (epsilon : Q') :
    (positiveArtanhAnchorOuterTolerance epsilon * Q'.ofNat 3).eqv
      (positiveArtanhAnchorInnerTolerance epsilon) := by
  unfold positiveArtanhAnchorOuterTolerance positiveArtanhAnchorInnerTolerance
  refine Q'.eqv_trans _
    (Q'.mkPos 1 24 (by decide) *
      (epsilon * Q'.ofNat 3)) _
    (Q'.mul_assoc_eqv (Q'.mkPos 1 24 (by decide)) epsilon
      (Q'.ofNat 3)) ?_
  refine Q'.eqv_trans _
    (Q'.mkPos 1 24 (by decide) *
      (Q'.ofNat 3 * epsilon)) _
    (Q'.mul_eqv_congr_left (Q'.mkPos 1 24 (by decide)) _ _
      (Q'.mul_comm_eqv epsilon (Q'.ofNat 3))) ?_
  refine Q'.eqv_trans _
    ((Q'.mkPos 1 24 (by decide) * Q'.ofNat 3) * epsilon) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.mkPos 1 24 (by decide))
        (Q'.ofNat 3) epsilon)) ?_
  refine Q'.eqv_trans _
    ((HalfPow.half * (HalfPow.half * HalfPow.half)) * epsilon) _
    (Q'.mul_eqv_congr_right _ _ epsilon (by decide)) ?_
  refine Q'.eqv_trans _
    (HalfPow.half *
      ((HalfPow.half * HalfPow.half) * epsilon)) _
    (Q'.mul_assoc_eqv HalfPow.half
      (HalfPow.half * HalfPow.half) epsilon) ?_
  exact Q'.mul_eqv_congr_left HalfPow.half _ _
    (Q'.mul_assoc_eqv HalfPow.half HalfPow.half epsilon)

/-- Five one-eighth error contributions fit inside the requested tolerance.
This is the complete budget used by the single-anchor evaluation compiler. -/
theorem positiveArtanhAnchor_five_budget_le (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    let t := positiveArtanhAnchorInnerTolerance epsilon
    let response :=
      positiveArtanhAnchorOuterTolerance epsilon * Q'.ofNat 3
    t + (t + (response + (t + t))) <= epsilon := by
  let t : Q' := positiveArtanhAnchorInnerTolerance epsilon
  let response : Q' :=
    positiveArtanhAnchorOuterTolerance epsilon * Q'.ofNat 3
  let four : Q' := (t + t) + (t + t)
  have ht0 : (0 : Q') <= t :=
    Q'.le_of_lt (positiveArtanhAnchorInnerTolerance_pos epsilon hepsilon)
  have hresponse : response.eqv t :=
    positiveArtanhAnchor_response_eqv_inner epsilon
  have htwo : (t + t).eqv
      (HalfPow.half * (HalfPow.half * epsilon)) :=
    ExpNeg.two_halves (HalfPow.half * (HalfPow.half * epsilon))
  have hfour : four.eqv (HalfPow.half * epsilon) := by
    refine Q'.eqv_trans _
      ((HalfPow.half * (HalfPow.half * epsilon)) +
        (HalfPow.half * (HalfPow.half * epsilon))) _
      (Q'.add_eqv_congr' htwo htwo) ?_
    exact ExpNeg.two_halves (HalfPow.half * epsilon)
  have hfourFour : (four + four).eqv epsilon := by
    refine Q'.eqv_trans _
      ((HalfPow.half * epsilon) + (HalfPow.half * epsilon)) _
      (Q'.add_eqv_congr' hfour hfour) ?_
    exact ExpNeg.two_halves epsilon
  have htFour : t <= four := by
    have htTwo : t <= t + t := Q'.add_le_self_of_nonneg t t ht0
    have htwoFour : t + t <= four :=
      Q'.add_le_self_of_nonneg (t + t) (t + t)
        (Q'.zero_le_add t t ht0 ht0)
    exact Q'.le_trans' _ _ _ htTwo htwoFour
  have hrest : (t + (response + (t + t))).eqv four := by
    refine Q'.eqv_trans _ ((t + response) + (t + t)) _
      (Q'.eqv_symm (Q'.add_assoc_eqv t response (t + t))) ?_
    exact Q'.add_eqv_congr_right _ _ (t + t)
      (Q'.add_eqv_congr_left t _ _ hresponse)
  have hfive : t + (t + (response + (t + t))) <= t + four :=
    Q'.le_of_eqv (Q'.add_eqv_congr_left t _ _ hrest)
  exact Q'.le_trans' _ _ _ hfive
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_right t four four htFour)
      (Q'.le_of_eqv hfourFour))

/-- The denominator-cleared defect at a finite positive-artanh/exponential
approximation.  Its vanishing equation is

`(1+z) * exponentialApproximation = 1-z`,

so the remaining analytic estimate can be stated without a reciprocal. -/
def positiveArtanhEulerClearedDefect
    (z : Q') (stage inner : Nat) : Q' :=
  (((1 : Q') + z) *
      ExpNeg.partialSum (positiveArtanhExponent z stage) inner) +
    -((1 : Q') + -z)

/-- A denominator-cleared relative-error bound implies the desired
two-sided ratio comparison.  The proof uses positive rational division only
after the open estimate has already been supplied in cross-multiplied form. -/
theorem close_to_positiveArtanhDecayRatio_of_clearedDefect
    (z : Q') (hz : (0 : Q') < z) (value q : Q')
    (hdefect :
      Q'.abs ((((1 : Q') + z) * value) + -((1 : Q') + -z)) <=
        q * ((1 : Q') + z)) :
    value <= positiveArtanhDecayRatio z hz + q /\
      positiveArtanhDecayRatio z hz <= value + q := by
  let denominator : Q' := (1 : Q') + z
  let numerator : Q' := (1 : Q') + -z
  let budget : Q' := q * denominator
  let defect : Q' := denominator * value + -numerator
  have hdenominator : (0 : Q') < denominator := one_add_pos_of_pos z hz
  have hdefect' : Q'.abs defect <= budget := hdefect
  have hupper : defect <= budget :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self defect) hdefect'
  have hlower : -budget <= defect :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hdefect')
      (ExpNeg.neg_abs_le defect)
  have hcancel : (defect + numerator).eqv (denominator * value) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (denominator * value) (-numerator) numerator) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (denominator * value) _ _
        (Q'.neg_add_self_eqv numerator)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' (denominator * value))
  have hvalueMul : value * denominator <= numerator + budget := by
    have hstep : defect + numerator <= budget + numerator :=
      Q'.add_le_add_right _ _ numerator hupper
    have hdenMul : denominator * value <= budget + numerator :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hstep
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv value denominator))
      (Q'.le_trans' _ _ _ hdenMul
        (Q'.le_of_eqv (Q'.add_comm_eqv budget numerator)))
  have hupperDiv : value <=
      Q'.divPos (numerator + budget) denominator hdenominator :=
    Q'.le_divPos_of_mul_le (numerator + budget) denominator
      hdenominator hvalueMul
  have hbudgetDiv :
      (Q'.divPos (numerator + budget) denominator hdenominator).eqv
        (positiveArtanhDecayRatio z hz + q) := by
    unfold Q'.divPos positiveArtanhDecayRatio
    refine Q'.eqv_trans _
      (numerator * Q'.recipPos denominator hdenominator +
        budget * Q'.recipPos denominator hdenominator) _
      (Q'.add_mul_eqv numerator budget
        (Q'.recipPos denominator hdenominator)) ?_
    refine Q'.add_eqv_congr' (Q'.eqv_refl _) ?_
    refine Q'.eqv_trans _
      (q * (denominator * Q'.recipPos denominator hdenominator)) _
      (Q'.mul_assoc_eqv q denominator
        (Q'.recipPos denominator hdenominator)) ?_
    refine Q'.eqv_trans _ (q * 1) _
      (Q'.mul_eqv_congr_left q _ _
        (Q'.mul_recipPos_eqv denominator hdenominator)) ?_
    exact Q'.mul_one_eqv q
  have hnumeratorLe : numerator <= denominator * value + budget := by
    have hstep : -budget + numerator <= defect + numerator :=
      Q'.add_le_add_right _ _ numerator hlower
    have hshift : numerator + -budget <= denominator * value := by
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.add_comm_eqv numerator (-budget))) ?_
      exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hcancel)
    have hrestore : (numerator + -budget) + budget <=
        denominator * value + budget :=
      Q'.add_le_add_right _ _ budget hshift
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hrestore
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv numerator (-budget) budget) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left numerator _ _
        (Q'.neg_add_self_eqv budget)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' numerator)
  have hsumMul : ((value + q) * denominator).eqv
      (denominator * value + budget) := by
    refine Q'.eqv_trans _
      (value * denominator + q * denominator) _
      (Q'.add_mul_eqv value q denominator) ?_
    exact Q'.add_eqv_congr'
      (Q'.mul_comm_eqv value denominator) (Q'.eqv_refl _)
  have hlowerMul : numerator <= (value + q) * denominator :=
    Q'.le_trans' _ _ _ hnumeratorLe
      (Q'.le_of_eqv (Q'.eqv_symm hsumMul))
  have hlowerDiv : Q'.divPos numerator denominator hdenominator <= value + q :=
    Q'.divPos_le_of_le_mul numerator denominator hdenominator hlowerMul
  exact
    ⟨Q'.le_trans' _ _ _ hupperDiv (Q'.le_of_eqv hbudgetDiv),
      hlowerDiv⟩

/-- The completely computed outer anchor stage for the positive-artanh
identity at tolerance `epsilon`. -/
def positiveArtanhEulerAnchorStage (epsilon : Q') : Nat :=
  positiveArtanhExponentModulus
    (positiveArtanhAnchorOuterTolerance epsilon)

/-- The completely computed inner exponential cutoff at the outer anchor. -/
def positiveArtanhEulerAnchorPivot (z : Q') (epsilon : Q') : Nat :=
  ExpNeg.Mexp
    (positiveArtanhExponent z (positiveArtanhEulerAnchorStage epsilon))
    (positiveArtanhAnchorInnerTolerance epsilon)

/-- The smallest current scalar certificate: for every tolerance it checks
one denominator-cleared rational defect at one fully computed outer stage and
one fully computed inner cutoff.  There is no stored modulus and no
quantification over all later stages. -/
structure PositiveWindowArtanhEulerSingleAnchorCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  anchorDefect : forall epsilon : Q', (0 : Q') < epsilon ->
    Q'.abs
        (positiveArtanhEulerClearedDefect z
          (positiveArtanhEulerAnchorStage epsilon)
          (positiveArtanhEulerAnchorPivot z epsilon)) <=
      positiveArtanhAnchorInnerTolerance epsilon * ((1 : Q') + z)

/-- A uniform producer of the single computed-anchor certificates. -/
structure PositiveWindowArtanhEulerSingleAnchorCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerSingleAnchorCertificate z hz hzb

namespace PositiveWindowArtanhEulerSingleAnchorCertificate

/-- One computed cleared-defect anchor constructs the full two-index Euler
evaluation.  Explicit artanh Cauchy control, the uniform finite exponential
response bound, and the explicit exponential Cauchy modulus propagate that
single anchor to every later outer and inner stage. -/
def toEvaluation
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate : PositiveWindowArtanhEulerSingleAnchorCertificate z hz hzb) :
    PositiveWindowArtanhEulerEvaluation z hz hzb where
  exponentialConverges := by
    intro epsilon hepsilon
    let innerTolerance : Q' :=
      positiveArtanhAnchorInnerTolerance epsilon
    let outerTolerance : Q' :=
      positiveArtanhAnchorOuterTolerance epsilon
    let response : Q' := outerTolerance * Q'.ofNat 3
    let anchorStage : Nat := positiveArtanhEulerAnchorStage epsilon
    let anchorExponent : Q' := positiveArtanhExponent z anchorStage
    let anchorPivot : Nat := positiveArtanhEulerAnchorPivot z epsilon
    let anchorValue : Q' := ExpNeg.partialSum anchorExponent anchorPivot
    have hinner : (0 : Q') < innerTolerance :=
      positiveArtanhAnchorInnerTolerance_pos epsilon hepsilon
    have houter : (0 : Q') < outerTolerance :=
      positiveArtanhAnchorOuterTolerance_pos epsilon hepsilon
    have hbudget : innerTolerance +
        (innerTolerance + (response + (innerTolerance + innerTolerance))) <=
        epsilon :=
      positiveArtanhAnchor_five_budget_le epsilon hepsilon
    have hanchorDefect := certificate.anchorDefect epsilon hepsilon
    have hanchorClose : anchorValue <=
          positiveArtanhDecayRatio z hz + innerTolerance /\
        positiveArtanhDecayRatio z hz <= anchorValue + innerTolerance :=
      close_to_positiveArtanhDecayRatio_of_clearedDefect
        z hz anchorValue innerTolerance hanchorDefect
    refine ⟨anchorStage, fun stage hstage => ?_⟩
    let stageExponent : Q' := positiveArtanhExponent z stage
    let stagePivot : Nat := ExpNeg.Mexp stageExponent innerTolerance
    let stageValue : Q' := ExpNeg.partialSum stageExponent stagePivot
    have hmoving := positiveArtanhEulerMovingPivot_cauchy_explicit
      z hz hzb innerTolerance outerTolerance hinner houter
      stage anchorStage hstage (Nat.le_refl anchorStage)
    change stageValue <=
          ((anchorValue + innerTolerance) + response) + innerTolerance /\
        anchorValue <=
          ((stageValue + innerTolerance) + response) + innerTolerance at hmoving
    refine ⟨stagePivot, fun n hn => ?_⟩
    have hcauchy := ExpNeg.expNeg_cauchy_explicit stageExponent
      (positiveArtanhExponent_nonnegative z hz stage)
      innerTolerance hinner stagePivot n (Nat.le_refl stagePivot) hn
    have regroup : forall x : Q',
        (((((x + innerTolerance) + innerTolerance) + response) +
              innerTolerance) + innerTolerance).eqv
          (x + (innerTolerance +
            (innerTolerance + (response +
              (innerTolerance + innerTolerance))))) := by
      intro x
      refine Q'.eqv_trans _
        ((((x + innerTolerance) + innerTolerance) + response) +
          (innerTolerance + innerTolerance)) _
        (Q'.add_assoc_eqv
          (((x + innerTolerance) + innerTolerance) + response)
          innerTolerance innerTolerance) ?_
      refine Q'.eqv_trans _
        (((x + innerTolerance) + innerTolerance) +
          (response + (innerTolerance + innerTolerance))) _
        (Q'.add_assoc_eqv ((x + innerTolerance) + innerTolerance)
          response (innerTolerance + innerTolerance)) ?_
      refine Q'.eqv_trans _
        ((x + innerTolerance) +
          (innerTolerance +
            (response + (innerTolerance + innerTolerance)))) _
        (Q'.add_assoc_eqv (x + innerTolerance) innerTolerance
          (response + (innerTolerance + innerTolerance))) ?_
      exact Q'.add_assoc_eqv x innerTolerance
        (innerTolerance + (response +
          (innerTolerance + innerTolerance)))
    have closeBudget : forall x : Q',
        (((((x + innerTolerance) + innerTolerance) + response) +
              innerTolerance) + innerTolerance) <= x + epsilon := by
      intro x
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (regroup x))
        (Q'.add_le_add_left x _ epsilon hbudget)
    change
      ExpNeg.partialSum stageExponent n <=
          positiveArtanhDecayRatio z hz + epsilon /\
        positiveArtanhDecayRatio z hz <=
          ExpNeg.partialSum stageExponent n + epsilon
    have hforwardAnchor :
        (((anchorValue + innerTolerance) + response) + innerTolerance) +
            innerTolerance <=
          ((((positiveArtanhDecayRatio z hz + innerTolerance) +
              innerTolerance) + response) + innerTolerance) +
            innerTolerance :=
      Q'.add_le_add_right _ _ innerTolerance
        (Q'.add_le_add_right _ _ innerTolerance
          (Q'.add_le_add_right _ _ response
            (Q'.add_le_add_right _ _ innerTolerance hanchorClose.1)))
    have hforward : ExpNeg.partialSum stageExponent n <=
        ((((positiveArtanhDecayRatio z hz + innerTolerance) +
            innerTolerance) + response) + innerTolerance) + innerTolerance :=
      Q'.le_trans' _ _ _ hcauchy.2
        (Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ innerTolerance hmoving.1)
          hforwardAnchor)
    have hbackwardStage :
        (((stageValue + innerTolerance) + response) + innerTolerance) +
            innerTolerance <=
          ((((ExpNeg.partialSum stageExponent n + innerTolerance) +
              innerTolerance) + response) + innerTolerance) +
            innerTolerance :=
      Q'.add_le_add_right _ _ innerTolerance
        (Q'.add_le_add_right _ _ innerTolerance
          (Q'.add_le_add_right _ _ response
            (Q'.add_le_add_right _ _ innerTolerance hcauchy.1)))
    have hbackward : positiveArtanhDecayRatio z hz <=
        ((((ExpNeg.partialSum stageExponent n + innerTolerance) +
            innerTolerance) + response) + innerTolerance) + innerTolerance :=
      Q'.le_trans' _ _ _ hanchorClose.2
        (Q'.le_trans' _ _ _
          (Q'.add_le_add_right _ _ innerTolerance hmoving.2)
          hbackwardStage)
    exact
      ⟨Q'.le_trans' _ _ _ hforward
          (closeBudget (positiveArtanhDecayRatio z hz)),
        Q'.le_trans' _ _ _ hbackward
          (closeBudget (ExpNeg.partialSum stageExponent n))⟩

end PositiveWindowArtanhEulerSingleAnchorCertificate

/-- Uniform single-anchor certificates compile directly to the smallest
positive-artanh evaluation interface. -/
def positiveWindowArtanhEulerCompilerOfSingleAnchor
    (compiler : PositiveWindowArtanhEulerSingleAnchorCompiler) :
    PositiveWindowArtanhEulerCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toEvaluation

/-- A one-index quantitative certificate for the positive artanh identity.

At every sufficiently late artanh stage it compares a single, computed
exponential partial sum with `(1-z)/(1+z)` to half the requested tolerance.
The already-proved explicit Cauchy modulus of `expNeg` then supplies every
later inner approximation and the other half of the tolerance. -/
structure PositiveWindowArtanhEulerPivotCertificate
    (z : Q') (hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  stageModulus : Q' -> Nat
  pivotClose : forall epsilon : Q', (0 : Q') < epsilon ->
    forall stage : Nat, stageModulus epsilon <= stage ->
      let q := HalfPow.half * epsilon
      let exponent := positiveArtanhExponent z stage
      let pivot := positiveArtanhEulerPivot z stage epsilon
      ExpNeg.partialSum exponent pivot <=
          positiveArtanhDecayRatio z hz + q /\
        positiveArtanhDecayRatio z hz <=
          ExpNeg.partialSum exponent pivot + q

/-- A uniform producer of explicit pivot certificates. -/
structure PositiveWindowArtanhEulerPivotCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPivotCertificate z hz hzb

/-- A division-free one-index certificate for the remaining positive-artanh
identity.  At the computed pivot it controls the absolute cleared defect by
`q * (1+z)`, which is exactly the cross-multiplied form of a `q`-error in the
target ratio. -/
structure PositiveWindowArtanhEulerClearedDefectCertificate
    (z : Q') (hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  stageModulus : Q' -> Nat
  pivotDefect : forall epsilon : Q', (0 : Q') < epsilon ->
    forall stage : Nat, stageModulus epsilon <= stage ->
      let q := HalfPow.half * epsilon
      let pivot := positiveArtanhEulerPivot z stage epsilon
      Q'.abs (positiveArtanhEulerClearedDefect z stage pivot) <=
        q * ((1 : Q') + z)

/-- A uniform producer of denominator-cleared pivot certificates. -/
structure PositiveWindowArtanhEulerClearedDefectCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerClearedDefectCertificate z hz hzb

namespace PositiveWindowArtanhEulerClearedDefectCertificate

/-- Clearing the positive denominator loses no information: a cleared-defect
certificate constructs the existing pivot certificate with the same outer
modulus and computed inner cutoff. -/
def toPivot
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate : PositiveWindowArtanhEulerClearedDefectCertificate z hz hzb) :
    PositiveWindowArtanhEulerPivotCertificate z hz hzb where
  stageModulus := certificate.stageModulus
  pivotClose epsilon hepsilon stage hstage := by
    exact close_to_positiveArtanhDecayRatio_of_clearedDefect z hz
      (ExpNeg.partialSum (positiveArtanhExponent z stage)
        (positiveArtanhEulerPivot z stage epsilon))
      (HalfPow.half * epsilon)
      (certificate.pivotDefect epsilon hepsilon stage hstage)

end PositiveWindowArtanhEulerClearedDefectCertificate

/-- Uniform cleared-defect certificates compile to the one-index pivot
interface; all later convergence and Wilson consumers are therefore reused. -/
def positiveWindowArtanhEulerPivotCompilerOfClearedDefect
    (compiler : PositiveWindowArtanhEulerClearedDefectCompiler) :
    PositiveWindowArtanhEulerPivotCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toPivot

namespace PositiveWindowArtanhEulerPivotCertificate

/-- The pivot certificate inhabits the one-copy Euler evaluation.  This
constructor discharges the entire inner exponential truncation from
`ExpNeg.expNeg_cauchy_explicit`; the remaining certificate is only the outer
artanh-stage comparison at one computed pivot. -/
def toEvaluation
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate : PositiveWindowArtanhEulerPivotCertificate z hz hzb) :
    PositiveWindowArtanhEulerEvaluation z hz hzb where
  exponentialConverges := by
    intro epsilon hepsilon
    let q : Q' := HalfPow.half * epsilon
    have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
    refine ⟨certificate.stageModulus epsilon, fun stage hstage => ?_⟩
    let exponent : Q' := positiveArtanhExponent z stage
    let pivot : Nat := positiveArtanhEulerPivot z stage epsilon
    have hpivot := certificate.pivotClose epsilon hepsilon stage hstage
    have hexponent : (0 : Q') <= exponent :=
      positiveArtanhExponent_nonnegative z hz stage
    refine ⟨pivot, fun n hn => ?_⟩
    have hcauchy := ExpNeg.expNeg_cauchy_explicit
      exponent hexponent q hq pivot n (Nat.le_refl pivot) hn
    change
      ExpNeg.partialSum exponent n <=
          positiveArtanhDecayRatio z hz + epsilon /\
        positiveArtanhDecayRatio z hz <=
          ExpNeg.partialSum exponent n + epsilon
    have hqq : (q + q).eqv epsilon := ExpNeg.two_halves epsilon
    have hforward : ExpNeg.partialSum exponent n <=
        (positiveArtanhDecayRatio z hz + q) + q :=
      Q'.le_trans' _ _ _ hcauchy.2
        (Q'.add_le_add_right _ _ q hpivot.1)
    have hbackward : positiveArtanhDecayRatio z hz <=
        (ExpNeg.partialSum exponent n + q) + q :=
      Q'.le_trans' _ _ _ hpivot.2
        (Q'.add_le_add_right _ _ q hcauchy.1)
    refine ⟨Q'.le_trans' _ _ _ hforward (Q'.le_of_eqv ?_),
      Q'.le_trans' _ _ _ hbackward (Q'.le_of_eqv ?_)⟩
    · exact Q'.eqv_trans _
        (positiveArtanhDecayRatio z hz + (q + q)) _
        (Q'.add_assoc_eqv (positiveArtanhDecayRatio z hz) q q)
        (Q'.add_eqv_congr_left
          (positiveArtanhDecayRatio z hz) _ _ hqq)
    · exact Q'.eqv_trans _
        (ExpNeg.partialSum exponent n + (q + q)) _
        (Q'.add_assoc_eqv (ExpNeg.partialSum exponent n) q q)
        (Q'.add_eqv_congr_left
          (ExpNeg.partialSum exponent n) _ _ hqq)

end PositiveWindowArtanhEulerPivotCertificate

/-- Uniform pivot certificates compile to the smallest current scalar inverse
interface without any choice or extraction from a propositional existential. -/
def positiveWindowArtanhEulerCompilerOfPivot
    (compiler : PositiveWindowArtanhEulerPivotCompiler) :
    PositiveWindowArtanhEulerCompiler where
  evaluate z hz hzb :=
    (compiler.evaluate z hz hzb).toEvaluation

/-- One copy of the negative-branch exponent. -/
def negativeArtanhExponent (y : Q') (stage : Nat) : Q' :=
  -(CRealLog.partialSum y stage + CRealLog.partialSum y stage)

/-- Pointwise nonnegativity of the one-copy negative-branch exponent. -/
theorem negativeArtanhExponent_nonnegative
    (y : Q') (hy : y < (0 : Q')) (stage : Nat) :
    (0 : Q') <= negativeArtanhExponent y stage := by
  have hyNonpositive : y <= (0 : Q') := Q'.le_of_lt hy
  have hpartial : CRealLog.partialSum y stage <= (0 : Q') := by
    have hanti := CRealLog.partialSum_anti_of_nonpos y hyNonpositive 0 stage
    rw [CRealLog.partialSum_zero, Nat.zero_add] at hanti
    exact hanti
  exact Q'.nonneg_neg_of_nonpos
    (Q'.le_trans' _ _ _ (Q'.add_le_add hpartial hpartial)
      (Q'.le_of_eqv (by decide : ((0 : Q') + 0).eqv 0)))

/-- Oddness identifies the positive exponent at `-y` with the one-copy
negative exponent at `y`. -/
theorem positiveArtanhExponent_neg_eqv_negative
    (y : Q') (stage : Nat) :
    (positiveArtanhExponent (-y) stage).eqv
      (negativeArtanhExponent y stage) := by
  unfold positiveArtanhExponent negativeArtanhExponent
  have hodd := CRealLogOddness.artanhPartial_neg_eqv y stage
  refine Q'.eqv_trans _
    ((-CRealLog.partialSum y stage) +
      (-CRealLog.partialSum y stage)) _ ?_ ?_
  · exact Q'.add_eqv_congr' hodd hodd
  · exact Q'.eqv_symm
      (Q'.neg_add_eqv
        (CRealLog.partialSum y stage)
        (CRealLog.partialSum y stage))

/-- The two one-copy exponents add to the existing square exponent. -/
theorem negativeArtanhExponent_add_self_eqv_square
    (y : Q') (stage : Nat) :
    (negativeArtanhExponent y stage + negativeArtanhExponent y stage).eqv
      (negativeArtanhSquareExponent y stage) := by
  let a : Q' := negativeArtanhExponent y stage
  change (a + a).eqv (a * ((1 : Q') + 1))
  refine Q'.eqv_trans _ (((1 : Q') + 1) * a) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.eqv_trans _ ((1 : Q') * a + (1 : Q') * a) _
        (Q'.add_mul_eqv 1 1 a)
        (Q'.add_eqv_congr'
          (Q'.one_mul_eqv a) (Q'.one_mul_eqv a)))
  · exact Q'.mul_comm_eqv ((1 : Q') + 1) a

/-- Negating the coordinate turns the positive-window decay ratio into the
negative-window inverse Mobius ratio. -/
theorem positiveArtanhDecayRatio_neg_eqv_artanhRatio
    (y : Q') (hy : y < (0 : Q')) :
    (positiveArtanhDecayRatio (-y) (neg_pos_of_strict_neg y hy)).eqv
      (artanhRatio y hy) := by
  unfold positiveArtanhDecayRatio artanhRatio
  have hnum : ((1 : Q') + -(-y)).eqv ((1 : Q') + y) :=
    Q'.add_eqv_congr_left 1 _ _ (Q'.neg_neg_eqv y)
  have hden : ((1 : Q') + -y).eqv ((1 : Q') + -y) :=
    Q'.eqv_refl _
  have hrecip :
      (Q'.recipPos ((1 : Q') + -y)
        (one_add_pos_of_pos (-y) (neg_pos_of_strict_neg y hy))).eqv
      (Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy)) :=
    Q'.recipPos_eqv_congr _ _ _ _ hden
  refine Q'.eqv_trans _
    (((1 : Q') + y) *
      Q'.recipPos ((1 : Q') + -y)
        (one_add_pos_of_pos (-y) (neg_pos_of_strict_neg y hy))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hnum
  · exact Q'.mul_eqv_congr_left _ _ _ hrecip

/-- The inverse Mobius transform recovers the original rational exactly:
if `y = (m-1)/(m+1)`, then `(1+y)/(1-y) = m`.  The proof uses only the positive
reciprocal law and commutative-ring normalization in `Q'`. -/
theorem artanhRatio_yOf_eqv
    (m : Q') (hm1 : (0 : Q') < m + 1)
    (hy : CRealLog.yOf m hm1 < (0 : Q')) :
    (artanhRatio (CRealLog.yOf m hm1) hy).eqv m := by
  let d : Q' := m + 1
  let r : Q' := Q'.recipPos d hm1
  let y : Q' := (m + -1) * r
  have hdr : (d * r).eqv (1 : Q') := Q'.mul_recipPos_eqv d hm1
  have hplusCollapse : ((m + 1) + (m + -1)).eqv (m + m) := by
    refine Q'.eqv_trans _ ((m + m) + ((1 : Q') + -1)) _
      (Q'.add_swap_inner m 1 m (-1)) ?_
    refine Q'.eqv_trans _ ((m + m) + 0) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (m + m) _ _
        (Q'.add_neg_self_eqv (1 : Q'))
    · exact QPoly.q_add_zero_eqv (m + m)
  have hminusCollapse : ((m + 1) + -(m + -1)).eqv
      ((1 : Q') + 1) := by
    have hneg : (-(m + -1)).eqv ((-m) + 1) := by
      refine Q'.eqv_trans _ ((-m) + -(-1 : Q')) _
        (Q'.neg_add_eqv m (-1)) ?_
      exact Q'.add_eqv_congr_left (-m) _ _
        (Q'.neg_neg_eqv (1 : Q'))
    refine Q'.eqv_trans _ ((m + 1) + ((-m) + 1)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (m + 1) _ _ hneg
    refine Q'.eqv_trans _ ((m + -m) + ((1 : Q') + 1)) _
      (Q'.add_swap_inner m 1 (-m) 1) ?_
    refine Q'.eqv_trans _ (0 + ((1 : Q') + 1)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ ((1 : Q') + 1)
        (Q'.add_neg_self_eqv m)
    · exact QPoly.q_zero_add_eqv ((1 : Q') + 1)
  have hnum : ((1 : Q') + y).eqv ((m + m) * r) := by
    refine Q'.eqv_trans _ ((d * r) + y) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_symm hdr) (Q'.eqv_refl y)
    · refine Q'.eqv_trans _ (((m + 1) + (m + -1)) * r) _ ?_ ?_
      · exact Q'.eqv_symm (Q'.add_mul_eqv (m + 1) (m + -1) r)
      · exact Q'.mul_eqv_congr_right _ _ r hplusCollapse
  have hden : ((1 : Q') + -y).eqv (((1 : Q') + 1) * r) := by
    refine Q'.eqv_trans _ ((d * r) + -y) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_symm hdr) (Q'.eqv_refl (-y))
    · have hnegMul : (-y).eqv ((-(m + -1)) * r) := by
        dsimp [y]
        exact Q'.eqv_symm (Q'.neg_mul_eqv (m + -1) r)
      refine Q'.eqv_trans _ (((m + 1) * r) + ((-(m + -1)) * r)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left ((m + 1) * r) _ _ hnegMul
      refine Q'.eqv_trans _ (((m + 1) + -(m + -1)) * r) _ ?_ ?_
      · exact Q'.eqv_symm (Q'.add_mul_eqv (m + 1) (-(m + -1)) r)
      · exact Q'.mul_eqv_congr_right _ _ r hminusCollapse
  have hmden : (m * ((1 : Q') + -y)).eqv ((1 : Q') + y) := by
    refine Q'.eqv_trans _ (m * (((1 : Q') + 1) * r)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left m _ _ hden
    · refine Q'.eqv_trans _ ((m + m) * r) _ ?_ ?_
      · refine Q'.eqv_trans _ ((m * ((1 : Q') + 1)) * r) _ ?_ ?_
        · exact Q'.eqv_symm (Q'.mul_assoc_eqv m ((1 : Q') + 1) r)
        · exact Q'.mul_eqv_congr_right _ _ r
            (Q'.eqv_trans _ (m * 1 + m * 1) _
              (Q'.mul_add_eqv m 1 1)
              (Q'.add_eqv_congr'
                (Q'.mul_one_eqv m) (Q'.mul_one_eqv m)))
      · exact Q'.eqv_symm hnum
  change
    ((((1 : Q') + y) *
      Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy)).eqv m)
  refine Q'.eqv_trans _
    ((m * ((1 : Q') + -y)) *
      Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hmden)
  · refine Q'.eqv_trans _
      (m * (((1 : Q') + -y) *
        Q'.recipPos ((1 : Q') + -y) (one_sub_pos_of_neg y hy))) _
      (Q'.mul_assoc_eqv m _ _) ?_
    refine Q'.eqv_trans _ (m * (1 : Q')) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left m _ _
        (Q'.mul_recipPos_eqv ((1 : Q') + -y)
          (one_sub_pos_of_neg y hy))
    · exact Q'.mul_one_eqv m

end YMGap.Constructive.CRealArtanhEulerRatio

#print axioms YMGap.Constructive.CRealArtanhEulerRatio.one_sub_pos_of_neg
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.negativeArtanhSquareExponent_nonnegative
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.neg_pos_of_strict_neg
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhExponent_nonnegative
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhExponent_le_one
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhExponent_cauchy_explicit
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhExpPartialSum_cauchy_explicit
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhEulerMovingPivot_cauchy_explicit
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhAnchor_response_eqv_inner
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhAnchor_five_budget_le
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.close_to_positiveArtanhDecayRatio_of_clearedDefect
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.PositiveWindowArtanhEulerSingleAnchorCertificate.toEvaluation
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveWindowArtanhEulerCompilerOfSingleAnchor
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.PositiveWindowArtanhEulerClearedDefectCertificate.toPivot
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveWindowArtanhEulerPivotCompilerOfClearedDefect
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.PositiveWindowArtanhEulerPivotCertificate.toEvaluation
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveWindowArtanhEulerCompilerOfPivot
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.negativeArtanhExponent_nonnegative
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhExponent_neg_eqv_negative
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.negativeArtanhExponent_add_self_eqv_square
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhDecayRatio_neg_eqv_artanhRatio
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.artanhRatio_yOf_eqv
