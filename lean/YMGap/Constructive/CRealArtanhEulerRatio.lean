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
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.close_to_positiveArtanhDecayRatio_of_clearedDefect
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.PositiveWindowArtanhEulerClearedDefectCertificate.toPivot
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveWindowArtanhEulerPivotCompilerOfClearedDefect
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.PositiveWindowArtanhEulerPivotCertificate.toEvaluation
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveWindowArtanhEulerCompilerOfPivot
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.negativeArtanhExponent_nonnegative
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhExponent_neg_eqv_negative
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.negativeArtanhExponent_add_self_eqv_square
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.positiveArtanhDecayRatio_neg_eqv_artanhRatio
#print axioms YMGap.Constructive.CRealArtanhEulerRatio.artanhRatio_yOf_eqv
