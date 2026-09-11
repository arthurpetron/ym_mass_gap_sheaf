/-
# Quantitative continuity data for the strict CReal reflection pairing

This module isolates the quantitative rational estimates needed before the strict
reflection pairing can be extended to two arguments in the staged OS
completion:

1. the exact bilinear difference split at every approximation stage;
2. a common-base, sqrt-free two-variable continuity bound; and
3. an explicit half-power Cauchy coefficient for every fixed pairing.

It also supplies a canonical explicitly regularized rational-sequence limit,
proved equivalent to the existing exact polarization.  This keeps all later
completion rates computational and choice-free.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
import YMGap.Continuum.GNSHilbertSpace
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingContinuity

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

private theorem neg_one_mul_eqv_local (value : Q') :
    ((-1 : Q') * value) ≈ -value := by
  ring_qeqv

private theorem q_sub_add_cancel_eqv_local (a b : Q') :
    ((a + -b) + b) ≈ a := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a (-b + b) 0 (Q'.neg_add_self_eqv b)) ?_
  exact QPoly.q_add_zero_eqv a

/-- Cancellation in the exact shape produced by the two bilinear difference
terms: `(a-b) + (b-c) ≃ a-c`. -/
private theorem q_sub_telescope_eqv_local (a b c : Q') :
    ((a + -b) + (b + -c)) ≈ (a + -c) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (a + -b) b (-c))) ?_
  exact Q'.add_eqv_congr_right
    ((a + -b) + b) a (-c) (q_sub_add_cancel_eqv_local a b)

/-! ## 1. Exact approximation-level bilinear difference split -/

/-- At every rational approximation stage,

`B(left,right) - B(left',right')`
`  = B(left-left',right) + B(left',right-right')`.

The equality is `Q'.eqv`, the native rational equality relation used by the
strict-cylinder presentation algebra. -/
theorem strictJointCylinderReflectionBilinear_approx_difference_split
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat}
    (left left' right right' : StrictJointCylinderVector base) :
    ((strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage +
        -(strictJointCylinderReflectionBilinear
          hcoupling hle left' right').approx stage) ≈
      ((strictJointCylinderReflectionBilinear hcoupling hle
          (strictJointCylinderDifference left left') right).approx stage +
        (strictJointCylinderReflectionBilinear hcoupling hle left'
          (strictJointCylinderDifference right right')).approx stage) := by
  have hleftAdd :=
    strictJointCylinderReflectionBilinear_approx_add_left_eqv
      hcoupling hle (stage := stage)
      left (left'.smul (-1)) right
  have hleftSmul :=
    strictJointCylinderReflectionBilinear_approx_smul_left_eqv
      hcoupling hle (stage := stage) (-1) left' right
  have hrightAdd :=
    strictJointCylinderReflectionBilinear_approx_add_right_eqv
      hcoupling hle (stage := stage)
      left' right (right'.smul (-1))
  have hrightSmul :=
    strictJointCylinderReflectionBilinear_approx_smul_right_eqv
      hcoupling hle (stage := stage) (-1) left' right'
  change
    (strictJointCylinderReflectionBilinear hcoupling hle
        (strictJointCylinderDifference left left') right).approx stage ≈
      (strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage +
        (strictJointCylinderReflectionBilinear
          hcoupling hle (left'.smul (-1)) right).approx stage at hleftAdd
  change
    (strictJointCylinderReflectionBilinear
        hcoupling hle (left'.smul (-1)) right).approx stage ≈
      (-1 : Q') *
        (strictJointCylinderReflectionBilinear
          hcoupling hle left' right).approx stage at hleftSmul
  change
    (strictJointCylinderReflectionBilinear hcoupling hle left'
        (strictJointCylinderDifference right right')).approx stage ≈
      (strictJointCylinderReflectionBilinear
          hcoupling hle left' right).approx stage +
        (strictJointCylinderReflectionBilinear
          hcoupling hle left' (right'.smul (-1))).approx stage at hrightAdd
  change
    (strictJointCylinderReflectionBilinear
        hcoupling hle left' (right'.smul (-1))).approx stage ≈
      (-1 : Q') *
        (strictJointCylinderReflectionBilinear
          hcoupling hle left' right').approx stage at hrightSmul
  have hfirst :
      (strictJointCylinderReflectionBilinear hcoupling hle
          (strictJointCylinderDifference left left') right).approx stage ≈
        (strictJointCylinderReflectionBilinear
            hcoupling hle left right).approx stage +
          -(strictJointCylinderReflectionBilinear
            hcoupling hle left' right).approx stage :=
    Q'.eqv_trans _ _ _ hleftAdd
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ hleftSmul
          (neg_one_mul_eqv_local
            ((strictJointCylinderReflectionBilinear
              hcoupling hle left' right).approx stage))))
  have hsecond :
      (strictJointCylinderReflectionBilinear hcoupling hle left'
          (strictJointCylinderDifference right right')).approx stage ≈
        (strictJointCylinderReflectionBilinear
            hcoupling hle left' right).approx stage +
          -(strictJointCylinderReflectionBilinear
            hcoupling hle left' right').approx stage :=
    Q'.eqv_trans _ _ _ hrightAdd
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ hrightSmul
          (neg_one_mul_eqv_local
            ((strictJointCylinderReflectionBilinear
              hcoupling hle left' right').approx stage))))
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hfirst hsecond) ?_)
  exact q_sub_telescope_eqv_local
    ((strictJointCylinderReflectionBilinear
      hcoupling hle left right).approx stage)
    ((strictJointCylinderReflectionBilinear
      hcoupling hle left' right).approx stage)
    ((strictJointCylinderReflectionBilinear
      hcoupling hle left' right').approx stage)

/-! ## 2. The common-base quantitative continuity estimate -/

/-- Sqrt-free joint continuity at a fixed base and approximation stage.

If both squared displacements are at most `delta`, the two undifferenced
quadratics required by the bilinear split are at most `bound`, and
`delta * bound ≤ (epsilon/2)^2`, then the two pairing values differ by at
most `epsilon`.
-/
theorem strictJointCylinderReflectionBilinear_approx_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat}
    (left left' right right' : StrictJointCylinderVector base)
    (epsilon delta bound : Q')
    (hepsilon : (0 : Q') < epsilon)
    (hdelta : (0 : Q') < delta)
    (hleftDist :
      ((strictJointCylinderDifference left left').reflectionQuadratic
        hcoupling hle).approx stage ≤ delta)
    (hrightDist :
      ((strictJointCylinderDifference right right').reflectionQuadratic
        hcoupling hle).approx stage ≤ delta)
    (hrightBound :
      (right.reflectionQuadratic hcoupling hle).approx stage ≤ bound)
    (hleft'Bound :
      (left'.reflectionQuadratic hcoupling hle).approx stage ≤ bound)
    (hbudget :
      delta * bound ≤
        (HalfPow.half * epsilon) * (HalfPow.half * epsilon)) :
    Q'.abs
      ((strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx stage +
        -(strictJointCylinderReflectionBilinear
          hcoupling hle left' right').approx stage) ≤ epsilon := by
  let leftDifference := strictJointCylinderDifference left left'
  let rightDifference := strictJointCylinderDifference right right'
  let firstTerm := strictJointCylinderReflectionBilinear
    hcoupling hle leftDifference right
  let secondTerm := strictJointCylinderReflectionBilinear
    hcoupling hle left' rightDifference
  have hhalfPos : (0 : Q') < HalfPow.half * epsilon :=
    ExpNeg.half_mul_pos epsilon hepsilon
  have hrightNonnegative :
      (0 : Q') ≤ (right.reflectionQuadratic hcoupling hle).approx stage :=
    centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
      coupling hcoupling base right.roots right.coefficient stage
  have hleft'Nonnegative :
      (0 : Q') ≤ (left'.reflectionQuadratic hcoupling hle).approx stage :=
    centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
      coupling hcoupling base left'.roots left'.coefficient stage
  have hfirstProduct :
      (leftDifference.reflectionQuadratic hcoupling hle).approx stage *
          (right.reflectionQuadratic hcoupling hle).approx stage ≤
        delta * bound :=
    Q'.mul_le_mul_of_nonneg hleftDist hrightBound
      (Q'.le_of_lt hdelta) hrightNonnegative
  have hfirstSquare :
      firstTerm.approx stage * firstTerm.approx stage ≤
        (HalfPow.half * epsilon) * (HalfPow.half * epsilon) := by
    refine Q'.le_trans' _ _ _
      (strictJointCylinderReflectionBilinear_approx_cauchy_schwarz
        hcoupling hle leftDifference right (stage := stage)) ?_
    exact Q'.le_trans' _ _ _ hfirstProduct hbudget
  have hfirstAbs :
      Q'.abs (firstTerm.approx stage) ≤ HalfPow.half * epsilon :=
    Q'.abs_le_of_sq_le_sq hhalfPos hfirstSquare
  have hsecondCS :=
    strictJointCylinderReflectionBilinear_approx_cauchy_schwarz
      hcoupling hle left' rightDifference (stage := stage)
  have hsecondCS' :
      secondTerm.approx stage * secondTerm.approx stage ≤
        (rightDifference.reflectionQuadratic hcoupling hle).approx stage *
          (left'.reflectionQuadratic hcoupling hle).approx stage :=
    Q'.le_trans' _ _ _ hsecondCS
      (Q'.le_of_eqv (Q'.mul_comm_eqv
        ((left'.reflectionQuadratic hcoupling hle).approx stage)
        ((rightDifference.reflectionQuadratic hcoupling hle).approx stage)))
  have hsecondProduct :
      (rightDifference.reflectionQuadratic hcoupling hle).approx stage *
          (left'.reflectionQuadratic hcoupling hle).approx stage ≤
        delta * bound :=
    Q'.mul_le_mul_of_nonneg hrightDist hleft'Bound
      (Q'.le_of_lt hdelta) hleft'Nonnegative
  have hsecondSquare :
      secondTerm.approx stage * secondTerm.approx stage ≤
        (HalfPow.half * epsilon) * (HalfPow.half * epsilon) :=
    Q'.le_trans' _ _ _ hsecondCS'
      (Q'.le_trans' _ _ _ hsecondProduct hbudget)
  have hsecondAbs :
      Q'.abs (secondTerm.approx stage) ≤ HalfPow.half * epsilon :=
    Q'.abs_le_of_sq_le_sq hhalfPos hsecondSquare
  have hsplit :=
    strictJointCylinderReflectionBilinear_approx_difference_split
      hcoupling hle (stage := stage) left left' right right'
  have habsSplit :
      Q'.abs
        ((strictJointCylinderReflectionBilinear
            hcoupling hle left right).approx stage +
          -(strictJointCylinderReflectionBilinear
            hcoupling hle left' right').approx stage) ≤
        Q'.abs (firstTerm.approx stage) +
          Q'.abs (secondTerm.approx stage) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit)) ?_
    exact Q'.abs_add_le' (firstTerm.approx stage) (secondTerm.approx stage)
  exact Q'.le_trans' _ _ _ habsSplit
    (Q'.le_trans' _ _ _ (Q'.add_le_add hfirstAbs hsecondAbs)
      (Q'.le_of_eqv (ExpNeg.two_halves epsilon)))

/-! ## 3. Explicit inner regularity of every fixed pairing -/

/-- The half-power coefficient controlling the rational approximation sequence
of one fixed strict reflection pairing. -/
def strictJointCylinderReflectionBilinearCauchyCoefficient
    {base : Nat} (left right : StrictJointCylinderVector base) : Q' :=
  Q'.abs strictJointPolarizationQuarter *
    (strictJointFixedQuadraticCauchyCoefficient
        (left.add right).roots (left.add right).coefficient +
      strictJointFixedQuadraticCauchyCoefficient
        (left.add (right.smul (-1))).roots
        (left.add (right.smul (-1))).coefficient)

theorem strictJointCylinderReflectionBilinearCauchyCoefficient_nonnegative
    {base : Nat} (left right : StrictJointCylinderVector base) :
    (0 : Q') ≤
      strictJointCylinderReflectionBilinearCauchyCoefficient left right := by
  unfold strictJointCylinderReflectionBilinearCauchyCoefficient
  exact Q'.mul_nonneg _ _
    (Q'.abs_nonneg strictJointPolarizationQuarter)
    (Q'.zero_le_add _ _
      (strictJointFixedQuadraticCauchyCoefficient_nonnegative
        (left.add right).roots (left.add right).coefficient)
      (strictJointFixedQuadraticCauchyCoefficient_nonnegative
        (left.add (right.smul (-1))).roots
        (left.add (right.smul (-1))).coefficient))

/-- Explicit half-power Cauchy estimate for the approximation sequence of a
fixed strict reflection pairing. -/
theorem strictJointCylinderReflectionBilinear_approx_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    (left right : StrictJointCylinderVector base) :
    Q'.abs
      ((strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx later +
        -(strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx earlier) ≤
      strictJointCylinderReflectionBilinearCauchyCoefficient left right *
        HalfPow.half ^ earlier := by
  let plus := left.add right
  let minus := left.add (right.smul (-1))
  let plusCoefficient :=
    strictJointFixedQuadraticCauchyCoefficient plus.roots plus.coefficient
  let minusCoefficient :=
    strictJointFixedQuadraticCauchyCoefficient minus.roots minus.coefficient
  let decay := HalfPow.half ^ earlier
  have hplus :=
    centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
      hcoupling hle hstage plus.rootsCanonical plus.coefficient
  have hminus :=
    centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
      hcoupling hle hstage minus.rootsCanonical minus.coefficient
  change
    Q'.abs
      (centralNormalizedStrictJointFixedQuadraticSequence
          coupling hcoupling base plus.roots plus.coefficient later +
        -centralNormalizedStrictJointFixedQuadraticSequence
          coupling hcoupling base plus.roots plus.coefficient earlier) ≤
      plusCoefficient * decay at hplus
  change
    Q'.abs
      (centralNormalizedStrictJointFixedQuadraticSequence
          coupling hcoupling base minus.roots minus.coefficient later +
        -centralNormalizedStrictJointFixedQuadraticSequence
          coupling hcoupling base minus.roots minus.coefficient earlier) ≤
      minusCoefficient * decay at hminus
  let plusDifference :=
    centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base plus.roots plus.coefficient later +
      -centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base plus.roots plus.coefficient earlier
  let minusDifference :=
    centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base minus.roots minus.coefficient later +
      -centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base minus.roots minus.coefficient earlier
  have hrewrite :
      ((strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx later +
        -(strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx earlier) ≈
        strictJointPolarizationQuarter *
          (plusDifference + -minusDifference) := by
    simp only [strictJointCylinderReflectionBilinear_approx]
    dsimp only [plusDifference, minusDifference, plus, minus]
    ring_qeqv
  have hminusAbs : Q'.abs (-minusDifference) ≤ minusCoefficient * decay :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_neg' minusDifference)) hminus
  have hinner :
      Q'.abs (plusDifference + -minusDifference) ≤
        plusCoefficient * decay + minusCoefficient * decay :=
    Q'.le_trans' _ _ _
      (Q'.abs_add_le' plusDifference (-minusDifference))
      (Q'.add_le_add hplus hminusAbs)
  have hscaled :
      Q'.abs strictJointPolarizationQuarter *
          Q'.abs (plusDifference + -minusDifference) ≤
        Q'.abs strictJointPolarizationQuarter *
          (plusCoefficient * decay + minusCoefficient * decay) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hinner
      (Q'.abs_nonneg strictJointPolarizationQuarter)
  have hfinalEqv :
      Q'.abs strictJointPolarizationQuarter *
          (plusCoefficient * decay + minusCoefficient * decay) ≈
        strictJointCylinderReflectionBilinearCauchyCoefficient left right *
          HalfPow.half ^ earlier := by
    unfold strictJointCylinderReflectionBilinearCauchyCoefficient
    dsimp only [plusCoefficient, minusCoefficient, plus, minus, decay]
    ring_qeqv
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hrewrite)) ?_
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_mul_le strictJointPolarizationQuarter
      (plusDifference + -minusDifference)) ?_
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfinalEqv)

/-! ## 4. The direct rational sequence is Cauchy -/

/-- The direct complete-support sequence inherits the same half-power pair
bound as the polarized `CReal` approximations. -/
theorem strictJointCylinderReflectionBilinearSequence_pair_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base earlier later : Nat} (hstage : earlier ≤ later)
    (left right : StrictJointCylinderVector base) :
    Q'.abs
      (strictJointCylinderReflectionBilinearSequence
          coupling hcoupling left right later +
        -strictJointCylinderReflectionBilinearSequence
          coupling hcoupling left right earlier) ≤
      strictJointCylinderReflectionBilinearCauchyCoefficient left right *
        HalfPow.half ^ earlier := by
  have hlater :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := later) left right
  have hearlier :=
    StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle (stage := earlier) left right
  have hdifference :
      (strictJointCylinderReflectionBilinearSequence
          coupling hcoupling left right later +
        -strictJointCylinderReflectionBilinearSequence
          coupling hcoupling left right earlier) ≈
      ((strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx later +
        -(strictJointCylinderReflectionBilinear
          hcoupling hle left right).approx earlier) :=
    Q'.add_eqv_congr'
      (Q'.eqv_symm hlater)
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hearlier))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (strictJointCylinderReflectionBilinear_approx_pair_abs_le
      hcoupling hle hstage left right)

/-- Explicit modulus for the direct rational strict-pairing sequence.  It is
the usual division-free coefficient rescaling followed by the closed-form
half-power cutoff `scaledTolerance.den`. -/
def strictJointCylinderReflectionBilinearCauchyRate
    {base : Nat} (left right : StrictJointCylinderVector base)
    (tolerance : Q') : Nat :=
  (tolerance * Q'.invSucc
    (strictJointCylinderReflectionBilinearCauchyCoefficient
      left right).num.toNat).den

/-- The direct rational complete-support pairing sequence is Cauchy with an
explicit Type-level modulus. -/
def strictJointCylinderReflectionBilinearQCauchy
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.QCauchy
      (strictJointCylinderReflectionBilinearSequence
        coupling hcoupling left right) where
  M := strictJointCylinderReflectionBilinearCauchyRate left right
  bound := by
    intro tolerance htolerance earlier later hearlier hlater
    let cauchyCoefficient :=
      strictJointCylinderReflectionBilinearCauchyCoefficient left right
    let scaledTolerance :=
      tolerance * Q'.invSucc cauchyCoefficient.num.toNat
    have hcoefficient : (0 : Q') ≤ cauchyCoefficient :=
      strictJointCylinderReflectionBilinearCauchyCoefficient_nonnegative
        left right
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos htolerance
        (Q'.invSucc_pos cauchyCoefficient.num.toNat)
    have hscaledFinal : cauchyCoefficient * scaledTolerance ≤ tolerance :=
      ExpNeg.mul_le_of_mul_invSucc_toNat cauchyCoefficient tolerance
        hcoefficient (Q'.le_of_lt htolerance)
    change scaledTolerance.den ≤ earlier at hearlier
    change scaledTolerance.den ≤ later at hlater
    rcases Nat.le_total earlier later with horder | horder
    · have hpair :=
        strictJointCylinderReflectionBilinearSequence_pair_abs_le
          hcoupling hle horder left right
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hearlier
      have hhalf : HalfPow.half ^ earlier ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance :
          HalfPow.half ^ scaledTolerance.den ≤ scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ earlier) scaledTolerance cauchyCoefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs :
          Q'.abs
            (strictJointCylinderReflectionBilinearSequence
                coupling hcoupling left right later +
              -strictJointCylinderReflectionBilinearSequence
                coupling hcoupling left right earlier) ≤ tolerance :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := Q'.two_sided_of_abs_sub_le habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        strictJointCylinderReflectionBilinearSequence_pair_abs_le
          hcoupling hle horder left right
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hlater
      have hhalf : HalfPow.half ^ later ≤
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance :
          HalfPow.half ^ scaledTolerance.den ≤ scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ later) scaledTolerance cauchyCoefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs :
          Q'.abs
            (strictJointCylinderReflectionBilinearSequence
                coupling hcoupling left right earlier +
              -strictJointCylinderReflectionBilinearSequence
                coupling hcoupling left right later) ≤ tolerance :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact Q'.two_sided_of_abs_sub_le habs

/-! ## 5. Canonical rational-sequence presentation of the pairing -/

/-- The direct complete-support rational sequence, completed canonically by
`CReal.ofQ'CauchySeq`. -/
def strictJointCylinderReflectionBilinearSequenceLimit
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) : CReal :=
  CReal.ofQ'CauchySeq
    (strictJointCylinderReflectionBilinearSequence
      coupling hcoupling left right)
    (strictJointCylinderReflectionBilinearQCauchy
      hcoupling hle left right)

/-- The canonical rational-sequence limit agrees with the existing exact
polarization construction.  Thus later completion work may use either
presentation without changing the represented constructive real. -/
theorem strictJointCylinderReflectionBilinearSequenceLimit_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinearSequenceLimit
        hcoupling hle left right)
      (strictJointCylinderReflectionBilinear hcoupling hle left right) := by
  refine CReal.Equiv_of_limit_of_equal
    (aSeq := fun stage => CReal.ofQ'
      (strictJointCylinderReflectionBilinearSequence
        coupling hcoupling left right stage))
    (bSeq := fun stage => CReal.ofQ'
      ((strictJointCylinderReflectionBilinear
        hcoupling hle left right).approx stage))
    (fun stage => ?_)
    (CReal.convergesTo_ofQ'CauchySeq
      (strictJointCylinderReflectionBilinearSequence
        coupling hcoupling left right)
      (strictJointCylinderReflectionBilinearQCauchy
        hcoupling hle left right))
    (CReal.convergesTo_self
      (strictJointCylinderReflectionBilinear hcoupling hle left right))
  exact CReal.ofQ'_equiv_of_eqv
    (Q'.eqv_symm
      (StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
        hcoupling hle (stage := stage) left right))

#print axioms strictJointCylinderReflectionBilinear_approx_difference_split
#print axioms strictJointCylinderReflectionBilinear_approx_abs_sub_le
#print axioms strictJointCylinderReflectionBilinearCauchyCoefficient_nonnegative
#print axioms strictJointCylinderReflectionBilinear_approx_pair_abs_le
#print axioms strictJointCylinderReflectionBilinearSequence_pair_abs_le
#print axioms strictJointCylinderReflectionBilinearQCauchy
#print axioms strictJointCylinderReflectionBilinearSequenceLimit
#print axioms strictJointCylinderReflectionBilinearSequenceLimit_equiv

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealPairingContinuity
