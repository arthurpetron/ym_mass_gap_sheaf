/-
# Actual centered Cauchy streams for the cutoff-removed reflected form

The scalar mean is the already constructed joint pairing with the original
unit. Subtract its rational approximations from the original presentation.
The exact squared distance between two terms is the square of their
coefficient difference. Clipping the scalar tolerance at one gives an
explicit squared-distance modulus without a square root or a choice.

This constructs vectors on the EXISTING joint completion, not on a new
centered surrogate carrier. Their pairing identities are subsequent
consumers. Nome and spatial width stay fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenterAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime

/-- A linear tolerance suffices for a squared distance when clipped at one. -/
def centerTolerance (epsilon : Q') : Q' := Q'.min' epsilon 1

theorem centerTolerance_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < centerTolerance epsilon := by
  unfold centerTolerance Q'.min'
  split
  · exact he
  · decide

theorem coefficient_square_bound {a b epsilon : Q'} (he : (0 : Q') < epsilon)
    (h : a ≤ b + centerTolerance epsilon ∧ b ≤ a + centerTolerance epsilon) :
    (a + -b)^2 ≤ epsilon := by
  let d := centerTolerance epsilon
  have hd : (0 : Q') ≤ d := Q'.le_of_lt (centerTolerance_positive he)
  have habs : Q'.abs (a + -b) ≤ d :=
    Q'.abs_le (Q'.neg_le_sub_of_le_add h.2) (Q'.sub_le_of_le_add h.1)
  have hs : (a + -b)*(a + -b) ≤ d*d :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv (a + -b)))
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ habs (Q'.abs_nonneg _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ habs hd))
  have hbudget : d*d ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.min_le_right' epsilon 1) hd)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv d))
        (Q'.min_le_left' epsilon 1))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left (a + -b) _ _
      (Q'.mul_one_eqv (a + -b)))) (Q'.le_trans' _ _ _ hs hbudget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width

/-- The original unit coefficient and its actual approximation data. -/
def mean (x : PhysicalSpan width) : CReal :=
  jointPairing hw0 hw1 width x (unit width)

def meanCauchy (x : PhysicalSpan width) : QCauchy (mean hw0 hw1 width x).approx :=
  jointPairingCauchy hw0 hw1 width x (unit width)

/-- The scalar modulus is retained as data; no legacy existential is chosen. -/
def centeredRate (x : PhysicalSpan width) (epsilon : Q') : Nat :=
  (meanCauchy hw0 hw1 width x).M (centerTolerance epsilon)

def centeredStream (x : PhysicalSpan width) : (D).Cauchy where
  seq n := centerApprox x ((mean hw0 hw1 width x).approx n)
  modulus := centeredRate hw0 hw1 width x
  isCauchy := by
    intro epsilon he m n hm hn
    have h := (meanCauchy hw0 hw1 width x).bound
      (centerTolerance epsilon) (centerTolerance_positive he) m n hm hn
    exact leEv_trans (leEv_of_equiv (centerApprox_distance hw0 hw1 width x _ _))
      (leEv_of_le (ofQ'_le_ofQ' (coefficient_square_bound he h)))

/-- An actual vector in the same joint carrier as the physical-time map. -/
def centeredVector (x : PhysicalSpan width) : JointCompletion hw0 hw1 width :=
  Quotient.mk (D).completionSetoid (centeredStream hw0 hw1 width x)

theorem centeredStream_seq (x : PhysicalSpan width) (n : Nat) :
    (centeredStream hw0 hw1 width x).seq n =
      centerApprox x ((mean hw0 hw1 width x).approx n) := rfl

theorem centeredStream_modulus (x : PhysicalSpan width) :
    (centeredStream hw0 hw1 width x).modulus = centeredRate hw0 hw1 width x := rfl

/-- Scalar convergence uses the displayed modulus in both indices. -/
theorem mean_approximations_converge (x : PhysicalSpan width) :
    ConvergesTo (fun n => ofQ' ((mean hw0 hw1 width x).approx n))
      (mean hw0 hw1 width x) := by
  intro epsilon he
  let c := meanCauchy hw0 hw1 width x
  exact ⟨c.M epsilon, fun n hn => ⟨c.M epsilon, fun k hk => c.bound epsilon he n k hn hk⟩⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.centerTolerance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.centerTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.coefficient_square_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.mean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.meanCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.centeredRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.centeredStream
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.centeredVector
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.centeredStream_seq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.centeredStream_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream.mean_approximations_converge
