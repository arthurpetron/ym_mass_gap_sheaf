/-
# Time increments controlled by the ACTUAL derivative image

The exact refinement square has nonnegative pairing with the coarser
quotient: the pairing is a sum of two positive original mixed moments.
Consequently the squared quotient norms increase to the squared norm
of the already constructed J. Finite time averages give
  ||T2 x - A_t T2 x||^2 <= t^2 ||J x||^2
at every nonnegative dyadic time, with constant one and no small-time
restriction. This is an IMAGE-norm bound, not a preimage-norm bound.
Its consumer is extension through the two-coordinate graph approximants.
No full-domain differentiation, physical time normalization, continuum
limit or all-group Clay conclusion is asserted. Fixed SU(2), nome 1/1024,
fixed spacing and the existing T2-time unit are unchanged.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeClosedGraph

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg)
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicPairingLimit (representativeInner)
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit (pairingRepresentative)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (smul_norm)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear (sequenceAction_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages
open YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative
open YMGap.Continuum.BF4ExactSlabThermodynamicScalarRows (pairing_converges limit_le_of_eventual)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X

theorem defect_refine (depth : Nat) (x : Completion) :
    defect depth x=completedAdd (defect (depth+1) x)
      (generator (depth+1) (defect (depth+1) x)) := by
  unfold defect
  rw [show generator (depth+1) (completedSub x (generator (depth+1) x))=
    completedSub (generator (depth+1) x) (generator (depth+1) (generator (depth+1) x)) from
      sequenceAction_sub _ _ _,generator_square,sub_telescope]

/-- The cross term is positive on the ORIGINAL completion, not an auxiliary norm. -/
theorem refinement_cross_nonnegative (depth : Nat) (x : Completion) :
    RCnonneg (B (defectPower (depth+1) 2 x) (defect depth x)) := by
  rw [defect_refine,completedInner_add_right]
  have h0 : B (defectPower (depth+1) 2 x) (defect (depth+1) x)=moment (depth+1) x 0 3 := by
    rw [defectPower_symmetric]
    rfl
  have h1 : B (defectPower (depth+1) 2 x) (generator (depth+1) (defect (depth+1) x))=
      moment (depth+1) x 1 3 := by
    rw [defectPower_symmetric]
    change B x (defectPower (depth+1) 2 (time (depth+1) 1 (defect (depth+1) x)))=_
    rw [← time_defectPower]
    rfl
  rw [h0,h1]
  have h := RCadd_le_add (moment_nonnegative (depth+1) x 0 3) (moment_nonnegative (depth+1) x 1 3)
  rw [rc_zero_add] at h
  exact h

theorem quotient_cross_nonnegative (depth : Nat) (x : Completion) :
    RCnonneg (B (completedSub (differenceQuotient (depth+1) x) (differenceQuotient depth x))
      (differenceQuotient depth x)) := by
  rw [quotient_step]
  unfold differenceQuotient
  rw [completedInner_smul_left,completedInner_smul_right]
  have h := RCscale_mono (ofNat_nonneg (2^depth)) (RCscale_mono (ofNat_nonneg (2^depth))
    (refinement_cross_nonnegative depth (twoStepTransfer x)))
  simp only [RCscale_RCzero] at h
  exact h

theorem norm_add_of_cross_nonnegative (x y : Completion) (h : RCnonneg (B y x)) :
    RCle (B x x) (B (completedAdd x y) (completedAdd x y)) := by
  have hxy : RCnonneg (B x y) := by rw [completedInner_symm]; exact h
  rw [completedInner_add_left,completedInner_add_right,completedInner_add_right]
  have hb := RCadd_le_add (RCadd_le_add (RCle_refl (B x x)) hxy)
    (RCadd_le_add h (completedInner_nonnegative y))
  simp only [rc_add_zero] at hb
  exact hb

theorem quotient_norm_step (depth : Nat) (x : Completion) :
    RCle (B (differenceQuotient depth x) (differenceQuotient depth x))
      (B (differenceQuotient (depth+1) x) (differenceQuotient (depth+1) x)) := by
  have h := norm_add_of_cross_nonnegative (differenceQuotient depth x)
    (completedSub (differenceQuotient (depth+1) x) (differenceQuotient depth x))
    (quotient_cross_nonnegative depth x)
  rw [completedAdd_comm,completedSub_add_cancel] at h
  exact h

theorem quotient_norm_mono (m n : Nat) (hmn : m≤n) (x : Completion) :
    RCle (B (differenceQuotient m x) (differenceQuotient m x))
      (B (differenceQuotient n x) (differenceQuotient n x)) := by
  induction hmn with
  | refl => exact RCle_refl _
  | step h ih => exact RCle_trans ih (quotient_norm_step _ x)

/-- Passing to the EXISTING explicit quotient limit gives the missing image estimate. -/
theorem quotient_image_bound (depth : Nat) (x : Completion) :
    RCle (B (differenceQuotient depth x) (differenceQuotient depth x))
      (B (derivativeAction x) (derivativeAction x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact limit_le_of_eventual
    (convergesTo_const (representativeInner (quotientRepresentative depth X) (quotientRepresentative depth X)))
    (pairing_converges (quotientRows X) (quotientRows X)) depth
    (fun n hn => quotient_norm_mono depth n hn (point X))

theorem meshQuotient_image_bound (depth n : Nat) (x : Completion) :
    RCle (B (meshQuotient depth n x) (meshQuotient depth n x))
      (B (derivativeAction x) (derivativeAction x)) := by
  rw [meshQuotient_average]
  apply average_norm_bound
  intro j _
  exact RCle_trans (time_contraction depth j (differenceQuotient depth x)) (quotient_image_bound depth x)

theorem mesh_increment_quotient (depth n : Nat) (x : Completion) :
    completedSub (twoStepTransfer x) (time depth (n+1) (twoStepTransfer x))=
      completedSmul (value ⟨depth,n+1⟩) (meshQuotient depth n x) := by
  unfold meshQuotient
  rw [completedSmul_mul,completedSmul_congr (mesh_normalization depth n),completedSmul_one]

/-- Uniform in ALL mesh increments, with the actual derivative image on the right. -/
theorem mesh_increment_image_bound (depth steps : Nat) (x : Completion) :
    RCle (completedDist (twoStepTransfer x) (time depth steps (twoStepTransfer x)))
      (RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩) (B (derivativeAction x) (derivativeAction x))) := by
  cases steps with
  | zero =>
      change RCle (completedDist (twoStepTransfer x) (twoStepTransfer x)) _
      rw [(completedDist_zero_iff _ _).mpr rfl]
      have h := RCscale_mono (SumOfSquares.q_mul_self_nonneg (value ⟨depth,0⟩))
        (completedInner_nonnegative (derivativeAction x))
      rw [RCscale_RCzero] at h
      exact h
  | succ n =>
      unfold completedDist
      rw [mesh_increment_quotient,smul_norm]
      exact RCscale_mono (SumOfSquares.q_mul_self_nonneg _) (meshQuotient_image_bound depth n x)

end YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.defect_refine
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.refinement_cross_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.quotient_cross_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.norm_add_of_cross_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.quotient_norm_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.quotient_norm_mono
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.quotient_image_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.meshQuotient_image_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.mesh_increment_quotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeImageBound.mesh_increment_image_bound
