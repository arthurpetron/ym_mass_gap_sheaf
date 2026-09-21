/-
# A positive two-step response on the SAME all-nome fixed-width carrier

Completed Cauchy--Schwarz and exact time balance turn the proved one-step
floor delta into delta^2 <= B(v,v)*B(v,T(2)v). The existing covariance cap
at lag zero gives the explicit positive norm ceiling P. Multiplication by
1/P then returns delta^2/P as a positive two-step floor.

Every vector, pairing and time map is the existing original fixed-width
joint completion. Nome and width remain explicit. No spatial-union carrier,
changing-spacing family, physical mass or continuum survival is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCompletedResponse
import YMGap.Continuum.WilsonMatrixCoefficientDecayHandoff

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCompletedResponse
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm (jointCenteredMoment_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance
  (separationCap separationCap_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement (completedInner_time_balance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

private theorem square_mono {a b : RC} (ha : RCnonneg a) (hab : RCle a b) :
    RCle (RCmul a a) (RCmul b b) := by
  have h1 := RCmul_mono_nonneg_left ha hab
  have h2 := RCmul_mono_nonneg_left (RCle_trans ha hab) hab
  rw [RCmul_comm b a] at h2
  exact RCle_trans h1 h2

private theorem inverse_scale (P : Q') (hP : (0 : Q') < P) (a : RC) :
    RCscale (Q'.recipPos P hP) (RCmul (Rq P) a) = a := by
  refine Quotient.inductionOn a ?_
  intro A
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv P hP)))
      (Q'.one_mul_eqv _))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "x" => faceSpan width face hf
local notation "v" => Subtype.val (faceExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width

/-- A computed positive cap; the original presentation's coefficient budget
has no nome, cutoff, external depth or time-lag input. -/
def normCeiling : Q' := 1 + separationCap width (x).val (x).val

theorem normCeiling_positive : (0 : Q') < normCeiling width face hf :=
  Q'.pos_add_nonneg (by decide : (0 : Q') < 1)
    (separationCap_nonnegative width (x).val (x).val)

/-- The lag-zero covariance estimate bounds this exact completed norm. -/
theorem faceExcitation_norm_ceiling : RCle (B v v) (Rq (normCeiling width face hf)) := by
  have hp := faceExcitation_correlator_pin hw0 hw1 width face hf 0
  rw [jointCompletedTime_zero] at hp
  rw [hp]
  apply leEv_trans (jointCenteredMoment_le hw0 hw1 width 0 x x)
  apply leEv_le_ofQ'_of_approx_le
  intro n
  change separationCap width (x).val (x).val * 1 ≤ normCeiling width face hf
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ 1 (by decide : (0 : Q') ≤ 1))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- Exact physical-time balance, on the existing completion and every input. -/
theorem completed_oneStep_diagonal (z : JointCompletion hw0 hw1 width) :
    B (T 1 z) (T 1 z) = B z (T 2 z) :=
  (completedInner_time_balance hw0 hw1 width 1 z (T 1 z)).trans
    (congrArg (fun y => B z y) (jointCompletedTime_add hw0 hw1 width 1 1 z).symm)

/-- The positive one-step lower bound is squared before applying completed
Cauchy--Schwarz. No positivity of the whole one-step operator is assumed. -/
theorem faceExcitation_response_square
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Rq (uniformFloor hw0 width * uniformFloor hw0 width))
      (RCmul (B v v) (B v (T 2 v))) := by
  have hd : RCnonneg (Rq (uniformFloor hw0 width)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt (uniformFloor_positive hw0 hw1 width))
  have h := RCle_trans
    (square_mono hd (faceExcitation_response_floor hw0 hw1 width face hf hactive))
    (completedInner_cauchySchwarz hw0 hw1 width v (T 1 v))
  rw [completed_oneStep_diagonal] at h
  exact h

/-- Explicit positive rational response witness for physical lag two. -/
def twoStepFloor : Q' :=
  (uniformFloor hw0 width * uniformFloor hw0 width) *
    Q'.recipPos (normCeiling width face hf) (normCeiling_positive width face hf)

include hw1 in
theorem twoStepFloor_positive : (0 : Q') < twoStepFloor hw0 width face hf :=
  Q'.mul_pos (Q'.mul_pos (uniformFloor_positive hw0 hw1 width)
    (uniformFloor_positive hw0 hw1 width)) (Q'.recipPos_pos _ _)

/-- Positive two-step response of the actual existing centered excitation. -/
theorem faceExcitation_twoStep_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Rq (twoStepFloor hw0 width face hf)) (B v (T 2 v)) := by
  have hnonneg : RCnonneg (B v (T 2 v)) := by
    rw [← completed_oneStep_diagonal]
    exact completedInner_nonnegative hw0 hw1 width (T 1 v)
  have hcap := RCmul_mono_nonneg_left hnonneg
    (faceExcitation_norm_ceiling hw0 hw1 width face hf)
  rw [RCmul_comm (B v (T 2 v)) (B v v),
    RCmul_comm (B v (T 2 v)) (Rq (normCeiling width face hf))] at hcap
  have h := RCscale_mono
    (Q'.le_of_lt (Q'.recipPos_pos (normCeiling width face hf) (normCeiling_positive width face hf)))
    (RCle_trans (faceExcitation_response_square hw0 hw1 width face hf hactive) hcap)
  rw [inverse_scale] at h
  have hp : RCscale (Q'.recipPos (normCeiling width face hf) (normCeiling_positive width face hf))
      (Rq (uniformFloor hw0 width * uniformFloor hw0 width)) =
      Rq (twoStepFloor hw0 width face hf) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_comm_eqv _ _))
  rw [hp] at h
  exact h

/-- A homogeneous Rayleigh lower witness obtained using the same explicit
norm cap. No assertion that this witness tends to one is made. -/
def relativeFloor : Q' := twoStepFloor hw0 width face hf *
  Q'.recipPos (normCeiling width face hf) (normCeiling_positive width face hf)

include hw1 in
theorem relativeFloor_positive : (0 : Q') < relativeFloor hw0 width face hf :=
  Q'.mul_pos (twoStepFloor_positive hw0 hw1 width face hf) (Q'.recipPos_pos _ _)

/-- The relative witness multiplies the ACTUAL squared norm, not its cap.
This supplies a genuine same-object lower Rayleigh inequality. -/
theorem faceExcitation_relative_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (RCscale (relativeFloor hw0 width face hf) (B v v)) (B v (T 2 v)) := by
  have h := RCscale_mono (Q'.le_of_lt (relativeFloor_positive hw0 hw1 width face hf))
    (faceExcitation_norm_ceiling hw0 hw1 width face hf)
  have hp : RCscale (relativeFloor hw0 width face hf) (Rq (normCeiling width face hf)) =
      Rq (twoStepFloor hw0 width face hf) := by
    apply Quotient.sound
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.mul_recipPos_eqv (normCeiling width face hf) (normCeiling_positive width face hf))))
        (Q'.mul_one_eqv _))
  rw [hp] at h
  exact RCle_trans h (faceExcitation_twoStep_floor hw0 hw1 width face hf hactive)

/-- A returned witness for the SAME actual two-step pairing, not an assumed
response certificate or a different spatial-union vector. -/
def positiveResponse
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    Σ' c : Q', ((0 : Q') < c) ×' RCle (Rq c) (B v (T 2 v)) :=
  ⟨twoStepFloor hw0 width face hf, twoStepFloor_positive hw0 hw1 width face hf,
    faceExcitation_twoStep_floor hw0 hw1 width face hf hactive⟩

/-- Finite strict spatial padding discharges every active-link premise. -/
theorem padded_faceExcitation_twoStep_floor {base width : Nat}
    (hwidth : base < width) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let hface := spatialFaces_mono (Nat.le_of_lt hwidth) hf
    let probe := (faceExcitation hw0 hw1 width face hface).val
    RCle (Rq (twoStepFloor hw0 width face hface))
      (completedInner hw0 hw1 width probe (jointCompletedTime hw0 hw1 width 2 probe)) :=
  faceExcitation_twoStep_floor hw0 hw1 width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.normCeiling_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.faceExcitation_norm_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.completed_oneStep_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.faceExcitation_response_square
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.twoStepFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.twoStepFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.faceExcitation_twoStep_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.relativeFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.relativeFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.faceExcitation_relative_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.positiveResponse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse.padded_faceExcitation_twoStep_floor
