/-
# Non-erasure of the actual plaquette orbit at EVERY finite time

At every strict nome and fixed width, the already constructed positive
two-step relative response supplies the all-nome joint-carrier propagation
theorem. The existing time-zero norm floor then gives the explicit positive
rational `relativeFloor^n * starRatio` below the squared norm of the time-n image.
The image stays in the existing vacuum complement and is not the actual zero.

The initial active-link guard is retained; strict spatial padding discharges
it. Nome and width are fixed during the construction. The witness is allowed
to decay with n and deteriorate with nome/width. This is NOT fixed-physical-
time survival, near-one calibration or continuum Yang--Mills. In particular,
the previous ceiling on the coarse relativeFloor remains unchanged.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredPairing (jointCompletedZero_norm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (faceExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "rho" => relativeFloor hw0 width face hf
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- The bound is rational data at each literal lattice lag, with all
parameters retained. No representative or modulus is chosen. -/
def timeNormFloor (n : Nat) : Q' := (rho)^n * starRatio w

include hw1 in
theorem timeNormFloor_positive (n : Nat) :
    (0 : Q') < timeNormFloor hw0 width face hf n :=
  Q'.mul_pos (HKPos.pow_pos (relativeFloor_positive hw0 hw1 width face hf) n)
    (starRatio_positive hw0 hw1)

/-- The SAME original connected even response has an explicit positive
floor at every even natural lag; it is not a new abstract moment sequence. -/
theorem faceExcitation_even_response_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (n : Nat) :
    RCle (Rq (timeNormFloor hw0 width face hf n)) (B v (T (2*n) v)) := by
  have h := evenResponse_geometric_lower hw0 hw1 width v rho
    (Q'.le_of_lt (relativeFloor_positive hw0 hw1 width face hf))
    (faceExcitation_relative_floor hw0 hw1 width face hf hactive) n
  have hz := RCscale_mono (Q'.pow_nonneg _
    (Q'.le_of_lt (relativeFloor_positive hw0 hw1 width face hf)) n)
    (faceExcitation_norm_floor hw0 hw1 width face hf)
  exact RCle_trans hz h

/-- No loss of the actual finite-time image in the existing completion. -/
theorem faceExcitation_time_norm_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (n : Nat) :
    RCle (Rq (timeNormFloor hw0 width face hf n)) (B (T n v) (T n v)) := by
  rw [completedInner_even_diagonal]
  exact faceExcitation_even_response_floor hw0 hw1 width face hf hactive n

/-- The explicit positive squared-norm floor rules out the actual completed zero. -/
theorem faceExcitation_time_ne_zero
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (n : Nat) : T n v ≠ jointEmbedSpan hw0 hw1 width (zero width) := by
  intro hz
  have h := faceExcitation_time_norm_floor hw0 hw1 width face hf hactive n
  rw [hz, jointCompletedZero_norm] at h
  have hle : timeNormFloor hw0 width face hf n ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (timeNormFloor_positive hw0 hw1 width face hf n) hle)

/-- The initial relative certificate also holds on each of these actual
nonzero time-translated vectors. No improvement toward one is asserted. -/
theorem faceExcitation_time_relative_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (n : Nat) :
    RCle (RCscale rho (B (T n v) (T n v))) (B (T n v) (T 2 (T n v))) :=
  timeImage_relative_floor hw0 hw1 width v rho
    (Q'.le_of_lt (relativeFloor_positive hw0 hw1 width face hf))
    (faceExcitation_relative_floor hw0 hw1 width face hf hactive) n

/-- The finite strict-padding theorem supplies every active-link premise. -/
theorem padded_faceExcitation_time_norm_floor {base width : Nat}
    (hwidth : base < width) (face : Z4Plaq) (hf : face ∈ spatialFaces base) (n : Nat) :
    let hface := spatialFaces_mono (Nat.le_of_lt hwidth) hf
    let probe := (faceExcitation hw0 hw1 width face hface).val
    RCle (Rq (timeNormFloor hw0 width face hface n))
      (completedInner hw0 hw1 width (jointCompletedTime hw0 hw1 width n probe)
        (jointCompletedTime hw0 hw1 width n probe)) :=
  faceExcitation_time_norm_floor hw0 hw1 width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf) n

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse.timeNormFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse.timeNormFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse.faceExcitation_even_response_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse.faceExcitation_time_norm_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse.faceExcitation_time_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse.faceExcitation_time_relative_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteOrbitResponse.padded_faceExcitation_time_norm_floor
