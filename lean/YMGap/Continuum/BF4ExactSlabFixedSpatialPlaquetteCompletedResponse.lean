/-
# A positive one-step response on the EXISTING all-nome completion

The same original Wilson connected scalar is the inner product of the
existing centered plaquette vector with its existing one-step physical time
translate. The explicit finite floor survives cutoff and time removal.
Strict spatial padding supplies the activity condition for a base plaquette.

The constant depends on nome and width. This does not supply a spatial- or
spacing-uniform response, finite physical mass calibration, a Hamiltonian,
or a continuum Yang--Mills theory.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor
import YMGap.Continuum.BF4WilsonAllNomePlaquetteMeanPin
import YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCompletedResponse

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
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws (jointPairing_symm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm (jointCenteredMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner (completedInner)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime (jointCompletedTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance
open YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor
open YMGap.Continuum.BF4WilsonAllNomePlaquetteMeanPin
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "x" => faceSpan width face hf
local notation "v" => Subtype.val (faceExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width

/-- The bound is on the original centered joint moment, with both mean
factors identified with the SAME completed pairing against the unit. -/
theorem jointCenteredMoment_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    leEv (ofQ' (uniformFloor hw0 width)) (jointCenteredMoment hw0 hw1 width 1 x x) := by
  have hm := jointPairing_mean hw0 hw1 width face hf
  have hu := (jointPairing_symm hw0 hw1 width (unit width) x).trans hm
  have hp := equiv_sub (jointPairing_lag hw0 hw1 width face hf 1)
    ((mul_congr_left hm).trans (TrigSignedAdd.mul_congr_right hu))
  exact leEv_trans (connected_response_floor hw0 hw1 width face hf hactive)
    (leEv_of_equiv hp.symm)

/-- Positive ORIGINAL one-step response on the already constructed vector
and operator. Neither a replacement carrier nor a new positive-response
assumption appears. -/
theorem faceExcitation_response_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    RCle (Quotient.mk crealSetoid (ofQ' (uniformFloor hw0 width))) (B v (T 1 v)) := by
  rw [faceExcitation_correlator_pin]
  exact jointCenteredMoment_floor hw0 hw1 width face hf hactive

/-- For a base plaquette, strict padding discharges activity by finite
geometry. Each width retains its OWN explicit constant. -/
theorem padded_faceExcitation_response_floor {base width : Nat}
    (hwidth : base < width) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let probe := (faceExcitation hw0 hw1 width face
      (spatialFaces_mono (Nat.le_of_lt hwidth) hf)).val
    RCle (Quotient.mk crealSetoid (ofQ' (uniformFloor hw0 width)))
      (completedInner hw0 hw1 width probe (jointCompletedTime hw0 hw1 width 1 probe)) :=
  faceExcitation_response_floor hw0 hw1 width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCompletedResponse

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCompletedResponse.jointCenteredMoment_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCompletedResponse.faceExcitation_response_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteCompletedResponse.padded_faceExcitation_response_floor
