/-
# Spatial padding wrapper for the same-carrier all-nome two-step response

This file isolates the spatial-face inclusion dependency from the core
two-step response compiler.  It adds no new estimate: it transports the
already checked width-level floor along `spatialFaces_mono` and the existing
active-block padding lemma.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse
import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponsePadded

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

theorem padded_plaquetteExcitation_twoStep_floor {base width : Nat}
    (hwidth : base < width) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let hface := spatialFaces_mono (Nat.le_of_lt hwidth) hf
    RCle (Rq (twoStepFloor hw0 hw1 width face hface))
      (completedInner hw0 hw1
        (plaquetteExcitation hw0 hw1 width face hface).val
        (completedTime hw0 hw1 2
          (plaquetteExcitation hw0 hw1 width face hface).val)) :=
  plaquetteExcitation_twoStep_floor hw0 hw1 width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf)

#print axioms padded_plaquetteExcitation_twoStep_floor

end YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponsePadded
