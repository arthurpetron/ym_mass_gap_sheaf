/-
# Scale-zero dyadic square / plaquette bridge

The geometrically scaled square with `scale = 0` is the unit square.  This
file identifies its literal source loop with the origin spatial plaquette and
transports the existing positive lag-two plaquette-response floor to the
dyadic-square excitation on the SAME completed Wilson carrier.

This is a finite same-parameter bridge.  It does not identify carriers across
scales, prove a changing-scale response floor, or close A03/A05, continuum,
physical-mass, or Clay obligations.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation
import YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponsePadded

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicScaleZeroPlaquetteBridge

set_option autoImplicit false
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSquare
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (orientedPlaquetteBoundary)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponse
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponsePadded
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- The origin face used by the existing plaquette excitation certificate. -/
abbrev originFace : Z4Plaq :=
  YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation.originFace

private theorem sourceLoop_ext {width : Nat} (p q : SourceLoop width)
    (hs : p.start = q.start) (he : p.edges = q.edges) : p = q := by
  cases p
  cases q
  cases hs
  cases he
  rfl

/-- At unit side, the square word is exactly the origin plaquette word. -/
theorem square_zero_edges_eq_origin_boundary :
    (square 0).edges = orientedPlaquetteBoundary originFace := by
  rfl

/-- The padded scale-zero square and the origin plaquette are the same
source loop, including their dependent compatibility and physical witnesses. -/
theorem paddedSquare_zero_eq_originPlaquette
    {width : Nat} (hwidth : side 0 < width) :
    let hface := spatialFaces_mono
      (Nat.le_of_lt (by simpa [side] using hwidth))
      (YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation.originFace_mem 0)
    paddedSquare 0 width hwidth = plaquetteLoop originFace hface := by
  dsimp
  apply sourceLoop_ext
  · rfl
  · exact (paddedSquare_edges 0 width hwidth).trans
      square_zero_edges_eq_origin_boundary

/-- The dyadic scale-zero centered state is the existing plaquette centered
state, after transporting along the literal loop equality. -/
theorem dyadicExcitation_zero_eq_plaquetteExcitation
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (hwidth : side 0 < width) :
    dyadicExcitation hw0 hw1 0 width hwidth =
      plaquetteExcitation hw0 hw1 width originFace
        (spatialFaces_mono
          (Nat.le_of_lt (by simpa [side] using hwidth))
          (YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation.originFace_mem 0)) := by
  unfold dyadicExcitation plaquetteExcitation
  congr 1

/-- The checked positive lag-two plaquette floor now applies to the literal
scale-zero dyadic-square excitation on the same completed carrier. -/
theorem dyadicExcitation_zero_twoStep_floor
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (hwidth : side 0 < width) :
    let hface := spatialFaces_mono
      (Nat.le_of_lt (by simpa [side] using hwidth))
      (YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation.originFace_mem 0)
    RCle (Rq (twoStepFloor hw0 hw1 width originFace hface))
      (completedInner hw0 hw1
        (dyadicExcitation hw0 hw1 0 width hwidth).val
        (completedTime hw0 hw1 2
          (dyadicExcitation hw0 hw1 0 width hwidth).val)) := by
  dsimp
  let hface := spatialFaces_mono
    (Nat.le_of_lt (by simpa [side] using hwidth))
    (YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation.originFace_mem 0)
  have hp := padded_plaquetteExcitation_twoStep_floor
    (w := w) hw0 hw1 (base := 1) (width := width)
    (by simpa [side] using hwidth) originFace
    (YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation.originFace_mem 0)
  rw [dyadicExcitation_zero_eq_plaquetteExcitation hw0 hw1 hwidth]
  exact hp

#print axioms square_zero_edges_eq_origin_boundary
#print axioms paddedSquare_zero_eq_originPlaquette
#print axioms dyadicExcitation_zero_eq_plaquetteExcitation
#print axioms dyadicExcitation_zero_twoStep_floor

end YMGap.Continuum.BF4WilsonAllNomeDyadicScaleZeroPlaquetteBridge
