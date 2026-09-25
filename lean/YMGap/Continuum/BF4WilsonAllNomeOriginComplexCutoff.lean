/-
# Origin plaquette complex-rate cutoff

The origin plaquette supplies a strictly positive two-step rate on the SAME
all-nome Wilson carrier after two explicit padding layers.  This file
consumes that positivity to construct the existing complex coefficient
cutoff.  The result is finite-parameter and coefficient-level: it does not
identify a continuum time scale, a physical mass, or a uniform rate.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexGap
import YMGap.Continuum.BF4WilsonAllNomePlaquetteRelativeFloor
import YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation

namespace YMGap.Continuum.BF4WilsonAllNomeOriginComplexCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
  (originFace originFace_mem)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteRelativeFloor
  (twoStepRate_positive_of_plaquette)
open YMGap.Continuum.BF4WilsonAllNomeComplexGap
  (complexRateCutoff complexRateCutoff_bound)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat)

/- The positive rate is discharged by the literal origin plaquette, with
   `width + 2` carrying the two strict padding layers used by the response
   construction. -/
theorem origin_twoStepRate_positive :
    (0 : Q') < twoStepRate hw0 hw1 (width + 2) := by
  apply twoStepRate_positive_of_plaquette hw0 hw1 (width + 2) originFace
  · exact originFace_mem (width + 1)
  · intro l hl
    exact plaquette_active_after_padding (by omega : 1 < width + 2)
      originFace (originFace_mem 0) l hl

/- The scalar coefficient cutoff is now an unconditional consequence of the
   supplied origin plaquette, apart from the explicit positive error target. -/
theorem origin_complexRateCutoff_bound (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) :
    (twoStepRate hw0 hw1 (width + 2)) ^
        (complexRateCutoff hw0 hw1 (width + 2) epsilon) ≤ epsilon := by
  exact complexRateCutoff_bound hw0 hw1 (width + 2) epsilon hepsilon
    (origin_twoStepRate_positive hw0 hw1 width)

#print axioms origin_twoStepRate_positive
#print axioms origin_complexRateCutoff_bound

end YMGap.Continuum.BF4WilsonAllNomeOriginComplexCutoff
