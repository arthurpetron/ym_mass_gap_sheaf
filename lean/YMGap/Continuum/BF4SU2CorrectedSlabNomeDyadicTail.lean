/-
# Affine dyadic cutoff schedule for the corrected SU(2) slab

The arbitrary-nome affine dyadic schedule for the ambient interacting box is
transported to the corrected slab by the existing supported zero-extension
injection.  At fixed nome and slab extent, the retained cutoff is affine in
the requested dyadic precision and controls every later corrected-slab cutoff
increment.

No physical-scale uniformity, thermodynamic limit, continuum theory, or mass
gap is asserted.

## Axiom gate

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
import YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance

namespace YMGap.Continuum.BF4SU2CorrectedSlabNomeDyadicTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeDyadicTolerance
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

/-- The corrected-slab increment inherits the affine dyadic ambient schedule
through the supported zero-extension subset. -/
theorem slabPhysicalNomeCutoffIncrement_le_dyad_linear
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent targetPrecision : Nat) {laterCutoff : Nat}
    (hlater :
      physicalNomeTensorDyadicRetainedCutoff
          w
          (plaquetteEdgeCount (extent + 1))
          targetPrecision <= laterCutoff) :
    slabParametricKCutoffIncrement
        w
        (physicalNomeTensorDyadicRetainedCutoff
          w
          (plaquetteEdgeCount (extent + 1))
          targetPrecision)
        laterCutoff extent <=
      dyad targetPrecision := by
  exact Q'.le_trans' _ _ _
    (slabParametricKCutoffIncrement_le_ambient
      (w := w) (Q'.le_of_lt hw0))
    (physicalNomeCutoffIncrement_le_dyad_linear
      hw0 hw1 (extent + 1) targetPrecision hlater)

#print axioms slabPhysicalNomeCutoffIncrement_le_dyad_linear

end YMGap.Continuum.BF4SU2CorrectedSlabNomeDyadicTail
