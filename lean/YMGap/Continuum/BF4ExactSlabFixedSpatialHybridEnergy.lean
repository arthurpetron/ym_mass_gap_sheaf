/-
# Original interacting transfer and endpoint energy through the local sweep

The actual temporal-face list supplies distinct, in-range pairs; these
guards are proved from the original geometry rather than supplied again.
The complete signed source V*g*f enters the hybrid kinetic sweep. The
signed correction involving P(V*g)-V*g remains unchanged and explicit.
No small energy, variance comparison, OS gap, or scaling result is asserted.
-/

import YMGap.Continuum.SU2QuaternionProductHeatHybridSweep
import YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionProductHeatHybridSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt activeBlocks_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (transferStep_eq_productMap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight activeBlocks

/-- Original interacting transfer, against every insertion on its original
one-slice Haar carrier. Inactive fringe slots remain Haar-averaged. -/
theorem transferStep_hybrid_carrier (w : Q') (K width : Nat) (f : RatPoly) :
    HaarCarrierEqv (N width) (transferStep w K width f)
      (hybridMap (N width) w K (activeBlocks width)
        (polyMul (spatialWeight w K width) f)) := by
  rw [transferStep_eq_productMap]
  exact (hybridMap_carrier (N width) w K (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width) _).symm

/-- The local sweep now reaches the original energy consumer. This is an
equality, not an upper bound: the endpoint correction has no assigned sign. -/
theorem energy_eq_hybrid_add_correction (w : Q') (K width : Nat) (g f : RatPoly) :
    energy w K width g f ≈
      let u := polyMul (endpointSource w K width g) f
      (quaternionHaar (N width) (polyMul u u) +
        -(quaternionHaar (N width)
          (polyMul u (hybridMap (N width) w K (activeBlocks width) u)))) +
        correction w K width g f := by
  have h := hybridMap_quadratic (N width) w K (activeBlocks width)
    (activeBlocks_nodup width) (activeBlocks_lt width)
    (polyMul (endpointSource w K width g) f)
  exact Q'.eqv_trans _ _ _ (energy_eq_bare_add_correction w K width g f)
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ h.symm))
      (Q'.eqv_refl _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy.transferStep_hybrid_carrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy.energy_eq_hybrid_add_correction
