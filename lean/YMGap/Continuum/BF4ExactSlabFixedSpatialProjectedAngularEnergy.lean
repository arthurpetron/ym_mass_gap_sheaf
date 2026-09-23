/-
# Original slab energy with inactive Haar residual retained

The proper active product heat map averages the inactive coordinates.  This
leaf applies the general projected-input angular estimate to the complete
original endpoint source `u=(V*g)*f`.  The inactive Haar residual and the
signed endpoint-source correction are both retained explicitly.
-/

import YMGap.Continuum.SU2QuaternionProductHeatInactiveAngularDefect
import YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedAngularEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily (labels_perm_range)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy
  (endpointSource bareEnergy correction energy_eq_bare_add_correction)
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject)
open YMGap.Continuum.SU2QuaternionHaarFamilyPythagoras (familyResidual)
open YMGap.Continuum.SU2QuaternionProductHeatInactiveAngularDefect
  (productMap_defect_le_projected_angular)
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularSquare)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity

local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight activeBlocks

private theorem fringe_active_perm_range (width : Nat) :
    (fringeBlocks width ++ activeBlocks width).Perm (List.range (N width)) := by
  have hswap : (fringeBlocks width ++ activeBlocks width).Perm
      (activeBlocks width ++ fringeBlocks width) :=
    List.perm_append_comm
  exact hswap.trans (by simpa [labels] using labels_perm_range width)

/-- The original finite temporal energy is controlled by the inactive
conditional-Haar residual, the angular energy of the projected endpoint
source, and the unchanged signed endpoint-source correction. -/
theorem energy_le_fringeResidual_add_projectedAngular_add_correction
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : sufficientCutoff w ≤ K) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (hb : 0 < N width) :
    energy w K width g f ≤
      quaternionHaar (N width)
          (polyMul
            (familyResidual (fringeBlocks width)
              (polyMul (endpointSource w K width g) f))
            (familyResidual (fringeBlocks width)
              (polyMul (endpointSource w K width g) f))) +
        ((2 * ((1 : Q') - w)) *
          finSum (fun i => quaternionHaar (N width)
            (blockAngularSquare i
              (familyProject (fringeBlocks width)
                (polyMul (endpointSource w K width g) f)))) (N width)) +
      correction w K width g f := by
  let u := polyMul (endpointSource w K width g) f
  have hu : SupportedQuaternionBlocks (N width) u :=
    supported_polyMul
      (supported_polyMul (spatialWeight_supported w K width) hg) hf
  have hN : N width - 1 + 1 = N width := by omega
  have hnot : ∀ i, i ∈ fringeBlocks width → i ∉ activeBlocks width :=
    fun i hi => ((fringeBlocks_mem_iff width i).mp hi).2
  have hbare : bareEnergy w K width g f ≤
      quaternionHaar (N width)
          (polyMul (familyResidual (fringeBlocks width) u)
            (familyResidual (fringeBlocks width) u)) +
        ((2 * ((1 : Q') - w)) *
          finSum (fun i => quaternionHaar (N width)
            (blockAngularSquare i (familyProject (fringeBlocks width) u))) (N width)) := by
    unfold bareEnergy
    simpa only [u, hN] using
      productMap_defect_le_projected_angular (N width - 1) hw0 hw1 K hK
        (activeBlocks width) (fringeBlocks width)
        (by simpa only [hN] using activeBlocks_lt width)
        (by simpa only [hN] using fringeBlocks_lt width) hnot
        (by simpa only [hN] using fringe_active_perm_range width) u
        (by simpa only [hN] using hu)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (energy_eq_bare_add_correction w K width g f))
    (Q'.add_le_add_right _ _ (correction w K width g f) hbare)

#print axioms energy_le_fringeResidual_add_projectedAngular_add_correction

/-- The original (unprojected) angular energy of the COMPLETE endpoint
source suffices. The inactive residual and signed correction remain intact. -/
theorem energy_le_fringeResidual_add_angular_add_correction
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : sufficientCutoff w ≤ K) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (hb : 0 < N width) :
    energy w K width g f ≤
      quaternionHaar (N width)
          (polyMul
            (familyResidual (fringeBlocks width)
              (polyMul (endpointSource w K width g) f))
            (familyResidual (fringeBlocks width)
              (polyMul (endpointSource w K width g) f))) +
        ((2 * ((1 : Q') - w)) *
          finSum (fun i => quaternionHaar (N width)
            (blockAngularSquare i (polyMul (endpointSource w K width g) f))) (N width)) +
      correction w K width g f := by
  let u := polyMul (endpointSource w K width g) f
  have hu : SupportedQuaternionBlocks (N width) u :=
    supported_polyMul
      (supported_polyMul (spatialWeight_supported w K width) hg) hf
  have hc : (0 : Q') ≤ 2*((1 : Q')-w) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
  have hangular := Q'.mul_le_mul_of_nonneg_left _ _ _
    (SU2QuaternionHaarFamilyAngularContraction.familyProject_angularSum_le
      (N width) (fringeBlocks width) (fringeBlocks_lt width) u hu) hc
  exact Q'.le_trans' _ _ _
    (energy_le_fringeResidual_add_projectedAngular_add_correction hw0 hw1 K width hK g f hg hf hb)
    (Q'.add_le_add_right _ _ (correction w K width g f)
      (Q'.add_le_add_left _ _ _ hangular))

#print axioms energy_le_fringeResidual_add_angular_add_correction

end YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedAngularEnergy
