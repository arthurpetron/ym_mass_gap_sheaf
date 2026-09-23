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
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionProductHeatHybridSweep
open YMGap.Continuum.SU2QuaternionProductHeatPositive (productMap_nonnegative)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
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

/-! ### Signed correction budget

The hybrid identity is useful only after the endpoint defect has an explicit
finite budget.  Keep that missing estimate as a named Type-level input rather
than hiding it in an opaque constant or asserting its sign.  The compiler
below is the elementary order consequence that turns such a budget into an
energy upper bound.  It is deliberately independent of any continuum,
thermodynamic, or OS interpretation.
-/

/-- A constructive finite budget for the signed endpoint correction.

This is a producer interface, not an inhabitant supplied by the current
finite calculation.  A future geometric/covariance argument must provide the
nonnegative `budget` and prove `correction_abs_le` for the same signed source
and cutoff appearing in `energy_eq_hybrid_add_correction`.
-/
structure SignedEndpointCorrectionBudget
    (w : Q') (K width : Nat) (g f : RatPoly) : Type where
  budget : Q'
  budget_nonneg : (0 : Q') ≤ budget
  correction_abs_le :
    Q'.abs (correction w K width g f) ≤ budget

/-- Compile a signed endpoint budget into an upper bound for the original
finite temporal energy. -/
theorem energy_le_bare_add_signedCorrectionBudget
    (w : Q') (K width : Nat) (g f : RatPoly)
    (hbudget : SignedEndpointCorrectionBudget w K width g f) :
    energy w K width g f ≤
      bareEnergy w K width g f + hbudget.budget := by
  have heq : energy w K width g f ≤
      bareEnergy w K width g f + correction w K width g f :=
    Q'.le_of_eqv (energy_eq_bare_add_correction w K width g f)
  have hcorr : correction w K width g f ≤ hbudget.budget :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self (correction w K width g f))
      hbudget.correction_abs_le
  exact Q'.le_trans' _ _ _ heq
    (Q'.add_le_add_left (bareEnergy w K width g f)
      (correction w K width g f) hbudget.budget hcorr)

private theorem endpointSource_mul_supported
    (w : Q') (K width : Nat) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width)
      (polyMul (endpointSource w K width g) f) := by
  unfold endpointSource
  exact supported_polyMul
    (supported_polyMul (spatialWeight_supported w K width) hg) hf

/-- The bare product-heat energy is bounded above by the source square once
the source is supported.  This is only finite Haar positivity; it is not a
strict contraction or a physical spectral-gap estimate. -/
theorem bareEnergy_le_endpointSquare
    (w : Q') (K width : Nat) (g f : RatPoly)
    (hw : (0 : Q') ≤ w)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) :
    bareEnergy w K width g f ≤
      quaternionHaar (N width)
        (polyMul (polyMul (endpointSource w K width g) f)
          (polyMul (endpointSource w K width g) f)) := by
  let u := polyMul (endpointSource w K width g) f
  have hu : SupportedQuaternionBlocks (N width) u :=
    endpointSource_mul_supported w K width g f hg hf
  have hcross : (0 : Q') ≤
      quaternionHaar (N width)
        (polyMul u (productMap (N width) w K (activeBlocks width) u)) :=
    productMap_nonnegative (N width) w hw K (activeBlocks width)
      (activeBlocks_lt width) u hu
  have hneg : -(quaternionHaar (N width)
      (polyMul u (productMap (N width) w K (activeBlocks width) u))) ≤
      (0 : Q') := Q'.nonpos_neg_of_nonneg hcross
  unfold bareEnergy
  change quaternionHaar (N width) (polyMul u u) +
      -(quaternionHaar (N width)
        (polyMul u (productMap (N width) w K (activeBlocks width) u))) ≤
      quaternionHaar (N width) (polyMul u u)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left (quaternionHaar (N width) (polyMul u u))
      (-(quaternionHaar (N width)
        (polyMul u (productMap (N width) w K (activeBlocks width) u))))
      0 hneg)
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- The first genuinely quantitative consequence of the correction budget:
the original finite energy is bounded by the explicit endpoint source square
plus the supplied signed-defect budget. -/
theorem energy_le_endpointSquare_add_signedCorrectionBudget
    (w : Q') (K width : Nat) (g f : RatPoly)
    (hw : (0 : Q') ≤ w)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f)
    (hbudget : SignedEndpointCorrectionBudget w K width g f) :
    energy w K width g f ≤
      quaternionHaar (N width)
        (polyMul (polyMul (endpointSource w K width g) f)
          (polyMul (endpointSource w K width g) f)) + hbudget.budget := by
  have hbare := bareEnergy_le_endpointSquare w K width g f hw hg hf
  have henergy := energy_le_bare_add_signedCorrectionBudget w K width g f hbudget
  exact Q'.le_trans' _ _ _ henergy
    (Q'.add_le_add_right (bareEnergy w K width g f)
      (quaternionHaar (N width)
        (polyMul (polyMul (endpointSource w K width g) f)
          (polyMul (endpointSource w K width g) f)))
      hbudget.budget hbare)

end YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy.transferStep_hybrid_carrier
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy.energy_eq_hybrid_add_correction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy.bareEnergy_le_endpointSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy.energy_le_endpointSquare_add_signedCorrectionBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialHybridEnergy.energy_le_bare_add_signedCorrectionBudget
