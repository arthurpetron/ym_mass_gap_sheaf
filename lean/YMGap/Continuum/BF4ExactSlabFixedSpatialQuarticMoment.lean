/-
# Original finite slab selected-link quartic moment

All inputs to the signed head/tail estimate are supplied by the ORIGINAL
spatial and terminal source and the retained spectator heat factors. The
right side is the SAME odd partition. This controls one selected relative
link, not a full-word mixed radial moment or centered interacting variance.
-/

import YMGap.Continuum.SU2QuaternionHeatQuarticBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialQuarticMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport (qpow)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialHeatNomeComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (eraseIndex mem_of_mem_erase)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.SU2QuaternionHeatQuarticExpansion (defect)
open YMGap.Continuum.SU2QuaternionHeatQuarticBound

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage oddMass

/-- Quantitative quartic link correction with no missing source certificate,
no inverse heat floor, and no discarded finite-cutoff coefficient. The
nome/split and original positivity cutoffs are all explicit. -/
theorem selected_quartic_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (S K width depth i : Nat) (hS : 1 ≤ S) (hK : S+3 ≤ K)
    (hhead : headCutoff w ≤ K) (hi : i ∈ activeBlocks width)
    (hhalf : (1 : Q') ≤ 2*w^(4*(S+2)))
    (hq : qpow w (S*S) ≤ Q'.mkPos 1 8 (by decide)) :
    selectedInsertion w K width depth i
      (polyMul
        (polyMul (defect (scalarAt (N width+i) i)) (defect (scalarAt (N width+i) i)))
        (heatPrefix w K (scalarAt (N width+i) i))) ≤
      quarticBudget w S * oddMass w K width depth := by
  let a := endpointSource w K width (terminalMessage w K width depth)
  let rest := eraseIndex i (activeBlocks width)
  let W := productHeat (N width) w K rest
  have hrest : ∀ j, j ∈ rest → j < N width :=
    fun j hj => activeBlocks_lt width j (mem_of_mem_erase i hj)
  have ha : SupportedQuaternionBlocks (N width) a :=
    supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width depth)
  let A : Certificate (N width) a :=
    (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hhead).mul
      (terminalMessage_certificate hw0 hw1 K width hhead depth)
  have R : Certificate (N width+N width) (polyMul W (polyMul a (liftBoundary (N width) a))) :=
    (productHeatCertificate (N width) hw0 hw1 K hhead rest hrest).mul
      ((certificate_extend (N width) ha A).mul (lift_certificate (N width) A))
  have h := prefix_quartic_bound (activeBlocks_lt width i hi)
    (productHeat_supported (N width) w K rest hrest)
    (productHeat_quadratic_nonnegative (N width) w (Q'.le_of_lt hw0) K rest hrest)
    ha R (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) S K hS hK hhalf hq
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (selectedMass_pin w K width depth i hi)))

#print axioms selected_quartic_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialQuarticMoment
