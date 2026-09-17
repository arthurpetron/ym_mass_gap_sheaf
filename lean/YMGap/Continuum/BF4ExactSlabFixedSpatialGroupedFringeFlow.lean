/-
# One grouped fringe test coupled to the original signed family

Prepend a single unit factor with the jump of the entire actual fringe
residual. The product remains the ORIGINAL kinetic weight. The mixed
term is the existing family flow evaluated at this fringe sum, so it is
retained exactly, without an orthogonality assumption or a factor-two
estimate combining two independent energy bounds.

The result still exposes a signed cost. It is not a uniform cost bound,
a completed-sector gap, or a physical-mass statement.
-/

import YMGap.Continuum.QuaternionHaarUnitFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeFlow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity energy energy_identity)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound (headFloor_le_oneThirtySecond)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension (certificate_extend)
open YMGap.Continuum.SU2QuaternionHaarCertificateLift (lift_certificate)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarFiniteFamilyDual
open YMGap.Continuum.QuaternionHaarUnitFamily

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] spatialWeight baseLinks kineticWeight

private theorem edge_pin (w : Q') (K width n : Nat) (tests : Nat → RatPoly)
    (p q : RatPoly) :
    quaternionHaar (N width+N width) (polyMul (endpointWeight w K width n)
      (polyMul (product (family w K width tests)) (polyMul p q))) ≈
      weightedPair (N width+N width) (edgeDensity w K width (terminalMessage w K width n)) p q := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  exact haar_of_coeff ((((family_product_pin w K width tests).mul_right _).mul_left _).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.var 3) (.mul (.mul (.var 2) (.var 0)) (.var 1))) (by decide)
      (fun
        | 0 => a | 1 => liftBoundary (N width) a | 2 => kineticWeight w K width
        | _ => polyMul p q)))

set_option maxHeartbeats 800000 in
/-- The original family and ONE whole fringe test share the same original
energy. The active--fringe cross term remains signed and explicit. -/
theorem grouped_fringe_marginal_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (tests seeds : Nat → RatPoly)
    (ht : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (tests i))
    (hc : ∀ i, i < N width → RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (tests i))) polyZero)
    (hs : ∀ i, i ∈ fringeBlocks width → SupportedQuaternionBlocks (N width) (seeds i))
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let r := fringeSum w K width n seeds
    let L := marginalFlow w K width n tests f + marginalPair w K width n f r
    headFloor w*(L*L) ≤ energy w K width (terminalMessage w K width n) f *
      (marginalCost w K width n tests + marginalPair w K width n r r +
        ((2 : Q')*headFloor w)*marginalFlow w K width n tests r) := by
  let r := fringeSum w K width n seeds
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let ps := family w K width tests
  let mu := endpointWeight w K width n
  let x := jump (N width) r
  let z := jump (N width) f
  let L := marginalFlow w K width n tests f + marginalPair w K width n f r
  let C := marginalCost w K width n tests + marginalPair w K width n r r +
    ((2 : Q')*headFloor w)*marginalFlow w K width n tests r
  let E := energy w K width (terminalMessage w K width n) f
  have hr := fringeSum_supported w K width n seeds hs
  have ha := supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)
  let A := (spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
    (terminalMessage_certificate hw0 hw1 K width hK n)
  have h := prepend_unit_dual (headFloor_positive hw0 hw1)
    (Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)) ps
    (familyFloorCertificates hw0 hw1 K width hK tests)
    (family_tests_supported w K width tests ht)
    ((certificate_extend (N width) ha A).mul (lift_certificate (N width) A))
    (jump_supported hf) (jump_supported hr)
  have hb : quaternionHaar (N width+N width) (polyMul mu (polyMul (product ps) (polyMul x z))) ≈
      (2 : Q')*marginalPair w K width n f r :=
    Q'.eqv_trans _ _ _ (edge_pin w K width n tests x z)
      (Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm x z).mul_right _))
        (fringeSum_jump_pairing w K width n seeds hs hf))
  have hd : quaternionHaar (N width+N width) (polyMul mu (polyMul (product ps) (polyMul x x))) ≈
      (2 : Q')*marginalPair w K width n r r :=
    Q'.eqv_trans _ _ _ (edge_pin w K width n tests x x)
      (fringeSum_jump_pairing w K width n seeds hs hr)
  have hj : quaternionHaar (N width+N width) (polyMul mu (polyMul (product ps) (polyMul z z))) ≈
      (2 : Q')*E :=
    Q'.eqv_trans _ _ _ (edge_pin w K width n tests z z)
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_symm (energy_identity w K width (terminalMessage_supported w K width n) hf)))
  have hx : quaternionHaar (N width+N width) (polyMul mu (polyMul x (flow ps))) ≈
      (2 : Q')*marginalFlow w K width n tests r :=
    Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.mul_comm x (flow ps)).mul_left mu))
      (flowPair_pin w K width n tests ht hc hr)
  have hl : flowPair w K width n tests f +
      quaternionHaar (N width+N width) (polyMul mu (polyMul (product ps) (polyMul x z))) ≈ (2 : Q')*L :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (flowPair_pin w K width n tests ht hc hf) hb)
      (Q'.eqv_symm (Q'.mul_add_eqv _ _ _))
  have hcost : signedCost w K width n tests +
      quaternionHaar (N width+N width) (polyMul mu (polyMul (product ps) (polyMul x x))) +
      ((2 : Q')*headFloor w)*quaternionHaar (N width+N width) (polyMul mu (polyMul x (flow ps))) ≈
      (2 : Q')*C :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_eqv_congr' (signedCost_pin w K width n tests ht hc) hd)
        (Q'.mul_eqv_congr_left _ _ _ hx))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
          (.mul (.mul (.const 2) (.var 2)) (.mul (.const 2) (.var 3))))
        (.mul (.const 2) (.add (.add (.var 0) (.var 1)) (.mul (.mul (.const 2) (.var 2)) (.var 3))))
        (by decide) (fun
          | 0 => marginalCost w K width n tests | 1 => marginalPair w K width n r r
          | 2 => headFloor w | _ => marginalFlow w K width n tests r))
  have hleft : headFloor w*((2 : Q')*L*((2 : Q')*L)) ≈ (4 : Q')*(headFloor w*(L*L)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.const 2) (.var 1)) (.mul (.const 2) (.var 1))))
      (.mul (.const 4) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (by decide)
      (fun | 0 => headFloor w | _ => L)
  have hright : ((2 : Q')*E)*((2 : Q')*C) ≈ (4 : Q')*(E*C) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
      (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => E | _ => C)
  have he := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hl) (Q'.mul_eqv_congr_left _ _ _ hl))) hleft))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hj) (Q'.mul_eqv_congr_left _ _ _ hcost)) hright)))
  exact Q'.le_of_mul_le_mul_left he (by decide : (0 : Q') < (4 : Q'))

end YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeFlow

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialGroupedFringeFlow.grouped_fringe_marginal_energy
