/-
# Fixed-parameter relative reconstruction for the ORIGINAL signed energy

The last-step terminal band eliminates the source-dependent reconstruction
coefficient: Z0*transferWeightedCap <= comparisonKappa*Z1. Only the fixed
positive kinetic floor is cancelled. No terminal mass or partition is
inverted, and signed sources with zero squared norm remain included.

The resulting computed relative onset depends on nome, spatial width and
tolerance, but not on late cutoff, terminal depth or source degree. This
does not supply a changing-family signed-cost bound or a scaling-uniform
modulus; the original energy and boundary drift remain literal.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferWeightedBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRatio
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition (iterateStep_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight weightedMass terminalMessage

private theorem smul_neg (p : RatPoly) : RatPolyCoeffEqv (polySmul (-1) p) (polyNeg p) :=
  (cap_mul_left (-1) p).symm.trans
    (coeffEvalExpr_eqv_of_normalize_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
      (by decide) (fun _ => p))

private theorem weighted_product_cap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) {p h : RatPoly} {c : Q'}
    (P : Certificate (N width) p)
    (H : Certificate (N width) (polyAdd (cap c) (polyNeg h))) :
    weightedMass w K width (polyMul p h) ≤ c*weightedMass w K width p := by
  have hn := weightedMass_nonnegative hw0 hw1 K width hK (P.mul H)
  have hd : RatPolyCoeffEqv (polyMul p (polyAdd (cap c) (polyNeg h)))
      (polyAdd (polyMul p (cap c)) (polySmul (-1) (polyMul p h))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 2) (.neg (.var 1))))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => p | 1 => h | _ => cap c)).trans
      ((RatPolyCoeffEqv.refl _).add (smul_neg _).symm)
  have hc : weightedMass w K width (polyMul p (cap c)) ≈ c*weightedMass w K width p :=
    Q'.eqv_trans _ _ _ (weightedMass_congr w K width
      ((RatPolyCoeffEqv.mul_comm _ _).trans (cap_mul_left c p)))
      (weightedMass_smul w K width c p)
  have he := Q'.eqv_trans _ _ _ (weightedMass_congr w K width hd)
    (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.add_eqv_congr' hc
        (Q'.eqv_trans _ _ _ (weightedMass_smul w K width (-1) _)
          (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hn (Q'.le_of_eqv he))

private theorem fixed_band_comparison (F U r Z0 Z1 m a E : Q')
    (hF : (0 : Q') < F) (hU : (0 : Q') ≤ U) (ha : (0 : Q') ≤ a)
    (hE : (0 : Q') ≤ E) (hr : F*r ≈ U)
    (hz0 : Z0 ≤ (U*m)*a) (hlo : (F*m)*E ≤ a) (hz1 : F*(a*a) ≤ Z1) :
    Z0*(U*E) ≤ (r*r)*Z1 := by
  have hUE := Q'.mul_nonneg _ _ hU hE
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _ (F*(U*E)) hz0
    (Q'.mul_nonneg _ _ (Q'.le_of_lt hF) hUE)
  have hl : (F*(U*E))*Z0 ≈ F*(Z0*(U*E)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.var 0) (.mul (.var 3) (.mul (.var 1) (.var 2)))) (by decide)
      (fun | 0 => F | 1 => U | 2 => E | _ => Z0)
  have hh : (F*(U*E))*((U*m)*a) ≈ ((U*U)*a)*((F*m)*E) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 1) (.var 3)) (.var 4)))
      (.mul (.mul (.mul (.var 1) (.var 1)) (.var 4))
        (.mul (.mul (.var 0) (.var 3)) (.var 2))) (by decide)
      (fun | 0 => F | 1 => U | 2 => E | 3 => m | _ => a)
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ ((U*U)*a) hlo
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hU hU) ha)
  have he : ((U*U)*a)*a ≈ (U*U)*(a*a) := Q'.mul_assoc_eqv _ _ _
  have hfirst : F*(Z0*(U*E)) ≤ (U*U)*(a*a) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
      (Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hh)
        (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv he))))
  have h3 := Q'.mul_le_mul_of_nonneg_left _ _ F hfirst (Q'.le_of_lt hF)
  have he3 : F*((U*U)*(a*a)) ≈ (U*U)*(F*(a*a)) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))))
      (.mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => F | 1 => U | _ => a)
  have h4 := Q'.mul_le_mul_of_nonneg_left _ _ (U*U) hz1 (Q'.mul_nonneg _ _ hU hU)
  have hrr : F*(F*(r*r)) ≈ U*U :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (by decide) (fun | 0 => F | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hr)
        (Q'.mul_eqv_congr_left _ _ _ hr))
  have he4 : F*(F*((r*r)*Z1)) ≈ (U*U)*Z1 :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 2))))
      (.mul (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1)))) (.var 2))
      (by decide) (fun | 0 => F | 1 => r | _ => Z1))
      (Q'.mul_eqv_congr_right _ _ Z1 hrr)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_of_mul_le_mul_left (Q'.le_trans' _ _ _ h3
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv he3)
        (Q'.le_trans' _ _ _ h4 (Q'.ge_of_eqv he4)))) hF) hF

set_option maxHeartbeats 2000000 in
/-- The actual last-step band pays the original transfer cap relative to Z1.
Only the fixed kinetic floor is cancelled, never a terminal mass. -/
theorem block_partition_cap_le_comparisonKappa {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) :
    let A := terminalMessage w K width (n+t)
    weightedMass w K width (polyMul A A) * transferWeightedCap w K width ≤
      comparisonKappa hw0 hw1 width *
        weightedMass w K width (polyMul A (transferStep w K width A)) := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let F := kineticFloor w width
  let U := kineticCap w width
  let m := weightedMass w K width (terminalMessage w K width (n+t-1))
  let a := weightedMass w K width A
  let E := weightedMass w K width polyOne
  let PA := terminalMessage_certificate hw0 hw1 K width hK (n+t)
  have hA := terminalMessage_supported w K width (n+t)
  have bands := blockWindowCertificates hw0 hw1 K width hK n t hdepth
  have hz0 : weightedMass w K width (polyMul A A) ≤ (U*m)*a :=
    weighted_product_cap hw0 hw1 K width hK PA bands.2
  have hlo0 := weightedMass_product_floor hw0 hw1 K width hK
    (Certificate.one (N width)) bands.1
  have hlo : (F*m)*E ≤ a := Q'.le_trans' _ _ _ hlo0
    (Q'.le_of_eqv (weightedMass_congr w K width (RatPolyCoeffEqv.one_mul A)))
  have hz10 := weightedMass_product_floor hw0 hw1 K width hK PA
    (transferStepLowerCertificate hw0 hw1 K width hK hA PA)
  have hz1 : F*(a*a) ≤ weightedMass w K width (polyMul A (transferStep w K width A)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv F a a)) hz10
  have hr : F*comparisonStretch hw0 hw1 width ≈ U :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => F | 1 => U | _ => Q'.recipPos F (kineticFloor_positive hw0 hw1 width)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left U _ _ (Q'.mul_recipPos_eqv F (kineticFloor_positive hw0 hw1 width)))
        (Q'.mul_one_eqv U))
  exact fixed_band_comparison F U (comparisonStretch hw0 hw1 width)
    _ _ m a E (kineticFloor_positive hw0 hw1 width)
    (kineticCap_nonnegative hw0 width)
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+t)))
    (weightedMass_nonnegative hw0 hw1 K width hK (Certificate.one _)) hr hz0 hlo hz1

private theorem source_supported (w : Q') (K width n t : Nat) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) :
    SupportedQuaternionBlocks (N width)
      (originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)) :=
  iterateStep_supported (kineticWeight_supported w K width) (spatialWeight_supported w K width)
    t (supported_polyMul (terminalMessage_supported w K width n) hp)

/-- The complete reconstruction coefficient has no remaining source/depth
dependence after extracting the original surviving partition and norm. -/
theorem blockEnergyErrorCoefficient_relative_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    blockEnergyErrorCoefficient w K width n t psi ≤
      (2*(1+comparisonKappa hw0 hw1 width)) *
        (weightedMass w K width (polyMul A (transferStep w K width A)) *
          weightedMass w K width (polyMul b b)) := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square b (source_supported w K width n t hp))
  have h := Q'.add_le_add_left Z1 _ _
    (block_partition_cap_le_comparisonKappa hw0 hw1 K width hK n t hdepth)
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ 2 h (by decide : (0 : Q') ≤ 2)
  have h3 := Q'.mul_le_mul_of_nonneg_right _ _ B h2 hB
  exact Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.mul (.const 2) (.add (.var 0) (.mul (.var 1) (.var 0)))) (.var 2))
    (.mul (.mul (.const 2) (.add (.const 1) (.var 1))) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => Z1 | 1 => comparisonKappa hw0 hw1 width | _ => B)))

/-- Computed fixed-nome/width relative onset, independent of late cutoff,
source, terminal length and polynomial degree. -/
def blockEnergyRelativeErrorCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (width : Nat) (epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff (mixRate hw0 hw1 width)
    (2*(1+comparisonKappa hw0 hw1 width)) epsilon

/-- The scalar error budget consumed by the original complete signed-cost
ceiling is relative to the SAME Z1*ell(b^2), including a zero signed source. -/
theorem blockEnergyError_relative_budget_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    (mixRate hw0 hw1 width)^k * blockEnergyErrorCoefficient w K width n t psi ≤
      epsilon * (weightedMass w K width (polyMul A (transferStep w K width A)) *
        weightedMass w K width (polyMul b b)) := by
  dsimp only
  let A := terminalMessage w K width (n+t)
  let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
  let Z1 := weightedMass w K width (polyMul A (transferStep w K width A))
  let B := weightedMass w K width (polyMul b b)
  have hZ1 : (0 : Q') ≤ Z1 := Q'.le_of_lt
    (weightedMass_pair_transfer_positive hw0 hw1 K width hK
      (terminalMessage_supported w K width (n+t))
      (terminalMessage_certificate hw0 hw1 K width hK (n+t))
      (terminalMessage_certificate hw0 hw1 K width hK (n+t))
      (terminalMessage_mass_positive hw0 hw1 K width hK (n+t))
      (terminalMessage_mass_positive hw0 hw1 K width hK (n+t)))
  have hB : (0 : Q') ≤ B := weightedMass_nonnegative hw0 hw1 K width hK
    (Certificate.square b (source_supported w K width n t hp))
  have hcoef : (0 : Q') ≤ 2*(1+comparisonKappa hw0 hw1 width) :=
    Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2)
      (Q'.zero_le_add _ _ Q'.zero_le_one (comparisonKappa_nonnegative hw0 hw1 width))
  have hgeo := PositiveContractionResidual.geometric_bound
    (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width)
    hcoef hepsilon k hk
  have hfirst := Q'.mul_le_mul_of_nonneg_left _ _ ((mixRate hw0 hw1 width)^k)
    (blockEnergyErrorCoefficient_relative_le hw0 hw1 K width hK n t hdepth hp)
    (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) k)
  have hsecond := Q'.mul_le_mul_of_nonneg_right _ _ (Z1*B) hgeo (Q'.mul_nonneg _ _ hZ1 hB)
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)) hsecond)

/-- SAME original energy/drift reconstruction with the computed relative
onset. Neither signed drift nor the surviving norm is replaced. -/
theorem blockConditionalRatio_energy_error_relative_tolerance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (K width : Nat) (hK : headCutoff w ≤ K)
    (n t : Nat) (hdepth : 1 ≤ n+t) {psi : RatPoly}
    (hp : SupportedQuaternionBlocks (N width) psi)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (k : Nat)
    (hk : blockEnergyRelativeErrorCutoff hw0 hw1 width epsilon ≤ k) :
    let A := terminalMessage w K width (n+t)
    let b := originalBlockTransfer w K width t (polyMul (terminalMessage w K width n) psi)
    let phi := blockConditionalRatio hw0 hw1 K width hK n t psi k
    Q'.abs (clearedRayleighCost w K width A b +
      -(weightedMass w K width (polyMul A A)*energy w K width A phi +
        boundaryDrift w K width A phi)) ≤
      epsilon * (weightedMass w K width (polyMul A (transferStep w K width A)) *
        weightedMass w K width (polyMul b b)) :=
  Q'.le_trans' _ _ _
    (blockConditionalRatio_energy_error_abs_le hw0 hw1 K width hK n t hdepth hp k)
    (blockEnergyError_relative_budget_tolerance hw0 hw1 K width hK n t hdepth hp epsilon hepsilon k hk)

end YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.block_partition_cap_le_comparisonKappa
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.blockEnergyErrorCoefficient_relative_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.blockEnergyRelativeErrorCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.blockEnergyError_relative_budget_tolerance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.blockConditionalRatio_energy_error_relative_tolerance
