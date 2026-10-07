/-
# Complete product-heat angular energy paid by ONE norm decrement

The original computed path tree supplies nonnegative diagonal masses and
the exact squared attenuation of the output. The scalar geometric estimate
then bounds the entire angular energy without counting coordinates or planes.
No assumed joint orthogonality, positive heat floor, source inverse, or
cutoff-largeness condition is needed. This is ordinary Haar, not a weighted
conditional-score estimate or a completed OS norm comparison.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSmoothing
import YMGap.Continuum.SU2HeatProductReversePoincare

namespace YMGap.Continuum.SU2QuaternionProductHeatReversePoincare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionCyclicHeatModeExpansion
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionCyclicDiagonalRemainder
open YMGap.Continuum.SU2QuaternionCyclicPathReassembly
open YMGap.Continuum.SU2QuaternionCyclicPathHeatEigen
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.SU2QuaternionProductHeatSmoothing
open YMGap.Continuum.SU2HeatProductTaylorRemainder
open YMGap.Continuum.SU2HeatProductReversePoincare
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Exact output square on the SAME input-dependent path tree. The squared
attenuation is derived from symmetry and the checked leaf heat action. -/
theorem productMap_square_grouped (tail : Nat) (w : Q') (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    H (tail+1) (polyMul (productMap (tail+1) w K (List.range (tail+1)) p)
      (productMap (tail+1) w K (List.range (tail+1)) p)) ≈
      leafSum tail (tail+1) p p (fun ds =>
        productAttenuation w K ds*productAttenuation w K ds) := by
  let Pp := productMap (tail+1) w K (List.range (tail+1)) p
  have hsum : H (tail+1) (polyMul Pp Pp) ≈
      leafSum tail (tail+1) p Pp (productAttenuation w K) :=
    Q'.eqv_trans _ _ _ (productMap_modeFold tail w K p hp Pp)
      (leafSum_modeFold tail (tail+1) p Pp _)
  apply Q'.eqv_trans _ _ _ hsum
  apply leafSum_pairing_congr
  intro ds hlen hpath
  have hs := path_supported tail ds p hp
  have hpair : H (tail+1) (polyMul Pp (pathPiece tail p ds)) ≈
      productAttenuation w K ds*H (tail+1) (polyMul p (pathPiece tail p ds)) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _
        (kineticPair_symm (tail+1) w K (List.range (tail+1))
          (fun i hi => List.mem_range.mp hi) (pathPiece tail p ds) p hs hp)
        (full_path_heat_pairing tail w K p hp ds hlen hpath p hp))
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hpair)
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

/-- Cleared global reverse-Poincare estimate for the ORIGINAL finite product
heat. The RHS includes just one original norm, regardless of extent. Both
nome endpoints, constant channels and omitted cutoff channels are retained. -/
theorem productMap_angular_norm_loss_le (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (tail+1) p) :
    (1-w*w)*angularListSum (tail+1) (List.range (tail+1))
        (productMap (tail+1) w K (List.range (tail+1)) p) +
      (w*w)*H (tail+1) (polyMul
        (productMap (tail+1) w K (List.range (tail+1)) p)
        (productMap (tail+1) w K (List.range (tail+1)) p)) ≤
      (w*w)*H (tail+1) (polyMul p p) := by
  let Pp := productMap (tail+1) w K (List.range (tail+1)) p
  let u := w*w
  let energyWeight := fun ds => totalCasimir ds*
    (productAttenuation w K ds*productAttenuation w K ds)
  let squareWeight := fun ds => productAttenuation w K ds*productAttenuation w K ds
  have he : angularListSum (tail+1) (List.range (tail+1)) Pp ≈
      leafSum tail (tail+1) p p energyWeight :=
    Q'.eqv_trans _ _ _
      (haar_activeCasimir_self (tail+1) (List.range (tail+1))
        (fun i hi => List.mem_range.mp hi) Pp).symm
      (productMap_casimir_grouped tail w K p hp)
  have hn := productMap_square_grouped tail w K p hp
  have hleft : (1-u)*angularListSum (tail+1) (List.range (tail+1)) Pp +
      u*H (tail+1) (polyMul Pp Pp) ≈
      leafSum tail (tail+1) p p (fun ds => (1-u)*energyWeight ds+u*squareWeight ds) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ he)
        (Q'.mul_eqv_congr_left _ _ _ hn))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (leafSum_smul tail (tail+1) p p (1-u) energyWeight).symm
          (leafSum_smul tail (tail+1) p p u squareWeight).symm)
        (leafSum_add tail (tail+1) p p _ _).symm)
  have hle : leafSum tail (tail+1) p p
      (fun ds => (1-u)*energyWeight ds+u*squareWeight ds) ≤
      leafSum tail (tail+1) p p (fun _ => u) := by
    apply leafSum_pairing_le
    intro ds hlen hpath
    have h := product_squared_reverse_poincare hw0 hw1 K ds
    have ha := Q'.add_le_add_right _ _ (u*squareWeight ds) h
    have hleftWeight : (1-u)*energyWeight ds+u*squareWeight ds ≈
        (1-u)*totalCasimir ds*squareWeight ds+u*squareWeight ds :=
      Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _).symm (Q'.eqv_refl _)
    have hrightWeight : u*(1-squareWeight ds)+u*squareWeight ds ≈ u :=
      poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.add (.const 1) (.neg (.var 1))))
          (.mul (.var 0) (.var 1))) (.var 0) (by decide)
        (fun | 0 => u | _ => squareWeight ds)
    have hw := Q'.le_trans' _ _ _ (Q'.le_of_eqv hleftWeight)
      (Q'.le_trans' _ _ _ ha (Q'.le_of_eqv hrightWeight))
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hw
      (full_path_pairing_nonnegative tail p hp ds hlen hpath)
  have hright : leafSum tail (tail+1) p p (fun _ => u) ≈
      u*H (tail+1) (polyMul p p) :=
    Q'.eqv_trans _ _ _
      (leafSum_congr tail (tail+1) p p _ _ (fun _ _ => (Q'.mul_one_eqv u).symm))
      (Q'.eqv_trans _ _ _ (leafSum_smul tail (tail+1) p p u (fun _ => (1 : Q')))
        (Q'.mul_eqv_congr_left u _ _ (full_leafSum_one tail p p hp)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hle (Q'.le_of_eqv hright))

end YMGap.Continuum.SU2QuaternionProductHeatReversePoincare

#print axioms YMGap.Continuum.SU2QuaternionProductHeatReversePoincare.productMap_square_grouped
#print axioms YMGap.Continuum.SU2QuaternionProductHeatReversePoincare.productMap_angular_norm_loss_le
