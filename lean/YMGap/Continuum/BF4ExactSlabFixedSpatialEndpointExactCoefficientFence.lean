/-
# Exact plaquette Young coefficient and its endpoint-floor fence

The signed `w^12,w^32` channel cost yields a smaller scalar ceiling than
the quadratic geometric budget. This is a fence on that particular
certificate, not a lower bound on the actual energy or a survival theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointExactCoefficientFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit (plaquetteChannelCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelHeatFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)

/-- The signed coefficient of the source-weighted plaquette square. -/
def squareCoefficient (w : Q') : Q' :=
  (1 : Q') + qpow w 32 - (2 : Q') * qpow w 12

/-- The sharp ceiling obtainable from only `0 ≤ H[q²f²] ≤ 4H[q²]`.
The branch is decidable in the project's constructive rational carrier. -/
def exactChannelCeiling (w : Q') : Q' :=
  let beta := squareCoefficient w
  if beta ≤ 0 then (1 : Q') - qpow w 32
  else ((1 : Q') - qpow w 32) + (4 : Q') * beta

private theorem not_le_zero_nonnegative {a : Q'} (h : ¬ a ≤ (0 : Q')) :
    (0 : Q') ≤ a := by
  change ¬ a.num * ((0 : Q').den : Int) ≤ (0 : Q').num * (a.den : Int) at h
  change (0 : Q').num * (a.den : Int) ≤ a.num * ((0 : Q').den : Int)
  omega

private theorem sourceSquare_nonnegative (width : Nat) (face : Z4Plaq)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    (0 : Q') ≤ rawSourceSquare width face q := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have hf : SupportedQuaternionBlocks (N width) f :=
    character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hs := (Certificate.square (polyMul q f) (supported_polyMul hq hf)).haar_nonnegative
  exact Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (haar_of_coeff
    (RatPolyCoeffEqv.mul_four_swap q f q f)))

private theorem sourceSquare_le_four_mass (width : Nat) (face : Z4Plaq)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    rawSourceSquare width face q ≤ (4 : Q') * rawSourceMass width q := by
  have h := Q'.add_le_self_of_nonneg (rawSourceSquare width face q)
    (geometricSourceCost width face q)
    (geometricSourceCost_nonnegative width face q hq)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by
    unfold geometricSourceCost
    exact poly_identity_of_normal_eq
      (.add (.var 0) (.add (.mul (.const 4) (.var 1)) (.neg (.var 0))))
      (.mul (.const 4) (.var 1)) (by decide)
      (fun | 0 => rawSourceSquare width face q | _ => rawSourceMass width q)))

/-- The exact signed `w^12,w^32` plaquette cost has no `960(1-w)^2` loss. -/
theorem plaquetteChannelCost_le_exactCeiling (w : Q') (width : Nat)
    (face : Z4Plaq) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    plaquetteChannelCost width face w q ≤
      exactChannelCeiling w * rawSourceMass width q := by
  let beta := squareCoefficient w
  let A := rawSourceMass width q
  let F := rawSourceSquare width face q
  have hF0 : (0 : Q') ≤ F := sourceSquare_nonnegative width face q hq
  have hF4 : F ≤ (4 : Q') * A := sourceSquare_le_four_mass width face q hq
  have hcol : plaquetteChannelCost width face w q ≈
      ((1 : Q') - qpow w 32) * A + beta * F := by
    simpa only [beta, squareCoefficient, A, F] using
      plaquetteChannelCost_collected w width face q
  by_cases hb : beta ≤ (0 : Q')
  · have hterm : beta * F ≤ (0 : Q') * F :=
      Q'.mul_le_mul_of_nonneg_right beta 0 F hb hF0
    have hbound := Q'.add_le_add_left (((1 : Q') - qpow w 32) * A)
      (beta * F) ((0 : Q') * F) hterm
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcol)
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (by
        simp only [exactChannelCeiling, beta, hb, ↓reduceIte]
        exact poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.mul (.const 0) (.var 2)))
          (.mul (.var 0) (.var 1)) (by decide)
          (fun | 0 => (1 : Q') - qpow w 32 | 1 => A | _ => F))))
  · have hb0 : (0 : Q') ≤ beta := not_le_zero_nonnegative hb
    have hterm : beta * F ≤ beta * ((4 : Q') * A) :=
      Q'.mul_le_mul_of_nonneg_left F ((4 : Q') * A) beta hF4 hb0
    have hbound := Q'.add_le_add_left (((1 : Q') - qpow w 32) * A)
      (beta * F) (beta * ((4 : Q') * A)) hterm
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcol)
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (by
        simp only [exactChannelCeiling, beta, hb, ↓reduceIte]
        exact poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1))
            (.mul (.var 2) (.mul (.const 4) (.var 1))))
          (.mul (.add (.var 0) (.mul (.const 4) (.var 2))) (.var 1))
          (by decide)
          (fun | 0 => (1 : Q') - qpow w 32 | 1 => A | _ => beta))))

/-- Even the exact signed scalar ceiling dominates the nome gap. -/
theorem gap_le_exactChannelCeiling {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (1 : Q') - w ≤ exactChannelCeiling w := by
  have hpow : qpow w 32 ≤ w := by
    have h := YMGap.Continuum.SU2HeatProductFirstMomentFloor.qpow_antitone_exponent
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) (a := 1) (b := 32) (by decide)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by
      change (1 : Q') * w ≈ w
      exact Q'.one_mul_eqv w))
  have hbase : (1 : Q') - w ≤ (1 : Q') - qpow w 32 := by
    have hneg := Q'.neg_le_neg hpow
    exact Q'.add_le_add_left 1 (-w) (-(qpow w 32)) hneg
  let beta := squareCoefficient w
  by_cases hb : beta ≤ (0 : Q')
  · simpa only [exactChannelCeiling, beta, hb, ↓reduceIte] using hbase
  · have hb0 := not_le_zero_nonnegative hb
    have hfour : (0 : Q') ≤ (4 : Q') * beta :=
      Q'.mul_nonneg _ _ (by decide) hb0
    exact Q'.le_trans' _ _ _ hbase (by
      simpa only [exactChannelCeiling, beta, hb, ↓reduceIte] using
        Q'.add_le_self_of_nonneg ((1 : Q') - qpow w 32) ((4 : Q') * beta) hfour)

/-- The computed endpoint floor is no larger than half this sharper ceiling.
This concerns the certificate only, not the actual energy. -/
theorem two_endpointFloor_le_exactChannelCeiling {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (2 : Q') * endpointChannelHeatFloor w ≤ exactChannelCeiling w := by
  have hpower := endpointFloorPower_le_gap hw0 hw1
  have hpin : (2 : Q') * endpointChannelHeatFloor w ≈
      YMGap.Continuum.RGTransport.qpow w (endpointChannelFloorExponent w) := by
    unfold endpointChannelHeatFloor
    exact Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (2 : Q') HalfPow.half _).symm
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide : (2 : Q') * HalfPow.half ≈ 1))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _ hpower (gap_le_exactChannelCeiling hw0 hw1))

/-- Any normalized bound using only this exact ceiling and the existing
endpoint floor has coefficient at least one. A stronger source-sensitive
estimate is required for a survival contraction. -/
theorem normalizedExactCeiling_not_subunit {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hdelta : exactChannelCeiling w ≤
      (2 : Q') * endpointChannelHeatFloor w * delta) :
    (1 : Q') ≤ delta := by
  have h := Q'.le_trans' _ _ _
    (two_endpointFloor_le_exactChannelCeiling hw0 hw1) hdelta
  apply Q'.le_of_mul_le_mul_left (c := (2 : Q') * endpointChannelHeatFloor w)
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_one_eqv ((2 : Q') * endpointChannelHeatFloor w))) h
  · exact Q'.mul_pos (by decide) (endpointChannelHeatFloor_positive hw0)

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointExactCoefficientFence

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.exactChannelCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.plaquetteChannelCost_le_exactCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.gap_le_exactChannelCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.two_endpointFloor_le_exactChannelCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointExactCoefficientFence.normalizedExactCeiling_not_subunit
