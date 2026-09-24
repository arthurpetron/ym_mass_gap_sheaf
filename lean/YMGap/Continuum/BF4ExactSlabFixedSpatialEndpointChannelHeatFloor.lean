/-
# A computed original-partition floor for the SAME endpoint channel norm

The positive full degree paths are summed before using the aggregate first
moment. Four active plaquette links supply a width/depth-independent constant
at fixed nome. The result compares the existing conditional channel norm with
the ORIGINAL odd marginal partition. It is not a centered-variance estimate,
a changing-spacing bound, or a continuum spectral statement.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelFirstMoment
import YMGap.Continuum.SU2QuaternionFirstMomentHeatFloor

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelHeatFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointRelativeBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelFirstMoment
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialPassiveChannels
open YMGap.Continuum.BF4ExactSlabFixedSpatialChannelActiveMoments
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor (pairCasimir)
open YMGap.Continuum.SU2QuaternionFirstMomentHeatFloor
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks terminalMessage marginalWeight

/-- A computed positive integer dominating twice the aggregate angular cap. -/
def endpointChannelFloorExponent (w : Q') : Nat :=
  (48 * (endpointRelativeCap w * endpointRelativeCap w)).num.toNat + 1

def endpointChannelHeatFloor (w : Q') : Q' :=
  HalfPow.half * RGTransport.qpow w (endpointChannelFloorExponent w)

def endpointChannelHeatCutoff (w : Q') : Nat :=
  max (endpointRelativeCutoff w) (endpointChannelFloorExponent w)

theorem endpointChannelFloorExponent_positive (w : Q') :
    0 < endpointChannelFloorExponent w := Nat.succ_pos _

theorem endpointChannelFloorExponent_sufficient (w : Q') :
    48 * (endpointRelativeCap w * endpointRelativeCap w) ≤
      Q'.ofNat (endpointChannelFloorExponent w) :=
  Q'.le_trans' _ _ _ (RatNat.le_ofNat_toNat _
    (Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg _)))
    (CReal.ofNat_le_ofNat (Nat.le_succ _))

private theorem qpow_positive {w : Q'} (hw : (0 : Q') < w) :
    ∀ n, (0 : Q') < RGTransport.qpow w n
  | 0 => by
      change (0 : Q') < (1 : Q')
      decide
  | n+1 => Q'.mul_pos (qpow_positive hw n) hw

theorem endpointChannelHeatFloor_positive {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') < endpointChannelHeatFloor w :=
  Q'.mul_pos (by decide : (0 : Q') < HalfPow.half) (qpow_positive hw _)

private theorem channelSum_congr (f g : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → f c.2 ≈ g c.2) → channelSum cs f ≈ channelSum cs g
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr f g cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_le (f g : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
    (∀ c, c ∈ cs → f c.2 ≤ g c.2) → channelSum cs f ≤ channelSum cs g
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self) (hw c List.mem_cons_self))
      (channelSum_le f g cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_nonnegative (f : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
    (∀ c, c ∈ cs → (0 : Q') ≤ f c.2) → (0 : Q') ≤ channelSum cs f
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (h c List.mem_cons_self))
      (channelSum_nonnegative f cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_scale (r : Q') (f : RatPoly → Q') : ∀ cs : List GramChannel,
    channelSum cs (fun c => r*f c) ≈ r*channelSum cs f
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv r)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_scale r f cs))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3))) (by decide)
        (fun | 0 => c.1 | 1 => r | 2 => f c.2 | _ => channelSum cs f))

private theorem channelSum_affine (r m : Q') (f g : RatPoly → Q') :
    ∀ cs : List GramChannel,
    channelSum cs (fun c => r*(m*f c-g c)) ≈
      r*(m*channelSum cs f-channelSum cs g)
  | [] => by
      exact poly_identity_of_normal_eq (.const 0)
        (.mul (.var 0) (.add (.mul (.var 1) (.const 0)) (.neg (.const 0))))
        (by decide) (fun | 0 => r | _ => m)
  | c::cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_affine r m f g cs))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.add (.mul (.var 2) (.var 3)) (.neg (.var 4)))))
          (.mul (.var 1) (.add (.mul (.var 2) (.var 5)) (.neg (.var 6)))))
        (.mul (.var 1)
          (.add (.mul (.var 2) (.add (.mul (.var 0) (.var 3)) (.var 5)))
            (.neg (.add (.mul (.var 0) (.var 4)) (.var 6))))) (by decide)
        (fun | 0 => c.1 | 1 => r | 2 => m | 3 => f c.2 | 4 => g c.2
             | 5 => channelSum cs f | _ => channelSum cs g))

/-- The computed positive floor compares the SAME original channel norm with
the ORIGINAL odd marginal partition, not with a replacement normalization. -/
theorem projectedEndpoint_channelNorm_le_originalPartition {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : endpointChannelHeatCutoff w ≤ K) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width) (ha : FullyActive width face) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    endpointChannelHeatFloor w *
        familyChannelQuadratic (N width) w K (spectatorBlocks width face) q ≤
      H (N width) (marginalWeight w K width depth) := by
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let cs := productChannels (N width) w K (spectatorBlocks width face)
  let b := plaquetteChannelSource w K width (terminalMessage w K width depth) face
  let A := familyChannelQuadratic (N width) w K (spectatorBlocks width face) q
  let E := channelSum cs (fun c => pairCasimir (N width-1) (b c) (b c))
  let Z := H (N width) (marginalWeight w K width depth)
  let M := endpointChannelFloorExponent w
  let m := Q'.ofNat M
  let power := RGTransport.qpow w M
  let norm := fun c => H (N width) (polyMul (b c) (b c))
  let heat := fun c => H (N width)
    (polyMul (b c) (productMap (N width) w K (List.range (N width)) (b c)))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (faceCarrier_positive width face hf)
  have hreg : endpointRelativeCutoff w ≤ K := Nat.le_trans (Nat.le_max_left _ _) hK
  have hMK : M ≤ K := Nat.le_trans (Nat.le_max_right _ _) hK
  have hb (c : GramChannel) (hc : c ∈ cs) : SupportedQuaternionBlocks (N width) (b c.2) :=
    plaquetteChannelSource_supported w K width _ (terminalMessage_supported w K width depth) face c hc
  have hw := productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K (spectatorBlocks width face)
  have hA : (0 : Q') ≤ A := channelSum_nonnegative norm cs hw
    (fun c hc => (Certificate.square (b c.2) (hb c hc)).haar_nonnegative)
  have hZ : Z ≈ channelSum cs heat :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one _)))
      (Q'.eqv_trans _ _ _
        (oddMoment_eq_plaquette_channels w K width depth face polyOne (supported_one _)
          (fun i _ => quaternionBlockIndependent_polyOne i)
          (fun i _ => quaternionBlockIndependent_polyOne i))
        (channelSum_congr _ _ cs (fun c _ =>
          haar_of_coeff ((RatPolyCoeffEqv.mul_one (b c.2)).mul_right _))))
  have hpoint : channelSum cs (fun c => power*(m*norm c-pairCasimir (N width-1) (b c) (b c))) ≤
      channelSum cs (fun c => m*heat c) := by
    apply channelSum_le _ _ cs hw
    intro c hc
    have h := fullProductPairing_firstMoment_floor (N width-1)
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K M hMK (b c.2)
      (by simpa only [hN] using hb c hc)
    simpa only [hN] using h
  have hheat : power*(m*A-E) ≤ m*Z :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (channelSum_affine power m norm
      (fun c => pairCasimir (N width-1) (b c) (b c)) cs))
      (Q'.le_trans' _ _ _ hpoint (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (channelSum_scale m heat cs) (Q'.mul_eqv_congr_left m _ _ (Q'.eqv_symm hZ)))))
  have hE := projectedEndpoint_plaquetteChannel_firstMoment_le hw0 hw1 K width hreg depth face hf ha
  have hm : (0 : Q') < m := Q'.ofNat_succ_pos _
  have hcap : 2*(24*(endpointRelativeCap w*endpointRelativeCap w)) ≤ m :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.const 2) (.mul (.const 24) (.var 0))) (.mul (.const 48) (.var 0))
      (by decide) (fun _ => endpointRelativeCap w*endpointRelativeCap w)))
      (endpointChannelFloorExponent_sufficient w)
  exact firstMoment_half_floor power m A E Z (24*(endpointRelativeCap w*endpointRelativeCap w))
    (Q'.le_of_lt (qpow_positive hw0 M)) hm hA hE hcap hheat

/-- Strict padding constructs the activity guard of the original-partition
comparison; the floor and cutoff depend only on the nome. -/
theorem padded_channelNorm_le_originalPartition {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) {base width : Nat} (hwidth : base < width)
    (hK : endpointChannelHeatCutoff w ≤ K) (depth : Nat)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    endpointChannelHeatFloor w *
        familyChannelQuadratic (N width) w K (spectatorBlocks width face) q ≤
      H (N width) (marginalWeight w K width depth) :=
  projectedEndpoint_channelNorm_le_originalPartition hw0 hw1 K width hK depth face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf) (plaquette_active_after_padding hwidth face hf)

#print axioms endpointChannelFloorExponent
#print axioms endpointChannelHeatFloor
#print axioms endpointChannelHeatCutoff
#print axioms endpointChannelFloorExponent_positive
#print axioms endpointChannelFloorExponent_sufficient
#print axioms endpointChannelHeatFloor_positive
#print axioms projectedEndpoint_channelNorm_le_originalPartition
#print axioms padded_channelNorm_le_originalPartition

end YMGap.Continuum.BF4ExactSlabFixedSpatialEndpointChannelHeatFloor
