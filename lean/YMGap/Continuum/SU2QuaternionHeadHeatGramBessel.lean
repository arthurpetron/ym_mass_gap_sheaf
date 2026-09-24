/-
# Conditional Bessel bound for the actual one-link heat channels

The two copies of the endpoint source share every untouched coordinate.
Their exact Gram sum is the original head-heat quadratic form. Thus summing
ALL real/imaginary tensor channels of this one-link factor costs coefficient one, not the diagonal
kernel trace or the number of channels. This holds at every finite cutoff
and 0 <= w <= 1, for an arbitrary signed supported source.

This is a conditional one-link estimate, not a comparison with the
interacting partition, centered variance, or a physical spectral gap.
-/

import YMGap.Continuum.SU2QuaternionSharedHeadGramPairing
import YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
import YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction
import YMGap.Continuum.SU2QuaternionHaarCertificateExtension

namespace YMGap.Continuum.SU2QuaternionHeadHeatGramBessel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarCertificateExtension
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionSpareHeadCopy
open YMGap.Continuum.SU2QuaternionSharedHeadGramPairing
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionHeadHeatPositiveContraction
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem support_smul {n : Nat} (c : Q') {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polySmul c p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem kernel_supported : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → SupportedQuaternionBlocks 1 c.2) →
    SupportedQuaternionBlocks 2 (channelKernel 1 cs)
  | [], _ => fun _ hm => False.elim (List.not_mem_nil hm)
  | c::cs, h => by
      have hc := h c List.mem_cons_self
      exact supported_add
        (support_smul c.1 (supported_polyMul
          (fun t ht => Nat.le_trans (hc t ht) (by decide)) (lift_supported hc 1)))
        (kernel_supported cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channels_pairing (tail : Nat) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (tail+1) q) : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → SupportedQuaternionBlocks 1 c.2) →
    H (tail+2) (polyMul (channelKernel 1 cs) (polyMul (copy q) (liftHead q))) ≈
      channelSum cs (fun h => H (tail+1)
        (polyMul (project 0 (polyMul q h)) (project 0 (polyMul q h))))
  | [], _ => haar_of_coeff (RatPolyCoeffEqv.mul_zero_left _)
  | c::cs, h => by
      let W := polyMul (copy q) (liftHead q)
      have hs := Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_left c.1
          (polyMul c.2 (liftHead c.2)) W))
        (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _)
          (Q'.mul_eqv_congr_left _ _ _
            (sharedHead_channel_pairing tail q c.2 hq (h c List.mem_cons_self))))
      change H (tail+2) (polyMul
        (polyAdd (polySmul c.1 (polyMul c.2 (liftHead c.2))) (channelKernel 1 cs)) W) ≈ _
      rw [polyMul_add_left_exact]
      exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' hs
          (channels_pairing tail q hq cs (fun d hd => h d (List.mem_cons_of_mem c hd))))

/-- Exact channel analysis norm, with the original source's spectators SHARED.
No independent copy of the untouched coordinates is introduced. -/
theorem heatChannels_project_square_eq_pair (tail : Nat) (w : Q') (K : Nat)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q) :
    channelSum (heatChannels 0 w K) (fun h => H (tail+1)
      (polyMul (project 0 (polyMul q h)) (project 0 (polyMul q h)))) ≈
      H (tail+1) (polyMul q (headMap w K q)) := by
  have hc := heatChannels_supported (by decide : 0 < 1) w K
  have hg := carrier_extend tail
    (heat_supported (by decide : 0 < 2) (by decide : 1 < 2) w K)
    (kernel_supported _ hc) (heatChannels_carrier 1 0 (by decide) w K)
  have hg' : HaarCarrierEqv (tail+2) (relativeHeat w K)
      (channelKernel 1 (heatChannels 0 w K)) := by
    simpa only [heatAt_zero_one, Nat.add_comm 2 tail] using hg
  have hp : heatPair tail w K q q ≈
      H (tail+2) (polyMul (channelKernel 1 (heatChannels 0 w K))
        (polyMul (copy q) (liftHead q))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _))
      (haar_of_carrier (HaarCarrierEqv.mul_right _ hg'))
  exact Q'.eqv_trans _ _ _ (channels_pairing tail q hq _ hc).symm
    (Q'.eqv_trans _ _ _ hp.symm
      (Q'.eqv_trans _ _ _ (headMap_pairing tail w K q q).symm
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))

/-- Coefficient ONE, independent of the finite channel count, nome and cutoff.
This bounds the raw source norm, NOT the original interacting partition. -/
theorem heatChannels_project_square_le (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q) :
    channelSum (heatChannels 0 w K) (fun h => H (tail+1)
      (polyMul (project 0 (polyMul q h)) (project 0 (polyMul q h)))) ≤
      H (tail+1) (polyMul q q) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (heatChannels_project_square_eq_pair tail w K q hq))
    (headMap_form_le_norm tail hw0 hw1 K q hq)

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

/-- A spectator-independent squared insertion passes through every channel.
The weighting is on the SAME source and costs no channel-count factor. -/
theorem heatChannels_project_weighted_square_le (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (q r : RatPoly) (hq : SupportedQuaternionBlocks (tail+1) q)
    (hr : SupportedQuaternionBlocks (tail+1) r)
    (hind : QuaternionBlockIndependent 0 r) :
    channelSum (heatChannels 0 w K) (fun h => H (tail+1)
      (polyMul (polyMul (project 0 (polyMul q h)) (project 0 (polyMul q h)))
        (polyMul r r))) ≤ H (tail+1) (polyMul (polyMul q q) (polyMul r r)) := by
  have hc (h : RatPoly) : RatPolyCoeffEqv
      (project 0 (polyMul (polyMul q r) h)) (polyMul (project 0 (polyMul q h)) r) :=
    (project_congr 0 (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => q | 1 => r | _ => h))).trans
      (project_mul_right_of_independent 0 (polyMul q h) r hind)
  have square (p : RatPoly) : RatPolyCoeffEqv
      (polyMul (polyMul p r) (polyMul p r)) (polyMul (polyMul p p) (polyMul r r)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1))) (by decide)
      (fun | 0 => p | _ => r)
  have he : channelSum (heatChannels 0 w K) (fun h => H (tail+1)
      (polyMul (project 0 (polyMul (polyMul q r) h))
        (project 0 (polyMul (polyMul q r) h)))) ≈
      channelSum (heatChannels 0 w K) (fun h => H (tail+1)
        (polyMul (polyMul (project 0 (polyMul q h)) (project 0 (polyMul q h)))
          (polyMul r r))) :=
    channelSum_congr _ _ (heatChannels 0 w K) (fun c _ =>
      haar_of_coeff (((hc c.2).mul (hc c.2)).trans (square _)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _
      (heatChannels_project_square_le tail hw0 hw1 K (polyMul q r) (supported_polyMul hq hr))
      (Q'.le_of_eqv (haar_of_coeff (square q))))

end YMGap.Continuum.SU2QuaternionHeadHeatGramBessel

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGramBessel.heatChannels_project_square_eq_pair
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGramBessel.heatChannels_project_square_le
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatGramBessel.heatChannels_project_weighted_square_le
