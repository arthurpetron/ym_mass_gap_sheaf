/-
# Whole-observable spectator contraction of the original Young cost

The observable is kept whole, including every signed cross term. Heat factors
on coordinates absent from that observable are removed only in the exact
one-ended cost pin, under supported Haar insertions. They remain present in
the actual positive channel weights and their projected complete sources.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments
import YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
import YMGap.Continuum.SU2QuaternionProductHeatJumpDensity
import YMGap.Continuum.SU2QuaternionFamilyHeatGramPositiveWeight

namespace YMGap.Continuum.SU2QuaternionProductHeatPassiveYoungContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments
open YMGap.Continuum.SU2QuaternionProductHeatInactiveProjection
open YMGap.Continuum.SU2QuaternionProductHeatJumpDensity
open YMGap.Continuum.SU2QuaternionFamilyHeatGramPositiveWeight
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem sum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (sum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

/-- Removing spectator heat from this exact cost is justified for the whole
observable. No independence is imposed on the complete source. -/
theorem singleEndedCost_drop_independent (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hcover : (passive++active).Perm (List.range n))
    (b f : RatPoly) (hb : SupportedQuaternionBlocks n b)
    (hf : SupportedQuaternionBlocks n f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    singleEndedCost n w K (List.range n) b f ≈
      singleEndedCost n w K active b f := by
  have hnd := hcover.symm.nodup (CayleyParentInj.range_nodup n)
  have ha : ∀ i, i ∈ active → i < n := fun i hi =>
    List.mem_range.mp (hcover.mem_iff.mp (List.mem_append_right passive hi))
  have hall : ∀ i, i ∈ passive++active → i < n := fun i hi =>
    List.mem_range.mp (hcover.mem_iff.mp hi)
  have hbb := supported_polyMul hb hb
  have hff := supported_polyMul hf hf
  have hbbf := supported_polyMul hbb hf
  have hd1 := productMap_drop_independent_prefix n w K active passive hnd hall f hf hind
  have hd2 := productMap_drop_independent_prefix n w K active passive hnd hall
    (polyMul f f) hff (fun i hi => quaternionBlockIndependent_polyMul (hind i hi) (hind i hi))
  have hp1 : RatPolyCoeffEqv
      (productMap n w K (List.range n) f)
      (productMap n w K (passive++active) f) :=
    partialHaarHeads_congr n ((polynomialProduct_perm _ hcover.symm).mul_right f)
  have hp2 : RatPolyCoeffEqv
      (productMap n w K (List.range n) (polyMul f f))
      (productMap n w K (passive++active) (polyMul f f)) :=
    partialHaarHeads_congr n
      ((polynomialProduct_perm _ hcover.symm).mul_right (polyMul f f))
  have hm1 := Q'.eqv_trans _ _ _ (haar_of_coeff (hp1.mul_left (polyMul (polyMul b b) f)))
    (hd1 (polyMul (polyMul b b) f) hbbf)
  have hm2 := Q'.eqv_trans _ _ _ (haar_of_coeff (hp2.mul_left (polyMul b b)))
    (hd2 (polyMul b b) hbb)
  exact Q'.eqv_trans _ _ _
    (singleEndedCost_eq_moments n w K (List.range n)
      (CayleyParentInj.range_nodup n) (fun _ hi => List.mem_range.mp hi) hb hf)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' hm2
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hm1))))
      (singleEndedCost_eq_moments n w K active
        (List.nodup_append.mp hnd).2.1 ha hb hf).symm)

/-- The full original cost is pinned to the certified density on the common
active footprint. This is one whole-observable identity, not a facewise sum. -/
theorem singleEndedCost_full_eq_jumpDensity (n : Nat) (w : Q') (K : Nat)
    (active passive : List Nat) (hcover : (passive++active).Perm (List.range n))
    (b f : RatPoly) (hb : SupportedQuaternionBlocks n b)
    (hf : SupportedQuaternionBlocks n f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    singleEndedCost n w K (List.range n) b f ≈
      quaternionHaar n (polyMul (polyMul b b) (jumpDensity n w K active f)) :=
  Q'.eqv_trans _ _ _
    (singleEndedCost_drop_independent n w K active passive hcover b f hb hf hind)
    (singleEndedCost_eq_jumpDensity n w K active
      (fun _ hi => List.mem_range.mp
        (hcover.mem_iff.mp (List.mem_append_right passive hi))) hb hf)

/-- Coefficient-one contraction of the exact whole-observable Young cost
under the actual spectator heat channels. Every cross term is retained. -/
theorem singleEndedCost_projected_channels_le (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (active passive : List Nat)
    (hcover : (passive++active).Perm (List.range n)) (q f : RatPoly)
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f)
    (hind : ∀ i, i ∈ passive → QuaternionBlockIndependent i f) :
    channelSum (productChannels n w K passive) (fun c =>
      singleEndedCost n w K (List.range n) (channelSource passive q c) f) ≤
      singleEndedCost n w K (List.range n) q f := by
  let e := jumpDensity n w K active f
  have hnd := hcover.symm.nodup (CayleyParentInj.range_nodup n)
  have ha : ∀ i, i ∈ active → i < n := fun i hi =>
    List.mem_range.mp (hcover.mem_iff.mp (List.mem_append_right passive hi))
  have hs : ∀ i, i ∈ passive → i < n := fun i hi =>
    List.mem_range.mp (hcover.mem_iff.mp (List.mem_append_left active hi))
  have hnot : ∀ i, i ∈ passive → i ∉ active := by
    intro i hi hm
    exact (List.nodup_append.mp hnd).2.2 i hi i hm rfl
  have he := jumpDensity_supported n w K active ha hf
  have E := jumpDensity_certificate n hw0 hw1 K hK active ha hf
  have hei : ∀ i, i ∈ passive → QuaternionBlockIndependent i e :=
    fun i hi => jumpDensity_independent n w K active ha hf i (hs i hi)
      (hnot i hi) (hind i hi)
  have hraw := singleEndedCost_full_eq_jumpDensity n w K active passive hcover q f hq hf hind
  have hsum := sum_congr
    (fun c => singleEndedCost n w K (List.range n) (channelSource passive q c) f)
    (fun c => quaternionHaar n
      (polyMul (polyMul (channelSource passive q c) (channelSource passive q c)) e))
    (productChannels n w K passive) (fun c hc =>
      singleEndedCost_full_eq_jumpDensity n w K active passive hcover
        (channelSource passive q c.2) f
        (familyProject_supported passive
          (supported_polyMul hq (productChannels_supported n w K passive hs c hc))) hf hind)
  have hbound := productChannels_familyProject_positiveWeighted_square_le
    n hw0 hw1 K hK passive (List.nodup_append.mp hnd).1 hs q e hq he E hei
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hraw.symm))

#print axioms singleEndedCost_drop_independent
#print axioms singleEndedCost_full_eq_jumpDensity
#print axioms singleEndedCost_projected_channels_le

end YMGap.Continuum.SU2QuaternionProductHeatPassiveYoungContraction
