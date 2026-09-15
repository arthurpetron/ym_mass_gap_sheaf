/-
# Original-law boundary comparison across slab parity

The zero-shift inclusion adds faces only beyond the source coordinate box.
A root with coordinate clearance margin is therefore at least margin from
every omitted face. A computed physical-face preimage proves this claim;
the existing active-core animal bound turns it into a core-size floor.

The proved arbitrary-mask estimate and original-action inclusion pin give
the full target/source normalized expectation comparison. Its odd/even
specialization uses the EXISTING odd expectation. The original target
insertion may be any supported literal polynomial with the displayed image
pin, interval and link-locality certificates. No reflection/T1 pin is assumed
implicitly, and no thermodynamic site form or completed T1 positivity is
claimed here. The coupling guards and probe-size loss stay explicit.
-/

import YMGap.Continuum.BF4ExactSlabCoordinateAction
import YMGap.Continuum.BF4ExactSlabCoreDistanceFloor
import YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison

namespace YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabCoordinateInclusion
open YMGap.Continuum.BF4ExactSlabCoordinateAction
open YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation (physical_base_coordinate_le cPlaq_uniform_shift)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabCoreDistanceFloor (active_core_linf_floor)
open YMGap.Continuum.BF4ExactSlabFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SepLatticeZ4Linf
open Dir4

private theorem small_face_mem {source : Nat} {p : Z4Plaq} (hp : ∀ m, cPlaq p m < source) :
    p ∈ boundaryCompleteSlabPlaquettes source := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  have h0 := hp x0; have h1 := hp x1; have h2 := hp x2; have h3 := hp x3
  simp only [cPlaq, vComp] at h0 h1 h2 h3
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  constructor
  · rw [mem_boxPlaquettes]
    change a < source+1 ∧ b < source+1 ∧ c < source+1 ∧ d < source+1
    exact ⟨by omega, by omega, by omega, by omega⟩
  · cases plane <;> simp only [plaquetteTimeAdmissible] <;> omega

/-- Actual source index, returned as data rather than chosen from existence. -/
def facePreimage (source : Nat) (p : Z4Plaq) (hp : ∀ m, cPlaq p m < source) :
    Σ' id : Nat, (id ∈ slabPhysicalFaceEdges source) ×' (slabPlaquetteAt source id = p) :=
  ⟨listIndexOf p (boundaryCompleteSlabPlaquettes source),
    List.mem_range.mpr (listIndexOf_lt_of_mem _ _ (small_face_mem hp)),
    getD_listIndexOf_of_mem _ _ _ (small_face_mem hp)⟩

private theorem small_id_included {source target id : Nat} (h : source ≤ target)
    (hi : id ∈ slabPhysicalFaceEdges target) (hp : ∀ m, cPlaq (slabPlaquetteAt target id) m < source) :
    id ∈ includedIds source target := by
  obtain ⟨i, hs, he⟩ := facePreimage source _ hp
  apply List.mem_map.mpr
  refine ⟨i, hs, ?_⟩
  apply slabPlaquetteAt_injective_on_physical (faceId_physical h hs) hi
  rw [faceId_pin h hs]
  exact he

/-- Only far-side clearance is needed: this inclusion adds no negative-coordinate faces. -/
def RootCeiling (source margin : Nat) (root : Z4Plaq) : Prop :=
  ∀ m, cPlaq root m+margin ≤ source

theorem exterior_distance {source target margin : Nat} (h : source ≤ target) {root : Z4Plaq}
    (hr : RootCeiling source margin root) {id : Nat} (hi : id ∈ slabPhysicalFaceEdges target)
    (ho : keep source target id = false) : margin ≤ linfDist root (slabPlaquetteAt target id) := by
  by_cases hd : margin ≤ linfDist root (slabPlaquetteAt target id)
  · exact hd
  · have hin := small_id_included h hi (by
      intro m
      have hroot := hr m
      have hdist := le_linfDist_comp root (slabPlaquetteAt target id) m
      simp only [natDist] at hdist
      omega)
    have hout : id ∉ includedIds source target := of_decide_eq_false ho
    exact False.elim (hout hin)

theorem shifted_base_ceiling {base : Nat} (margin : Nat) {p : Z4Plaq}
    (hp : p ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) :
    RootCeiling (centralExtent (base+margin)) margin (shiftFace margin margin p) := by
  intro m
  rw [cPlaq_uniform_shift]
  have h := physical_base_coordinate_le hp m
  unfold centralExtent at h ⊢
  omega

theorem core_size_floor {source target margin : Nat} (h : source ≤ target) {links : List Z4Link}
    (probe : ProbeCarrier links) (hr : RootCeiling source margin probe.animal.root) {anchor : List Nat}
    (ha : anchor ∈ activeAnchors target links (keep source target) (slabPhysicalFaceEdges target)) :
    margin+1-probe.animal.support.length ≤ anchor.length := by
  have hd := active_core_linf_floor probe (CayleyParentInj.range_nodup _) (fun _ hi => hi) ha
    (fun _ hi ho => exterior_distance h hr hi ho)
  omega

/-- All analytic estimates are existing; the new input is the actual mask geometry. -/
theorem expectation_bound {source target margin : Nat} (h : source ≤ target)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks source).length p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks target).length q)
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks target).length ((embedding h).polynomial p) q)
    (c : Q') (hc : Interval (boundaryCompleteSlabLinks target).length q c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal target links q)
    (hr : RootCeiling source margin probe.animal.root) :
    leEv (CReal.abs (CReal.sub
      (expectation w hw0 hw1 hsmall hd target (slabPhysicalFaceEdges target) (fun _ hi => hi) q)
      (expectation w hw0 hw1 hsmall hd source (slabPhysicalFaceEdges source) (fun _ hi => hi) p)))
      (ofQ' ((c+c)*summedBoundaryBudget probe w hd hs (margin+1-probe.animal.support.length))) := by
  have hb := mask_tail_bound w hw0 hw1 hsmall hd target (slabPhysicalFaceEdges target) (fun _ hi => hi)
    (keep source target) hs q c hc links probe hl (margin+1-probe.animal.support.length)
    (CayleyParentInj.range_nodup _) (fun _ ha => core_size_floor h probe hr ha)
  exact (leEv_congr (abs_equiv_congr (CReal.sub_congr_right
    (expectation_pin_of_prefix h w hw0 hw1 hsmall hd p hp q hq he))) (Equiv.refl _)).mp hb

/-- Cross-parity comparison with the existing original odd expectation. -/
theorem odd_even_bound (radius margin : Nat)
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent radius)).length p)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (adjacentEvenExtent radius)).length q)
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (adjacentEvenExtent radius)).length
      ((embedding (odd_even_room radius)).polynomial p) q)
    (c : Q') (hc : Interval (boundaryCompleteSlabLinks (adjacentEvenExtent radius)).length q c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal (adjacentEvenExtent radius) links q)
    (hr : RootCeiling (centralExtent radius) margin probe.animal.root) :
    leEv (CReal.abs (CReal.sub
      (expectation w hw0 hw1 hsmall hd (adjacentEvenExtent radius) (slabPhysicalFaceEdges (adjacentEvenExtent radius))
        (fun _ hi => hi) q)
      (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 radius p)))
      (ofQ' ((c+c)*summedBoundaryBudget probe w hd hs (margin+1-probe.animal.support.length))) :=
  (leEv_congr (abs_equiv_congr (CReal.sub_congr_right (odd_expectation_pin w hw0 hw1 hsmall hd radius p)))
    (Equiv.refl _)).mp
      (expectation_bound (odd_even_room radius) w hw0 hw1 hsmall hd hs p hp q hq he c hc links probe hl hr)

end YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison

#print axioms YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison.facePreimage
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison.RootCeiling
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison.exterior_distance
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison.shifted_base_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison.core_size_floor
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison.expectation_bound
#print axioms YMGap.Continuum.BF4ExactSlabCoordinateBoundaryComparison.odd_even_bound
