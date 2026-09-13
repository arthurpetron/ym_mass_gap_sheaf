/-
# Original boundary decay for every admissible time offset

The actual exterior separation feeds the existing arbitrary-mask core sum.
The resulting determinant retains both original unit moments, and the
coefficient has no dependence on the outer padding or its time offset.
Coupling, observable interval and probe-size dependence remain explicit.
This is boundary sensitivity, not a time-correlation or spectral-gap bound.
-/

import YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation
import YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay

namespace YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget (summedBoundaryBudget mixedNumerator_tail_bound)
open YMGap.Continuum.BF4ExactSlabInnerMarginBoundaryDecay
  (singlePlaquetteBudget singlePlaquetteAmplitude singleton_budget_pin singlePlaquetteBudget_factor)
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetAction
open YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

section SmallNome

variable {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
include hw0 hw1 hsmall hd hs

theorem boundary_tail_bound (P : Placement) (K : Nat) (p : RatPoly) (c : Q')
    (hp : Interval (boundaryCompleteSlabLinks P.target).length p c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal P.target links p)
    (d : Nat) (hsize : ∀ anchor, anchor ∈ activeAnchors P.target links (keep P)
      (slabPhysicalFaceEdges P.target) → d ≤ anchor.length) :
    Q'.abs (boundaryNumerator P w K p) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs d) *
        (fullMoment P w K polyOne * interiorMoment P w K polyOne) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (boundary_mixedNumerator P w K p)))
    (Q'.le_trans' _ _ _ (mixedNumerator_tail_bound hw0 hw1 hsmall hd hs K P.target
      (keep P) p c hp links probe hl _ d (CayleyParentInj.range_nodup _) (fun _ hi => hi) hsize)
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (boundary_mixedPartition P w K))))

theorem protected_boundary_bound (P : Placement) (K margin : Nat) (p : RatPoly) (c : Q')
    (hp : Interval (boundaryCompleteSlabLinks P.target).length p c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal P.target links p)
    (hr : ProtectedRoot P margin probe.animal.root) :
    Q'.abs (boundaryNumerator P w K p) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs (margin+1-probe.animal.support.length)) *
        (fullMoment P w K polyOne * interiorMoment P w K polyOne) :=
  boundary_tail_bound hw0 hw1 hsmall hd hs P K p c hp links probe hl _
    (fun _ ha => protected_core_size_floor P probe hr ha)

theorem shifted_base_boundary_bound (P : Placement) (K base margin : Nat)
    (hhalf : P.half=base+margin) (baseFace : Z4Plaq)
    (hf : baseFace ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (p : RatPoly) (c : Q')
    (hp : Interval (boundaryCompleteSlabLinks P.target).length p c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal P.target links p)
    (hr : probe.animal.root = shiftFace P.padding P.time (shiftFace margin margin baseFace)) :
    Q'.abs (boundaryNumerator P w K p) ≤
      ((c+c)*summedBoundaryBudget probe w hd hs (margin+1-probe.animal.support.length)) *
        (fullMoment P w K polyOne * interiorMoment P w K polyOne) :=
  protected_boundary_bound hw0 hw1 hsmall hd hs P K margin p c hp links probe hl
    (hr.symm ▸ shifted_base_protected P margin hhalf hf)

/-- The singleton carrier and its core-size floor are constructed, for every allowed offset. -/
theorem singlePlaquette_boundary_bound (P : Placement) (K base margin : Nat)
    (hhalf : P.half=base+margin) (baseFace : Z4Plaq)
    (hf : baseFace ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (p : RatPoly) (c : Q')
    (hp : Interval (boundaryCompleteSlabLinks P.target).length p c)
    (hl : LinkLocal P.target (edgesOf (shiftFace P.padding P.time (shiftFace margin margin baseFace))) p) :
    Q'.abs (boundaryNumerator P w K p) ≤
      ((c+c)*singlePlaquetteBudget w hd hs margin) *
        (fullMoment P w K polyOne * interiorMoment P w K polyOne) := by
  let q := shiftFace P.padding P.time (shiftFace margin margin baseFace)
  have h := shifted_base_boundary_bound hw0 hw1 hsmall hd hs P K base margin hhalf baseFace hf p c hp
    (edgesOf q) (singletonCarrier q) hl rfl
  have hm : margin+1-(singletonCarrier q).animal.support.length = margin := Nat.add_sub_cancel margin 1
  rw [hm, singleton_budget_pin] at h
  exact h

/-- Geometric boundary sensitivity, with all coupling dependence explicit. -/
theorem singlePlaquette_boundary_geometric_bound (P : Placement) (K base margin : Nat)
    (hhalf : P.half=base+margin) (baseFace : Z4Plaq)
    (hf : baseFace ∈ boundaryCompleteSlabPlaquettes (centralExtent base)) (p : RatPoly) (c : Q')
    (hp : Interval (boundaryCompleteSlabLinks P.target).length p c)
    (hl : LinkLocal P.target (edgesOf (shiftFace P.padding P.time (shiftFace margin margin baseFace))) p) :
    Q'.abs (boundaryNumerator P w K p) ≤
      (((c+c)*singlePlaquetteAmplitude w hd hs) * (entropyRate 625 (adjustedCoreRate w hd))^margin) *
        (fullMoment P w K polyOne * interiorMoment P w K polyOne) :=
  Q'.le_trans' _ _ _ (singlePlaquette_boundary_bound hw0 hw1 hsmall hd hs P K base margin hhalf baseFace hf p c hp hl)
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (c+c) _ _ (singlePlaquetteBudget_factor w hd hs margin))
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))

end SmallNome

end YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay

#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay.boundary_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay.protected_boundary_bound
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay.shifted_base_boundary_bound
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay.singlePlaquette_boundary_bound
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay.singlePlaquette_boundary_geometric_bound
