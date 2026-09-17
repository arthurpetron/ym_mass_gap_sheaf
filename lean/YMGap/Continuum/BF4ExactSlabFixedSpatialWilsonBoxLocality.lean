/-
# Fixed-box locality of the literal recentered Wilson window

The source slice retains links whose spatial base coordinates may equal
the width. A box of side max(base+1,L+1) covers these fringe links and
every scheduled offset through L. Recentring and time placement translate
that SAME finite box; neither the ambient extent nor the larger source
width enters its size. Repeated links and all signed algebra operations
are retained in the syntactic locality proof.

The consumer is FixedSpatialBoxBoundary.finiteValue_bound, with its
separate actual interval certificate and aligned-action translation pin.
This module proves only the finite containing-box geometry and returns
its connected ProbeCarrier. It asserts no spatial limit, OS norm bound,
completed-carrier extension or continuum result.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
import YMGap.Continuum.BF4ExactSlabSpatialWilsonControl
import YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier

/-- The extra spatial unit retains the inclusive original source fringe. -/
def boxSize (base L : Nat) : Nat := max (base+1) (L+1)

theorem boxSize_pos (base L : Nat) : 0 < boxSize base L := by
  have h := Nat.le_max_right (base+1) (L+1)
  unfold boxSize
  omega

private theorem sourceLink_box {base L offset : Nat} (ho : offset ≤ L)
    {link : Z4Link} (hl : link ∈ baseLinks base) :
    timeShiftLink offset link ∈ boxLinks (boxSize base L) := by
  have hs := (baseLinks_mem_iff base link).mp hl
  rcases link with ⟨⟨a,b,c,t⟩,dir⟩
  change dir ≠ .x3 ∧ a ≤ base ∧ b ≤ base ∧ c ≤ base ∧ t=0 at hs
  have hb := Nat.le_max_left (base+1) (L+1)
  have ht := Nat.le_max_right (base+1) (L+1)
  apply boundary_mem_boxLinks (p := linkCarrierPlaquette (timeShiftLink offset ((a,b,c,t),dir)))
  · apply (mem_boxPlaquettes _ _).mpr
    cases dir <;> simp only [linkCarrierPlaquette, timeShiftLink, timeShiftVertex, boxSize]
    all_goals exact ⟨by omega, by omega, by omega, by omega⟩
  · exact link_mem_carrier_boundary _

private theorem shifted_source_link (space start offset : Nat) (link : Z4Link) :
    shiftLink space start (timeShiftLink offset link) =
      timeShiftLink (start+offset) (shiftLink space 0 link) := by
  rcases link with ⟨⟨a,b,c,t⟩,dir⟩
  simp only [shiftLink, shiftVertex, timeShiftLink, timeShiftVertex, Nat.add_zero]
  have ht : (t+offset)+start = t+(start+offset) := by omega
  rw [ht]

/-- Literal link membership is proved before invoking polynomial locality. -/
theorem placedLinks_recenter_subset {base targetWidth space : Nat}
    (hroom : base+space ≤ targetWidth) (start L : Nat) :
    ∀ e : WindowExpression base, Within L e → ∀ link,
    link ∈ placedLinks start (recenterExpression hroom e) →
      link ∈ (boxLinks (boxSize base L)).map (shiftLink space start)
  | .one, _, _, hl => by
      simp only [recenterExpression, placedLinks, List.not_mem_nil] at hl
  | .loop offset value _, he, link, hl => by
      change link ∈ (value.edges.map (translateEntry space)).map
        (fun entry => timeShiftLink (start+offset) entry.link) at hl
      rw [List.map_map] at hl
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hl
      apply List.mem_map.mpr
      refine ⟨timeShiftLink offset entry.link, sourceLink_box he (value.physical entry hentry), ?_⟩
      exact shifted_source_link space start offset entry.link
  | .add e f, he, link, hl => by
      rcases List.mem_append.mp hl with h | h
      · exact placedLinks_recenter_subset hroom start L e he.1 link h
      · exact placedLinks_recenter_subset hroom start L f he.2 link h
  | .mul e f, he, link, hl => by
      rcases List.mem_append.mp hl with h | h
      · exact placedLinks_recenter_subset hroom start L e he.1 link h
      · exact placedLinks_recenter_subset hroom start L f he.2 link h
  | .smul _ e, he, link, hl => placedLinks_recenter_subset hroom start L e he link hl

/-- Actual placed polynomial on one fixed translated box, with no ambient-room
assumption added to locality. Physical room is separately used for intervals. -/
theorem placed_recenter_local {base targetWidth space start extent : Nat}
    (hroom : base+space ≤ targetWidth) (L : Nat) (e : WindowExpression base)
    (he : Within L e) :
    LinkLocal extent ((boxLinks (max (base+1) (L+1))).map (shiftLink space start))
      (placedPolynomial extent start (recenterExpression hroom e)) :=
  placed_local_in extent start (recenterExpression hroom e) _
    (placedLinks_recenter_subset hroom start L e he)

/-- Explicit connected support data, independent of the ambient/larger width. -/
def boxCarrier (base L space start : Nat) :
    ProbeCarrier ((boxLinks (boxSize base L)).map (shiftLink space start)) :=
  shiftedBoxProbe (boxSize base L) space start (boxSize_pos base L)

theorem boxCarrier_size (base L space start : Nat) :
    (boxCarrier base L space start).animal.support.length =
      (boxSize base L * boxSize base L * boxSize base L * boxSize base L)*6 :=
  shiftedBoxProbe_size _ _ _ _

#print axioms boxSize
#print axioms boxSize_pos
#print axioms placedLinks_recenter_subset
#print axioms placed_recenter_local
#print axioms boxCarrier
#print axioms boxCarrier_size

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBoxLocality
