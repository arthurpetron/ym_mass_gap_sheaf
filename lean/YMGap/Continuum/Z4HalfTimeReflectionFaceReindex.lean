/-
# A computable face-coordinate reflection for the boundary-complete Z4 slab

`Z4HalfTimeReflectionGeometry` proves that the corrected slab plaquette list
is reflection-invariant and that the current physical full-box list is not.
This file turns the positive statement into an actual constructive numerical
reindex.  A primitive recursive list search locates the reflected plaquette;
no choice principle is used.

The resulting face-ID map preserves the finite physical range, is an
involution there, preserves bounded face-spin labellings, and leaves the exact
coupling-parametric heat-kernel face product invariant.  Thus the remaining
reflection-weight obstruction is no longer the face factor: it is the
shared-link fusion/multiplicity product, whose `incidentPlaqIds` and
order-sensitive `fuseLabels` are still defined only for the old asymmetric
box enumeration.
-/

import YMGap.Continuum.Z4HalfTimeReflectionGeometry

namespace YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

private theorem rangeNodupLocal (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

/-! ## 1. Constructive list indexing -/

/-- The first index of `target`, with zero as the irrelevant empty fallback. -/
def listIndexOf {A : Type} [DecidableEq A] (target : A) : List A -> Nat
  | [] => 0
  | head :: tail =>
      if target = head then 0 else listIndexOf target tail + 1

theorem listIndexOf_lt_of_mem {A : Type} [DecidableEq A]
    (target : A) :
    ∀ (xs : List A), target ∈ xs -> listIndexOf target xs < xs.length
  | [], hmem => absurd hmem List.not_mem_nil
  | head :: tail, hmem => by
      by_cases heq : target = head
      · simp [listIndexOf, heq]
      · have htail : target ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left heq
        have ih := listIndexOf_lt_of_mem target tail htail
        simp [listIndexOf, heq]
        omega

theorem getD_listIndexOf_of_mem {A : Type} [DecidableEq A]
    (fallback target : A) :
    ∀ (xs : List A), target ∈ xs ->
      xs.getD (listIndexOf target xs) fallback = target
  | [], hmem => absurd hmem List.not_mem_nil
  | head :: tail, hmem => by
      by_cases heq : target = head
      · subst target
        simp [listIndexOf]
      · have htail : target ∈ tail :=
          (List.mem_cons.mp hmem).resolve_left heq
        rw [listIndexOf]
        simp only [if_neg heq, List.getD_cons_succ]
        exact getD_listIndexOf_of_mem fallback target tail htail

private theorem enumerateFrom_getD_mem_local {A : Type} (fallback : A) :
    ∀ (start : Nat) (xs : List A) (i : Nat), i < xs.length ->
      (start + i, xs.getD i fallback) ∈ enumerateFrom start xs
  | _, [], _, hi => absurd hi (Nat.not_lt_zero _)
  | start, head :: tail, 0, _ => by
      simp [enumerateFrom]
  | start, head :: tail, i + 1, hi => by
      have ih := enumerateFrom_getD_mem_local fallback
        (start + 1) tail i (by
          simp only [List.length_cons] at hi
          omega)
      have hindex : start + (i + 1) = (start + 1) + i := by omega
      rw [hindex]
      simp only [List.getD_cons_succ, enumerateFrom, List.mem_cons]
      exact Or.inr ih

/-! ## 2. Corrected slab face coordinates -/

def slabPhysicalFaceEdges (extent : Nat) : List Nat :=
  List.range (boundaryCompleteSlabPlaquettes extent).length

def slabPlaquetteAt (extent id : Nat) : Z4Plaq :=
  (boundaryCompleteSlabPlaquettes extent).getD id fallbackPlaquette

theorem slabPhysicalFaceId_lt
    {extent id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    id < (boundaryCompleteSlabPlaquettes extent).length := by
  exact List.mem_range.mp hid

theorem slabPlaquetteAt_mem_enumerate
    {extent id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    (id, slabPlaquetteAt extent id) ∈
      enumerate (boundaryCompleteSlabPlaquettes extent) := by
  unfold enumerate slabPlaquetteAt
  simpa only [Nat.zero_add] using
    (enumerateFrom_getD_mem_local fallbackPlaquette 0
      (boundaryCompleteSlabPlaquettes extent) id
      (slabPhysicalFaceId_lt hid))

theorem slabPlaquetteAt_mem
    {extent id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    slabPlaquetteAt extent id ∈
      boundaryCompleteSlabPlaquettes extent := by
  have hindexed := slabPlaquetteAt_mem_enumerate hid
  have hmapped : slabPlaquetteAt extent id ∈
      (enumerate (boundaryCompleteSlabPlaquettes extent)).map Prod.snd :=
    List.mem_map.mpr
      ⟨(id, slabPlaquetteAt extent id), hindexed, rfl⟩
  rw [enumerate_map_snd] at hmapped
  exact hmapped

theorem slabPlaquetteAt_injective_on_physical
    {extent left right : Nat}
    (hleft : left ∈ slabPhysicalFaceEdges extent)
    (hright : right ∈ slabPhysicalFaceEdges extent)
    (heq : slabPlaquetteAt extent left = slabPlaquetteAt extent right) :
    left = right := by
  have hleftLt := slabPhysicalFaceId_lt hleft
  have hrightLt := slabPhysicalFaceId_lt hright
  apply List.getElem?_inj hleftLt
    (boundaryCompleteSlabPlaquettes_nodup extent)
  rw [List.getElem?_eq_getElem hleftLt,
    List.getElem?_eq_getElem hrightLt]
  have hleftGet := List.getElem_eq_getD
    (l := boundaryCompleteSlabPlaquettes extent)
    (i := left) (h := hleftLt) fallbackPlaquette
  have hrightGet := List.getElem_eq_getD
    (l := boundaryCompleteSlabPlaquettes extent)
    (i := right) (h := hrightLt) fallbackPlaquette
  change some ((boundaryCompleteSlabPlaquettes extent)[left]) =
    some ((boundaryCompleteSlabPlaquettes extent)[right])
  congr 1
  rw [hleftGet, hrightGet]
  exact heq

/-! ## 3. The numerical reflection involution -/

def slabFaceReflectId (extent id : Nat) : Nat :=
  listIndexOf
    (timeReflectPlaquette extent (slabPlaquetteAt extent id))
    (boundaryCompleteSlabPlaquettes extent)

theorem slabFaceReflectId_physical
    {extent id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    slabFaceReflectId extent id ∈ slabPhysicalFaceEdges extent := by
  unfold slabPhysicalFaceEdges slabFaceReflectId
  apply List.mem_range.mpr
  apply listIndexOf_lt_of_mem
  exact timeReflectPlaquette_mem_boundaryCompleteSlab
    (slabPlaquetteAt_mem hid)

theorem slabPlaquetteAt_slabFaceReflectId
    {extent id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    slabPlaquetteAt extent (slabFaceReflectId extent id) =
      timeReflectPlaquette extent (slabPlaquetteAt extent id) := by
  unfold slabPlaquetteAt slabFaceReflectId
  exact getD_listIndexOf_of_mem fallbackPlaquette _ _
    (timeReflectPlaquette_mem_boundaryCompleteSlab
      (slabPlaquetteAt_mem hid))

theorem slabFaceReflectId_involutive
    {extent id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    slabFaceReflectId extent (slabFaceReflectId extent id) = id := by
  have hreflectedPhysical := slabFaceReflectId_physical hid
  apply slabPlaquetteAt_injective_on_physical
    (slabFaceReflectId_physical hreflectedPhysical) hid
  rw [slabPlaquetteAt_slabFaceReflectId hreflectedPhysical,
    slabPlaquetteAt_slabFaceReflectId hid]
  apply timeReflectPlaquette_involutive
  exact ((mem_boundaryCompleteSlabPlaquettes extent _).mp
    (slabPlaquetteAt_mem hid)).2

theorem slabFaceReflectId_injective_on_physical
    {extent left right : Nat}
    (hleft : left ∈ slabPhysicalFaceEdges extent)
    (hright : right ∈ slabPhysicalFaceEdges extent)
    (heq : slabFaceReflectId extent left =
      slabFaceReflectId extent right) : left = right := by
  exact (slabFaceReflectId_involutive hleft).symm.trans
    ((congrArg (slabFaceReflectId extent) heq).trans
      (slabFaceReflectId_involutive hright))

theorem slabFaceReflectId_range_perm (extent : Nat) :
    (slabPhysicalFaceEdges extent).map (slabFaceReflectId extent) |>.Perm
      (slabPhysicalFaceEdges extent) := by
  apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · apply nodup_map_of_injOn
      (slabFaceReflectId extent) (slabPhysicalFaceEdges extent)
      (by unfold slabPhysicalFaceEdges; exact rangeNodupLocal _)
    intro left hleft right hright heq
    exact slabFaceReflectId_injective_on_physical hleft hright heq
  · unfold slabPhysicalFaceEdges
    exact rangeNodupLocal _
  · intro id
    constructor
    · intro hid
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hid
      rw [← hsourceEq]
      exact slabFaceReflectId_physical hsource
    · intro hid
      have hreflected := slabFaceReflectId_physical hid
      exact List.mem_map.mpr
        ⟨slabFaceReflectId extent id, hreflected,
          slabFaceReflectId_involutive hid⟩

/-! ## 4. Bounded physical face labellings -/

def reflectSlabFaceLabelling
    (extent : Nat) (physical : EdgeLabelling) : EdgeLabelling :=
  fun id => physical (slabFaceReflectId extent id)

def SlabFaceLabellingBounded
    (cutoff extent : Nat) (physical : EdgeLabelling) : Prop :=
  ∀ id, id ∈ slabPhysicalFaceEdges extent -> physical id ≤ cutoff

theorem reflectSlabFaceLabelling_bounded
    {cutoff extent : Nat} {physical : EdgeLabelling}
    (hbounded : SlabFaceLabellingBounded cutoff extent physical) :
    SlabFaceLabellingBounded cutoff extent
      (reflectSlabFaceLabelling extent physical) := by
  intro id hid
  exact hbounded _ (slabFaceReflectId_physical hid)

theorem reflectSlabFaceLabelling_involutive_on_physical
    (extent : Nat) (physical : EdgeLabelling)
    {id : Nat} (hid : id ∈ slabPhysicalFaceEdges extent) :
    reflectSlabFaceLabelling extent
        (reflectSlabFaceLabelling extent physical) id = physical id := by
  unfold reflectSlabFaceLabelling
  rw [slabFaceReflectId_involutive hid]

/-! ## 5. Exact heat-kernel face-factor invariance -/

def slabParametricKPhysicalFaceFactor
    (w : Q') (K extent : Nat) (physical : EdgeLabelling) : Q' :=
  eliminateLinks
    (fun edge => coeffAt (heatKernelPacket K w) (physical edge))
    (slabPhysicalFaceEdges extent)

private theorem eliminateLinks_comp_map
    (value : Nat -> Q') (reindex : Nat -> Nat) :
    ∀ ids : List Nat,
      eliminateLinks (fun id => value (reindex id)) ids =
        eliminateLinks value (ids.map reindex)
  | [] => rfl
  | head :: tail => by
      simp only [eliminateLinks, List.map_cons]
      rw [eliminateLinks_comp_map value reindex tail]

/-- The exact derived heat-kernel face product is reflection-invariant on the
corrected slab for every coupling and cutoff. -/
theorem slabParametricKPhysicalFaceFactor_reflection
    (w : Q') (K extent : Nat) (physical : EdgeLabelling) :
    slabParametricKPhysicalFaceFactor w K extent
        (reflectSlabFaceLabelling extent physical) ≈
      slabParametricKPhysicalFaceFactor w K extent physical := by
  unfold slabParametricKPhysicalFaceFactor reflectSlabFaceLabelling
  rw [eliminateLinks_comp_map
    (fun edge => coeffAt (heatKernelPacket K w) (physical edge))
    (slabFaceReflectId extent) (slabPhysicalFaceEdges extent)]
  exact eliminateLinks_perm _ (slabFaceReflectId_range_perm extent)

/-! ## Axiom audit -/

#print axioms listIndexOf_lt_of_mem
#print axioms getD_listIndexOf_of_mem
#print axioms slabPlaquetteAt_mem
#print axioms slabPlaquetteAt_injective_on_physical
#print axioms slabFaceReflectId_physical
#print axioms slabPlaquetteAt_slabFaceReflectId
#print axioms slabFaceReflectId_involutive
#print axioms slabFaceReflectId_range_perm
#print axioms reflectSlabFaceLabelling_bounded
#print axioms reflectSlabFaceLabelling_involutive_on_physical
#print axioms slabParametricKPhysicalFaceFactor_reflection

end YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
