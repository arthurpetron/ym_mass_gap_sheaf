/-
# Constructive named-Boolean reindexing for the elementary cube

The six outward elementary-cube faces expose their four trace indices in
face-major order.  The already contracted depth-twenty-four cube network,
however, reads the same independent indices in vertex-major numerical order.
This leaf certifies the finite permutation between those two name lists and
lifts it through the rational-complex named-Boolean sum.

Only the twenty-four tag names are inspected.  No Boolean assignment carrier
is constructed, and the depth-twenty-four addition tree is never unfolded,
simplified, evaluated, or printed.  In particular, this is a permutation of
additive binder names after Haar evaluation, not a permutation of polynomial
factors.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, bulk permutation
decider, or custom axiom.  The permutation witness is obtained structurally
from duplicate-freeness and exact membership using `List.Perm` constructors.
-/

import YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum
import YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge

namespace YMGap.Continuum.SU2QuaternionElementaryCubeNamedBoolReindex

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionRationalComplexNamedBoolSum
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge

/-! ## 1. Exact face-major tag carrier -/

/-- Flattening the six audited outward rows recovers exactly the established
face-corner tag carrier. -/
theorem radiusZeroElementaryCubeOutwardFaceRows_flatMap_tags :
    radiusZeroElementaryCubeOutwardFaceRows.flatMap
        TaggedOrientedPlaquetteRow.tags =
      radiusZeroElementaryCubeFaceCornerTags := by
  rfl

/-- The flattened row order is the literal face-major order supplied by the
six audited outward plaquettes.  The entries themselves remain the canonical
vertex-major tag names. -/
theorem radiusZeroElementaryCubeFaceCornerTags_eq_faceMajorOrder :
    radiusZeroElementaryCubeFaceCornerTags =
      [0, 9, 6, 3,
       1, 4, 15, 12,
       2, 13, 21, 10,
       14, 16, 18, 22,
       11, 23, 19, 7,
       5, 8, 20, 17] := by
  rfl

/-- Closed Boolean audit that every entry of the concrete face-major tag
word lies below twenty four.  This reduces only the twenty-four names. -/
private theorem radiusZeroElementaryCubeFaceCornerTags_all_lt :
    radiusZeroElementaryCubeFaceCornerTags.all
        (fun tag => decide (tag < 24)) = true := by
  decide

/-- Closed finite audit that every canonical tag below twenty four occurs in
the concrete face-major word. -/
private theorem radiusZeroElementaryCubeFinTag_mem_faceCornerTags :
    ∀ tag : Fin 24,
      tag.1 ∈ radiusZeroElementaryCubeFaceCornerTags := by
  decide

/-- Exact membership characterization of the flattened face-major tag list.
This checks only twenty-four names and does not inspect Boolean assignments. -/
theorem radiusZeroElementaryCubeFaceCornerTags_mem_iff (tag : Nat) :
    tag ∈ radiusZeroElementaryCubeFaceCornerTags ↔ tag < 24 := by
  constructor
  · intro hmem
    have hcheck := List.all_eq_true.mp
      radiusZeroElementaryCubeFaceCornerTags_all_lt tag hmem
    exact of_decide_eq_true hcheck
  · intro hlt
    exact radiusZeroElementaryCubeFinTag_mem_faceCornerTags ⟨tag, hlt⟩

/-! ## 2. Constructive permutation certificate -/

/-- Local axiom-clean duplicate-freeness proof for `List.range`.  The core
`List.nodup_range` is deliberately avoided because its implementation in the
project toolchain passes through a classical simplification certificate. -/
private theorem rangeNodupLocal (count : Nat) :
    (List.range count).Nodup := by
  induction count with
  | zero => exact List.nodup_nil
  | succ count ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = count := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl count)

/-- Duplicate-free lists with the same members are constructively
permutations.  The membership proof itself supplies every split position, so
no decidable equality or finite permutation decider is needed. -/
private theorem permOfNodupMemIff {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hy := (hmem item).1
            (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := permOfNodupMemIff
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

/-- The face-major reading contains every canonical tag `0, ..., 23`
exactly once.  This is the finite name permutation used by the binder bridge. -/
theorem radiusZeroElementaryCubeFaceCornerTags_perm_range :
    radiusZeroElementaryCubeFaceCornerTags.Perm (List.range 24) := by
  apply permOfNodupMemIff
  · exact radiusZeroElementaryCubeFaceCornerTags_nodup
  · exact rangeNodupLocal 24
  · intro tag
    exact (radiusZeroElementaryCubeFaceCornerTags_mem_iff tag).trans
      List.mem_range.symm

/-! ## 3. Additive named-binder reindex -/

/-- **Elementary-cube named-Boolean reindexing.**  For every opaque
rational-complex integrand on named Boolean environments, summing in the six
face rows' order agrees with summing in canonical vertex-major order.

The proof transports the explicit finite tag permutation through the generic
named-binder theorem.  It does not commute raw complex-polynomial binders and
does not enumerate any of the `2^24` assignments. -/
theorem rationalComplexNamedBoolSum_radiusZeroElementaryCubeFaceCornerTags_eq_range
    (family : (Nat → Bool) → RationalComplex) :
    RationalComplexEqv
      (rationalComplexNamedBoolSum
        radiusZeroElementaryCubeFaceCornerTags family)
      (rationalComplexNamedBoolSum (List.range 24) family) :=
  rationalComplexNamedBoolSum_perm
    radiusZeroElementaryCubeFaceCornerTags_perm_range family

#print axioms radiusZeroElementaryCubeOutwardFaceRows_flatMap_tags
#print axioms radiusZeroElementaryCubeFaceCornerTags_eq_faceMajorOrder
#print axioms radiusZeroElementaryCubeFaceCornerTags_mem_iff
#print axioms radiusZeroElementaryCubeFaceCornerTags_perm_range
#print axioms rationalComplexNamedBoolSum_radiusZeroElementaryCubeFaceCornerTags_eq_range

end YMGap.Continuum.SU2QuaternionElementaryCubeNamedBoolReindex
