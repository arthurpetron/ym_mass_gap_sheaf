/-
# Two distinct original links share at most one physical plaquette

Two distinct literal boundary links determine a coordinate unit plaquette.
Physical face identifiers are injective, so the existing original shared
face list has length at most one. Distinctness is essential: a link may be
incident to six faces. This is geometry only, not a conditional influence
or spatial-decay estimate.
-/

import YMGap.Continuum.BF4ExactSlabSharedFaceGeometry
import YMGap.Continuum.Z4PlaquetteBoundaryRigidity

namespace YMGap.Continuum.BF4ExactSlabSharedFaceUniqueness

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabSharedFaceGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4PlaquetteBoundaryRigidity

/-- The original shared-face list contains at most one identifier for distinct links. -/
theorem sharedIds_length_le_one (extent : Nat) (left right : Z4Link) (hne : left ≠ right) :
    (sharedIds extent left right).length ≤ 1 := by
  let ids := sharedIds extent left right
  have hn : ids.Nodup := List.filter_sublist.nodup (CayleyParentInj.range_nodup _)
  have hm (id : Nat) (hi : id ∈ ids) := (mem_sharedIds_iff extent left right id).mp hi
  change ids.length ≤ 1
  cases he : ids with
  | nil => exact Nat.zero_le _
  | cons a rest =>
      cases rest with
      | nil => exact Nat.le_refl _
      | cons b rest =>
          have ha := hm a (he ▸ List.mem_cons_self)
          have hb := hm b (he ▸ List.mem_cons_of_mem _ List.mem_cons_self)
          have hab : a = b := slabPlaquetteAt_injective_on_physical ha.1 hb.1
            (two_boundary_links_determine_face _ _ left right ha.2.1 ha.2.2 hne hb.2.1 hb.2.2)
          rw [he] at hn
          exact False.elim ((List.nodup_cons.mp hn).1 (List.mem_cons.mpr (Or.inl hab)))

end YMGap.Continuum.BF4ExactSlabSharedFaceUniqueness

#print axioms YMGap.Continuum.BF4ExactSlabSharedFaceUniqueness.sharedIds_length_le_one
