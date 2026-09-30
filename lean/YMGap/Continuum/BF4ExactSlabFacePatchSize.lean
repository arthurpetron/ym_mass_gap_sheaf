/-
# Four-link bound for selected original physical face patches

Each literal selected patch is a duplicate-free sublist of the original
eight-layer schedule. A face has four distinct physical boundary links;
after fixing one patch member, at most three other members remain.
-/

import YMGap.Continuum.BF4ExactSlabFacePatchIncidence
import YMGap.Continuum.BF4ExactSlabWardIncidenceSum

namespace YMGap.Continuum.BF4ExactSlabFacePatchSize

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabFacePatchIncidence
open YMGap.Continuum.BF4ExactSlabWardIncidenceSum

private instance (extent : Nat) : DecidableEq (PhysicalLink extent) :=
  inferInstanceAs (DecidableEq {i // i ∈
    YMGap.Continuum.Z4HalfTimeReflectionGeometry.boundaryCompleteSlabLinks extent})

/-- The actual schedule links belonging to one original physical face. -/
def facePatch (extent id : Nat) : List (PhysicalLink extent) :=
  (schedule extent).filter (keep extent id)

theorem facePatch_nodup (extent id : Nat) : (facePatch extent id).Nodup :=
  List.filter_sublist.nodup (physical_schedule_nodup extent)

/-- This is the pre-existing face row, specialized to the actual schedule. -/
theorem facePatch_eq_faceRow (extent id : Nat) :
    facePatch extent id = faceRow extent id (schedule extent) := rfl

theorem facePatch_length_le_four (extent id : Nat) :
    (facePatch extent id).length ≤ 4 := by
  rw [facePatch_eq_faceRow]
  exact faceRow_length_le_four extent id (schedule extent)
    (physical_schedule_nodup extent)

private theorem filter_other_length_lt {A : Type} [DecidableEq A] :
    ∀ (xs : List A) (i : A), i ∈ xs →
      (xs.filter (fun j => if i = j then false else true)).length < xs.length
  | [], _, h => False.elim (List.not_mem_nil h)
  | x::xs, i, h => by
      rcases List.mem_cons.mp h with heq | htail
      · subst i
        simp only [List.filter_cons, List.length_cons]
        exact Nat.lt_succ_of_le (List.length_filter_le _ _)
      · by_cases heq : i = x
        · subst i
          simp only [List.filter_cons, List.length_cons]
          exact Nat.lt_succ_of_le (List.length_filter_le _ _)
        · have ht := filter_other_length_lt xs i htail
          simpa only [List.filter_cons, List.length_cons, if_neg heq] using
            Nat.succ_lt_succ ht

/-- With one selected member fixed, the patch has at most three other
physical links. The predicate retains only literal unequal subtype links. -/
theorem facePatch_other_length_le_three (extent id : Nat)
    (i : PhysicalLink extent) (hi : i ∈ facePatch extent id) :
    ((facePatch extent id).filter
      (fun j => if i = j then false else true)).length ≤ 3 := by
  have hlt := filter_other_length_lt (facePatch extent id) i hi
  have hfour := facePatch_length_le_four extent id
  omega

#print axioms facePatch
#print axioms facePatch_nodup
#print axioms facePatch_eq_faceRow
#print axioms facePatch_length_le_four
#print axioms facePatch_other_length_le_three

end YMGap.Continuum.BF4ExactSlabFacePatchSize
