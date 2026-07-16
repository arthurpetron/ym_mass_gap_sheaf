/-
# A marked-family bound for an arbitrary finite compatibility gas

For a finite hard-core gas with exact nonnegative activities, mark an
arbitrary Boolean class of atoms.  This module proves that the total weight
of compatible families containing at least one marked atom is bounded by

  (sum of the marked single-atom activities) * (the full partition).

The proof is a constructive add-one induction.  It is the generic finite-gas
form of the one-polymer bridge estimate and is intended for repeated pinned
layer deletion.  No thermodynamic, continuum, or Yang--Mills conclusion is
asserted here.
-/

import YMGap.Continuum.FiniteCompatibilityGas

namespace YMGap.Continuum.FiniteCompatibilityMarkedBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

variable {A : Type}

/-! ## Exact list algebra -/

private theorem listQSum_append_local (value : A → Q') :
    ∀ left right : List A,
      listQSum value (left ++ right) ≈
        listQSum value left + listQSum value right
  | [], right => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | head :: tail, right => by
      change value head + listQSum value (tail ++ right) ≈
        (value head + listQSum value tail) + listQSum value right
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_append_local value tail right)) ?_
      exact Q'.eqv_symm
        (Q'.add_assoc_eqv (value head)
          (listQSum value tail) (listQSum value right))

private theorem listQSum_map_cons_weight
    (weight : A → Q') (head : A) :
    ∀ families : List (List A),
      listQSum (familyWeight weight)
          (families.map (fun family => head :: family)) ≈
        weight head * listQSum (familyWeight weight) families
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv (weight head))
  | family :: families => by
      change weight head * familyWeight weight family +
          listQSum (familyWeight weight)
            (families.map (fun rest => head :: rest)) ≈
        weight head *
          (familyWeight weight family +
            listQSum (familyWeight weight) families)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_map_cons_weight weight head families)) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv (weight head)
          (familyWeight weight family)
          (listQSum (familyWeight weight) families))

private theorem filter_map_cons_local (head : A)
    (test : List A → Bool) (families : List (List A)) :
    (families.map (fun family => head :: family)).filter test =
      (families.filter (fun family => test (head :: family))).map
        (fun family => head :: family) := by
  rw [List.filter_map]
  rfl

private theorem filter_const_false_local {B : Type} :
    ∀ xs : List B, xs.filter (fun _ => false) = []
  | [] => rfl
  | _ :: tail => by
      simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte]
      exact filter_const_false_local tail

private theorem all_and_local (first second : A → Bool) :
    ∀ family : List A,
      (family.all first && family.all second) =
        family.all (fun atom => first atom && second atom)
  | [] => rfl
  | head :: tail => by
      simp only [List.all_cons, ← all_and_local first second tail]
      rw [Bool.and_assoc, Bool.and_assoc,
        ← Bool.and_assoc (tail.all first),
        ← Bool.and_assoc (second head)]
      rw [Bool.and_comm (tail.all first) (second head)]

private theorem listQSum_filter_le_local {B : Type}
    (value : B → Q') (test : B → Bool)
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ xs : List B,
      listQSum value (xs.filter test) ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_local value test hvalue tail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            ↓reduceIte, listQSum]
          have hhead : listQSum value tail ≤
              value head + listQSum value tail := by
            have h := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail)
                (hvalue head)
            rwa [Q'.zero_add'] at h
          exact Q'.le_trans' _ _ _ ih hhead
      | true =>
          simp only [List.filter_cons, htest, ↓reduceIte, listQSum]
          exact Q'.add_le_add_left _ _ _ ih

private theorem filter_filter_comm_local
    (first second : A → Bool) : ∀ ambient : List A,
    (ambient.filter first).filter second =
      (ambient.filter second).filter first
  | [] => rfl
  | head :: tail => by
      have ih := filter_filter_comm_local first second tail
      cases hfirst : first head <;> cases hsecond : second head <;>
        simp only [List.filter_cons, hfirst, hsecond,
          Bool.false_eq_true, ↓reduceIte] <;> rw [ih]

/-! ## Restricted partitions and their monotonicity -/

theorem restrictedPartition_nonnegative
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (keep : A → Bool) (ambient : List A) :
    (0 : Q') ≤ restrictedPartition compat weight keep ambient := by
  unfold restrictedPartition
  exact listQSum_nonnegative_generic _
    (familyWeight_nonnegative weight hweight) _

private theorem restrictedCompatibleFamilies_eq_family_filter
    (compat : A → A → Bool) (keep : A → Bool)
    (ambient : List A) :
    restrictedCompatibleFamilies compat keep ambient =
      (compatibleFamilies compat ambient).filter
        (fun family => family.all keep) := by
  unfold restrictedCompatibleFamilies compatibleFamilies
  rw [List.filter_filter]

/-- Removing atoms cannot increase a nonnegative finite-gas partition. -/
theorem partition_filter_le
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (keep : A → Bool) (ambient : List A) :
    partition compat weight (ambient.filter keep) ≤
      partition compat weight ambient := by
  rw [← restrictedPartition_eq_filter]
  unfold restrictedPartition partition
  rw [restrictedCompatibleFamilies_eq_family_filter]
  exact listQSum_filter_le_local _ _
    (familyWeight_nonnegative weight hweight) _

private theorem filter_and_eq_filter_filter
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun atom => first atom && second atom) =
      (ambient.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro atom _
  exact Bool.and_comm (first atom) (second atom)

/-- Strengthening the per-atom restriction cannot increase the partition. -/
theorem restrictedPartition_predicate_mono
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (first second : A → Bool) (ambient : List A) :
    restrictedPartition compat weight
        (fun atom => first atom && second atom) ambient ≤
      restrictedPartition compat weight first ambient := by
  rw [restrictedPartition_eq_filter, restrictedPartition_eq_filter]
  rw [filter_and_eq_filter_filter]
  exact partition_filter_le compat weight hweight second
    (ambient.filter first)

/-! ## Marked families and exact add-one branches -/

/-- Restricted compatible families containing at least one marked atom. -/
def markedRestrictedNumerator
    (compat : A → A → Bool) (weight : A → Q')
    (keep mark : A → Bool) (ambient : List A) : Q' :=
  listQSum (familyWeight weight)
    ((sublists ambient).filter (fun family =>
      (family.all keep && familyCompatibleB compat family) &&
        family.any mark))

/-- Sum of the marked single-atom activities in the ambient list. -/
def markedActivitySum (weight : A → Q')
    (mark : A → Bool) (ambient : List A) : Q' :=
  listQSum weight (ambient.filter mark)

theorem markedActivitySum_nonnegative
    (weight : A → Q') (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (mark : A → Bool) (ambient : List A) :
    (0 : Q') ≤ markedActivitySum weight mark ambient := by
  unfold markedActivitySum
  exact listQSum_nonnegative_generic weight hweight _

/-- Restricting the ambient atom list cannot increase the activity of a
fixed marked layer.  This is the monotonicity needed when several marked
layers are deleted successively. -/
theorem markedActivitySum_filter_le
    (weight : A → Q') (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (mark keep : A → Bool) (ambient : List A) :
    markedActivitySum weight mark (ambient.filter keep) ≤
      markedActivitySum weight mark ambient := by
  unfold markedActivitySum
  have hfiltered := listQSum_filter_le_local weight keep hweight
    (ambient.filter mark)
  have hreorder :
      (ambient.filter keep).filter mark =
        (ambient.filter mark).filter keep :=
    filter_filter_comm_local keep mark ambient
  rw [hreorder]
  exact hfiltered

theorem markedRestrictedNumerator_cons
    (compat : A → A → Bool) (weight : A → Q')
    (keep mark : A → Bool) (head : A) (tail : List A) :
    markedRestrictedNumerator compat weight keep mark (head :: tail) ≈
      markedRestrictedNumerator compat weight keep mark tail +
        listQSum (familyWeight weight)
          (((sublists tail).map (fun family => head :: family)).filter
            (fun family =>
              (family.all keep && familyCompatibleB compat family) &&
                family.any mark)) := by
  unfold markedRestrictedNumerator
  rw [sublists, List.filter_append]
  exact listQSum_append_local _ _ _

theorem markedRestrictedNumerator_mapbranch_none
    (compat : A → A → Bool) (keep mark : A → Bool)
    (head : A) (tail : List A) (hkeep : keep head = false) :
    (((sublists tail).map (fun family => head :: family)).filter
      (fun family =>
        (family.all keep && familyCompatibleB compat family) &&
          family.any mark)) = [] := by
  rw [filter_map_cons_local]
  have hcongr :
      (sublists tail).filter (fun family =>
          (((head :: family).all keep &&
              familyCompatibleB compat (head :: family)) &&
            (head :: family).any mark)) =
        (sublists tail).filter (fun _ => false) := by
    apply List.filter_congr
    intro family _
    simp only [List.all_cons, hkeep, Bool.false_and]
  rw [hcongr, filter_const_false_local, List.map_nil]

theorem markedRestrictedNumerator_mapbranch_marked
    (compat : A → A → Bool) (weight : A → Q')
    (keep mark : A → Bool) (head : A) (tail : List A)
    (hkeep : keep head = true) (hmark : mark head = true) :
    listQSum (familyWeight weight)
        (((sublists tail).map (fun family => head :: family)).filter
          (fun family =>
            (family.all keep && familyCompatibleB compat family) &&
              family.any mark)) ≈
      weight head * restrictedPartition compat weight
        (fun atom => keep atom && compat head atom) tail := by
  rw [filter_map_cons_local]
  have hcongr :
      (sublists tail).filter (fun family =>
          (((head :: family).all keep &&
              familyCompatibleB compat (head :: family)) &&
            (head :: family).any mark)) =
        (sublists tail).filter (fun family =>
          family.all (fun atom => keep atom && compat head atom) &&
            familyCompatibleB compat family) := by
    apply List.filter_congr
    intro family _
    simp only [List.any_cons, hmark, Bool.true_or, Bool.and_true,
      List.all_cons, hkeep, Bool.true_and, familyCompatibleB_cons]
    rw [← Bool.and_assoc,
      all_and_local keep (fun atom => compat head atom) family]
  rw [hcongr]
  unfold restrictedPartition restrictedCompatibleFamilies
  exact listQSum_map_cons_weight weight head _

theorem markedRestrictedNumerator_mapbranch_unmarked
    (compat : A → A → Bool) (weight : A → Q')
    (keep mark : A → Bool) (head : A) (tail : List A)
    (hkeep : keep head = true) (hmark : mark head = false) :
    listQSum (familyWeight weight)
        (((sublists tail).map (fun family => head :: family)).filter
          (fun family =>
            (family.all keep && familyCompatibleB compat family) &&
              family.any mark)) ≈
      weight head * markedRestrictedNumerator compat weight
        (fun atom => keep atom && compat head atom) mark tail := by
  rw [filter_map_cons_local]
  have hcongr :
      (sublists tail).filter (fun family =>
          (((head :: family).all keep &&
              familyCompatibleB compat (head :: family)) &&
            (head :: family).any mark)) =
        (sublists tail).filter (fun family =>
          (family.all (fun atom => keep atom && compat head atom) &&
            familyCompatibleB compat family) && family.any mark) := by
    apply List.filter_congr
    intro family _
    simp only [List.any_cons, hmark, Bool.false_or,
      List.all_cons, hkeep, Bool.true_and, familyCompatibleB_cons]
    rw [← Bool.and_assoc,
      all_and_local keep (fun atom => compat head atom) family]
  rw [hcongr]
  unfold markedRestrictedNumerator
  exact listQSum_map_cons_weight weight head _

/-! ## Restricted-partition add-one tools -/

private theorem restrictedPartition_mapbranch_true
    (compat : A → A → Bool) (weight : A → Q')
    (keep : A → Bool) (head : A) (tail : List A)
    (hkeep : keep head = true) :
    listQSum (familyWeight weight)
        (((sublists tail).map (fun family => head :: family)).filter
          (fun family =>
            family.all keep && familyCompatibleB compat family)) ≈
      weight head * restrictedPartition compat weight
        (fun atom => keep atom && compat head atom) tail := by
  rw [filter_map_cons_local]
  have hcongr :
      (sublists tail).filter (fun family =>
          ((head :: family).all keep &&
            familyCompatibleB compat (head :: family))) =
        (sublists tail).filter (fun family =>
          family.all (fun atom => keep atom && compat head atom) &&
            familyCompatibleB compat family) := by
    apply List.filter_congr
    intro family _
    simp only [List.all_cons, hkeep, Bool.true_and,
      familyCompatibleB_cons]
    rw [← Bool.and_assoc,
      all_and_local keep (fun atom => compat head atom) family]
  rw [hcongr]
  unfold restrictedPartition restrictedCompatibleFamilies
  exact listQSum_map_cons_weight weight head _

theorem restrictedPartition_cons_split_true
    (compat : A → A → Bool) (weight : A → Q')
    (keep : A → Bool) (head : A) (tail : List A)
    (hkeep : keep head = true) :
    restrictedPartition compat weight keep (head :: tail) ≈
      restrictedPartition compat weight keep tail +
        weight head * restrictedPartition compat weight
          (fun atom => keep atom && compat head atom) tail := by
  unfold restrictedPartition restrictedCompatibleFamilies
  rw [sublists, List.filter_append]
  exact Q'.eqv_trans _ _ _ (listQSum_append_local _ _ _) <|
    Q'.add_eqv_congr_left _ _ _
      (restrictedPartition_mapbranch_true compat weight keep
        head tail hkeep)

theorem restrictedPartition_le_cons
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (keep : A → Bool) (head : A) (tail : List A) :
    restrictedPartition compat weight keep tail ≤
      restrictedPartition compat weight keep (head :: tail) := by
  unfold restrictedPartition restrictedCompatibleFamilies
  rw [sublists, List.filter_append]
  let left := (sublists tail).filter
    (fun family => family.all keep && familyCompatibleB compat family)
  let right := ((sublists tail).map (fun family => head :: family)).filter
    (fun family => family.all keep && familyCompatibleB compat family)
  have hright : (0 : Q') ≤
      listQSum (familyWeight weight) right :=
    listQSum_nonnegative_generic _
      (familyWeight_nonnegative weight hweight) right
  have hadd : listQSum (familyWeight weight) left ≤
      listQSum (familyWeight weight) left +
        listQSum (familyWeight weight) right :=
    Q'.add_le_self_of_nonneg _ _ hright
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (listQSum_append_local (familyWeight weight) left right)))

theorem markedActivitySum_filter_le_cons
    (weight : A → Q') (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (mark : A → Bool) (head : A) (tail : List A) :
    markedActivitySum weight mark tail ≤
      markedActivitySum weight mark (head :: tail) := by
  unfold markedActivitySum
  cases hmark : mark head with
  | false =>
      simp only [List.filter_cons, hmark, Bool.false_eq_true, ↓reduceIte]
      exact Q'.le_refl' _
  | true =>
      simp only [List.filter_cons, hmark, ↓reduceIte, listQSum]
      have h := Q'.add_le_add_right
        (0 : Q') (weight head)
          (listQSum weight (tail.filter mark)) (hweight head)
      rwa [Q'.zero_add'] at h

/-! ## The marked-family bound -/

/-- Compatible restricted families hitting a marked class are bounded by
the marked one-atom activity sum times the full restricted partition. -/
theorem markedRestrictedNumerator_le_activitySum_mul_partition
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (mark : A → Bool) :
    ∀ (ambient : List A) (keep : A → Bool),
      markedRestrictedNumerator compat weight keep mark ambient ≤
        markedActivitySum weight mark ambient *
          restrictedPartition compat weight keep ambient
  | [], keep => by
      show (0 : Q') ≤ 0 * restrictedPartition compat weight keep []
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | head :: tail, keep => by
      have hpart0 := restrictedPartition_nonnegative compat weight
        hweight keep tail
      have hhead0 := hweight head
      have hsum0 := markedActivitySum_nonnegative weight hweight mark tail
      have ih := markedRestrictedNumerator_le_activitySum_mul_partition
        compat weight hweight mark tail keep
      cases hkeep : keep head with
      | false =>
          have hbranch := markedRestrictedNumerator_mapbranch_none
            compat keep mark head tail hkeep
          have hmarked :
              markedRestrictedNumerator compat weight keep mark
                  (head :: tail) ≈
                markedRestrictedNumerator compat weight keep mark tail := by
            refine Q'.eqv_trans _ _ _
              (markedRestrictedNumerator_cons compat weight keep mark
                head tail) ?_
            rw [hbranch]
            exact Q'.eqv_of_eq (Q'.add_zero' _)
          refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hmarked) ?_
          refine Q'.le_trans' _ _ _ ih ?_
          refine Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left _ _ _
              (restrictedPartition_le_cons compat weight hweight
                keep head tail) hsum0) ?_
          exact Q'.mul_le_mul_of_nonneg_right _ _ _
            (markedActivitySum_filter_le_cons weight hweight
              mark head tail)
            (restrictedPartition_nonnegative compat weight hweight
              keep (head :: tail))
      | true =>
          have hsplit := restrictedPartition_cons_split_true
            compat weight keep head tail hkeep
          cases hmark : mark head with
          | true =>
              have hbranch :=
                markedRestrictedNumerator_mapbranch_marked
                  compat weight keep mark head tail hkeep hmark
              have h1 :
                  markedRestrictedNumerator compat weight keep mark
                      (head :: tail) ≤
                    markedActivitySum weight mark tail *
                        restrictedPartition compat weight keep tail +
                      weight head * restrictedPartition compat weight
                        (fun atom => keep atom && compat head atom) tail := by
                refine Q'.le_trans' _ _ _
                  (Q'.le_of_eqv
                    (markedRestrictedNumerator_cons compat weight
                      keep mark head tail)) ?_
                exact Q'.add_le_add ih (Q'.le_of_eqv hbranch)
              have hrestricted :
                  restrictedPartition compat weight
                      (fun atom => keep atom && compat head atom) tail ≤
                    restrictedPartition compat weight keep tail :=
                restrictedPartition_predicate_mono compat weight hweight
                  keep (fun atom => compat head atom) tail
              have h2 :
                  weight head * restrictedPartition compat weight
                      (fun atom => keep atom && compat head atom) tail ≤
                    weight head *
                      restrictedPartition compat weight keep tail :=
                Q'.mul_le_mul_of_nonneg_left _ _ _ hrestricted hhead0
              have hfold :
                  markedActivitySum weight mark tail *
                        restrictedPartition compat weight keep tail +
                      weight head *
                        restrictedPartition compat weight keep tail ≈
                    (weight head + markedActivitySum weight mark tail) *
                      restrictedPartition compat weight keep tail := by
                refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
                exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
              have h3 :
                  markedRestrictedNumerator compat weight keep mark
                      (head :: tail) ≤
                    (weight head + markedActivitySum weight mark tail) *
                      restrictedPartition compat weight keep tail := by
                exact Q'.le_trans' _ _ _ h1
                  (Q'.le_trans' _ _ _
                    (Q'.add_le_add (Q'.le_refl' _) h2)
                    (Q'.le_of_eqv hfold))
              have hfactor0 : (0 : Q') ≤
                  weight head + markedActivitySum weight mark tail :=
                Q'.zero_le_add _ _ hhead0 hsum0
              have h4 :
                  (weight head + markedActivitySum weight mark tail) *
                      restrictedPartition compat weight keep tail ≤
                    (weight head + markedActivitySum weight mark tail) *
                      restrictedPartition compat weight keep
                        (head :: tail) :=
                Q'.mul_le_mul_of_nonneg_left _ _ _
                  (restrictedPartition_le_cons compat weight hweight
                    keep head tail) hfactor0
              have hsum : markedActivitySum weight mark (head :: tail) =
                  weight head + markedActivitySum weight mark tail := by
                unfold markedActivitySum
                simp only [List.filter_cons, hmark, ↓reduceIte, listQSum]
              rw [hsum]
              exact Q'.le_trans' _ _ _ h3 h4
          | false =>
              have hbranch :=
                markedRestrictedNumerator_mapbranch_unmarked
                  compat weight keep mark head tail hkeep hmark
              have ihRestricted :=
                markedRestrictedNumerator_le_activitySum_mul_partition
                  compat weight hweight mark tail
                    (fun atom => keep atom && compat head atom)
              have h1 :
                  markedRestrictedNumerator compat weight keep mark
                      (head :: tail) ≤
                    markedActivitySum weight mark tail *
                        restrictedPartition compat weight keep tail +
                      weight head *
                        (markedActivitySum weight mark tail *
                          restrictedPartition compat weight
                            (fun atom => keep atom && compat head atom)
                            tail) := by
                refine Q'.le_trans' _ _ _
                  (Q'.le_of_eqv
                    (markedRestrictedNumerator_cons compat weight
                      keep mark head tail)) ?_
                refine Q'.add_le_add ih ?_
                exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hbranch)
                  (Q'.mul_le_mul_of_nonneg_left _ _ _
                    ihRestricted hhead0)
              have hswap :
                  weight head *
                      (markedActivitySum weight mark tail *
                        restrictedPartition compat weight
                          (fun atom => keep atom && compat head atom) tail) ≈
                    markedActivitySum weight mark tail *
                      (weight head * restrictedPartition compat weight
                        (fun atom => keep atom && compat head atom) tail) := by
                refine Q'.eqv_trans _ _ _
                  (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
                refine Q'.eqv_trans _ _ _
                  (Q'.mul_eqv_congr_right _ _ _
                    (Q'.mul_comm_eqv _ _)) ?_
                exact Q'.mul_assoc_eqv _ _ _
              have hfold :
                  markedActivitySum weight mark tail *
                        restrictedPartition compat weight keep tail +
                      markedActivitySum weight mark tail *
                        (weight head * restrictedPartition compat weight
                          (fun atom => keep atom && compat head atom) tail) ≈
                    markedActivitySum weight mark tail *
                      restrictedPartition compat weight keep
                        (head :: tail) := by
                refine Q'.eqv_trans _ _ _
                  (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)) ?_
                exact Q'.mul_eqv_congr_left _ _ _
                  (Q'.eqv_symm hsplit)
              have hsum : markedActivitySum weight mark (head :: tail) =
                  markedActivitySum weight mark tail := by
                unfold markedActivitySum
                simp only [List.filter_cons, hmark, Bool.false_eq_true,
                  ↓reduceIte]
              rw [hsum]
              exact Q'.le_trans' _ _ _ h1
                (Q'.le_trans' _ _ _
                  (Q'.add_le_add (Q'.le_refl' _)
                    (Q'.le_of_eqv hswap))
                  (Q'.le_of_eqv hfold))

/-! ## Unrestricted finite-gas specialization -/

private theorem all_true_local : ∀ family : List A,
    family.all (fun _ => true) = true
  | [] => rfl
  | _ :: tail => by
      simp only [List.all_cons, Bool.true_and]
      exact all_true_local tail

theorem markedRestrictedNumerator_true_eq_eventNumerator
    (compat : A → A → Bool) (weight : A → Q')
    (mark : A → Bool) (ambient : List A) :
    markedRestrictedNumerator compat weight (fun _ => true) mark ambient =
      eventNumerator compat weight ambient (fun family => family.any mark) := by
  unfold markedRestrictedNumerator eventNumerator compatibleFamilies
  apply congrArg (listQSum (familyWeight weight))
  rw [List.filter_filter]
  apply List.filter_congr
  intro family _
  rw [all_true_local]
  exact Bool.and_comm
    (familyCompatibleB compat family) (family.any mark)

theorem restrictedPartition_true_eq_partition
    (compat : A → A → Bool) (weight : A → Q')
    (ambient : List A) :
    restrictedPartition compat weight (fun _ => true) ambient =
      partition compat weight ambient := by
  rw [restrictedPartition_eq_filter]
  have hfilter : ambient.filter (fun _ => true) = ambient := by
    induction ambient with
    | nil => rfl
    | cons head tail ih =>
        simp only [List.filter_cons, ↓reduceIte]
        rw [ih]
  rw [hfilter]

/-- Unrestricted marked-event numerator bound for an arbitrary exact finite
compatibility gas. -/
theorem markedEventNumerator_le_activitySum_mul_partition
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (mark : A → Bool) (ambient : List A) :
    eventNumerator compat weight ambient (fun family => family.any mark) ≤
      markedActivitySum weight mark ambient *
        partition compat weight ambient := by
  rw [← markedRestrictedNumerator_true_eq_eventNumerator]
  rw [← restrictedPartition_true_eq_partition]
  exact markedRestrictedNumerator_le_activitySum_mul_partition
    compat weight hweight mark ambient (fun _ => true)

/-! ## Exact avoidance split and one-layer deletion inequality -/

private theorem listQSum_filter_partition_local {B : Type}
    (value : B → Q') (test : B → Bool) :
    ∀ xs : List B,
      listQSum value xs ≈
        listQSum value (xs.filter test) +
          listQSum value (xs.filter (fun item => !(test item)))
  | [] => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
  | head :: tail => by
      have ih := listQSum_filter_partition_local value test tail
      cases htest : test head with
      | false =>
          simp only [listQSum, List.filter_cons, htest,
            Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (value head) _ _ ih) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.add_comm_eqv (value head)
                (listQSum value (tail.filter test)))) ?_
          exact Q'.add_assoc_eqv _ _ _
      | true =>
          simp only [listQSum, List.filter_cons, htest, ↓reduceIte,
            Bool.not_true, Bool.false_eq_true]
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (value head) _ _ ih) ?_
          exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem all_not_eq_not_any_local (mark : A → Bool) :
    ∀ family : List A,
      family.all (fun atom => !(mark atom)) = !(family.any mark)
  | [] => rfl
  | head :: tail => by
      rw [List.all_cons, List.any_cons,
        all_not_eq_not_any_local mark tail]
      cases mark head <;> cases tail.any mark <;> rfl

/-- The numerator of families avoiding every marked atom is exactly the
partition on the ambient list with those atoms deleted. -/
theorem avoidingEventNumerator_eq_partition_filter
    (compat : A → A → Bool) (weight : A → Q')
    (mark : A → Bool) (ambient : List A) :
    eventNumerator compat weight ambient
        (fun family => !(family.any mark)) =
      partition compat weight
        (ambient.filter (fun atom => !(mark atom))) := by
  rw [← restrictedPartition_eq_filter]
  unfold eventNumerator restrictedPartition
  rw [restrictedCompatibleFamilies_eq_family_filter]
  apply congrArg (listQSum (familyWeight weight))
  apply List.filter_congr
  intro family _
  exact (all_not_eq_not_any_local mark family).symm

/-- Literal marked/avoiding decomposition of the complete partition. -/
theorem partition_eqv_marked_add_avoiding
    (compat : A → A → Bool) (weight : A → Q')
    (mark : A → Bool) (ambient : List A) :
    partition compat weight ambient ≈
      eventNumerator compat weight ambient
          (fun family => family.any mark) +
        partition compat weight
          (ambient.filter (fun atom => !(mark atom))) := by
  unfold partition eventNumerator
  have hsplit := listQSum_filter_partition_local
    (familyWeight weight) (fun family : List A => family.any mark)
    (compatibleFamilies compat ambient)
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_of_eq
        (avoidingEventNumerator_eq_partition_filter
          compat weight mark ambient)))

/-- One marked layer can change the finite partition only through its exact
single-atom activity sum.  This division-free form is the input for any
explicit small-layer factor such as `sum ≤ 1/2`. -/
theorem partition_le_avoiding_add_activitySum_mul_partition
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (mark : A → Bool) (ambient : List A) :
    partition compat weight ambient ≤
      partition compat weight
          (ambient.filter (fun atom => !(mark atom))) +
        markedActivitySum weight mark ambient *
          partition compat weight ambient := by
  have hsplit := partition_eqv_marked_add_avoiding
    compat weight mark ambient
  have hmarked := markedEventNumerator_le_activitySum_mul_partition
    compat weight hweight mark ambient
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ hmarked) ?_
  exact Q'.le_of_eqv (Q'.add_comm_eqv _ _)

private theorem le_two_mul_of_le_add_half {value bound : Q'}
    (h : value ≤ bound + Q'.mkPos 1 2 (by decide) * value) :
    value ≤ Q'.ofNat 2 * bound := by
  let half : Q' := Q'.mkPos 1 2 (by decide)
  have hscaled : Q'.ofNat 2 * value ≤
      Q'.ofNat 2 * (bound + half * value) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h (by decide)
  have htwoHalf : Q'.ofNat 2 * half ≈ (1 : Q') := by
    decide
  have hcollapse : Q'.ofNat 2 * (half * value) ≈ value := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 2) half value)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ value htwoHalf) ?_
    exact Q'.one_mul_eqv value
  have hright : Q'.ofNat 2 * (bound + half * value) ≈
      Q'.ofNat 2 * bound + value := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.ofNat 2) bound (half * value)) ?_
    exact Q'.add_eqv_congr_left _ _ _ hcollapse
  have hreordered : Q'.ofNat 2 * value ≤
      value + Q'.ofNat 2 * bound :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ hright
          (Q'.add_comm_eqv _ _)))
  have hsub : Q'.ofNat 2 * value + -value ≤
      Q'.ofNat 2 * bound :=
    Q'.sub_le_of_le_add hreordered
  have htwo : Q'.ofNat 2 ≈ (1 : Q') + 1 := by
    decide
  have htwoValue : Q'.ofNat 2 * value ≈ value + value := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ value htwo) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (1 : Q') 1 value) ?_
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv value) (Q'.one_mul_eqv value)
  have hleft : Q'.ofNat 2 * value + -value ≈ value := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-value) htwoValue) ?_
    refine Q'.eqv_trans _ (value + (value + -value)) _
      (Q'.add_assoc_eqv value value (-value)) ?_
    refine Q'.eqv_trans _ (value + 0) _
      (Q'.add_eqv_congr_left value _ _
        (Q'.add_neg_self_eqv value)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' value)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hleft)) hsub

/-- If the total activity of one marked layer is at most one half, deleting
that entire layer costs at most the exact rational factor two. -/
theorem partition_le_two_mul_avoiding_of_activitySum_le_half
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (mark : A → Bool) (ambient : List A)
    (hsmall : markedActivitySum weight mark ambient ≤
      Q'.mkPos 1 2 (by decide)) :
    partition compat weight ambient ≤
      Q'.ofNat 2 * partition compat weight
        (ambient.filter (fun atom => !(mark atom))) := by
  have hraw := partition_le_avoiding_add_activitySum_mul_partition
    compat weight hweight mark ambient
  have hpartition0 := partition_nonnegative compat weight hweight ambient
  have hscaled :
      markedActivitySum weight mark ambient *
          partition compat weight ambient ≤
        Q'.mkPos 1 2 (by decide) *
          partition compat weight ambient :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsmall hpartition0
  have hhalf : partition compat weight ambient ≤
      partition compat weight
          (ambient.filter (fun atom => !(mark atom))) +
        Q'.mkPos 1 2 (by decide) *
          partition compat weight ambient :=
    Q'.le_trans' _ _ _ hraw
      (Q'.add_le_add_left _ _ _ hscaled)
  exact le_two_mul_of_le_add_half hhalf

end YMGap.Continuum.FiniteCompatibilityMarkedBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteCompatibilityMarkedBound.partition_filter_le
#print axioms YMGap.Continuum.FiniteCompatibilityMarkedBound.restrictedPartition_predicate_mono
#print axioms YMGap.Continuum.FiniteCompatibilityMarkedBound.markedActivitySum_filter_le
#print axioms YMGap.Continuum.FiniteCompatibilityMarkedBound.markedRestrictedNumerator_le_activitySum_mul_partition
#print axioms YMGap.Continuum.FiniteCompatibilityMarkedBound.markedEventNumerator_le_activitySum_mul_partition
#print axioms YMGap.Continuum.FiniteCompatibilityMarkedBound.avoidingEventNumerator_eq_partition_filter
#print axioms YMGap.Continuum.FiniteCompatibilityMarkedBound.partition_le_avoiding_add_activitySum_mul_partition
#print axioms YMGap.Continuum.FiniteCompatibilityMarkedBound.partition_le_two_mul_avoiding_of_activitySum_le_half
