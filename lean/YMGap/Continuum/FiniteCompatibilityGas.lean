/-
# A finite hard-core gas with arbitrary compatibility and exact activities

This module isolates the constructive finite combinatorics needed by the
canonical cutoff-one polymer gas.  The atom type, Boolean compatibility
relation, and rational activity are all parameters.  In particular, no
face-disjointness convention is built into the definitions.

The central result is the exact add-one identity

  Z(a :: Gamma) = Z(Gamma) + z(a) Z(Gamma.filter (compat a)),

up to the repository's rational equivalence.  Its proof is a literal split of
the finite sublist enumeration.  This is the compatibility-correct starting
point for deletion recurrences and a signed Mayer/Ursell expansion.
-/

import YMGap.Continuum.PenroseDomInduction
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

namespace YMGap.Continuum.FiniteCompatibilityGas

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Families, weights, and the finite partition -/

/-- Pairwise compatibility in ambient-list order.  No symmetry assumption is
needed for the finite add-one identity. -/
def familyCompatibleB {A : Type} (compat : A → A → Bool) : List A → Bool
  | [] => true
  | head :: tail => tail.all (compat head) && familyCompatibleB compat tail

@[simp] theorem familyCompatibleB_nil {A : Type}
    (compat : A → A → Bool) :
    familyCompatibleB compat ([] : List A) = true := rfl

@[simp] theorem familyCompatibleB_cons {A : Type}
    (compat : A → A → Bool) (head : A) (tail : List A) :
    familyCompatibleB compat (head :: tail) =
      (tail.all (compat head) && familyCompatibleB compat tail) := rfl

/-- Product of exact rational single-atom activities. -/
def familyWeight {A : Type} (weight : A → Q') : List A → Q'
  | [] => 1
  | head :: tail => weight head * familyWeight weight tail

@[simp] theorem familyWeight_nil {A : Type} (weight : A → Q') :
    familyWeight weight ([] : List A) = 1 := rfl

@[simp] theorem familyWeight_cons {A : Type} (weight : A → Q')
    (head : A) (tail : List A) :
    familyWeight weight (head :: tail) =
      weight head * familyWeight weight tail := rfl

theorem familyWeight_nonnegative {A : Type} (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom) :
    ∀ family : List A, (0 : Q') ≤ familyWeight weight family
  | [] => by
      change (0 : Q') ≤ 1
      decide
  | head :: tail =>
      Q'.mul_nonneg _ _ (hweight head)
        (familyWeight_nonnegative weight hweight tail)

/-- The compatible subfamilies of a finite ambient atom list. -/
def compatibleFamilies {A : Type} (compat : A → A → Bool)
    (ambient : List A) : List (List A) :=
  (sublists ambient).filter (familyCompatibleB compat)

/-- Exact finite hard-core partition function. -/
def partition {A : Type} (compat : A → A → Bool)
    (weight : A → Q') (ambient : List A) : Q' :=
  listQSum (familyWeight weight) (compatibleFamilies compat ambient)

/-- Compatible subfamilies with an additional per-atom restriction. -/
def restrictedCompatibleFamilies {A : Type}
    (compat : A → A → Bool) (keep : A → Bool)
    (ambient : List A) : List (List A) :=
  (sublists ambient).filter
    (fun family => family.all keep && familyCompatibleB compat family)

def restrictedPartition {A : Type} (compat : A → A → Bool)
    (weight : A → Q') (keep : A → Bool) (ambient : List A) : Q' :=
  listQSum (familyWeight weight)
    (restrictedCompatibleFamilies compat keep ambient)

/-- Numerator of an arbitrary decidable event on compatible families. -/
def eventNumerator {A : Type} (compat : A → A → Bool)
    (weight : A → Q') (ambient : List A)
    (event : List A → Bool) : Q' :=
  listQSum (familyWeight weight)
    ((compatibleFamilies compat ambient).filter event)

/-! ## 2. Exact list-sum algebra -/

theorem listQSum_nonnegative_generic {B : Type} (value : B → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ xs : List B, (0 : Q') ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _ (hvalue head)
        (listQSum_nonnegative_generic value hvalue tail)

theorem partition_nonnegative {A : Type} (compat : A → A → Bool)
    (weight : A → Q') (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (ambient : List A) :
    (0 : Q') ≤ partition compat weight ambient := by
  unfold partition
  exact listQSum_nonnegative_generic _
    (familyWeight_nonnegative weight hweight) _

theorem eventNumerator_nonnegative {A : Type}
    (compat : A → A → Bool) (weight : A → Q')
    (hweight : ∀ atom, (0 : Q') ≤ weight atom)
    (ambient : List A) (event : List A → Bool) :
    (0 : Q') ≤ eventNumerator compat weight ambient event := by
  unfold eventNumerator
  exact listQSum_nonnegative_generic _
    (familyWeight_nonnegative weight hweight) _

private theorem listQSum_append_local {B : Type} (value : B → Q') :
    ∀ left right : List B,
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

private theorem listQSum_map_cons_weight {A : Type}
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

/-! ## 3. Restricting the ambient list -/

private theorem filter_const_false_local {B : Type} :
    ∀ xs : List B, xs.filter (fun _ => false) = []
  | [] => rfl
  | _ :: tail => filter_const_false_local tail

/-- Power-set enumeration commutes exactly with filtering the ambient list. -/
theorem sublists_filter {A : Type} (keep : A → Bool) :
    ∀ ambient : List A,
      sublists (ambient.filter keep) =
        (sublists ambient).filter (fun family => family.all keep)
  | [] => rfl
  | head :: tail => by
      cases hhead : keep head with
      | false =>
          simp only [List.filter_cons, hhead, Bool.false_eq_true,
            ↓reduceIte, sublists]
          rw [List.filter_append, List.filter_map]
          have hbranch :
              (sublists tail).filter
                  ((fun family => family.all keep) ∘
                    fun family => head :: family) = [] := by
            have heq :
                (sublists tail).filter
                    ((fun family => family.all keep) ∘
                      fun family => head :: family) =
                  (sublists tail).filter (fun _ => false) := by
              apply List.filter_congr
              intro family _
              simp only [Function.comp_apply, List.all_cons, hhead,
                Bool.false_and]
            rw [heq]
            exact filter_const_false_local _
          rw [hbranch, List.map_nil, List.append_nil]
          exact sublists_filter keep tail
      | true =>
          simp only [List.filter_cons, hhead, ↓reduceIte, sublists]
          rw [List.filter_append, List.filter_map]
          have hbranch :
              (sublists tail).filter
                  ((fun family => family.all keep) ∘
                    fun family => head :: family) =
                (sublists tail).filter (fun family => family.all keep) := by
            apply List.filter_congr
            intro family _
            simp only [Function.comp_apply, List.all_cons, hhead,
              Bool.true_and]
          rw [hbranch, ← sublists_filter keep tail]

/-- A restriction in the family predicate is literally the unrestricted gas
on the filtered ambient atom list. -/
theorem restrictedCompatibleFamilies_eq_filter {A : Type}
    (compat : A → A → Bool) (keep : A → Bool)
    (ambient : List A) :
    restrictedCompatibleFamilies compat keep ambient =
      compatibleFamilies compat (ambient.filter keep) := by
  unfold restrictedCompatibleFamilies compatibleFamilies
  rw [sublists_filter, List.filter_filter]
  apply List.filter_congr
  intro family _
  exact Bool.and_comm
    (family.all keep) (familyCompatibleB compat family)

theorem restrictedPartition_eq_filter {A : Type}
    (compat : A → A → Bool) (weight : A → Q')
    (keep : A → Bool) (ambient : List A) :
    restrictedPartition compat weight keep ambient =
      partition compat weight (ambient.filter keep) := by
  unfold restrictedPartition partition
  rw [restrictedCompatibleFamilies_eq_filter]

/-! ## 4. The exact add-one/delete recurrence -/

private theorem compatible_map_branch {A : Type}
    (compat : A → A → Bool) (head : A) (tail : List A) :
    ((sublists tail).map (fun family => head :: family)).filter
        (familyCompatibleB compat) =
      (restrictedCompatibleFamilies compat (compat head) tail).map
        (fun family => head :: family) := by
  rw [List.filter_map]
  rfl

/-- Exact finite hard-core add-one identity.  It assumes neither symmetry nor
any geometric interpretation of `compat`. -/
theorem partition_cons_split {A : Type}
    (compat : A → A → Bool) (weight : A → Q')
    (head : A) (tail : List A) :
    partition compat weight (head :: tail) ≈
      partition compat weight tail +
        weight head * partition compat weight
          (tail.filter (compat head)) := by
  unfold partition compatibleFamilies
  rw [sublists, List.filter_append]
  refine Q'.eqv_trans _ _ _
    (listQSum_append_local (familyWeight weight) _ _) ?_
  rw [compatible_map_branch]
  refine Q'.add_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_map_cons_weight weight head _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_of_eq
      (restrictedPartition_eq_filter compat weight (compat head) tail))

@[simp] theorem partition_nil {A : Type}
    (compat : A → A → Bool) (weight : A → Q') :
    partition compat weight ([] : List A) = 1 := rfl

/-- The vacuum family contributes one to every nonnegative finite gas. -/
theorem partition_ge_one {A : Type} (compat : A → A → Bool)
    (weight : A → Q') (hweight : ∀ atom, (0 : Q') ≤ weight atom) :
    ∀ ambient : List A, (1 : Q') ≤ partition compat weight ambient
  | [] => Q'.le_refl' 1
  | head :: tail => by
      refine Q'.le_trans' _ _ _
        (partition_ge_one compat weight hweight tail) ?_
      refine Q'.le_trans' _ _ _ ?_
        (Q'.ge_of_eqv (partition_cons_split compat weight head tail))
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (hweight head)
          (partition_nonnegative compat weight hweight _))

end YMGap.Continuum.FiniteCompatibilityGas

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteCompatibilityGas.familyWeight_nonnegative
#print axioms YMGap.Continuum.FiniteCompatibilityGas.sublists_filter
#print axioms YMGap.Continuum.FiniteCompatibilityGas.restrictedCompatibleFamilies_eq_filter
#print axioms YMGap.Continuum.FiniteCompatibilityGas.partition_cons_split
#print axioms YMGap.Continuum.FiniteCompatibilityGas.partition_ge_one
