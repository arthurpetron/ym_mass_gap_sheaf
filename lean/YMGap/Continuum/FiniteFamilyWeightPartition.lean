/-
# Exact weighted partition of a finite family by a Boolean test

Filtering a family by a Boolean test and its complement partitions every
factor exactly.  Because rational multiplication is represented up to
`Q'.eqv`, the proof records the commutative regrouping explicitly.
-/

import YMGap.Continuum.FiniteCompatibilitySwitching

namespace YMGap.Continuum.FiniteFamilyWeightPartition

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas

local infix:50 " ≈ " => Q'.eqv

theorem familyWeight_filter_partition
    {A : Type} (weight : A → Q') (test : A → Bool) :
    ∀ family : List A,
      familyWeight weight family ≈
        familyWeight weight (family.filter test) *
          familyWeight weight (family.filter (fun item => !(test item)))
  | [] => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | head :: rest => by
      have ih := familyWeight_filter_partition weight test rest
      cases htest : test head with
      | true =>
          simp only [familyWeight_cons, List.filter_cons, htest,
            ↓reduceIte, Bool.not_true, Bool.false_eq_true]
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (weight head) _ _ ih)
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv (weight head)
                (familyWeight weight (rest.filter test))
                (familyWeight weight
                  (rest.filter (fun item => !(test item))))))
      | false =>
          simp only [familyWeight_cons, List.filter_cons, htest,
            Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (weight head) _ _ ih) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv (weight head)
                (familyWeight weight (rest.filter test))
                (familyWeight weight
                  (rest.filter (fun item => !(test item)))))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_comm_eqv (weight head)
                (familyWeight weight (rest.filter test)))) ?_
          exact Q'.mul_assoc_eqv
            (familyWeight weight (rest.filter test))
            (weight head)
            (familyWeight weight
              (rest.filter (fun item => !(test item))))

end YMGap.Continuum.FiniteFamilyWeightPartition

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteFamilyWeightPartition.familyWeight_filter_partition
