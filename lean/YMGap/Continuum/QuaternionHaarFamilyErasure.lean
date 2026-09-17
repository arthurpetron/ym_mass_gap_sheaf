/-
# Positional erasure expansion of the finite-family dual flow

Single and double cuts retain all unselected factors in their original order.
They do not compare polynomial factors or discard repeated entries. The exact
coefficient identities expose the signed one-erasure diagonal and unordered
two-erasure cross terms of the existing finite-family cost. No positivity,
centering, norm budget, or spectral gap is asserted by these algebraic pins.
-/

import YMGap.Continuum.QuaternionHaarFiniteFamilyDual
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.SU2QuaternionRatPolyDifferential

namespace YMGap.Continuum.QuaternionHaarFamilyErasure

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarFiniteFamilyDual

/-- Every positional single cut, together with its ordered remainder. -/
def singleCuts {A : Type} : List A → List (A × List A)
  | [] => []
  | i :: ids => (i, ids) :: (singleCuts ids).map (fun p => (p.1, i :: p.2))

/-- Every positional unordered pair, in its original order, and its remainder. -/
def pairCuts {A : Type} : List A → List (A × A × List A)
  | [] => []
  | i :: ids =>
      (singleCuts ids).map (fun p => (i, p.1, p.2)) ++
        (pairCuts ids).map (fun p => (p.1, p.2.1, i :: p.2.2))

/-- A single cut only permutes the original occurrences. -/
theorem singleCuts_perm {A : Type} {ids : List A} {i : A} {rest : List A}
    (hm : (i, rest) ∈ singleCuts ids) : ids.Perm (i :: rest) := by
  induction ids generalizing i rest with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons a ids ih =>
      rcases List.mem_cons.mp hm with he | ht
      · rcases Prod.mk.inj he with ⟨hi, hr⟩
        subst i
        subst rest
        exact List.Perm.refl _
      · obtain ⟨⟨j, js⟩, hj, he⟩ := List.mem_map.mp ht
        rcases Prod.mk.inj he with ⟨hi, hr⟩
        subst i
        subst rest
        exact (List.Perm.cons a (ih hj)).trans (List.Perm.swap j a js)

/-- A double cut only permutes the original occurrences. -/
theorem pairCuts_perm {A : Type} {ids : List A} {i j : A} {rest : List A}
    (hm : (i, j, rest) ∈ pairCuts ids) : ids.Perm (i :: j :: rest) := by
  induction ids generalizing i j rest with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons a ids ih =>
      rcases List.mem_append.mp hm with hh | ht
      · obtain ⟨⟨b, bs⟩, hb, he⟩ := List.mem_map.mp hh
        rcases Prod.mk.inj he with ⟨hi, he⟩
        rcases Prod.mk.inj he with ⟨hj, hr⟩
        subst i
        subst j
        subst rest
        exact List.Perm.cons a (singleCuts_perm hb)
      · obtain ⟨⟨b, c, bs⟩, hb, he⟩ := List.mem_map.mp ht
        rcases Prod.mk.inj he with ⟨hi, he⟩
        rcases Prod.mk.inj he with ⟨hj, hr⟩
        subst i
        subst j
        subst rest
        exact (List.Perm.cons a (ih hb)).trans
          ((List.Perm.swap b a (c :: bs)).trans
            (List.Perm.cons b (List.Perm.swap c a bs)))

/-- The indexed factor/test presentation preserves the original product. -/
theorem product_indexed {A : Type} (factor test : A → RatPoly) (ids : List A) :
    product (ids.map (fun i => (factor i, test i))) = polynomialProduct factor ids := by
  induction ids with
  | nil => rfl
  | cons i ids ih =>
      change polyMul (factor i) (product (ids.map (fun j => (factor j, test j)))) =
        polyMul (factor i) (polynomialProduct factor ids)
      rw [ih]

/-- The signed single-erasure sum. -/
def singleSum {A : Type} (factor test : A → RatPoly) (ids : List A) : RatPoly :=
  polySum ((singleCuts ids).map
    (fun p => polyMul (polynomialProduct factor p.2) (test p.1)))

/-- The signed pair-erasure sum, with each positional unordered pair once. -/
def pairSum {A : Type} (factor test : A → RatPoly) (ids : List A) : RatPoly :=
  polySum ((pairCuts ids).map
    (fun p => polyMul (polynomialProduct factor p.2.2)
      (polyMul (test p.1) (test p.2.1))))

private theorem sum_congr {A : Type} (ids : List A) (f g : A → RatPoly)
    (h : ∀ i, i ∈ ids → RatPolyCoeffEqv (f i) (g i)) :
    RatPolyCoeffEqv (polySum (ids.map f)) (polySum (ids.map g)) := by
  revert h
  induction ids with
  | nil => intro _; exact RatPolyCoeffEqv.refl _
  | cons i ids ih =>
      intro h
      exact RatPolyCoeffEqv.add (h i List.mem_cons_self)
        (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem sum_mul_left {A : Type} (a : RatPoly) (f : A → RatPoly)
    (ids : List A) :
    RatPolyCoeffEqv (polyMul a (polySum (ids.map f)))
      (polySum (ids.map (fun i => polyMul a (f i)))) := by
  simpa only [List.map_map, Function.comp_def] using
    (RatPolyCoeffEqv.mul_polySum_right a (ids.map f))

/-- The single-cut recurrence, before any Haar integration. -/
theorem singleSum_cons {A : Type} (factor test : A → RatPoly) (i : A) (ids : List A) :
    RatPolyCoeffEqv (singleSum factor test (i :: ids))
      (polyAdd (polyMul (polynomialProduct factor ids) (test i))
        (polyMul (factor i) (singleSum factor test ids))) := by
  have ht : RatPolyCoeffEqv
      (polySum ((singleCuts ids).map (fun p =>
        polyMul (polyMul (factor i) (polynomialProduct factor p.2)) (test p.1))))
      (polyMul (factor i) (singleSum factor test ids)) :=
    (sum_congr (singleCuts ids) _ _ (fun p _ =>
      RatPolyCoeffEqv.mul_assoc _ _ _)).trans (sum_mul_left (factor i) _ _).symm
  simpa only [singleSum, singleCuts, List.map_cons, List.map_map,
    Function.comp_def, polySum] using
    (RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.refl (polyMul (polynomialProduct factor ids) (test i))) ht)

set_option maxHeartbeats 800000 in
/-- The pair-cut recurrence retains the cross term with its original sign. -/
theorem pairSum_cons {A : Type} (factor test : A → RatPoly) (i : A) (ids : List A) :
    RatPolyCoeffEqv (pairSum factor test (i :: ids))
      (polyAdd (polyMul (test i) (singleSum factor test ids))
        (polyMul (factor i) (pairSum factor test ids))) := by
  have hh : RatPolyCoeffEqv
      (polySum ((singleCuts ids).map (fun p =>
        polyMul (polynomialProduct factor p.2) (polyMul (test i) (test p.1)))))
      (polyMul (test i) (singleSum factor test ids)) :=
    (sum_congr (singleCuts ids) _ _ (fun p _ =>
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm.trans
        (((RatPolyCoeffEqv.mul_comm _ _).mul_right _).trans
          (RatPolyCoeffEqv.mul_assoc _ _ _)))).trans
      (sum_mul_left (test i) _ _).symm
  have ht : RatPolyCoeffEqv
      (polySum ((pairCuts ids).map (fun p =>
        polyMul (polyMul (factor i) (polynomialProduct factor p.2.2))
          (polyMul (test p.1) (test p.2.1)))))
      (polyMul (factor i) (pairSum factor test ids)) :=
    (sum_congr (pairCuts ids) _ _ (fun p _ =>
      RatPolyCoeffEqv.mul_assoc _ _ _)).trans (sum_mul_left (factor i) _ _).symm
  have hs := (RatPolyCoeffEqv.polySum_append
    ((singleCuts ids).map (fun p =>
      polyMul (polynomialProduct factor p.2) (polyMul (test i) (test p.1))))
    ((pairCuts ids).map (fun p =>
      polyMul (polyMul (factor i) (polynomialProduct factor p.2.2))
        (polyMul (test p.1) (test p.2.1))))).symm.trans (hh.add ht)
  simpa only [pairSum, pairCuts, List.map_append, List.map_map, Function.comp_def] using hs

/-- Exact one-erasure expansion of the finite-family flow. -/
theorem flow_expansion {A : Type} (factor test : A → RatPoly) (ids : List A) :
    RatPolyCoeffEqv (flow (ids.map (fun i => (factor i, test i))))
      (singleSum factor test ids) := by
  induction ids with
  | nil => exact RatPolyCoeffEqv.zero_smul polyOne
  | cons i ids ih =>
      change RatPolyCoeffEqv
        (polyAdd (polyMul (product (ids.map (fun j => (factor j, test j)))) (test i))
          (polyMul (factor i) (flow (ids.map (fun j => (factor j, test j)))))) _
      rw [product_indexed factor test ids]
      exact ((RatPolyCoeffEqv.refl _).add (ih.mul_left _)).trans
        (singleSum_cons factor test i ids).symm

private theorem cost_reassociate (p x a d l q c : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd
        (polyAdd (polyMul p (polyMul x x))
          (polyMul a (polyAdd d (polyMul c (polyAdd q q)))))
        (polyMul c (polyAdd (polyMul x l) (polyMul x l))))
      (polyAdd
        (polyAdd (polyMul p (polyMul x x)) (polyMul a d))
        (polyMul c
          (polyAdd (polyAdd (polyMul x l) (polyMul a q))
            (polyAdd (polyMul x l) (polyMul a q))))) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.var 2) (.add (.var 3) (.mul (.var 6) (.add (.var 5) (.var 5))))))
      (.mul (.var 6) (.add (.mul (.var 1) (.var 4)) (.mul (.var 1) (.var 4)))))
    (.add
      (.add (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 3)))
      (.mul (.var 6)
        (.add (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 5)))
          (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 5))))))
    (by decide) (fun
      | 0 => p | 1 => x | 2 => a | 3 => d | 4 => l | 5 => q | _ => c)

/-- Exact signed cost: one-erasure squares plus twice the unordered pair sum.
No pair term has been discarded or replaced by its absolute value. -/
theorem cost_expansion {A : Type} (h : Q') (factor test : A → RatPoly) (ids : List A) :
    RatPolyCoeffEqv (cost h (ids.map (fun i => (factor i, test i))))
      (polyAdd (singleSum factor (fun i => polyMul (test i) (test i)) ids)
        (polyMul (cap h) (polyAdd (pairSum factor test ids) (pairSum factor test ids)))) := by
  induction ids with
  | nil =>
      exact (RatPolyCoeffEqv.zero_smul polyOne).trans
        ((RatPolyCoeffEqv.zero_add _).trans
          (RatPolyCoeffEqv.mul_zero_right (cap h))).symm
  | cons i ids ih =>
      change RatPolyCoeffEqv
        (polyAdd
          (polyAdd (polyMul (product (ids.map (fun j => (factor j, test j))))
              (polyMul (test i) (test i)))
            (polyMul (factor i) (cost h (ids.map (fun j => (factor j, test j))))))
          (polyMul (cap h)
            (polyAdd (polyMul (test i) (flow (ids.map (fun j => (factor j, test j)))))
              (polyMul (test i) (flow (ids.map (fun j => (factor j, test j)))))))) _
      rw [product_indexed factor test ids]
      have hf := (flow_expansion factor test ids).mul_left (test i)
      have he := ((RatPolyCoeffEqv.refl
        (polyMul (polynomialProduct factor ids) (polyMul (test i) (test i)))).add
          (ih.mul_left (factor i))).add
        ((hf.add hf).mul_left (cap h))
      have hd := singleSum_cons factor (fun j => polyMul (test j) (test j)) i ids
      have hp := pairSum_cons factor test i ids
      exact he.trans ((cost_reassociate (polynomialProduct factor ids) (test i) (factor i)
        (singleSum factor (fun j => polyMul (test j) (test j)) ids)
        (singleSum factor test ids) (pairSum factor test ids) (cap h)).trans
          (hd.add ((hp.add hp).mul_left (cap h))).symm)

end YMGap.Continuum.QuaternionHaarFamilyErasure

#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.singleCuts
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.pairCuts
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.singleCuts_perm
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.pairCuts_perm
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.product_indexed
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.singleSum
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.pairSum
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.singleSum_cons
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.pairSum_cons
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.flow_expansion
#print axioms YMGap.Continuum.QuaternionHaarFamilyErasure.cost_expansion
