/-
# Count-compressed Gaussian recurrence for actual translated coordinate words

Equal-label contractions leave coefficient-equivalent words. Their sum is
therefore the number of matching labels times one erased word and the
actual tail radius. The partial Gaussian product law pulls out that radius,
giving a recurrence that removes TWO coordinate factors per nonzero step.
All word lengths and all tail coefficient probes are retained.
-/

import YMGap.Continuum.SU2QuaternionTranslationGaussianStein
import YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct

namespace YMGap.Continuum.SU2QuaternionTranslationGaussianCountRecursion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct
open YMGap.Continuum.SU2QuaternionTranslationGaussianStein

private theorem mul_swap (a b c : RatPoly) :
    RatPolyCoeffEqv (polyMul a (polyMul b c)) (polyMul b (polyMul a c)) :=
  (RatPolyCoeffEqv.mul_assoc a b c).symm.trans
    (((RatPolyCoeffEqv.mul_comm a b).mul_right c).trans (RatPolyCoeffEqv.mul_assoc b a c))

private theorem scale_mul_swap (a : Q') (l r p : RatPoly) :
    RatPolyCoeffEqv (polyMul l (polySmul a (polyMul r p)))
      (polySmul a (polyMul r (polyMul l p))) :=
  (RatPolyCoeffEqv.polyMul_smul_right a l (polyMul r p)).trans ((mul_swap l r p).smul a)

/-- Erasing one existing label removes exactly one factor from the actual
word; only the commuting REAL coordinate polynomials are reordered. -/
theorem translatedWord_erase (right : Bool) (i : Fin 4) : ∀ word : List (Fin 4), i ∈ word →
    RatPolyCoeffEqv (translatedWord right word)
      (polyMul (translatedCoordinate right i) (translatedWord right (word.erase i)))
  | [], h => False.elim (List.not_mem_nil h)
  | j :: rest, h => by
    by_cases hji : j = i
    · subst j
      simp only [List.erase_cons_head]
      exact RatPolyCoeffEqv.refl _
    · have hr : i ∈ rest := by
        rcases List.mem_cons.mp h with h | h
        · exact False.elim (hji h.symm)
        · exact h
      rw [List.erase_cons_tail (by simp [hji])]
      exact ((translatedWord_erase right i rest hr).mul_left (translatedCoordinate right j)).trans
        (mul_swap (translatedCoordinate right j) (translatedCoordinate right i) (translatedWord right (rest.erase i)))

private theorem scaled_erase (right : Bool) (i : Fin 4) (word : List (Fin 4)) :
    RatPolyCoeffEqv
      (polySmul (Q'.ofNat (word.count i))
        (polyMul (translatedCoordinate right i) (translatedWord right (word.erase i))))
      (polySmul (Q'.ofNat (word.count i)) (translatedWord right word)) := by
  by_cases hm : i ∈ word
  · exact (translatedWord_erase right i word hm).symm.smul _
  · rw [List.count_eq_zero_of_not_mem hm]
    exact (RatPolyCoeffEqv.zero_smul _).trans (RatPolyCoeffEqv.zero_smul _).symm

private theorem scaled_erase_radius (right : Bool) (i : Fin 4) (word : List (Fin 4)) :
    RatPolyCoeffEqv
      (polySmul (Q'.ofNat (word.count i)) (polyMul (quaternionRadiusPolynomial 1)
        (polyMul (translatedCoordinate right i) (translatedWord right (word.erase i)))))
      (polySmul (Q'.ofNat (word.count i)) (polyMul (quaternionRadiusPolynomial 1) (translatedWord right word))) :=
  (RatPolyCoeffEqv.polyMul_smul_right _ _ _).symm.trans
    (((scaled_erase right i word).mul_left (quaternionRadiusPolynomial 1)).trans
      (RatPolyCoeffEqv.polyMul_smul_right _ _ _))

/-- Every matching contraction is the same erased coordinate product.
No pairings or moment tables are enumerated. -/
theorem contractedWord_eq_count (right : Bool) (i : Fin 4) : ∀ word : List (Fin 4),
    RatPolyCoeffEqv (contractedWord right i word)
      (polySmul (Q'.ofNat (word.count i))
        (polyMul (quaternionRadiusPolynomial 1) (translatedWord right (word.erase i))))
  | [] => (RatPolyCoeffEqv.zero_smul _).symm
  | j :: rest => by
    by_cases hij : i = j
    · subst j
      simp only [contractedWord, List.count_cons_self, List.erase_cons_head]
      have ht := ((contractedWord_eq_count right i rest).mul_left (translatedCoordinate right i)).trans
        ((scale_mul_swap (Q'.ofNat (rest.count i)) (translatedCoordinate right i)
          (quaternionRadiusPolynomial 1) (translatedWord right (rest.erase i))).trans
          (scaled_erase_radius right i rest))
      refine ((RatPolyCoeffEqv.one_smul _).symm.add ht).trans ?_
      refine (RatPolyCoeffEqv.add_smul_same 1 (Q'.ofNat (rest.count i)) _).trans ?_
      exact RatPolyCoeffEqv.smul_coefficient
        (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 1 (Q'.ofNat (rest.count i)))
          (Q'.eqv_symm (Q'.ofNat_add_eqv (rest.count i) 1))) _
    · have hji : j ≠ i := fun h => hij h.symm
      have herase : (j :: rest).erase i = j :: rest.erase i := List.erase_cons_tail (by simp [hji])
      simp only [contractedWord, if_neg hij, List.count_cons_of_ne hji,
        herase, translatedWord]
      refine ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.refl _)).trans ?_
      refine (RatPolyCoeffEqv.zero_add _).trans ?_
      exact ((contractedWord_eq_count right i rest).mul_left (translatedCoordinate right j)).trans
        (scale_mul_swap _ _ _ _)

/-- The original partial Gaussian moments satisfy a two-factor descent:
E[L_i word] = count_i(word) * |a|^2 * E[word with one i erased].
The identity holds even when the count is zero; no division is used. -/
theorem translatedWord_gaussian_count (right : Bool) (i : Fin 4) (word : List (Fin 4)) :
    RatPolyCoeffEqv (partialGaussianHead (translatedWord right (i :: word)))
      (polySmul (Q'.ofNat (word.count i)) (polyMul (quaternionRadiusPolynomial 0)
        (partialGaussianHead (translatedWord right (word.erase i))))) :=
  (translatedWord_gaussian_recursion right i word).trans
    ((partialGaussianHead_congr (contractedWord_eq_count right i word)).trans
      ((partialGaussianHead_smul _ _).trans ((partialGaussianHead_radius_mul _).smul _)))

end YMGap.Continuum.SU2QuaternionTranslationGaussianCountRecursion

#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianCountRecursion.translatedWord_erase
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianCountRecursion.contractedWord_eq_count
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianCountRecursion.translatedWord_gaussian_count
