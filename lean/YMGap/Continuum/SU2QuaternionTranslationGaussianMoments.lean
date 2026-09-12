/-
# Closed all-degree Gaussian moments of the ORIGINAL quaternion translations

The count-compressed Wick recurrence determines each translated coordinate
word by strict two-factor descent. Its coefficient is the library's exact
four-coordinate Gaussian moment, and its tail factor is the actual radius
to half the word length. Unmatched labels give zero without division.

The result is coefficientwise and is transported to the EXISTING
translatedHeadMonomial API. Sphere conversion and full Haar translation
are subsequent obligations, not conclusions of this Gaussian theorem.
-/

import YMGap.Continuum.SU2QuaternionTranslationGaussianCountRecursion

namespace YMGap.Continuum.SU2QuaternionTranslationGaussianMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionGaussianMomentRecurrence
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionHeadGaussianIBP
open YMGap.Continuum.SU2QuaternionHeadGaussianConditionalProduct
open YMGap.Continuum.SU2QuaternionTranslationGaussianStein
open YMGap.Continuum.SU2QuaternionTranslationGaussianCountRecursion

local infix:50 " ≈ " => Q'.eqv

/-- The existing exact Gaussian moment evaluated at the four label counts. -/
def gaussianWordMoment (word : List (Fin 4)) : Q' :=
  gaussianMoment4 (word.count 0) (word.count 1) (word.count 2) (word.count 3)

/-- Constructive count/erase identity for the decidable four-label carrier.
The generic core List.count_erase theorem uses Classical.choice, so it is
not used in this proof path. -/
theorem labelCount_erase (a b : Fin 4) : ∀ word : List (Fin 4),
    (word.erase b).count a = word.count a - if b = a then 1 else 0
  | [] => by simp only [List.erase_nil, List.count_nil, Nat.zero_sub]
  | c :: rest => by
    by_cases hcb : c = b
    · subst c
      simp only [List.erase_cons_head, List.count_cons]
      by_cases hba : b = a
      · have hb : (b == a) = true := decide_eq_true hba
        rw [if_pos hb, if_pos hba, Nat.add_sub_cancel]
      · simp [hba]
    · have herase : (c :: rest).erase b = c :: rest.erase b := List.erase_cons_tail (by simp [hcb])
      rw [herase, List.count_cons, labelCount_erase a b rest, List.count_cons]
      by_cases hba : b = a
      · subst b
        simp [hcb]
      · simp only [if_neg hba, Nat.sub_zero]

/-- Constructive length descent on the same decidable label carrier; the
generic List.length_erase_of_mem theorem is also outside this axiom gate. -/
theorem labelErase_length (i : Fin 4) : ∀ word : List (Fin 4), i ∈ word →
    (word.erase i).length = word.length - 1
  | [], h => False.elim (List.not_mem_nil h)
  | j :: rest, h => by
    by_cases hji : j = i
    · subst j
      simp only [List.erase_cons_head, List.length_cons, Nat.add_sub_cancel]
    · have hm : i ∈ rest := by
        rcases List.mem_cons.mp h with h | h
        · exact False.elim (hji h.symm)
        · exact h
      have he : (j :: rest).erase i = j :: rest.erase i := List.erase_cons_tail (by simp [hji])
      rw [he, List.length_cons, labelErase_length i rest hm, List.length_cons]
      have hp := List.length_pos_of_mem hm
      omega

private theorem ibp0 (a b c d : Nat) :
    gaussianMoment4 (a + 1) b c d ≈ Q'.ofNat a * gaussianMoment4 (a - 1) b c d := by
  cases a with
  | zero =>
    have h : gaussianMoment4 1 b c d = 0 := by simp [gaussianMoment4]
    rw [h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ a => exact gaussianMoment4_shift0 a b c d

private theorem ibp1 (a b c d : Nat) :
    gaussianMoment4 a (b + 1) c d ≈ Q'.ofNat b * gaussianMoment4 a (b - 1) c d := by
  cases b with
  | zero =>
    have h : gaussianMoment4 a 1 c d = 0 := by simp [gaussianMoment4]
    rw [h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ b => exact gaussianMoment4_shift1 a b c d

private theorem ibp2 (a b c d : Nat) :
    gaussianMoment4 a b (c + 1) d ≈ Q'.ofNat c * gaussianMoment4 a b (c - 1) d := by
  cases c with
  | zero =>
    have h : gaussianMoment4 a b 1 d = 0 := by simp [gaussianMoment4]
    rw [h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ c => exact gaussianMoment4_shift2 a b c d

private theorem ibp3 (a b c d : Nat) :
    gaussianMoment4 a b c (d + 1) ≈ Q'.ofNat d * gaussianMoment4 a b c (d - 1) := by
  cases d with
  | zero =>
    have h : gaussianMoment4 a b c 1 = 0 := by simp [gaussianMoment4]
    rw [h]
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ d => exact gaussianMoment4_shift3 a b c d

/-- The existing Gaussian moment satisfies the SAME label-count descent,
including the zero-count case. This identifies, rather than defines, it. -/
theorem gaussianWordMoment_cons (i : Fin 4) (word : List (Fin 4)) :
    gaussianWordMoment (i :: word) ≈ Q'.ofNat (word.count i) * gaussianWordMoment (word.erase i) := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl
  all_goals
    simp only [gaussianWordMoment, labelCount_erase]
    simp
    first | exact ibp0 _ _ _ _ | exact ibp1 _ _ _ _ | exact ibp2 _ _ _ _ | exact ibp3 _ _ _ _

private theorem radius_power_step (r : RatPoly) (n : Nat) :
    RatPolyCoeffEqv (polyMul r (ratPolyPow r n)) (ratPolyPow r (n + 1)) :=
  RatPolyCoeffEqv.mul_comm _ _

/-- Closed exact Gaussian moment of EVERY actual translated coordinate word.
All tail coefficients are retained, and no unit-radius premise is used. -/
theorem translatedWord_gaussian_closed (right : Bool) (word : List (Fin 4)) :
    RatPolyCoeffEqv (partialGaussianHead (translatedWord right word))
      (polySmul (gaussianWordMoment word) (ratPolyPow (quaternionRadiusPolynomial 0) (word.length / 2))) := by
  have aux : ∀ n : Nat, ∀ word : List (Fin 4), word.length = n →
      RatPolyCoeffEqv (partialGaussianHead (translatedWord right word))
        (polySmul (gaussianWordMoment word) (ratPolyPow (quaternionRadiusPolynomial 0) (word.length / 2))) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro word hlen
      cases word with
      | nil =>
        exact partialGaussianHead_one.trans (RatPolyCoeffEqv.one_smul polyOne).symm
      | cons i rest =>
        have hrec := translatedWord_gaussian_count right i rest
        have hg := gaussianWordMoment_cons i rest
        by_cases hm : i ∈ rest
        · have hpos := List.length_pos_of_mem hm
          have hlength := labelErase_length i rest hm
          have hless : (rest.erase i).length < n := by simp only [List.length_cons] at hlen; omega
          have hk : (i :: rest).length / 2 = (rest.erase i).length / 2 + 1 := by
            simp only [List.length_cons]
            omega
          have hs := ih (rest.erase i).length hless (rest.erase i) rfl
          refine hrec.trans (((hs.mul_left (quaternionRadiusPolynomial 0)).smul (Q'.ofNat (rest.count i))).trans ?_)
          refine ((RatPolyCoeffEqv.polyMul_smul_right (gaussianWordMoment (rest.erase i))
            (quaternionRadiusPolynomial 0) _).smul (Q'.ofNat (rest.count i))).trans ?_
          refine (RatPolyCoeffEqv.smul_assoc (Q'.ofNat (rest.count i)) (gaussianWordMoment (rest.erase i)) _).trans ?_
          refine (RatPolyCoeffEqv.smul_coefficient (Q'.eqv_symm hg) _).trans ?_
          rw [hk]
          exact (radius_power_step _ _).smul (gaussianWordMoment (i :: rest))
        · have hc := List.count_eq_zero_of_not_mem hm
          rw [hc] at hrec hg
          have hz : gaussianWordMoment (i :: rest) ≈ 0 :=
            Q'.eqv_trans _ _ _ hg (Q'.zero_mul_eqv _)
          exact (hrec.trans (RatPolyCoeffEqv.zero_smul _)).trans
            ((RatPolyCoeffEqv.smul_coefficient hz _).trans (RatPolyCoeffEqv.zero_smul _)).symm
  exact aux word.length word rfl

theorem gaussianWordMoment_exponents (e0 e1 e2 e3 : Nat) :
    gaussianWordMoment (translatedExponentWord e0 e1 e2 e3) = gaussianMoment4 e0 e1 e2 e3 := by
  simp [gaussianWordMoment, translatedExponentWord, List.count_replicate]

/-- Closed moments for the ORIGINAL four-exponent left/right translated
monomial used by the existing Haar-translation API, at every exponent. -/
theorem translatedHeadMonomial_gaussian_closed (right : Bool) (e0 e1 e2 e3 : Nat) :
    RatPolyCoeffEqv (partialGaussianHead (translatedHeadMonomial
      (if right then rightTranslatedHeadQuaternion else leftTranslatedHeadQuaternion) e0 e1 e2 e3))
      (polySmul (gaussianMoment4 e0 e1 e2 e3)
        (ratPolyPow (quaternionRadiusPolynomial 0) ((e0 + e1 + e2 + e3) / 2))) := by
  have h := (partialGaussianHead_congr (translatedHeadMonomial_eq_word right e0 e1 e2 e3)).trans
    (translatedWord_gaussian_closed right (translatedExponentWord e0 e1 e2 e3))
  rw [gaussianWordMoment_exponents] at h
  simpa only [translatedExponentWord, List.length_append,
    List.length_replicate, Nat.add_assoc] using h

end YMGap.Continuum.SU2QuaternionTranslationGaussianMoments

#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianMoments.gaussianWordMoment
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianMoments.labelCount_erase
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianMoments.labelErase_length
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianMoments.gaussianWordMoment_cons
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianMoments.translatedWord_gaussian_closed
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianMoments.gaussianWordMoment_exponents
#print axioms YMGap.Continuum.SU2QuaternionTranslationGaussianMoments.translatedHeadMonomial_gaussian_closed
