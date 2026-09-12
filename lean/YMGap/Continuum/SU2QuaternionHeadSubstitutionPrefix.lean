/-
# Structural coordinate semantics of head substitution

The original polynomial substitution respects finite-coordinate prefix
equivalence. It replaces the four head variables by the supplied quaternion
and fixes every tail variable. Padding is retained explicitly; no polynomial
scan, sphere relation, or Haar integration is used in these identities.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

theorem prefix_symm {blocks : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv blocks p q) :
    QuaternionPrefixPolynomialEqv blocks q p := by
  induction h with
  | nil => exact .nil
  | cons ht _ ih =>
      exact .cons ⟨Q'.eqv_symm ht.coefficient, fun i hi => (ht.exponent i hi).symm⟩ ih

theorem prefix_one_mul (blocks : Nat) : ∀ p : RatPoly,
    QuaternionPrefixPolynomialEqv blocks (polyMul polyOne p) p
  | [] => .nil
  | t :: rest => by
      apply QuaternionPrefixPolynomialEqv.cons
      · exact ⟨Q'.one_mul_eqv t.2, fun _ _ => rfl⟩
      · exact prefix_one_mul blocks rest

theorem prefix_mul_one (blocks : Nat) : ∀ p : RatPoly,
    QuaternionPrefixPolynomialEqv blocks (polyMul p polyOne) p
  | [] => .nil
  | t :: rest => by
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact Q'.mul_one_eqv t.2
        · intro i _
          simp only [exponentAt_monoMul]
          simp [exponentAt]
      · exact prefix_mul_one blocks rest

private theorem lift_exponent (m : List Nat) (i : Nat) :
    exponentAt ([0, 0, 0, 0] ++ m.drop 4) i =
      if i < 4 then 0 else exponentAt m i := by
  by_cases hi : i < 4
  · have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> rfl
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
    rw [if_neg (by omega)]
    rw [Nat.add_comm 4 j]
    change exponentAt (m.drop 4) j = exponentAt m (j + 4)
    rw [Nat.add_comm j 4]
    exact exponentAt_drop m 4 j

theorem headTailLiftTerm_prefix {blocks : Nat} {s t : RatTerm}
    (h : QuaternionPrefixTermEqv blocks s t) :
    QuaternionPrefixPolynomialEqv blocks (headTailLiftTerm s) (headTailLiftTerm t) := by
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact h.coefficient
    · intro i hi
      simp only [lift_exponent]
      split
      · rfl
      · exact h.exponent i hi
  · exact .nil

/-- Substitution retains every in-carrier coefficient, even when the two
representations use different trailing-zero padding. -/
theorem translatedHeadPolynomial_prefix {blocks : Nat} (hb : 0 < blocks)
    (translated : PolyQuaternion) {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv blocks p q) :
    QuaternionPrefixPolynomialEqv blocks
      (translatedHeadPolynomial translated p) (translatedHeadPolynomial translated q) := by
  induction h with
  | nil => exact .nil
  | @cons s t _ _ ht _ ih =>
      apply QuaternionPrefixPolynomialEqv.append _ ih
      unfold translatedHeadTerm
      rw [ht.exponent 0 (by omega), ht.exponent 1 (by omega),
        ht.exponent 2 (by omega), ht.exponent 3 (by omega)]
      exact (QuaternionPrefixPolynomialEqv.refl blocks _).mul (headTailLiftTerm_prefix ht)

private theorem lift_head_var_prefix (blocks i : Nat) (hi : i < 4) :
    QuaternionPrefixPolynomialEqv blocks (headTailLiftTerm (varMono i, 1)) polyOne := by
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro j _
      change exponentAt ([0, 0, 0, 0] ++ (varMono i).drop 4) j = exponentAt [] j
      rw [lift_exponent]
      split
      · rfl
      · rw [exponentAt_varMono, if_neg (by omega)]
        rfl
  · exact .nil

/-- Coordinate selector with no out-of-range interpretation. -/
def component (q : PolyQuaternion) (i : Fin 4) : RatPoly :=
  match i.val with
  | 0 => q.scalar
  | 1 => q.iPart
  | 2 => q.jPart
  | _ => q.kPart

private theorem monomial_head_var (blocks : Nat) (q : PolyQuaternion) (i : Fin 4) :
    QuaternionPrefixPolynomialEqv blocks
      (translatedHeadMonomial q (exponentAt (varMono i.val) 0)
        (exponentAt (varMono i.val) 1) (exponentAt (varMono i.val) 2)
        (exponentAt (varMono i.val) 3)) (component q i) := by
  obtain ⟨i, hi⟩ := i
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · exact ((prefix_one_mul blocks q.scalar).mul
      (prefix_one_mul blocks (polyMul polyOne polyOne) |>.trans (prefix_one_mul blocks polyOne))).trans
      (prefix_mul_one blocks q.scalar)
  · exact (prefix_one_mul blocks _).trans
      (((prefix_one_mul blocks q.iPart).mul (prefix_one_mul blocks polyOne)).trans
        (prefix_mul_one blocks q.iPart))
  · exact (prefix_one_mul blocks _).trans ((prefix_one_mul blocks _).trans
      (((prefix_one_mul blocks q.jPart).mul (QuaternionPrefixPolynomialEqv.refl blocks polyOne)).trans
        (prefix_mul_one blocks q.jPart)))
  · exact (prefix_one_mul blocks _).trans ((prefix_one_mul blocks _).trans
      ((prefix_one_mul blocks _).trans (prefix_one_mul blocks q.kPart)))

theorem translatedHeadPolynomial_head_coordinate (blocks : Nat)
    (q : PolyQuaternion) (i : Fin 4) :
    QuaternionPrefixPolynomialEqv blocks
      (translatedHeadPolynomial q (polyVar i.val)) (component q i) := by
  change QuaternionPrefixPolynomialEqv blocks
    (polyAdd (translatedHeadTerm q (varMono i.val, 1)) []) _
  simp only [polyAdd, List.append_nil, translatedHeadTerm]
  exact ((monomial_head_var blocks q i).mul (lift_head_var_prefix blocks i.val i.isLt)).trans
    (prefix_mul_one blocks _)

theorem translatedHeadPolynomial_tail_coordinate
    (q : PolyQuaternion) (i : Nat) (hi : 4 ≤ i) :
    translatedHeadPolynomial q (polyVar i) = polyVar i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_comm 4 j]
  simp [translatedHeadPolynomial, translatedHeadTerm, translatedHeadMonomial,
    ratPolyPow, headTailLiftTerm, polyVar, polyAdd, polyMul, polyOne, polyZero,
    exponentAt, varMono, monoMul, List.drop_append, List.replicate] <;> decide

end YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix

#print axioms YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.prefix_symm
#print axioms YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.prefix_one_mul
#print axioms YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.prefix_mul_one
#print axioms YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.headTailLiftTerm_prefix
#print axioms YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.translatedHeadPolynomial_prefix
#print axioms YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.component
#print axioms YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.translatedHeadPolynomial_head_coordinate
#print axioms YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix.translatedHeadPolynomial_tail_coordinate
