/-
# Coordinate semantics of quaternion-block conjugation

The original finite sign substitution conjugates precisely its named
quaternion block and fixes every other block. Its ordered multiplicativity
and involution laws hold before integration, modulo finite-coordinate prefix
equivalence. These are the sign identities required by inverse Haar shears.
-/

import YMGap.Continuum.SU2QuaternionSelectedTranslationCoordinates

namespace YMGap.Continuum.SU2QuaternionCoordinateConjugation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord

theorem selectedExponentParity_var (selected : Nat → Bool) (coordinate : Nat) :
    ∀ n, selectedExponentParity n selected (varMono coordinate) =
      if coordinate < n then selected coordinate else false
  | 0 => by simp [selectedExponentParity]
  | n + 1 => by
      have hrec : selectedExponentParity (n + 1) selected (varMono coordinate) =
          if selected n then
            xor (selectedExponentParity n selected (varMono coordinate))
              (decide (exponentAt (varMono coordinate) n % 2 = 1))
          else selectedExponentParity n selected (varMono coordinate) := by
        simp only [selectedExponentParity, List.range_succ, List.foldl_append,
          List.foldl_cons, List.foldl_nil]
      rw [hrec, selectedExponentParity_var selected coordinate n, exponentAt_varMono]
      by_cases hlt : coordinate < n
      · have hne : n ≠ coordinate := by omega
        simp [hlt, hne, show coordinate < n + 1 by omega]
      · by_cases heq : n = coordinate
        · subst coordinate
          simp [hlt]
        · simp [hlt, heq, show ¬ coordinate < n + 1 by omega]

theorem signSelectedPolynomial_var (n : Nat) (selected : Nat → Bool)
    (coordinate : Nat) (hc : coordinate < n) :
    signSelectedPolynomial n selected (polyVar coordinate) =
      if selected coordinate then polyNeg (polyVar coordinate) else polyVar coordinate := by
  simp only [signSelectedPolynomial, polyVar, List.map_cons, List.map_nil, signSelectedTerm,
    selectedExponentParity_var, if_pos hc]
  split <;> rfl

private theorem conjugate_selector (block source i : Nat) (hi : i < 4) :
    quaternionConjugateCoordinateSelector block (4 * source + i) =
      decide (source = block ∧ i ≠ 0) := by
  unfold quaternionConjugateCoordinateSelector
  by_cases hs : source = block
  · subst source
    by_cases hz : i = 0
    · have h1 : 4 * block + i ≠ 4 * block + 1 := by omega
      have h2 : 4 * block + i ≠ 4 * block + 2 := by omega
      have h3 : 4 * block + i ≠ 4 * block + 3 := by omega
      rw [decide_eq_false (fun h => h.elim h1 (fun h => h.elim h2 h3)),
        decide_eq_false (fun h => h.2 hz)]
    · have hc : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      have hp : 4 * block + i = 4 * block + 1 ∨
          4 * block + i = 4 * block + 2 ∨ 4 * block + i = 4 * block + 3 := by
        rcases hc with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
      rw [decide_eq_true hp, decide_eq_true ⟨rfl, hz⟩]
  · have h1 : 4 * source + i ≠ 4 * block + 1 := by omega
    have h2 : 4 * source + i ≠ 4 * block + 2 := by omega
    have h3 : 4 * source + i ≠ 4 * block + 3 := by omega
    rw [decide_eq_false (fun h => h.elim h1 (fun h => h.elim h2 h3)),
      decide_eq_false (fun h => hs h.1)]

def conjugateBlockQuaternion (blocks block : Nat) (q : PolyQuaternion) : PolyQuaternion where
  scalar := conjugateQuaternionBlockPolynomial blocks block q.scalar
  iPart := conjugateQuaternionBlockPolynomial blocks block q.iPart
  jPart := conjugateQuaternionBlockPolynomial blocks block q.jPart
  kPart := conjugateQuaternionBlockPolynomial blocks block q.kPart

theorem conjugateBlockQuaternion_coordinate (blocks block source : Nat) (hs : source < blocks) :
    conjugateBlockQuaternion blocks block (PolyQuaternion.coordinateVariable source) =
      if source = block then PolyQuaternion.conj (PolyQuaternion.coordinateVariable source)
      else PolyQuaternion.coordinateVariable source := by
  have hv (i : Nat) (hi : i < 4) :
      conjugateQuaternionBlockPolynomial blocks block (polyVar (4 * source + i)) =
        if source = block ∧ i ≠ 0 then polyNeg (polyVar (4 * source + i))
        else polyVar (4 * source + i) := by
    unfold conjugateQuaternionBlockPolynomial
    rw [signSelectedPolynomial_var _ _ _ (by omega), conjugate_selector block source i hi]
    simp only [decide_eq_true_eq]
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.add_zero, ne_eq, not_true_eq_false, and_false, if_false] at h0
  by_cases heq : source = block
  · rw [if_pos heq]
    simp only [conjugateBlockQuaternion, PolyQuaternion.coordinateVariable, h0, h1, h2, h3,
      PolyQuaternion.conj]
    simp only [heq]
    rfl
  · simp only [conjugateBlockQuaternion, PolyQuaternion.coordinateVariable, h0, h1, h2, h3,
      heq, false_and, if_false]

theorem conjugateBlockQuaternion_prefix {blocks : Nat} (block : Nat) {p q : PolyQuaternion}
    (h : QuaternionPrefixPolyQuaternionEqv blocks p q) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (conjugateBlockQuaternion blocks block p) (conjugateBlockQuaternion blocks block q) :=
  ⟨h.scalar.signSelected _, h.iPart.signSelected _, h.jPart.signSelected _, h.kPart.signSelected _⟩

theorem conjugateBlockQuaternion_conj (blocks block : Nat) (q : PolyQuaternion) :
    conjugateBlockQuaternion blocks block (PolyQuaternion.conj q) =
      PolyQuaternion.conj (conjugateBlockQuaternion blocks block q) := by
  simp only [conjugateBlockQuaternion, PolyQuaternion.conj, conjugateQuaternionBlockPolynomial,
    signSelectedPolynomial_neg]

theorem conjugateBlockQuaternion_mul (blocks block : Nat) (p q : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (conjugateBlockQuaternion blocks block (PolyQuaternion.mul p q))
      (PolyQuaternion.mul (conjugateBlockQuaternion blocks block p)
        (conjugateBlockQuaternion blocks block q)) := by
  have hm := signSelectedPolynomial_mul_prefix blocks (quaternionConjugateCoordinateSelector block)
  constructor
  · simpa only [conjugateBlockQuaternion, PolyQuaternion.mul, conjugateQuaternionBlockPolynomial,
      signSelectedPolynomial_add, signSelectedPolynomial_neg] using
      (hm p.scalar q.scalar).append
        (((hm p.iPart q.iPart).append ((hm p.jPart q.jPart).append (hm p.kPart q.kPart))).neg)
  · simpa only [conjugateBlockQuaternion, PolyQuaternion.mul, conjugateQuaternionBlockPolynomial,
      signSelectedPolynomial_add, signSelectedPolynomial_neg] using
      (hm p.scalar q.iPart).append ((hm p.iPart q.scalar).append
        ((hm p.jPart q.kPart).append ((hm p.kPart q.jPart).neg)))
  · simpa only [conjugateBlockQuaternion, PolyQuaternion.mul, conjugateQuaternionBlockPolynomial,
      signSelectedPolynomial_add, signSelectedPolynomial_neg] using
      (hm p.scalar q.jPart).append ((hm p.jPart q.scalar).append
        ((hm p.kPart q.iPart).append ((hm p.iPart q.kPart).neg)))
  · simpa only [conjugateBlockQuaternion, PolyQuaternion.mul, conjugateQuaternionBlockPolynomial,
      signSelectedPolynomial_add, signSelectedPolynomial_neg] using
      (hm p.scalar q.kPart).append ((hm p.kPart q.scalar).append
        ((hm p.iPart q.jPart).append ((hm p.jPart q.iPart).neg)))

theorem signSelectedPolynomial_involutive_prefix (blocks : Nat) (selected : Nat → Bool) :
    ∀ p : RatPoly, QuaternionPrefixPolynomialEqv blocks
      (signSelectedPolynomial (4 * blocks) selected (signSelectedPolynomial (4 * blocks) selected p)) p
  | [] => .nil
  | t :: rest => by
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · simp only [signSelectedTerm]
          cases hp : selectedExponentParity (4 * blocks) selected t.1
          · exact Q'.eqv_refl _
          · exact Q'.neg_neg_eqv t.2
        · intro _ _
          rfl
      · exact signSelectedPolynomial_involutive_prefix blocks selected rest

theorem conjugateBlockQuaternion_involutive (blocks block : Nat) (q : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (conjugateBlockQuaternion blocks block (conjugateBlockQuaternion blocks block q)) q :=
  ⟨signSelectedPolynomial_involutive_prefix blocks _ q.scalar,
    signSelectedPolynomial_involutive_prefix blocks _ q.iPart,
    signSelectedPolynomial_involutive_prefix blocks _ q.jPart,
    signSelectedPolynomial_involutive_prefix blocks _ q.kPart⟩

end YMGap.Continuum.SU2QuaternionCoordinateConjugation

#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.selectedExponentParity_var
#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.signSelectedPolynomial_var
#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.conjugateBlockQuaternion
#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.conjugateBlockQuaternion_coordinate
#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.conjugateBlockQuaternion_prefix
#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.conjugateBlockQuaternion_conj
#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.conjugateBlockQuaternion_mul
#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.signSelectedPolynomial_involutive_prefix
#print axioms YMGap.Continuum.SU2QuaternionCoordinateConjugation.conjugateBlockQuaternion_involutive
