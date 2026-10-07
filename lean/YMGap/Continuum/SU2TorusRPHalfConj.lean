/-
# Torus RP assembly (d3e): conjugation only matters where the monomial lives

* `parity_congr`: the selected parity depends only on the selection at coordinates where the monomial has odd
  exponent.
* `sign_congr`: hence two selections that agree on all odd-exponent coordinates of every monomial of `X` give the
  same sign flip of `X` (literally).
* `sign_first_half`: a selection vanishing on the first `4a` coordinates fixes every first-half polynomial.
* `sign_second_half`: on a polynomial with no exponent in the first `4a` coordinates, selection `S` and the
  second-half restriction `S ∧ (i ≥ 4a)` give the same flip.
So the second-half-only conj `Ŝ` fixes `Wp` and agrees with the full temporal conj on `reindex Wp`. With
`theta_shift`, `Ŝ (thetaPoly Wp) ≈PE shiftPoly Wp`.

**RP FOR THE ACTUAL TORUS MEASURE IS OPEN** (still to do: the crossing split, the RPK crossing words, and assembly).
-/

import YMGap.Continuum.SU2TorusRPFactor

namespace YMGap.Continuum.SU2TorusRPHalfConj

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
  (selectedExponentParity signSelectedPolynomial signSelectedTerm)
open YMGap.Continuum.SU2TorusRPConj (step parity_eq)

theorem fold_congr (S S' : Nat → Bool) (m : List Nat)
    (h : ∀ c, exponentAt m c % 2 = 1 → S c = S' c) : ∀ (l : List Nat) (p : Bool),
    l.foldl (step S m) p = l.foldl (step S' m) p
  | [], _ => rfl
  | c :: l, p => by
    simp only [List.foldl_cons]
    have : step S m p c = step S' m p c := by
      unfold step
      by_cases hc : exponentAt m c % 2 = 1
      · rw [h c hc]
      · have hd : decide (exponentAt m c % 2 = 1) = false := decide_eq_false hc
        rw [hd]
        cases S c <;> cases S' c <;> cases p <;> rfl
    rw [this]; exact fold_congr S S' m h l _

theorem parity_congr (N : Nat) (S S' : Nat → Bool) (m : List Nat)
    (h : ∀ c, exponentAt m c % 2 = 1 → S c = S' c) :
    selectedExponentParity N S m = selectedExponentParity N S' m := by
  rw [parity_eq, parity_eq]; exact fold_congr S S' m h _ _

theorem sign_congr (N : Nat) (S S' : Nat → Bool) : ∀ X : RatPoly,
    (∀ t ∈ X, ∀ c, exponentAt t.1 c % 2 = 1 → S c = S' c) →
    signSelectedPolynomial N S X = signSelectedPolynomial N S' X
  | [], _ => rfl
  | t :: X, h => by
    show signSelectedTerm N S t :: signSelectedPolynomial N S X = signSelectedTerm N S' t :: signSelectedPolynomial N S' X
    rw [sign_congr N S S' X fun s hs => h s (List.mem_cons_of_mem _ hs)]
    unfold signSelectedTerm
    rw [parity_congr N S S' t.1 (h t (List.mem_cons_self ..))]

/-- Restriction of a selection to coordinates `≥ c0`. -/
def above (c0 : Nat) (S : Nat → Bool) (i : Nat) : Bool := decide (c0 ≤ i) && S i

theorem sign_none (N : Nat) (S : Nat → Bool) (X : RatPoly) (h : ∀ t ∈ X, ∀ c, exponentAt t.1 c % 2 = 1 → S c = false) :
    signSelectedPolynomial N S X = signSelectedPolynomial N (fun _ => false) X :=
  sign_congr N S _ X h

/-- With the empty selection the flip is coefficientwise the identity. -/
theorem sign_empty (n N : Nat) (X : RatPoly) :
    YMGap.Continuum.SU2HaarAlgebra.PE n (signSelectedPolynomial N (fun _ => false) X) X := by
  have hp : ∀ m, selectedExponentParity N (fun _ => false) m = false := fun m => by
    rw [parity_eq]
    suffices ∀ (l : List Nat), l.foldl (step (fun _ => false) m) false = false from this _
    intro l; induction l with
    | nil => rfl
    | cons c l ih => simp only [List.foldl_cons]; exact ih
  have e : signSelectedPolynomial N (fun _ => false) X = X := by
    unfold signSelectedPolynomial
    conv => rhs; rw [← List.map_id X]
    refine List.map_congr_left fun t _ => ?_
    unfold signSelectedTerm; rw [hp]; rfl
  rw [e]; exact YMGap.Continuum.SU2HaarAlgebra.pe_refl n X

/-- First-half polynomials are fixed by any second-half selection. -/
theorem sign_first_half (n N c0 : Nat) (S : Nat → Bool) (X : RatPoly) (hX : ∀ t ∈ X, t.1.length ≤ c0) :
    YMGap.Continuum.SU2HaarAlgebra.PE n (signSelectedPolynomial N (above c0 S) X) X := by
  rw [sign_none N _ X fun t ht c hc => by
    unfold above
    have : c < c0 := Nat.lt_of_not_le fun hn => by
      rw [YMGap.Continuum.SU2MultiLinkHaarFactorization.exponentAt_of_length_le _ _
        (Nat.le_trans (hX t ht) hn)] at hc
      exact absurd hc (by decide)
    rw [decide_eq_false (Nat.not_le_of_lt this)]; rfl]
  exact sign_empty n N X

/-- On second-half polynomials, `S` and `above c0 S` flip identically. -/
theorem sign_second_half (N c0 : Nat) (S : Nat → Bool) (X : RatPoly)
    (hX : ∀ t ∈ X, ∀ c, c < c0 → exponentAt t.1 c = 0) :
    signSelectedPolynomial N S X = signSelectedPolynomial N (above c0 S) X :=
  sign_congr N S _ X fun t ht c hc => by
    unfold above
    have : c0 ≤ c := Nat.le_of_not_lt fun hlt => by rw [hX t ht c hlt] at hc; exact absurd hc (by decide)
    rw [decide_eq_true this]; rfl

end YMGap.Continuum.SU2TorusRPHalfConj

#print axioms YMGap.Continuum.SU2TorusRPHalfConj.parity_congr
#print axioms YMGap.Continuum.SU2TorusRPHalfConj.sign_first_half
#print axioms YMGap.Continuum.SU2TorusRPHalfConj.sign_second_half
