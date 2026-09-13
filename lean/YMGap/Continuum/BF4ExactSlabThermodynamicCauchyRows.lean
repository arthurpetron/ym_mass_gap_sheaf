/-
# Constructed limits of ORIGINAL thermodynamic Cauchy rows

A represented family supplies actual original Cauchy rows and an outer
modulus in the SAME completed squared distance. Diagonal sampling has rate
max(outerModulus(epsilon/16), (epsilon/16).den), and its completed limit
has rate outerModulus(epsilon/16).

The limit is unique, independent of the supplied row representatives, and
recovers the existing completion class for rows of original presentations.
No arbitrary quotient representatives are selected. Full quotient-level
completeness is a distinct obligation, not an implicit premise or conclusion.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos invSucc_le_of_den)

private theorem rc_zero_of_small (a : RC) (ha : RCnonneg a)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon → RCle a (Quotient.mk crealSetoid (ofQ' epsilon))) : a = RCzero := by
  revert ha h
  refine Quotient.inductionOn a ?_
  intro A ha h
  apply Quotient.sound
  apply equiv_of_leEv_leEv ?_ ha
  intro epsilon he
  have hh := ExpNeg.half_mul_pos epsilon he
  have hb : leEv A (ofQ' (HalfPow.half * epsilon)) := h (HalfPow.half * epsilon) hh
  obtain ⟨N, hN⟩ := hb (HalfPow.half * epsilon) hh
  refine ⟨N, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon) (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))

local notation "D" => seminorm

/-- Represented Cauchy families; the rows and outer rate are retained as data. -/
structure CauchyRows where
  row : Nat → (seminorm).Cauchy
  modulus : Q' → Nat
  isCauchy : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ m n,
    modulus epsilon ≤ m → modulus epsilon ≤ n →
    RCle (completedDist
      (Quotient.mk (seminorm).completionSetoid (row m))
      (Quotient.mk (seminorm).completionSetoid (row n)))
      (Quotient.mk crealSetoid (ofQ' epsilon))

def rowPoint (R : CauchyRows) (n : Nat) : Completion :=
  Quotient.mk (D).completionSetoid (R.row n)

def diagonal (R : CauchyRows) (n : Nat) : Presentation :=
  approximant (R.row n) n

def diagonalRate (R : CauchyRows) (epsilon : Q') : Nat :=
  max (R.modulus (quarter (quarter epsilon))) (quarter (quarter epsilon)).den

theorem diagonal_close_row (R : CauchyRows) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : epsilon.den ≤ n) :
    RCle (completedDist (embedPresentation (diagonal R n)) (rowPoint R n))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hrelax : RCle (Quotient.mk crealSetoid (ofQ' (Q'.invSucc n))) (Quotient.mk crealSetoid (ofQ' epsilon)) :=
    leEv_le_ofQ'_of_approx_le (fun _ => invSucc_le_of_den he hn)
  exact RCle_trans (approximant_bound (R.row n) n) hrelax

theorem diagonal_bound (R : CauchyRows) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : diagonalRate R epsilon ≤ m) (hn : diagonalRate R epsilon ≤ n) :
    leEv (distSq (diagonal R m) (diagonal R n)) (ofQ' epsilon) := by
  let delta := quarter (quarter epsilon)
  have hd : (0 : Q') < delta := quarter_pos (quarter_pos he)
  have hdm : delta.den ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
  have hdn : delta.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hmm : R.modulus delta ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
  have hmn : R.modulus delta ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hleft := diagonal_close_row R delta hd m hdm
  have hright := diagonal_close_row R delta hd n hdn
  rw [completedDist_symm (embedPresentation (diagonal R n))] at hright
  have h := completedDist_three_segment
    (embedPresentation (diagonal R m)) (rowPoint R m)
    (rowPoint R n) (embedPresentation (diagonal R n))
    epsilon he hleft (R.isCauchy delta hd m n hmm hmn) hright
  rw [completedDist_embedPresentation] at h
  exact h

def diagonalCauchy (R : CauchyRows) : (D).Cauchy where
  seq := diagonal R
  modulus := diagonalRate R
  isCauchy := diagonal_bound R

def rowLimit (R : CauchyRows) : Completion :=
  Quotient.mk (D).completionSetoid (diagonalCauchy R)

def rowLimitRate (R : CauchyRows) (epsilon : Q') : Nat := R.modulus (quarter (quarter epsilon))

theorem rowLimit_bound (R : CauchyRows) (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : rowLimitRate R epsilon ≤ k) :
    RCle (completedDist (rowPoint R k) (rowLimit R))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let delta := quarter (quarter epsilon)
  have hd : (0 : Q') < delta := quarter_pos (quarter_pos he)
  apply representativeDist_le_of_eventually (R.row k) (diagonalCauchy R) epsilon
    (max (diagonalRate R epsilon) ((R.row k).modulus delta))
  intro n hn
  have hnrate : diagonalRate R epsilon ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hninner : (R.row k).modulus delta ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hnouter : R.modulus delta ≤ n := Nat.le_trans (Nat.le_max_left _ _) hnrate
  have hnden : delta.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hnrate
  have hleft := constantApproximation_bound (R.row k) delta hd n hninner
  have hright := diagonal_close_row R delta hd n hnden
  rw [completedDist_symm (embedPresentation (diagonal R n))] at hright
  have h := completedDist_three_segment
    (embedPresentation ((R.row k).seq n)) (rowPoint R k)
    (rowPoint R n) (embedPresentation (diagonal R n))
    epsilon he hleft (R.isCauchy delta hd k n hk hnouter) hright
  rw [completedDist_embedPresentation] at h
  exact h

theorem completed_eq_of_small (x y : Completion)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon → RCle (completedDist x y) (Quotient.mk crealSetoid (ofQ' epsilon))) :
    x = y :=
  (completedDist_zero_iff x y).mp (rc_zero_of_small _ (completedDist_nonnegative x y) h)

theorem rowLimit_eq_of_bound (R : CauchyRows) (L : Completion) (rate : Q' → Nat)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
      RCle (completedDist (rowPoint R n) L) (Quotient.mk crealSetoid (ofQ' epsilon))) :
    rowLimit R = L := by
  apply completed_eq_of_small
  intro epsilon he
  let q := quarter epsilon
  have hq : (0 : Q') < q := quarter_pos he
  let n := max (rowLimitRate R q) (rate q)
  have hleft := rowLimit_bound R q hq n (Nat.le_max_left _ _)
  rw [completedDist_symm] at hleft
  exact completedDist_two_segment (rowLimit R) (rowPoint R n) L epsilon
    hleft (h q hq n (Nat.le_max_right _ _))

/-- The diagonal's value does not depend on row representatives or their moduli. -/
theorem rowLimit_independent (R S : CauchyRows)
    (h : ∀ n, rowPoint R n = rowPoint S n) : rowLimit R = rowLimit S := by
  apply rowLimit_eq_of_bound R (rowLimit S) (rowLimitRate S)
  intro epsilon he n hn
  rw [h n]
  exact rowLimit_bound S epsilon he n hn

/-- Every original Cauchy representative supplies a represented family of dense states. -/
def presentationRows (X : (D).Cauchy) : CauchyRows where
  row := fun n => (D).constant (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (completedDist (embedPresentation (X.seq m))
      (embedPresentation (X.seq n))) (Quotient.mk crealSetoid (ofQ' epsilon))
    rw [completedDist_embedPresentation]
    exact X.isCauchy epsilon he m n hm hn

theorem presentationRows_rowPoint (X : (D).Cauchy) (n : Nat) :
    rowPoint (presentationRows X) n = embedPresentation (X.seq n) := rfl

/-- The new limit constructor recovers the SAME original completion class. -/
theorem rowLimit_presentationRows (X : (D).Cauchy) :
    rowLimit (presentationRows X) = Quotient.mk (D).completionSetoid X := by
  apply rowLimit_eq_of_bound (presentationRows X) (Quotient.mk (D).completionSetoid X) X.modulus
  exact constantApproximation_bound X

end YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.CauchyRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.rowPoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.diagonal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.diagonalRate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.diagonal_close_row
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.diagonal_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.diagonalCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.rowLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.rowLimitRate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.rowLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.completed_eq_of_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.rowLimit_eq_of_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.rowLimit_independent
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.presentationRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.presentationRows_rowPoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows.rowLimit_presentationRows
