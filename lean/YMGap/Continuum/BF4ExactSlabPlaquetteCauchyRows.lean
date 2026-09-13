/-
# Diagonal limits of supplied Cauchy rows in the ORIGINAL completion

For a family with actual Cauchy representatives and an outer squared-distance
modulus, the diagonal samples row n at its own modulus(invSucc n).
Its Cauchy rate is max(outerModulus(epsilon/16), (epsilon/16).den).
The resulting completed limit has convergence rate outerModulus(epsilon/16).

The limit is unique and independent of the supplied row representatives.
This does NOT select representatives of an arbitrary quotient-valued Cauchy
sequence, and is not asserted as that stronger completeness theorem.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

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

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

local notation "D" => seminorm w hw0 hw1 half

/-- Represented Cauchy families; the rows and outer rate are retained as data. -/
structure CauchyRows (half : Nat) where
  row : Nat → (seminorm w hw0 hw1 half).Cauchy
  modulus : Q' → Nat
  isCauchy : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ m n,
    modulus epsilon ≤ m → modulus epsilon ≤ n →
    RCle (completedDist w hw0 hw1
      (Quotient.mk (seminorm w hw0 hw1 half).completionSetoid (row m))
      (Quotient.mk (seminorm w hw0 hw1 half).completionSetoid (row n)))
      (Quotient.mk crealSetoid (ofQ' epsilon))

def rowPoint (R : CauchyRows w hw0 hw1 half) (n : Nat) : Completion w hw0 hw1 half :=
  Quotient.mk (D).completionSetoid (R.row n)

def diagonal (R : CauchyRows w hw0 hw1 half) (n : Nat) : PlaquetteExpression half :=
  approximant w hw0 hw1 (R.row n) n

def diagonalRate (R : CauchyRows w hw0 hw1 half) (epsilon : Q') : Nat :=
  max (R.modulus (quarter (quarter epsilon))) (quarter (quarter epsilon)).den

theorem diagonal_close_row (R : CauchyRows w hw0 hw1 half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : epsilon.den ≤ n) :
    RCle (completedDist w hw0 hw1 (embedExpression w hw0 hw1 (diagonal w hw0 hw1 R n)) (rowPoint w hw0 hw1 R n))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hrelax : RCle (Quotient.mk crealSetoid (ofQ' (Q'.invSucc n))) (Quotient.mk crealSetoid (ofQ' epsilon)) :=
    leEv_le_ofQ'_of_approx_le (fun _ => invSucc_le_of_den he hn)
  exact RCle_trans (approximant_bound w hw0 hw1 (R.row n) n) hrelax

theorem diagonal_bound (R : CauchyRows w hw0 hw1 half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : diagonalRate w hw0 hw1 R epsilon ≤ m) (hn : diagonalRate w hw0 hw1 R epsilon ≤ n) :
    leEv (distSq w hw0 hw1 (diagonal w hw0 hw1 R m) (diagonal w hw0 hw1 R n)) (ofQ' epsilon) := by
  let delta := quarter (quarter epsilon)
  have hd : (0 : Q') < delta := quarter_pos (quarter_pos he)
  have hdm : delta.den ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
  have hdn : delta.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hmm : R.modulus delta ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
  have hmn : R.modulus delta ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hleft := diagonal_close_row w hw0 hw1 R delta hd m hdm
  have hright := diagonal_close_row w hw0 hw1 R delta hd n hdn
  rw [completedDist_symm w hw0 hw1 (embedExpression w hw0 hw1 (diagonal w hw0 hw1 R n))] at hright
  have h := completedDist_three_segment w hw0 hw1
    (embedExpression w hw0 hw1 (diagonal w hw0 hw1 R m)) (rowPoint w hw0 hw1 R m)
    (rowPoint w hw0 hw1 R n) (embedExpression w hw0 hw1 (diagonal w hw0 hw1 R n))
    epsilon he hleft (R.isCauchy delta hd m n hmm hmn) hright
  rw [completedDist_embedExpression] at h
  exact h

def diagonalCauchy (R : CauchyRows w hw0 hw1 half) : (D).Cauchy where
  seq := diagonal w hw0 hw1 R
  modulus := diagonalRate w hw0 hw1 R
  isCauchy := diagonal_bound w hw0 hw1 R

def rowLimit (R : CauchyRows w hw0 hw1 half) : Completion w hw0 hw1 half :=
  Quotient.mk (D).completionSetoid (diagonalCauchy w hw0 hw1 R)

def rowLimitRate (R : CauchyRows w hw0 hw1 half) (epsilon : Q') : Nat := R.modulus (quarter (quarter epsilon))

theorem rowLimit_bound (R : CauchyRows w hw0 hw1 half) (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : rowLimitRate w hw0 hw1 R epsilon ≤ k) :
    RCle (completedDist w hw0 hw1 (rowPoint w hw0 hw1 R k) (rowLimit w hw0 hw1 R))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let delta := quarter (quarter epsilon)
  have hd : (0 : Q') < delta := quarter_pos (quarter_pos he)
  apply representativeDist_le_of_eventually w hw0 hw1 (R.row k) (diagonalCauchy w hw0 hw1 R) epsilon
    (max (diagonalRate w hw0 hw1 R epsilon) ((R.row k).modulus delta))
  intro n hn
  have hnrate : diagonalRate w hw0 hw1 R epsilon ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hninner : (R.row k).modulus delta ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hnouter : R.modulus delta ≤ n := Nat.le_trans (Nat.le_max_left _ _) hnrate
  have hnden : delta.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hnrate
  have hleft := constantApproximation_bound w hw0 hw1 (R.row k) delta hd n hninner
  have hright := diagonal_close_row w hw0 hw1 R delta hd n hnden
  rw [completedDist_symm w hw0 hw1 (embedExpression w hw0 hw1 (diagonal w hw0 hw1 R n))] at hright
  have h := completedDist_three_segment w hw0 hw1
    (embedExpression w hw0 hw1 ((R.row k).seq n)) (rowPoint w hw0 hw1 R k)
    (rowPoint w hw0 hw1 R n) (embedExpression w hw0 hw1 (diagonal w hw0 hw1 R n))
    epsilon he hleft (R.isCauchy delta hd k n hk hnouter) hright
  rw [completedDist_embedExpression] at h
  exact h

theorem completed_eq_of_small (x y : Completion w hw0 hw1 half)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon → RCle (completedDist w hw0 hw1 x y) (Quotient.mk crealSetoid (ofQ' epsilon))) :
    x = y :=
  (completedDist_zero_iff w hw0 hw1 x y).mp (rc_zero_of_small _ (completedDist_nonnegative w hw0 hw1 x y) h)

theorem rowLimit_eq_of_bound (R : CauchyRows w hw0 hw1 half) (L : Completion w hw0 hw1 half) (rate : Q' → Nat)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
      RCle (completedDist w hw0 hw1 (rowPoint w hw0 hw1 R n) L) (Quotient.mk crealSetoid (ofQ' epsilon))) :
    rowLimit w hw0 hw1 R = L := by
  apply completed_eq_of_small w hw0 hw1
  intro epsilon he
  let q := quarter epsilon
  have hq : (0 : Q') < q := quarter_pos he
  let n := max (rowLimitRate w hw0 hw1 R q) (rate q)
  have hleft := rowLimit_bound w hw0 hw1 R q hq n (Nat.le_max_left _ _)
  rw [completedDist_symm] at hleft
  exact completedDist_two_segment w hw0 hw1 (rowLimit w hw0 hw1 R) (rowPoint w hw0 hw1 R n) L epsilon
    hleft (h q hq n (Nat.le_max_right _ _))

/-- The diagonal's value does not depend on row representatives or their moduli. -/
theorem rowLimit_independent (R S : CauchyRows w hw0 hw1 half)
    (h : ∀ n, rowPoint w hw0 hw1 R n = rowPoint w hw0 hw1 S n) : rowLimit w hw0 hw1 R = rowLimit w hw0 hw1 S := by
  apply rowLimit_eq_of_bound w hw0 hw1 R (rowLimit w hw0 hw1 S) (rowLimitRate w hw0 hw1 S)
  intro epsilon he n hn
  rw [h n]
  exact rowLimit_bound w hw0 hw1 S epsilon he n hn

/-- Every original Cauchy representative supplies a represented family of dense states. -/
def expressionRows (X : (D).Cauchy) : CauchyRows w hw0 hw1 half where
  row := fun n => (D).constant (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (completedDist w hw0 hw1 (embedExpression w hw0 hw1 (X.seq m))
      (embedExpression w hw0 hw1 (X.seq n))) (Quotient.mk crealSetoid (ofQ' epsilon))
    rw [completedDist_embedExpression]
    exact X.isCauchy epsilon he m n hm hn

theorem expressionRows_rowPoint (X : (D).Cauchy) (n : Nat) :
    rowPoint w hw0 hw1 (expressionRows w hw0 hw1 X) n = embedExpression w hw0 hw1 (X.seq n) := rfl

/-- The new limit constructor recovers the SAME original completion class. -/
theorem rowLimit_expressionRows (X : (D).Cauchy) :
    rowLimit w hw0 hw1 (expressionRows w hw0 hw1 X) = Quotient.mk (D).completionSetoid X := by
  apply rowLimit_eq_of_bound w hw0 hw1 (expressionRows w hw0 hw1 X) (Quotient.mk (D).completionSetoid X) X.modulus
  exact constantApproximation_bound w hw0 hw1 X

end YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.CauchyRows
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.rowPoint
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.diagonal
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.diagonalRate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.diagonal_close_row
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.diagonal_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.diagonalCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.rowLimit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.rowLimitRate
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.rowLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.completed_eq_of_small
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.rowLimit_eq_of_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.rowLimit_independent
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.expressionRows
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.expressionRows_rowPoint
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteCauchyRows.rowLimit_expressionRows
