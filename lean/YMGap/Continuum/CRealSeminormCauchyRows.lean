/-
# Computed limits of supplied Cauchy representatives

Each row and its inner modulus are supplied as Type-level data. The outer
modulus measures the SAME completed distance. Sampling row n at its own
invSucc n tolerance constructs a dense Cauchy stream with rate
max(outerModulus(epsilon/16), (epsilon/16).den). Its completion class has
outer convergence rate outerModulus(epsilon/16).

Uniqueness, independence of row representatives and recovery of the
original class are proved below. No arbitrary Nat-to-quotient sequence is
lifted to representatives; that stronger choice-sensitive completeness
statement is neither assumed nor concluded.
-/

import YMGap.Continuum.CRealSeminormCompletedApproximation

namespace YMGap.Continuum.CRealSeminormCauchyRows

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion (SquaredSeminorm)
open YMGap.Continuum.CRealSeminormCompletedApproximation
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation
  (quarter quarter_pos invSucc_le_of_den)

private theorem rc_zero_of_small (a : RC) (ha : RCnonneg a)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon →
      RCle a (Quotient.mk crealSetoid (ofQ' epsilon))) : a = RCzero := by
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
    (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
      (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))

variable {D : SquaredSeminorm} (P : DistanceData D)

/-- Actual representatives and an outer modulus in the completed distance.
No existence assertion is used to select a row. -/
structure CauchyRows where
  row : Nat → D.Cauchy
  modulus : Q' → Nat
  isCauchy : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ m n,
    modulus epsilon ≤ m → modulus epsilon ≤ n →
    RCle (P.completedDist
      (Quotient.mk D.completionSetoid (row m))
      (Quotient.mk D.completionSetoid (row n)))
      (Quotient.mk crealSetoid (ofQ' epsilon))

def rowPoint (R : CauchyRows P) (n : Nat) : D.Completion :=
  Quotient.mk D.completionSetoid (R.row n)

def diagonal (R : CauchyRows P) (n : Nat) : D.Carrier :=
  approximant P (R.row n) n

def diagonalRate (R : CauchyRows P) (epsilon : Q') : Nat :=
  max (R.modulus (quarter (quarter epsilon))) (quarter (quarter epsilon)).den

theorem diagonal_close_row (R : CauchyRows P) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : epsilon.den ≤ n) :
    RCle (P.completedDist (D.embedRep (diagonal P R n)) (rowPoint P R n))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have hrelax : RCle (Quotient.mk crealSetoid (ofQ' (Q'.invSucc n)))
      (Quotient.mk crealSetoid (ofQ' epsilon)) :=
    leEv_le_ofQ'_of_approx_le (fun _ => invSucc_le_of_den he hn)
  exact RCle_trans (approximant_bound P (R.row n) n) hrelax

theorem diagonal_bound (R : CauchyRows P) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : diagonalRate P R epsilon ≤ m) (hn : diagonalRate P R epsilon ≤ n) :
    leEv (D.distSq (diagonal P R m) (diagonal P R n)) (ofQ' epsilon) := by
  let delta := quarter (quarter epsilon)
  have hd : (0 : Q') < delta := quarter_pos (quarter_pos he)
  have hdm : delta.den ≤ m := Nat.le_trans (Nat.le_max_right _ _) hm
  have hdn : delta.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hmm : R.modulus delta ≤ m := Nat.le_trans (Nat.le_max_left _ _) hm
  have hmn : R.modulus delta ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hleft := diagonal_close_row P R delta hd m hdm
  have hright := diagonal_close_row P R delta hd n hdn
  rw [P.completedDist_symm (D.embedRep (diagonal P R n))] at hright
  have h := completedDist_three_segment P
    (D.embedRep (diagonal P R m)) (rowPoint P R m)
    (rowPoint P R n) (D.embedRep (diagonal P R n))
    epsilon he hleft (R.isCauchy delta hd m n hmm hmn) hright
  rw [completedDist_embedRep] at h
  exact h

/-- The diagonal and BOTH layers of rates remain computable data. -/
def diagonalCauchy (R : CauchyRows P) : D.Cauchy where
  seq := diagonal P R
  modulus := diagonalRate P R
  isCauchy := diagonal_bound P R

def rowLimit (R : CauchyRows P) : D.Completion :=
  Quotient.mk D.completionSetoid (diagonalCauchy P R)

def rowLimitRate (R : CauchyRows P) (epsilon : Q') : Nat :=
  R.modulus (quarter (quarter epsilon))

theorem rowLimit_bound (R : CauchyRows P) (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : rowLimitRate P R epsilon ≤ k) :
    RCle (P.completedDist (rowPoint P R k) (rowLimit P R))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let delta := quarter (quarter epsilon)
  have hd : (0 : Q') < delta := quarter_pos (quarter_pos he)
  change RCle (P.completedDist (Quotient.mk D.completionSetoid (R.row k))
    (Quotient.mk D.completionSetoid (diagonalCauchy P R))) _
  rw [P.completedDist_mk]
  apply representativeDist_le_of_eventually P (R.row k) (diagonalCauchy P R) epsilon
    (max (diagonalRate P R epsilon) ((R.row k).modulus delta))
  intro n hn
  have hnrate : diagonalRate P R epsilon ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hninner : (R.row k).modulus delta ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hnouter : R.modulus delta ≤ n := Nat.le_trans (Nat.le_max_left _ _) hnrate
  have hnden : delta.den ≤ n := Nat.le_trans (Nat.le_max_right _ _) hnrate
  have hleft := constantApproximation_bound P (R.row k) delta hd n hninner
  have hright := diagonal_close_row P R delta hd n hnden
  rw [P.completedDist_symm (D.embedRep (diagonal P R n))] at hright
  have h := completedDist_three_segment P
    (D.embedRep ((R.row k).seq n)) (rowPoint P R k)
    (rowPoint P R n) (D.embedRep (diagonal P R n))
    epsilon he hleft (R.isCauchy delta hd k n hk hnouter) hright
  rw [completedDist_embedRep] at h
  exact h

theorem completed_eq_of_small (x y : D.Completion)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon →
      RCle (P.completedDist x y) (Quotient.mk crealSetoid (ofQ' epsilon))) : x = y :=
  (P.completedDist_zero_iff x y).mp
    (rc_zero_of_small _ (P.completedDist_nonnegative x y) h)

theorem rowLimit_eq_of_bound (R : CauchyRows P) (L : D.Completion) (rate : Q' → Nat)
    (h : ∀ epsilon : Q', (0 : Q') < epsilon → ∀ n, rate epsilon ≤ n →
      RCle (P.completedDist (rowPoint P R n) L)
        (Quotient.mk crealSetoid (ofQ' epsilon))) : rowLimit P R = L := by
  apply completed_eq_of_small P
  intro epsilon he
  let q := quarter epsilon
  have hq : (0 : Q') < q := quarter_pos he
  let n := max (rowLimitRate P R q) (rate q)
  have hleft := rowLimit_bound P R q hq n (Nat.le_max_left _ _)
  rw [P.completedDist_symm] at hleft
  exact completedDist_two_segment P (rowLimit P R) (rowPoint P R n) L epsilon
    hleft (h q hq n (Nat.le_max_right _ _))

/-- Different supplied rows/moduli representing the same points give the
same limit on the original completion. -/
theorem rowLimit_independent (R S : CauchyRows P)
    (h : ∀ n, rowPoint P R n = rowPoint P S n) : rowLimit P R = rowLimit P S := by
  apply rowLimit_eq_of_bound P R (rowLimit P S) (rowLimitRate P S)
  intro epsilon he n hn
  rw [h n]
  exact rowLimit_bound P S epsilon he n hn

/-- A supplied original Cauchy stream gives a family of dense constants. -/
def presentationRows (X : D.Cauchy) : CauchyRows P where
  row := fun n => D.constant (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    change RCle (P.completedDist (D.embedRep (X.seq m)) (D.embedRep (X.seq n)))
      (Quotient.mk crealSetoid (ofQ' epsilon))
    rw [completedDist_embedRep]
    exact X.isCauchy epsilon he m n hm hn

theorem presentationRows_rowPoint (X : D.Cauchy) (n : Nat) :
    rowPoint P (presentationRows P X) n = D.embedRep (X.seq n) := rfl

/-- The constructed limit recovers the SAME original completion class. -/
theorem rowLimit_presentationRows (X : D.Cauchy) :
    rowLimit P (presentationRows P X) = Quotient.mk D.completionSetoid X := by
  apply rowLimit_eq_of_bound P (presentationRows P X)
    (Quotient.mk D.completionSetoid X) X.modulus
  exact constantApproximation_bound P X

end YMGap.Continuum.CRealSeminormCauchyRows

#print axioms YMGap.Continuum.CRealSeminormCauchyRows.CauchyRows
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.rowPoint
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.diagonal
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.diagonalRate
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.diagonal_close_row
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.diagonal_bound
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.diagonalCauchy
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.rowLimit
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.rowLimitRate
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.rowLimit_bound
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.completed_eq_of_small
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.rowLimit_eq_of_bound
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.rowLimit_independent
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.presentationRows
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.presentationRows_rowPoint
#print axioms YMGap.Continuum.CRealSeminormCauchyRows.rowLimit_presentationRows
