/-
# Faithful finite-Haar two-mode GNS connector

The legacy character Hilbert scaffold has a zero dense map, while the actual
midpoint-Riemann calculation lives in `CReal`.  This file supplies the missing
nondegenerate *finite two-mode* GNS object without claiming that it is already
the interacting Wilson finite-volume state.

The rational GNS datum is the orthogonal direct sum of two unit lines.  Its two
basis classes are nonzero and distinct.  Assuming only the existing genuine
semicircle value residual, every entry of the faithful normalized Riemann Gram
table agrees with the `CReal` lift of this rational GNS form.  Thus the analytic
normalization residual and the old zero-image obstruction are cleanly
separated: once normalization is proved, the two character modes have an
explicit positive-definite GNS carrier.

The diagonal character evolution with exact eigenvalues `1/8` and `1/256` is
also defined on the dense rational carrier, and its two eigen-equations are
proved.  Extending that map to the completed interacting Wilson GNS still
requires the same-state `E_Lambda` identification; no such identification is
assumed here.
-/

import YMGap.Continuum.SU2FiniteHaarRiemannTwoMode
import YMGap.Continuum.SU2HaarTwoModePositiveTimePilot
import YMGap.Continuum.PositiveTimeCompressedTransfer

namespace YMGap.Continuum.SU2FaithfulTwoModeGNSConnector

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveTimeCompressedTransfer
open YMGap.Continuum.SU2FiniteHaarRiemannTwoMode
open YMGap.Continuum.SU2HaarTwoModePositiveTimePilot

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

def modeZero : Fin 2 := ⟨0, by decide⟩
def modeOne : Fin 2 := ⟨1, by decide⟩

/-- Every index in the retained two-character sector is one of the two
explicit modes. -/
theorem fin_two_cases (i : Fin 2) : i = modeZero ∨ i = modeOne := by
  cases i with
  | mk n hn =>
      cases n with
      | zero => exact Or.inl rfl
      | succ n =>
          have hn0 : n = 0 := by omega
          subst n
          exact Or.inr rfl

/-- The nondegenerate rational two-mode GNS datum. -/
abbrev faithfulModeGNS : GNSData := positivePlane

def firstModeVector : faithfulModeGNS.V := (1, 0)
def secondModeVector : faithfulModeGNS.V := (0, 1)

def modeVector (i : Fin 2) : faithfulModeGNS.V :=
  if i.val = 0 then firstModeVector else secondModeVector

/-- Its Gram matrix is exactly the two-by-two identity. -/
theorem mode_gram (i j : Fin 2) :
    faithfulModeGNS.B (modeVector i) (modeVector j) ≈
      if i.val = j.val then 1 else 0 := by
  rcases fin_two_cases i with hi | hi <;> subst i
  <;> rcases fin_two_cases j with hj | hj <;> subst j
  <;> simp only [modeVector, firstModeVector, secondModeVector, modeZero,
    modeOne, gnsProduct, unitQGNS]
  <;> decide

/-- The first basis class is genuinely nonzero in the GNS quotient. -/
theorem first_mode_qmk_ne_zero :
    faithfulModeGNS.qmk firstModeVector ≠
      faithfulModeGNS.qmk faithfulModeGNS.zero := by
  intro h
  have hr : faithfulModeGNS.rad firstModeVector faithfulModeGNS.zero :=
    Quotient.exact h
  unfold GNSData.rad GNSData.sub faithfulModeGNS positivePlane gnsProduct
    unitQGNS firstModeVector at hr
  exact (by decide : ¬ ((((1 : Q') *
      (((1 : Q') + -(0 : Q')) * ((1 : Q') + -(0 : Q')))) +
    ((1 : Q') * (((0 : Q') + -(0 : Q')) *
      ((0 : Q') + -(0 : Q'))))).eqv 0)) hr

/-- The second basis class is genuinely nonzero in the GNS quotient. -/
theorem second_mode_qmk_ne_zero :
    faithfulModeGNS.qmk secondModeVector ≠
      faithfulModeGNS.qmk faithfulModeGNS.zero := by
  intro h
  have hr : faithfulModeGNS.rad secondModeVector faithfulModeGNS.zero :=
    Quotient.exact h
  unfold GNSData.rad GNSData.sub faithfulModeGNS positivePlane gnsProduct
    unitQGNS secondModeVector at hr
  exact (by decide : ¬ ((((1 : Q') *
      (((0 : Q') + -(0 : Q')) * ((0 : Q') + -(0 : Q')))) +
    ((1 : Q') * (((1 : Q') + -(0 : Q')) *
      ((1 : Q') + -(0 : Q'))))).eqv 0)) hr

/-- The two retained character modes remain distinct after quotienting. -/
theorem mode_classes_distinct :
    faithfulModeGNS.qmk firstModeVector ≠
      faithfulModeGNS.qmk secondModeVector := by
  intro h
  have hr : faithfulModeGNS.rad firstModeVector secondModeVector :=
    Quotient.exact h
  unfold GNSData.rad GNSData.sub faithfulModeGNS positivePlane gnsProduct
    unitQGNS firstModeVector secondModeVector at hr
  exact (by decide : ¬ ((((1 : Q') *
      (((1 : Q') + -(0 : Q')) * ((1 : Q') + -(0 : Q')))) +
    ((1 : Q') * (((0 : Q') + -(1 : Q')) *
      ((0 : Q') + -(1 : Q'))))).eqv 0)) hr

/-- Every retained character index has a nonzero reconstructed quotient
class; this is the direct replacement for the legacy zero-image scaffold. -/
theorem every_mode_qmk_ne_zero (i : Fin 2) :
    faithfulModeGNS.qmk (modeVector i) ≠ faithfulModeGNS.qZero := by
  rcases fin_two_cases i with hi | hi
  · subst i
    simpa [GNSData.qZero, modeVector, modeZero] using first_mode_qmk_ne_zero
  · subst i
    simpa [GNSData.qZero, modeVector, modeOne] using second_mode_qmk_ne_zero

/-- Any genuinely off-diagonal faithful Riemann moment is already zero,
without the semicircle value theorem. -/
theorem normalized_offdiagonal_of_ne {i j : Fin 2}
    (hij : i.val ≠ j.val) :
    CReal.Equiv (normalizedMoment i j) CReal.czero := by
  change CReal.Equiv
    (CReal.mul Constructive.Pi.twoOverPi
      (if i.val = j.val then SemicircleBoundClosed.semiInt else CReal.czero))
    CReal.czero
  rw [if_neg hij]
  exact HaarClassIntegral.mul_czero Constructive.Pi.twoOverPi

/-- Conditional only on the genuine semicircle normalization, the faithful
midpoint-Riemann Gram is exactly the `CReal` lift of the nondegenerate rational
GNS Gram. -/
theorem faithful_normalized_moment_matches_gns
    (hsemi : SemicircleValue.SemiConvergesToHalfPi) (i j : Fin 2) :
    CReal.Equiv (normalizedMoment i j)
      (CReal.ofQ' (faithfulModeGNS.B (modeVector i) (modeVector j))) := by
  by_cases hij : i.val = j.val
  · have hfin : i = j := Fin.eq_of_val_eq hij
    subst j
    have hB : faithfulModeGNS.B (modeVector i) (modeVector i) ≈ 1 := by
      simpa using mode_gram i i
    exact CReal.Equiv.trans
      (normalized_diagonal_of_semiConverges hsemi i)
      (CReal.Equiv.symm (CReal.ofQ'_equiv_of_eqv hB))
  · have hB : faithfulModeGNS.B (modeVector i) (modeVector j) ≈ 0 := by
      simpa [hij] using mode_gram i j
    refine CReal.Equiv.trans (normalized_offdiagonal_of_ne hij) ?_
    change CReal.Equiv (CReal.ofQ' 0)
      (CReal.ofQ' (faithfulModeGNS.B (modeVector i) (modeVector j)))
    exact CReal.Equiv.symm (CReal.ofQ'_equiv_of_eqv hB)

/-! ## Exact dense character evolution -/

def denseCharacterTransfer (v : faithfulModeGNS.V) : faithfulModeGNS.V :=
  (firstEigenvalue * v.1, secondEigenvalue * v.2)

theorem dense_character_first_eigen :
    faithfulModeGNS.veq (denseCharacterTransfer firstModeVector)
      (faithfulModeGNS.smul firstEigenvalue firstModeVector) := by
  unfold denseCharacterTransfer faithfulModeGNS positivePlane gnsProduct
    unitQGNS firstModeVector
  exact ⟨Q'.eqv_refl _, by decide⟩

theorem dense_character_second_eigen :
    faithfulModeGNS.veq (denseCharacterTransfer secondModeVector)
      (faithfulModeGNS.smul secondEigenvalue secondModeVector) := by
  unfold denseCharacterTransfer faithfulModeGNS positivePlane gnsProduct
    unitQGNS secondModeVector
  exact ⟨by decide, Q'.eqv_refl _⟩

/-- The dense character evolution is self-adjoint for the faithful two-mode
GNS form. -/
theorem dense_character_selfAdjoint (a b : faithfulModeGNS.V) :
    faithfulModeGNS.B (denseCharacterTransfer a) b ≈
      faithfulModeGNS.B a (denseCharacterTransfer b) := by
  unfold denseCharacterTransfer faithfulModeGNS positivePlane gnsProduct
    unitQGNS
  ring_qeqv

/-- Both exact character eigenvalues are nonnegative, hence the dense
evolution is positive for the faithful two-mode form. -/
theorem dense_character_positive (a : faithfulModeGNS.V) :
    (0 : Q') ≤ faithfulModeGNS.B (denseCharacterTransfer a) a := by
  have h0sq : (0 : Q') ≤ a.1 * a.1 :=
    SumOfSquares.q_mul_self_nonneg a.1
  have h1sq : (0 : Q') ≤ a.2 * a.2 :=
    SumOfSquares.q_mul_self_nonneg a.2
  have h0core : (0 : Q') ≤ firstEigenvalue * (a.1 * a.1) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt two_strict_eigenvalue_windows.1.1) h0sq
  have h1core : (0 : Q') ≤ secondEigenvalue * (a.2 * a.2) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt two_strict_eigenvalue_windows.2.1) h1sq
  have h0term : (0 : Q') ≤
      1 * ((firstEigenvalue * a.1) * a.1) := by
    refine Q'.le_trans' _ _ _ h0core (Q'.le_of_eqv (Q'.eqv_symm ?_))
    exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
      (Q'.mul_assoc_eqv firstEigenvalue a.1 a.1)
  have h1term : (0 : Q') ≤
      1 * ((secondEigenvalue * a.2) * a.2) := by
    refine Q'.le_trans' _ _ _ h1core (Q'.le_of_eqv (Q'.eqv_symm ?_))
    exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
      (Q'.mul_assoc_eqv secondEigenvalue a.2 a.2)
  unfold denseCharacterTransfer faithfulModeGNS positivePlane gnsProduct
    unitQGNS
  exact Q'.zero_le_add _ _ h0term h1term

/-- Since both exact eigenvalues lie in `[0,1]`, the dense evolution is a
contraction in squared GNS norm. -/
theorem dense_character_contraction (a : faithfulModeGNS.V) :
    faithfulModeGNS.B (denseCharacterTransfer a) (denseCharacterTransfer a) ≤
      faithfulModeGNS.B a a := by
  have h0sq : (0 : Q') ≤ a.1 * a.1 :=
    SumOfSquares.q_mul_self_nonneg a.1
  have h1sq : (0 : Q') ≤ a.2 * a.2 :=
    SumOfSquares.q_mul_self_nonneg a.2
  have h0lam : firstEigenvalue * firstEigenvalue ≤ (1 : Q') := by decide
  have h1lam : secondEigenvalue * secondEigenvalue ≤ (1 : Q') := by decide
  have h0core := Q'.mul_le_mul_of_nonneg_right
    (firstEigenvalue * firstEigenvalue) 1 (a.1 * a.1) h0lam h0sq
  have h1core := Q'.mul_le_mul_of_nonneg_right
    (secondEigenvalue * secondEigenvalue) 1 (a.2 * a.2) h1lam h1sq
  have h0term :
      1 * ((firstEigenvalue * a.1) * (firstEigenvalue * a.1)) ≤
        1 * (a.1 * a.1) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h0core
    refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
    ring_qeqv
  have h1term :
      1 * ((secondEigenvalue * a.2) * (secondEigenvalue * a.2)) ≤
        1 * (a.2 * a.2) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h1core
    refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
    ring_qeqv
  unfold denseCharacterTransfer faithfulModeGNS positivePlane gnsProduct
    unitQGNS
  exact Q'.add_le_add h0term h1term

theorem dense_character_eigenvalue_windows :
    ((0 : Q') < firstEigenvalue ∧ firstEigenvalue < (1 : Q')) ∧
      ((0 : Q') < secondEigenvalue ∧ secondEigenvalue < (1 : Q')) :=
  two_strict_eigenvalue_windows

#print axioms fin_two_cases
#print axioms mode_gram
#print axioms first_mode_qmk_ne_zero
#print axioms second_mode_qmk_ne_zero
#print axioms mode_classes_distinct
#print axioms every_mode_qmk_ne_zero
#print axioms normalized_offdiagonal_of_ne
#print axioms faithful_normalized_moment_matches_gns
#print axioms dense_character_first_eigen
#print axioms dense_character_second_eigen
#print axioms dense_character_selfAdjoint
#print axioms dense_character_positive
#print axioms dense_character_contraction
#print axioms dense_character_eigenvalue_windows

end YMGap.Continuum.SU2FaithfulTwoModeGNSConnector
