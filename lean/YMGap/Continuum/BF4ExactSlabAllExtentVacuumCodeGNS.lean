/-
# Completed non-null code and same-object centered pairings

The specified trivial-representation boundary code has completed norm one
and is nonzero at every odd extent. Its exact rational mean gives a finite
boundary observable orthogonal to that SAME code. The centered completed
pairing is the original bilinear minus the product of its own code means;
a computed common stage pins all three terms to the original finite law.

These are code-relative Gram/covariance statements. They do not identify
the code with a physical stationary vacuum, the all-label heat-dressed unit,
or a time-dependent connected correlator. No transfer, inter-slab map or
strict spectral estimate is introduced.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization

namespace YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitGNS
open YMGap.Continuum.BF4ExactSlabAllExtentVacuumNormalization

local infix:50 " ≈ " => Q'.eqv

private theorem unit_not_rad (D : GNSData) (a : D.V) (ha : D.B a a ≈ 1) : ¬ D.rad a D.zero := by
  intro h
  exact (by decide : ¬ (1 : Q') ≈ 0)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm ha) ((D.rad_zero_iff a).mp h))

theorem vacuumCode_not_null (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    ¬ (cutoffLimitGNSData w hw half).rad (vacuumCode half) (cutoffLimitGNSData w hw half).zero := by
  apply unit_not_rad
  rw [cutoffLimitGNSData_form]
  exact vacuumCode_limit_norm w half

theorem vacuumCode_completed_norm (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    (cutoffLimitCompletion w hw half).hilbert.cinner
      (cutoffLimitEmbed w hw (vacuumCode half)) (cutoffLimitEmbed w hw (vacuumCode half)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 1) :=
  (cutoffLimitEmbed_pairing w hw _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (vacuumCode_limit_norm w half)))

theorem vacuumCode_completed_ne_zero (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    cutoffLimitEmbed w hw (vacuumCode half) ≠ cutoffLimitEmbed w hw (BoundaryObservable.zero half) := by
  intro h
  have he := (cutoffLimitCompletion w hw half).hilbert.ι_injective h
  exact vacuumCode_not_null w hw half (Quotient.exact he)

def codeMean (w : Q') {half : Nat} (a : BoundaryObservable half) : Q' :=
  limitForm w a (vacuumCode half)

/-- Exact rational centering remains inside the same finite-boundary carrier. -/
def centerCode (w : Q') {half : Nat} (a : BoundaryObservable half) : BoundaryObservable half :=
  a.add ((vacuumCode half).smul (-(codeMean w a)))

def codeCovariance (w : Q') {half : Nat} (a b : BoundaryObservable half) : Q' :=
  limitForm w a b - codeMean w a * codeMean w b

theorem centerCode_orthogonal (w : Q') {half : Nat} (a : BoundaryObservable half) :
    limitForm w (centerCode w a) (vacuumCode half) ≈ 0 :=
  Q'.eqv_trans _ _ _ (limitForm_add_left w _ _ _) (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_trans _ _ _ (limitForm_smul_left w _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (vacuumCode_limit_norm w half)) (Q'.mul_one_eqv _))))
    (Q'.add_neg_self_eqv _))

theorem centerCode_left {w : Q'} (hw : (0 : Q') ≤ w) {half : Nat} (a b : BoundaryObservable half) :
    limitForm w (centerCode w a) b ≈ codeCovariance w a b :=
  Q'.eqv_trans _ _ _ (limitForm_add_left w _ _ _) (Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.eqv_trans _ _ _ (limitForm_smul_left w _ _ _) (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (limitForm_symm hw (vacuumCode half) b)) (Q'.neg_mul_eqv _ _))))

private theorem form_add_right {w : Q'} (hw : (0 : Q') ≤ w) {half : Nat}
    (a b c : BoundaryObservable half) : limitForm w a (b.add c) ≈ limitForm w a b + limitForm w a c :=
  Q'.eqv_trans _ _ _ (limitForm_symm hw _ _) (Q'.eqv_trans _ _ _ (limitForm_add_left w _ _ _)
    (Q'.add_eqv_congr' (limitForm_symm hw _ _) (limitForm_symm hw _ _)))

private theorem form_smul_right {w : Q'} (hw : (0 : Q') ≤ w) {half : Nat}
    (s : Q') (a b : BoundaryObservable half) : limitForm w a (b.smul s) ≈ s * limitForm w a b :=
  Q'.eqv_trans _ _ _ (limitForm_symm hw _ _) (Q'.eqv_trans _ _ _ (limitForm_smul_left w _ _ _)
    (Q'.mul_eqv_congr_left _ _ _ (limitForm_symm hw _ _)))

theorem centerCode_pairing {w : Q'} (hw : (0 : Q') ≤ w) {half : Nat} (a b : BoundaryObservable half) :
    limitForm w (centerCode w a) (centerCode w b) ≈ codeCovariance w a b :=
  Q'.eqv_trans _ _ _ (form_add_right hw _ _ _) (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (centerCode_left hw a b) (Q'.eqv_trans _ _ _ (form_smul_right hw _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (centerCode_orthogonal w a)) (Q'.mul_zero_eqv _))))
    (Q'.eqv_of_eq (Q'.add_zero' _)))

theorem codeCovariance_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) {half : Nat} (a : BoundaryObservable half) :
    (0 : Q') ≤ codeCovariance w a a :=
  Q'.le_trans' _ _ _ (limitForm_nonnegative hw (centerCode w a)) (Q'.le_of_eqv (centerCode_pairing hw a a))

/-- The joint form and BOTH original one-point forms share this computed stage. -/
def covarianceModulus (w : Q') {half : Nat} (a b : BoundaryObservable half) : Nat :=
  max (formModulus w a b) (max (formModulus w a (vacuumCode half)) (formModulus w b (vacuumCode half)))

def finiteCodeCovariance (w : Q') (K : Nat) {half : Nat} (a b : BoundaryObservable half) : Q' :=
  finiteForm w K a b - finiteForm w K a (vacuumCode half) * finiteForm w K b (vacuumCode half)

theorem finiteCodeCovariance_stable (w : Q') (K : Nat) {half : Nat} (a b : BoundaryObservable half)
    (hK : covarianceModulus w a b ≤ K) : finiteCodeCovariance w K a b ≈ codeCovariance w a b := by
  have hab := finiteForm_stable w K a b (Nat.le_trans (Nat.le_max_left _ _) hK)
  have ha := finiteForm_stable w K a (vacuumCode half)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hK)
  have hb := finiteForm_stable w K b (vacuumCode half)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hK)
  exact Q'.add_eqv_congr' hab (Q'.neg_eqv_congr _ _ (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)))

theorem centerCode_completed_orthogonal (w : Q') (hw : (0 : Q') ≤ w) {half : Nat}
    (a : BoundaryObservable half) :
    (cutoffLimitCompletion w hw half).hilbert.cinner
      (cutoffLimitEmbed w hw (centerCode w a)) (cutoffLimitEmbed w hw (vacuumCode half)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' 0) :=
  (cutoffLimitEmbed_pairing w hw _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (centerCode_orthogonal w a)))

theorem centerCode_completed_pairing (w : Q') (hw : (0 : Q') ≤ w) {half : Nat}
    (a b : BoundaryObservable half) :
    (cutoffLimitCompletion w hw half).hilbert.cinner
      (cutoffLimitEmbed w hw (centerCode w a)) (cutoffLimitEmbed w hw (centerCode w b)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (codeCovariance w a b)) :=
  (cutoffLimitEmbed_pairing w hw _ _).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (centerCode_pairing hw a b)))

/-- The centered completed pairing is the SAME finite-law covariance, not an external scalar. -/
theorem centerCode_completed_finite_pairing (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    {half : Nat} (a b : BoundaryObservable half) (hK : covarianceModulus w a b ≤ K) :
    (cutoffLimitCompletion w hw half).hilbert.cinner
      (cutoffLimitEmbed w hw (centerCode w a)) (cutoffLimitEmbed w hw (centerCode w b)) =
      Quotient.mk CReal.crealSetoid (CReal.ofQ' (finiteCodeCovariance w K a b)) :=
  (centerCode_completed_pairing w hw a b).trans
    (Quotient.sound (CReal.ofQ'_equiv_of_eqv (Q'.eqv_symm (finiteCodeCovariance_stable w K a b hK))))

end YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.vacuumCode_not_null
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.vacuumCode_completed_norm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.vacuumCode_completed_ne_zero
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.codeMean
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.centerCode
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.codeCovariance
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.centerCode_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.centerCode_left
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.centerCode_pairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.codeCovariance_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.covarianceModulus
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.finiteCodeCovariance
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.finiteCodeCovariance_stable
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.centerCode_completed_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.centerCode_completed_pairing
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentVacuumCodeGNS.centerCode_completed_finite_pairing
