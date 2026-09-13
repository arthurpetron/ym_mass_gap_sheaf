/-
# Positive-definite ORIGINAL thermodynamic OS null quotient

Zero reflected squared distance on the EXISTING semantic observable algebra
is exactly equality of all reflected pairings. The actual original limit
form descends to this null quotient, becomes positive definite, and retains
its unit of norm one and original mean coefficient.

Only addition and rational scaling descend here. No multiplication/action
on OS states is assumed. This is not a Hilbert completion, physical
stationary vacuum, time-transfer operator, spectral gap or continuum QFT.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear
import YMGap.Continuum.RCBilinearDifference

namespace YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear

def subtract (x y : Observable) : Observable := qadd x (qsmul (-1) y)

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (QPoly.q_add_zero_eqv (A.approx n))))

private theorem rc_eq_of_sub_zero {a b : RC} (h : RCsub a b = RCzero) : a = b := by
  have hc : RCadd (RCsub a b) b = a := by
    refine Quotient.inductionOn₂ a b ?_
    intro A B
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B.approx n)))
  rw [h, rc_zero_add] at hc
  exact hc.symm

private theorem rc_minusOne_mul (a : RC) :
    RCmul (Quotient.mk crealSetoid (ofQ' (-1))) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))))

theorem pairing_neg_left (x y : Observable) : pairing (qsmul (-1) x) y = RCneg (pairing x y) := by
  rw [pairing_smul_left]
  exact rc_minusOne_mul _

theorem pairing_sub_left (x y z : Observable) :
    pairing (subtract x y) z = RCsub (pairing x z) (pairing y z) := by
  unfold subtract
  rw [pairing_add_left, pairing_neg_left]
  rfl

theorem pairing_sub_right (x y z : Observable) :
    pairing x (subtract y z) = RCsub (pairing x y) (pairing x z) := by
  rw [pairing_symm x (subtract y z), pairing_sub_left, pairing_symm y x, pairing_symm z x]

def Null (x y : Observable) : Prop := pairing (subtract x y) (subtract x y) = RCzero

theorem null_iff_pairing (x y : Observable) :
    Null x y ↔ ∀ z, pairing x z = pairing y z := by
  constructor
  · intro h z
    have hz := pairing_radical_zero (subtract x y) z h
    rw [pairing_sub_left] at hz
    exact rc_eq_of_sub_zero hz
  · intro h
    unfold Null
    rw [pairing_sub_left, h (subtract x y), rc_sub_self]

def nullSetoid : Setoid Observable where
  r := Null
  iseqv := ⟨fun x => (null_iff_pairing x x).mpr (fun _ => rfl),
    fun h => (null_iff_pairing _ _).mpr (fun z => ((null_iff_pairing _ _).mp h z).symm),
    fun h k => (null_iff_pairing _ _).mpr (fun z =>
      ((null_iff_pairing _ _).mp h z).trans ((null_iff_pairing _ _).mp k z))⟩

theorem pairing_null_congr {x x' y y' : Observable} (hx : Null x x') (hy : Null y y') :
    pairing x y = pairing x' y' := by
  rw [(null_iff_pairing _ _).mp hx y, pairing_symm x' y,
    (null_iff_pairing _ _).mp hy x', pairing_symm y' x']

theorem null_zero_iff (x : Observable) : Null x zero ↔ pairing x x = RCzero := by
  unfold Null
  rw [pairing_sub_left, pairing_zero_left, rc_sub_zero,
    pairing_sub_right, pairing_zero_right, rc_sub_zero]

theorem null_add {x x' y y' : Observable} (hx : Null x x') (hy : Null y y') :
    Null (qadd x y) (qadd x' y') := by
  apply (null_iff_pairing _ _).mpr
  intro z
  rw [pairing_add_left, pairing_add_left, (null_iff_pairing _ _).mp hx z, (null_iff_pairing _ _).mp hy z]

theorem null_smul (c : Q') {x y : Observable} (h : Null x y) : Null (qsmul c x) (qsmul c y) := by
  apply (null_iff_pairing _ _).mpr
  intro z
  rw [pairing_smul_left, pairing_smul_left, (null_iff_pairing _ _).mp h z]

theorem value_null {x y : Observable} (h : Null x y) : value x = value y := by
  have he := (null_iff_pairing x y).mp h unit
  rwa [pairing_unit_right_value, pairing_unit_right_value] at he

def Carrier : Type := Quotient nullSetoid

def project (x : Observable) : Carrier := Quotient.mk nullSetoid x

def inner : Carrier → Carrier → RC :=
  Quotient.lift₂ pairing (fun _ _ _ _ hx hy => pairing_null_congr hx hy)

def osZero : Carrier := project zero

def osUnit : Carrier := project unit

def osAdd : Carrier → Carrier → Carrier :=
  Quotient.lift₂ (fun x y => project (qadd x y)) (fun _ _ _ _ hx hy => Quotient.sound (null_add hx hy))

def osSmul (c : Q') : Carrier → Carrier :=
  Quotient.lift (fun x => project (qsmul c x)) (fun _ _ h => Quotient.sound (null_smul c h))

def unitCoefficient : Carrier → RC :=
  Quotient.lift value (fun _ _ h => value_null h)

theorem inner_project (x y : Observable) : inner (project x) (project y) = pairing x y := rfl

theorem unitCoefficient_project (x : Observable) : unitCoefficient (project x) = value x := rfl

theorem inner_symm (x y : Carrier) : inner x y = inner y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact pairing_symm

theorem inner_nonnegative (x : Carrier) : RCnonneg (inner x x) := by
  refine Quotient.inductionOn x ?_
  exact pairing_nonnegative

theorem inner_add_left (x y z : Carrier) : inner (osAdd x y) z = RCadd (inner x z) (inner y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact pairing_add_left

theorem inner_smul_left (c : Q') (x y : Carrier) :
    inner (osSmul c x) y = RCmul (Quotient.mk crealSetoid (ofQ' c)) (inner x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact pairing_smul_left c

theorem inner_cauchySchwarz (x y : Carrier) :
    RCle (RCmul (inner x y) (inner x y)) (RCmul (inner x x) (inner y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact pairing_cauchySchwarz

theorem inner_posdef (x : Carrier) : inner x x = RCzero ↔ x = osZero := by
  refine Quotient.inductionOn x ?_
  intro e
  exact ⟨fun h => Quotient.sound ((null_zero_iff e).mpr h),
    fun h => (null_zero_iff e).mp (Quotient.exact h)⟩

theorem unit_norm_one : inner osUnit osUnit = Quotient.mk crealSetoid cone := pairing_unit

theorem inner_unit_coefficient (x : Carrier) : inner osUnit x = unitCoefficient x := by
  refine Quotient.inductionOn x ?_
  exact pairing_unit_left_value

theorem osUnit_ne_zero : osUnit ≠ osZero := by
  intro h
  have hz := (inner_posdef osUnit).mpr h
  rw [unit_norm_one] at hz
  have hreal : Equiv cone czero := Quotient.exact hz
  obtain ⟨N, hN⟩ := hreal HalfPow.half (by decide)
  exact (by decide : ¬ ((1 : Q') ≤ 0 + HalfPow.half)) (hN N (Nat.le_refl N)).1

end YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.subtract
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.pairing_neg_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.pairing_sub_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.pairing_sub_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.Null
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.null_iff_pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.nullSetoid
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.pairing_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.null_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.null_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.null_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.value_null
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.Carrier
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.project
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.osZero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.osUnit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.osAdd
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.osSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.unitCoefficient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner_project
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.unitCoefficient_project
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner_posdef
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.unit_norm_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.inner_unit_coefficient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicNullQuotient.osUnit_ne_zero
