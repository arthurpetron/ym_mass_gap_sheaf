/-
# Computed norm-normalization scalar for a witnessed positive CReal

Clamping rational samples at the supplied positive floor preserves their
QCauchy modulus and their ORIGINAL real value. The constructed Heron/root
and reciprocal streams therefore return s, its QCauchy modulus, and
s*(s*a)=1 for that same a. An upper bound a<=P also gives 1/P<=s^2.
No representative, modulus, root or inverse is selected by choice.
-/

import YMGap.Continuum.PositiveRationalCauchySquareRoot
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.PositiveCRealNormalizationScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap (leEv_cancel_mul_right_posEv)

theorem clamp_step (a b rho epsilon : Q') (he : (0 : Q')≤epsilon)
    (h : a≤b+epsilon) : Q'.max' a rho≤Q'.max' b rho+epsilon :=
  (Q'.max'_le_iff' _ _ _).mpr
    ⟨Q'.le_trans' _ _ _ h (Q'.add_le_add_right _ _ epsilon (Q'.le_max'_left b rho)),
      Q'.le_trans' _ _ _ (Q'.le_max'_right b rho) (Q'.add_le_self_of_nonneg _ _ he)⟩

variable (a : CReal) (ca : QCauchy a.approx) (rho : Q') (hrho : (0 : Q')<rho)
  (hfloor : leEv (ofQ' rho) a)

def clamped (n : Nat) : Q' := Q'.max' (a.approx n) rho

def clampedCauchy : QCauchy (clamped a rho) where
  M := ca.M
  bound := fun epsilon he p q hp hq =>
    ⟨clamp_step _ _ _ _ (Q'.le_of_lt he) (ca.bound epsilon he p q hp hq).1,
      clamp_step _ _ _ _ (Q'.le_of_lt he) (ca.bound epsilon he p q hp hq).2⟩

include hfloor in
theorem clamped_value : Equiv (PositiveRationalCauchySquareRoot.source (clampedCauchy a ca rho)) a := by
  intro epsilon he
  obtain ⟨N,hN⟩ := hfloor epsilon he
  refine ⟨N,fun n hn => ⟨?_,?_⟩⟩
  · exact (Q'.max'_le_iff' _ _ _).mpr
      ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he),hN n hn⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

def lowerRoot : Q' := Q'.min' 1 rho

include hrho in
theorem lowerRoot_positive : (0 : Q')<lowerRoot rho := by
  unfold lowerRoot Q'.min'
  by_cases h : (1 : Q')≤rho
  · rw [if_pos h]; decide
  · rw [if_neg h]; exact hrho

include hrho in
theorem lowerRoot_square_le : lowerRoot rho*lowerRoot rho≤rho :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.min_le_left' 1 rho)
    (Q'.le_of_lt (lowerRoot_positive rho hrho)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) (Q'.min_le_right' 1 rho))

include hrho in
theorem clamped_square_floor (n : Nat) : lowerRoot rho*lowerRoot rho≤clamped a rho n :=
  Q'.le_trans' _ _ _ (lowerRoot_square_le rho hrho) (Q'.le_max'_right _ _)

def scalar : CReal :=
  PositiveRationalCauchySquareRoot.inverse (clampedCauchy a ca rho)
    (lowerRoot rho) (lowerRoot_positive rho hrho) (clamped_square_floor a rho hrho)

def scalarCauchy : QCauchy (scalar a ca rho hrho).approx :=
  PositiveRationalCauchySquareRoot.inverseCauchy (clampedCauchy a ca rho)
    (lowerRoot rho) (lowerRoot_positive rho hrho) (clamped_square_floor a rho hrho)

theorem scalar_positive (n : Nat) : (0 : Q')<(scalar a ca rho hrho).approx n :=
  PositiveRationalCauchySquareRoot.inverse_positive _ _ _ _ n

theorem scalar_nonnegative : leEv czero (scalar a ca rho hrho) :=
  leEv_ofQ'_of_approx_ge (fun n => Q'.le_of_lt (scalar_positive a ca rho hrho n))

def scalarSquare : CReal := CReal.mul (scalar a ca rho hrho) (scalar a ca rho hrho)

theorem scalarSquare_nonnegative : leEv czero (scalarSquare a ca rho hrho) :=
  leEv_ofQ'_of_approx_ge (fun n => Q'.le_of_lt (Q'.mul_pos
    (scalar_positive a ca rho hrho n) (scalar_positive a ca rho hrho n)))

include hfloor in
theorem scalar_normalizes :
    Equiv (CReal.mul (scalar a ca rho hrho) (CReal.mul (scalar a ca rho hrho) a)) cone :=
  (Pivot2.mul_congr_right (Pivot2.mul_congr_right (clamped_value a ca rho hfloor).symm)).trans
    (PositiveRationalCauchySquareRoot.inverse_square_source _ _ _ _)

include hfloor in
theorem scalarSquare_normalizes : Equiv (CReal.mul (scalarSquare a ca rho hrho) a) cone :=
  (cmul_assoc _ _ _).trans (scalar_normalizes a ca rho hrho hfloor)

include hfloor in
theorem scalarSquare_floor (P : Q') (hP : (0 : Q')<P) (hupper : leEv a (ofQ' P)) :
    leEv (ofQ' (Q'.recipPos P hP)) (scalarSquare a ca rho hrho) := by
  apply leEv_cancel_mul_right_posEv (F:=ofQ' P) ⟨P,hP,leEv_refl _⟩
  have hcancel : Equiv (CReal.mul (ofQ' (Q'.recipPos P hP)) (ofQ' P)) cone :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv P hP))
  exact leEv_trans (leEv_of_equiv hcancel)
    (leEv_trans (leEv_of_equiv (scalarSquare_normalizes a ca rho hrho hfloor).symm)
      (leEv_mul_nonneg_left (scalarSquare_nonnegative a ca rho hrho) hupper))

include hfloor in
theorem normalized_weight_floor (P beta : Q') (hP : (0 : Q')<P) (hbeta : (0 : Q')<beta)
    (hupper : leEv a (ofQ' P)) (b : CReal) (hb : leEv (ofQ' beta) b) :
    leEv (ofQ' (Q'.divPos beta P hP))
      (CReal.mul (scalar a ca rho hrho) (CReal.mul (scalar a ca rho hrho) b)) := by
  have hscale := leEv_smul_nonneg (Q'.le_of_lt hbeta)
    (scalarSquare_floor a ca rho hrho hfloor P hP hupper)
  exact leEv_trans (leEv_of_equiv (ofQ'_mul beta (Q'.recipPos P hP)))
    (leEv_trans hscale (leEv_trans (leEv_of_equiv (cmul_comm _ _))
      (leEv_trans (leEv_mul_nonneg_left (scalarSquare_nonnegative a ca rho hrho) hb)
        (leEv_of_equiv (cmul_assoc _ _ _)))))

end YMGap.Continuum.PositiveCRealNormalizationScalar

#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.clamp_step
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.clamped
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.clampedCauchy
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.clamped_value
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.lowerRoot
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.lowerRoot_positive
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.lowerRoot_square_le
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.clamped_square_floor
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalar
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalarCauchy
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalar_positive
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalar_nonnegative
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalarSquare
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalarSquare_nonnegative
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalar_normalizes
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalarSquare_normalizes
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.scalarSquare_floor
#print axioms YMGap.Continuum.PositiveCRealNormalizationScalar.normalized_weight_floor
