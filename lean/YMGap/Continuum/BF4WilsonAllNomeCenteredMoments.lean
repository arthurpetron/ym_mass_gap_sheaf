/-
# Centered moments of the SAME literal-width all-nome Wilson form

The unit coefficient is a constructive real, not necessarily rational.
Rationally centered intrinsic expressions therefore supply the positivity,
contraction and dyadic Cauchy--Schwarz laws before taking their explicit
scalar limits. No real-linear completed operations, centered vector, decay
envelope, strict gap or continuum survival is assumed.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4WilsonAllNomeCenteredMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra (centerApprox)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_zero)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeFormLaws
open YMGap.Continuum.BF4WilsonAllNomeCauchySchwarz
open YMGap.Continuum.BF4WilsonAllNomeTimeForm
open YMGap.Continuum.BF4WilsonAllNomeTimeContraction (intrinsicForm_advance_contraction)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
  (scalarAddCauchy scalarNegCauchy scalarMulCauchy)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "F" => intrinsicForm hw0 hw1
local notation "u" => unit width

def centeredTimeMoment (n : Nat) (x y : IntrinsicExpression width) : CReal :=
  sub (F x (advance n y)) (mul (F x u) (F u y))

def centeredTimeMomentCauchy (n : Nat) (x y : IntrinsicExpression width) :
    QCauchy (centeredTimeMoment hw0 hw1 n x y).approx :=
  let A := F x (advance n y)
  let L := F x u
  let R := F u y
  scalarAddCauchy A (neg (mul L R)) (intrinsicFormCauchy hw0 hw1 x (advance n y))
    (scalarNegCauchy (mul L R) (scalarMulCauchy L R
      (intrinsicFormCauchy hw0 hw1 x u) (intrinsicFormCauchy hw0 hw1 u y)))

def evenMoment (x : IntrinsicExpression width) (k : Nat) : CReal :=
  centeredTimeMoment hw0 hw1 (2*k) x x

attribute [local irreducible] intrinsicForm

private theorem sub_congr {a b c d : CReal} (h : Equiv a b) (j : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add h (neg_congr j)

/-- Actual unit stationarity, recovered from the already proved SAME operator. -/
theorem intrinsicForm_unit_invariant (n : Nat) (x : IntrinsicExpression width) :
    Equiv (F (advance n x) u) (F x u) := by
  have h := completedInner_time_balance hw0 hw1 n (embed hw0 hw1 x)
    (unitState hw0 hw1 width)
  rw [completedUnit_fixed, completedTime_embed] at h
  unfold unitState at h
  rw [completedInner_embed, completedInner_embed] at h
  exact Quotient.exact h

theorem intrinsicForm_unit_invariant_right (n : Nat) (x : IntrinsicExpression width) :
    Equiv (F u (advance n x)) (F u x) :=
  (intrinsicForm_symm hw0 hw1 u (advance n x)).trans
    ((intrinsicForm_unit_invariant hw0 hw1 n x).trans (intrinsicForm_symm hw0 hw1 x u))

theorem centerApprox_pairing_left (x y : IntrinsicExpression width) (q : Q') :
    Equiv (F (centerApprox x q) y) (sub (F x y) (mul (ofQ' q) (F u y))) :=
  (intrinsicForm_difference_left hw0 hw1 x (smul q u) y).trans
    (sub_congr (Equiv.refl _) (intrinsicForm_smul_left hw0 hw1 q u y))

theorem centerApprox_pairing_right (x y : IntrinsicExpression width) (q : Q') :
    Equiv (F x (centerApprox y q)) (sub (F x y) (mul (ofQ' q) (F x u))) :=
  (intrinsicForm_difference_right hw0 hw1 x y (smul q u)).trans
    (sub_congr (Equiv.refl _) (intrinsicForm_smul_right hw0 hw1 q x u))

theorem centerApprox_unit (x : IntrinsicExpression width) (q : Q') :
    Equiv (F (centerApprox x q) u) (sub (F x u) (ofQ' q)) :=
  (centerApprox_pairing_left hw0 hw1 x u q).trans
    (sub_congr (Equiv.refl _)
      ((Pivot2.mul_congr_right (intrinsicForm_unit_unit hw0 hw1)).trans
        (CRealAlg.cmul_cone (ofQ' q))))

/-- The physical lag and rational approximation index are independent. -/
theorem centerApprox_time_pairing (n : Nat) (x : IntrinsicExpression width) (q : Q') :
    Equiv (F (centerApprox x q) (advance n (centerApprox x q)))
      (sub (sub (F x (advance n x)) (mul (ofQ' q) (F u x)))
        (mul (ofQ' q) (sub (F x u) (ofQ' q)))) := by
  have hleft := (intrinsicForm_time_balance hw0 hw1 n (centerApprox x q) x).trans
    ((centerApprox_pairing_left hw0 hw1 x (advance n x) q).trans
      (sub_congr (Equiv.refl _)
        (Pivot2.mul_congr_right (intrinsicForm_unit_invariant_right hw0 hw1 n x))))
  have hunit := (intrinsicForm_unit_invariant hw0 hw1 n (centerApprox x q)).trans
    (centerApprox_unit hw0 hw1 x q)
  exact (intrinsicForm_time_balance hw0 hw1 n (centerApprox x q) (centerApprox x q)).symm.trans
    ((centerApprox_pairing_right hw0 hw1 (advance n (centerApprox x q)) x q).trans
      (sub_congr hleft (Pivot2.mul_congr_right hunit)))

/-- This convergence proof uses the existing explicit inner Cauchy modulus. -/
theorem mean_approximations_converge (x : IntrinsicExpression width) :
    ConvergesTo (fun k => ofQ' ((F x u).approx k)) (F x u) := by
  intro epsilon he
  let c := intrinsicFormCauchy hw0 hw1 x u
  exact ⟨c.M epsilon, fun k hk =>
    ⟨c.M epsilon, fun j hj => c.bound epsilon he k j hk hj⟩⟩

/-- Rational centering converges to the original connected scalar. No
completed real scalar multiplication or selected representative is needed. -/
theorem centeredApprox_time_converges (n : Nat) (x : IntrinsicExpression width) :
    ConvergesTo (fun k => F (centerApprox x ((F x u).approx k))
      (advance n (centerApprox x ((F x u).approx k))))
      (centeredTimeMoment hw0 hw1 n x x) := by
  let A := F x (advance n x)
  let mu := F x u
  let E := F u x
  let S (k : Nat) := sub (sub A (mul (ofQ' (mu.approx k)) E))
    (mul (ofQ' (mu.approx k)) (sub mu (ofQ' (mu.approx k))))
  have hc : ConvergesTo S (sub (sub A (mul mu E)) (mul mu (sub mu mu))) :=
    TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (convergesTo_const A)
        (TrigAddCReal.convergesTo_neg
          (convergesTo_mul_general (mean_approximations_converge hw0 hw1 x)
            (convergesTo_const E))))
      (TrigAddCReal.convergesTo_neg
        (convergesTo_mul_general (mean_approximations_converge hw0 hw1 x)
          (TrigAddCReal.convergesTo_add (convergesTo_const mu)
            (TrigAddCReal.convergesTo_neg (mean_approximations_converge hw0 hw1 x)))))
  have hz : Equiv (mul mu (sub mu mu)) czero :=
    (Pivot2.mul_congr_right (sub_self_eqv_zero mu)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun k => Q'.mul_zero_eqv (mu.approx k)))
  have he : Equiv (sub (sub A (mul mu E)) (mul mu (sub mu mu)))
      (centeredTimeMoment hw0 hw1 n x x) :=
    (sub_congr (Equiv.refl _) hz).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun k =>
        Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
          (Q'.eqv_of_eq (Q'.add_zero' _))))
  exact TrigAddCReal.convergesTo_congr_seq
    (fun k => (centerApprox_time_pairing hw0 hw1 n x (mu.approx k)).symm)
    (ArctanTrigConvergesProof.convergesTo_of_equiv hc he)

private theorem raw_even_diagonal (x : IntrinsicExpression width) (k : Nat) :
    Equiv (F (advance k x) (advance k x)) (F x (advance (2*k) x)) := by
  simpa only [Nat.two_mul] using intrinsicForm_time_sum hw0 hw1 k k x x

private theorem raw_even_nonnegative (x : IntrinsicExpression width) (k : Nat) :
    leEv czero (F x (advance (2*k) x)) :=
  leEv_trans (intrinsicForm_nonnegative hw0 hw1 (advance k x))
    (leEv_of_equiv (raw_even_diagonal hw0 hw1 x k))

private theorem raw_even_le_zero (x : IntrinsicExpression width) (k : Nat) :
    leEv (F x (advance (2*k) x)) (F x (advance (2*0) x)) := by
  rw [Nat.mul_zero, advance_zero]
  exact leEv_trans (leEv_of_equiv (raw_even_diagonal hw0 hw1 x k).symm)
    (intrinsicForm_advance_contraction hw0 hw1 k x)

private theorem raw_even_dyadic (x : IntrinsicExpression width) (k : Nat) :
    leEv (mul (F x (advance (2*k) x)) (F x (advance (2*k) x)))
      (mul (F x (advance (2*(k+k)) x)) (F x (advance (2*0) x))) := by
  rw [Nat.mul_zero, advance_zero]
  have hd : Equiv (F (advance (2*k) x) (advance (2*k) x))
      (F x (advance (2*(k+k)) x)) := by
    simpa only [show 2*k+2*k=2*(k+k) by omega] using
      intrinsicForm_time_sum hw0 hw1 (2*k) (2*k) x x
  exact leEv_trans (intrinsicForm_cauchySchwarz hw0 hw1 x (advance (2*k) x))
    (leEv_of_equiv ((Pivot2.mul_congr_right hd).trans (CRealAlg.cmul_comm _ _)))

theorem evenMoment_nonnegative (x : IntrinsicExpression width) (k : Nat) :
    leEv czero (evenMoment hw0 hw1 x k) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (centeredApprox_time_converges hw0 hw1 (2*k) x)
    (fun j => raw_even_nonnegative hw0 hw1 (centerApprox x ((F x u).approx j)) k)

theorem evenMoment_le_zero (x : IntrinsicExpression width) (k : Nat) :
    leEv (evenMoment hw0 hw1 x k) (evenMoment hw0 hw1 x 0) :=
  leEv_of_convergesTo_le (centeredApprox_time_converges hw0 hw1 (2*k) x)
    (centeredApprox_time_converges hw0 hw1 (2*0) x)
    (fun j => raw_even_le_zero hw0 hw1 (centerApprox x ((F x u).approx j)) k)

theorem evenMoment_dyadic (x : IntrinsicExpression width) (k : Nat) :
    leEv (mul (evenMoment hw0 hw1 x k) (evenMoment hw0 hw1 x k))
      (mul (evenMoment hw0 hw1 x (k+k)) (evenMoment hw0 hw1 x 0)) :=
  leEv_of_convergesTo_le
    (convergesTo_mul_general (centeredApprox_time_converges hw0 hw1 (2*k) x)
      (centeredApprox_time_converges hw0 hw1 (2*k) x))
    (convergesTo_mul_general (centeredApprox_time_converges hw0 hw1 (2*(k+k)) x)
      (centeredApprox_time_converges hw0 hw1 (2*0) x))
    (fun j => raw_even_dyadic hw0 hw1 (centerApprox x ((F x u).approx j)) k)

#print axioms centeredTimeMomentCauchy
#print axioms intrinsicForm_unit_invariant
#print axioms intrinsicForm_unit_invariant_right
#print axioms centerApprox_pairing_left
#print axioms centerApprox_pairing_right
#print axioms centerApprox_unit
#print axioms centerApprox_time_pairing
#print axioms mean_approximations_converge
#print axioms centeredApprox_time_converges
#print axioms evenMoment_nonnegative
#print axioms evenMoment_le_zero
#print axioms evenMoment_dyadic

end YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
