/-
# Direct complexification of the SAME all-nome joint completion

The carrier is two copies of the actual joint completion.  Complex scalar
components retain supplied rational Cauchy moduli.  No representative or
modulus is selected from a quotient real.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalar
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRealScalarAlgebra

/-- Complex values, without selecting moduli for their quotient components. -/
abbrev ComplexValue := RC × RC

def valueAdd (z u : ComplexValue) : ComplexValue :=
  (RCadd z.1 u.1, RCadd z.2 u.2)

def valueMul (z u : ComplexValue) : ComplexValue :=
  (RCsub (RCmul z.1 u.1) (RCmul z.2 u.2),
    RCadd (RCmul z.1 u.2) (RCmul z.2 u.1))

def valueConj (z : ComplexValue) : ComplexValue := (z.1, RCneg z.2)

def scalarValue (s t : CReal) : ComplexValue :=
  (Quotient.mk crealSetoid s, Quotient.mk crealSetoid t)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_zero_add_eqv (A.approx n)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
      (fun _ => A.approx n)))

private theorem rc_sub_swap (a b : RC) : RCsub a b = RCneg (RCsub b a) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 1)))
      (.neg (.add (.var 1) (.neg (.var 0)))) (by decide)
      (fun | 0 => A.approx n | _ => B.approx n)))

private theorem rc_add_exchange (a b c d : RC) :
    RCadd (RCadd a b) (RCadd c d) = RCadd (RCadd a c) (RCadd b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3))) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => D.approx n)))

private theorem rc_add_sub_exchange (a b c d : RC) :
    RCsub (RCadd a b) (RCadd c d) = RCadd (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => D.approx n)))

private theorem rc_scalar_pair_real (s t : CReal) (a b c d : RC) :
    RCadd
        (RCsub (RCmul (Quotient.mk crealSetoid s) a) (RCmul (Quotient.mk crealSetoid t) b))
        (RCadd (RCmul (Quotient.mk crealSetoid t) c) (RCmul (Quotient.mk crealSetoid s) d)) =
      RCsub (RCmul (Quotient.mk crealSetoid s) (RCadd a d))
        (RCmul (Quotient.mk crealSetoid t) (RCsub b c)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
        (.add (.mul (.var 1) (.var 4)) (.mul (.var 0) (.var 5))))
      (.add (.mul (.var 0) (.add (.var 2) (.var 5)))
        (.neg (.mul (.var 1) (.add (.var 3) (.neg (.var 4)))))) (by decide)
      (fun | 0 => s.approx n | 1 => t.approx n | 2 => A.approx n | 3 => B.approx n | 4 => C.approx n | _ => D.approx n)))

private theorem rc_scalar_pair_imag (s t : CReal) (a b c d : RC) :
    RCsub
        (RCadd (RCmul (Quotient.mk crealSetoid t) a) (RCmul (Quotient.mk crealSetoid s) b))
        (RCsub (RCmul (Quotient.mk crealSetoid s) c) (RCmul (Quotient.mk crealSetoid t) d)) =
      RCadd (RCmul (Quotient.mk crealSetoid s) (RCsub b c))
        (RCmul (Quotient.mk crealSetoid t) (RCadd a d)) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3)))
        (.neg (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 5))))))
      (.add (.mul (.var 0) (.add (.var 3) (.neg (.var 4))))
        (.mul (.var 1) (.add (.var 2) (.var 5)))) (by decide)
      (fun | 0 => s.approx n | 1 => t.approx n | 2 => A.approx n | 3 => B.approx n | 4 => C.approx n | _ => D.approx n)))

theorem valueConj_mul (z u : ComplexValue) :
    valueConj (valueMul z u) = valueMul (valueConj z) (valueConj u) := by
  rcases z with ⟨a,b⟩
  rcases u with ⟨c,d⟩
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  apply Prod.ext
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 3))))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.neg (.var 1)) (.neg (.var 3)))))
        (by decide) (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => D.approx n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.neg (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))
        (.add (.mul (.var 0) (.neg (.var 3))) (.mul (.neg (.var 1)) (.var 2)))
        (by decide) (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => D.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "Z" => completedZero hw0 hw1 width
local notation "A" => completedAdd hw0 hw1 width
local notation "D" => completedSub hw0 hw1 width
local notation "S" => completedRealSmul hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width

abbrev ComplexCarrier := V × V

local notation "VC" => ComplexCarrier hw0 hw1 width

def embedReal (x : V) : VC := (x,Z)
def complexZero : VC := (Z,Z)
def complexAdd (x y : VC) : VC := (A x.1 y.1, A x.2 y.2)

/-- Conjugate-linear in the first argument and linear in the second. -/
def inner (x y : VC) : ComplexValue :=
  (RCadd (B x.1 y.1) (B x.2 y.2), RCsub (B x.1 y.2) (B x.2 y.1))

def complexSmul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : VC) : VC :=
  (D (S s cs x.1) (S t ct x.2), A (S t ct x.1) (S s cs x.2))

def complexTime (n : Nat) (x : VC) : VC := (T n x.1, T n x.2)

local notation "I" => inner hw0 hw1 width
local notation "E" => embedReal hw0 hw1 width
local notation "CZ" => complexZero hw0 hw1 width
local notation "CA" => complexAdd hw0 hw1 width
local notation "CS" => complexSmul hw0 hw1 width
local notation "CT" => complexTime hw0 hw1 width

theorem embedReal_injective (x y : V) (h : E x = E y) : x = y := congrArg Prod.fst h

theorem inner_embedReal (x y : V) : I (E x) (E y) = (B x y,RCzero) := by
  simp only [inner, embedReal, completedInner_zero_left, completedInner_zero_right,
    rc_add_zero, rc_sub_self]

theorem inner_conj_symm (x y : VC) : I x y = valueConj (I y x) := by
  apply Prod.ext
  · change RCadd (B x.1 y.1) (B x.2 y.2) = RCadd (B y.1 x.1) (B y.2 x.2)
    rw [completedInner_symm hw0 hw1 width x.1 y.1,
      completedInner_symm hw0 hw1 width x.2 y.2]
  · change RCsub (B x.1 y.2) (B x.2 y.1) = RCneg (RCsub (B y.1 x.2) (B y.2 x.1))
    rw [completedInner_symm hw0 hw1 width y.1 x.2,
      completedInner_symm hw0 hw1 width y.2 x.1]
    exact rc_sub_swap _ _

theorem inner_diagonal (x : VC) :
    I x x = (RCadd (B x.1 x.1) (B x.2 x.2),RCzero) := by
  change (_,RCsub (B x.1 x.2) (B x.2 x.1)) = _
  rw [completedInner_symm hw0 hw1 width x.2 x.1, rc_sub_self]

theorem inner_nonnegative (x : VC) : RCnonneg (I x x).1 := by
  have h := RCadd_le_add (completedInner_nonnegative hw0 hw1 width x.1)
    (completedInner_nonnegative hw0 hw1 width x.2)
  rw [rc_add_zero] at h
  exact h

theorem inner_posdef (x : VC) : (I x x).1 = RCzero ↔ x = CZ := by
  constructor
  · intro h
    have h1 := RCadd_le_add (RCle_refl (B x.1 x.1))
      (completedInner_nonnegative hw0 hw1 width x.2)
    have h2 := RCadd_le_add (completedInner_nonnegative hw0 hw1 width x.1)
      (RCle_refl (B x.2 x.2))
    change RCadd (B x.1 x.1) (B x.2 x.2) = RCzero at h
    rw [rc_add_zero,h] at h1
    rw [rc_zero_add,h] at h2
    apply Prod.ext
    · exact (completedInner_posdef hw0 hw1 width x.1).mp
        (RCle_antisymm h1 (completedInner_nonnegative hw0 hw1 width x.1))
    · exact (completedInner_posdef hw0 hw1 width x.2).mp
        (RCle_antisymm h2 (completedInner_nonnegative hw0 hw1 width x.2))
  · intro h
    rw [h]
    change RCadd (B Z Z) (B Z Z) = RCzero
    rw [completedInner_zero_left,rc_add_zero]

theorem inner_add_right (x y z : VC) : I x (CA y z) = valueAdd (I x y) (I x z) := by
  apply Prod.ext
  · simp only [inner,complexAdd,valueAdd,completedInner_add_right]
    exact rc_add_exchange _ _ _ _
  · simp only [inner,complexAdd,valueAdd,completedInner_add_right]
    exact rc_add_sub_exchange _ _ _ _

theorem inner_add_left (x y z : VC) : I (CA x y) z = valueAdd (I x z) (I y z) := by
  apply Prod.ext
  · simp only [inner,complexAdd,valueAdd,completedInner_add_left]
    exact rc_add_exchange _ _ _ _
  · simp only [inner,complexAdd,valueAdd,completedInner_add_left]
    exact rc_add_sub_exchange _ _ _ _

theorem inner_smul_right (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x y : VC) : I x (CS s t cs ct y) = valueMul (scalarValue s t) (I x y) := by
  apply Prod.ext
  · simp only [inner,complexSmul,valueMul,scalarValue,completedInner_sub_right,
      completedInner_add_right,completedInner_realSmul_right]
    exact rc_scalar_pair_real s t _ _ _ _
  · simp only [inner,complexSmul,valueMul,scalarValue,completedInner_sub_right,
      completedInner_add_right,completedInner_realSmul_right]
    exact rc_scalar_pair_imag s t _ _ _ _

theorem inner_smul_left (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x y : VC) : I (CS s t cs ct x) y = valueMul (valueConj (scalarValue s t)) (I x y) := by
  rw [inner_conj_symm hw0 hw1 width (CS s t cs ct x) y,
    inner_smul_right, valueConj_mul, ← inner_conj_symm hw0 hw1 width x y]

theorem complexTime_embedReal (n : Nat) (x : V) : CT n (E x) = E (T n x) := by
  simp only [complexTime,embedReal,completedTime_zero_element]

theorem complexTime_zero (x : VC) : CT 0 x = x := by
  simp only [complexTime,jointCompletedTime_zero]

theorem complexTime_add (m n : Nat) (x : VC) : CT (m+n) x = CT m (CT n x) := by
  simp only [complexTime,jointCompletedTime_add]

theorem complexTime_addition (n : Nat) (x y : VC) :
    CT n (CA x y) = CA (CT n x) (CT n y) := by
  simp only [complexTime,complexAdd,completedTime_additive]

theorem complexTime_smul (n : Nat) (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : VC) :
    CT n (CS s t cs ct x) = CS s t cs ct (CT n x) := by
  simp only [complexTime,complexSmul,completedTime_sub,completedTime_additive,
    completedTime_realSmul]

theorem inner_time_balance (n : Nat) (x y : VC) : I (CT n x) y = I x (CT n y) := by
  simp only [inner,complexTime,completedInner_time_balance]

#print axioms valueAdd
#print axioms valueMul
#print axioms valueConj
#print axioms scalarValue
#print axioms valueConj_mul
#print axioms embedReal
#print axioms complexZero
#print axioms complexAdd
#print axioms inner
#print axioms complexSmul
#print axioms complexTime
#print axioms embedReal_injective
#print axioms inner_embedReal
#print axioms inner_conj_symm
#print axioms inner_diagonal
#print axioms inner_nonnegative
#print axioms inner_posdef
#print axioms inner_add_right
#print axioms inner_add_left
#print axioms inner_smul_right
#print axioms inner_smul_left
#print axioms complexTime_embedReal
#print axioms complexTime_zero
#print axioms complexTime_add
#print axioms complexTime_addition
#print axioms complexTime_smul
#print axioms inner_time_balance

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification
