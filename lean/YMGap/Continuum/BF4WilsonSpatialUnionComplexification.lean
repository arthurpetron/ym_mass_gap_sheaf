/-
# Direct complexification of the CURRENT completed Wilson carrier

The vector carrier is exactly two copies of the existing UnionCompletion,
with its real carrier embedded as x |-> (x,0). The Hermitian pairing is

  <(x,y),(u,v)> = (B(x,u)+B(y,v), B(x,v)-B(y,u)).

It is positive definite, additive and sesquilinear for complex scalars
whose TWO real components carry supplied QCauchy moduli. The actual time
maps and actual Wilson character multipliers act componentwise; their
complex linearity, symmetry, semigroup and commuting-multiplier laws are
inherited from the proved laws on the SAME original real carrier.

No scalar representative or modulus is selected for an arbitrary RC.
This is not an unrestricted RC x RC scalar-field/module interface, nor a
proof of arbitrary quotient-sequence metric completeness. Such a scalar
interface and complex completeness, continuous-time/generator control,
changing-spacing reconstruction and full continuum QFT remain separate.
The original small-nome guards, group and lattice spacing are unchanged.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionRealScalarAlgebra
import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroCommutation

namespace YMGap.Continuum.BF4WilsonSpatialUnionComplexification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedRealScalar
open YMGap.Continuum.BF4WilsonSpatialUnionRealScalarAlgebra
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier (completedMultiply)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroOperator
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroCommutation (completedMultiply_comm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_add_zero rc_sub_self rc_sub_zero)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Complex coefficient VALUES; no unprovided scalar modulus is selected. -/
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
      (fun
        | 0 => s.approx n
        | 1 => t.approx n
        | 2 => A.approx n
        | 3 => B.approx n
        | 4 => C.approx n
        | _ => D.approx n)))

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
      (fun
        | 0 => s.approx n
        | 1 => t.approx n
        | 2 => A.approx n
        | 3 => B.approx n
        | 4 => C.approx n
        | _ => D.approx n)))

theorem valueConj_involutive (z : ComplexValue) : valueConj (valueConj z) = z := by
  rcases z with ⟨a,b⟩
  apply Prod.ext
  · rfl
  · change RCneg (RCneg b) = b
    refine Quotient.inductionOn b ?_
    exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.neg_neg_eqv (A.approx n)))

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
        (by decide)
        (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => D.approx n)))
  · exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.neg (.add (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2))))
        (.add (.mul (.var 0) (.neg (.var 3))) (.mul (.neg (.var 1)) (.var 2)))
        (by decide)
        (fun | 0 => A.approx n | 1 => B.approx n | 2 => C.approx n | _ => D.approx n)))

section CurrentCarrier

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "D" => completedSub hw0 hw1 hsmall hd hs
local notation "S" => completedRealSmul hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "M" => completedMultiply hw0 hw1 hsmall hd hs

/-- Two copies of the actual carrier; no identification with a legacy model. -/
abbrev ComplexCarrier := V × V

local notation "VC" => ComplexCarrier hw0 hw1 hsmall hd hs

def embedReal (x : V) : VC := (x,Z)

def complexZero : VC := (Z,Z)

def complexAdd (x y : VC) : VC := (A x.1 y.1, A x.2 y.2)

/-- The first argument is conjugate-linear and the second is linear. -/
def inner (x y : VC) : ComplexValue :=
  (RCadd (B x.1 y.1) (B x.2 y.2), RCsub (B x.1 y.2) (B x.2 y.1))

/-- Both scalar components retain their supplied constructive moduli. -/
def complexSmul (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (x : VC) : VC :=
  (D (S s cs x.1) (S t ct x.2), A (S t ct x.1) (S s cs x.2))

def complexTime (n : Nat) (x : VC) : VC := (T n x.1, T n x.2)

def complexMultiply {base : Nat} (L : SourceLoop base) (spin : Nat) (x : VC) : VC :=
  (M L spin x.1, M L spin x.2)

local notation "I" => inner hw0 hw1 hsmall hd hs
local notation "E" => embedReal hw0 hw1 hsmall hd hs
local notation "CZ" => complexZero hw0 hw1 hsmall hd hs
local notation "CA" => complexAdd hw0 hw1 hsmall hd hs
local notation "CS" => complexSmul hw0 hw1 hsmall hd hs
local notation "CT" => complexTime hw0 hw1 hsmall hd hs
local notation "CM" => complexMultiply hw0 hw1 hsmall hd hs

theorem embedReal_injective (x y : V) (h : E x = E y) : x = y := congrArg Prod.fst h

theorem complexAdd_assoc (x y z : VC) : CA (CA x y) z = CA x (CA y z) := by
  simp only [complexAdd,completedAdd_assoc]

theorem complexAdd_comm (x y : VC) : CA x y = CA y x := by
  apply Prod.ext
  · exact completedAdd_comm hw0 hw1 hsmall hd hs x.1 y.1
  · exact completedAdd_comm hw0 hw1 hsmall hd hs x.2 y.2

theorem complexAdd_zero (x : VC) : CA x CZ = x := by
  simp only [complexAdd,complexZero,completedAdd_zero]

/-- The unit scalar acts as the identity for any supplied constant moduli. -/
theorem complexSmul_one (c1 : QCauchy cone.approx) (c0 : QCauchy czero.approx)
    (x : VC) : CS cone czero c1 c0 x = x := by
  simp only [complexSmul,completedRealSmul_one,completedRealSmul_zero,
    completedSub_zero,completedZero_add]

/-- Multiplication by i is the actual quarter-turn of the real pair. -/
theorem complexSmul_i (c0 : QCauchy czero.approx) (c1 : QCauchy cone.approx)
    (x : VC) : CS czero cone c0 c1 x =
      (completedNeg hw0 hw1 hsmall hd hs x.2,x.1) := by
  simp only [complexSmul,completedRealSmul_one,completedRealSmul_zero,
    completedSub,completedZero_add,completedAdd_zero]

/-- The real pairing is preserved exactly by the explicit embedding. -/
theorem inner_embedReal (x y : V) : I (E x) (E y) = (B x y,RCzero) := by
  simp only [inner, embedReal, completedInner_zero_left, completedInner_zero_right,
    rc_add_zero, rc_sub_self]

theorem inner_conj_symm (x y : VC) : I x y = valueConj (I y x) := by
  apply Prod.ext
  · change RCadd (B x.1 y.1) (B x.2 y.2) = RCadd (B y.1 x.1) (B y.2 x.2)
    rw [completedInner_symm hw0 hw1 hsmall hd hs x.1 y.1,
      completedInner_symm hw0 hw1 hsmall hd hs x.2 y.2]
  · change RCsub (B x.1 y.2) (B x.2 y.1) = RCneg (RCsub (B y.1 x.2) (B y.2 x.1))
    rw [completedInner_symm hw0 hw1 hsmall hd hs y.1 x.2,
      completedInner_symm hw0 hw1 hsmall hd hs y.2 x.1]
    exact rc_sub_swap _ _

theorem inner_diagonal (x : VC) :
    I x x = (RCadd (B x.1 x.1) (B x.2 x.2),RCzero) := by
  change (_,RCsub (B x.1 x.2) (B x.2 x.1)) = _
  rw [completedInner_symm hw0 hw1 hsmall hd hs x.2 x.1, rc_sub_self]

theorem inner_nonnegative (x : VC) : RCnonneg (I x x).1 := by
  have h := RCadd_le_add
    (completedInner_nonnegative hw0 hw1 hsmall hd hs x.1)
    (completedInner_nonnegative hw0 hw1 hsmall hd hs x.2)
  rw [rc_add_zero] at h
  exact h

/-- The complex norm vanishes exactly at the pair of the actual real zeros. -/
theorem inner_posdef (x : VC) : (I x x).1 = RCzero ↔ x = CZ := by
  constructor
  · intro h
    have h1 := RCadd_le_add (RCle_refl (B x.1 x.1))
      (completedInner_nonnegative hw0 hw1 hsmall hd hs x.2)
    have h2 := RCadd_le_add (completedInner_nonnegative hw0 hw1 hsmall hd hs x.1)
      (RCle_refl (B x.2 x.2))
    change RCadd (B x.1 x.1) (B x.2 x.2) = RCzero at h
    rw [rc_add_zero,h] at h1
    rw [rc_zero_add,h] at h2
    apply Prod.ext
    · exact (completedInner_posdef hw0 hw1 hsmall hd hs x.1).mp
        (RCle_antisymm h1 (completedInner_nonnegative hw0 hw1 hsmall hd hs x.1))
    · exact (completedInner_posdef hw0 hw1 hsmall hd hs x.2).mp
        (RCle_antisymm h2 (completedInner_nonnegative hw0 hw1 hsmall hd hs x.2))
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

/-- Sesquilinearity uses the existing real scalar actions, with their
supplied moduli, not a new action of arbitrary quotient-real values. -/
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
  rw [inner_conj_symm hw0 hw1 hsmall hd hs (CS s t cs ct x) y,
    inner_smul_right, valueConj_mul, ← inner_conj_symm hw0 hw1 hsmall hd hs x y]

/-- The two moduli may differ; only equivalence of their scalar values matters. -/
theorem complexSmul_congr (s t s' t' : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx)
    (cs' : QCauchy s'.approx) (ct' : QCauchy t'.approx)
    (hs' : Equiv s s') (ht' : Equiv t t') (x : VC) :
    CS s t cs ct x = CS s' t' cs' ct' x := by
  unfold complexSmul
  rw [completedRealSmul_congr hw0 hw1 hsmall hd hs s s' cs cs' hs' x.1,
    completedRealSmul_congr hw0 hw1 hsmall hd hs s s' cs cs' hs' x.2,
    completedRealSmul_congr hw0 hw1 hsmall hd hs t t' ct ct' ht' x.1,
    completedRealSmul_congr hw0 hw1 hsmall hd hs t t' ct ct' ht' x.2]

theorem complexTime_embedReal (n : Nat) (x : V) : CT n (E x) = E (T n x) := by
  simp only [complexTime,embedReal,completedTime_zero_vector]

theorem complexTime_zero (x : VC) : CT 0 x = x := by
  simp only [complexTime,completedTime_zero]

theorem complexTime_add (m n : Nat) (x : VC) : CT (m+n) x = CT m (CT n x) := by
  simp only [complexTime,completedTime_add]

theorem complexTime_addition (n : Nat) (x y : VC) : CT n (CA x y) = CA (CT n x) (CT n y) := by
  simp only [complexTime,complexAdd,completedTime_addition]

theorem complexTime_smul (n : Nat) (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : VC) :
    CT n (CS s t cs ct x) = CS s t cs ct (CT n x) := by
  simp only [complexTime,complexSmul,completedTime_sub,completedTime_addition,
    completedTime_realSmul]

theorem inner_time_balance (n : Nat) (x y : VC) : I (CT n x) y = I x (CT n y) := by
  simp only [inner,complexTime,completedInner_time_balance]

private theorem completedMultiply_sub {base : Nat} (L : SourceLoop base) (spin : Nat)
    (x y : V) : M L spin (D x y) = D (M L spin x) (M L spin y) := by
  unfold completedSub completedNeg
  rw [completedMultiply_add,completedMultiply_smul]

theorem complexMultiply_embedReal {base : Nat} (L : SourceLoop base) (spin : Nat) (x : V) :
    CM L spin (E x) = E (M L spin x) := by
  simp only [complexMultiply,embedReal,completedMultiply_zero]

theorem complexMultiply_addition {base : Nat} (L : SourceLoop base) (spin : Nat) (x y : VC) :
    CM L spin (CA x y) = CA (CM L spin x) (CM L spin y) := by
  simp only [complexMultiply,complexAdd,completedMultiply_add]

theorem complexMultiply_smul {base : Nat} (L : SourceLoop base) (spin : Nat)
    (s t : CReal) (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : VC) :
    CM L spin (CS s t cs ct x) = CS s t cs ct (CM L spin x) := by
  simp only [complexMultiply,complexSmul,completedMultiply_sub,completedMultiply_add,
    completedMultiply_realSmul]

theorem inner_multiplier_balance {base : Nat} (L : SourceLoop base) (spin : Nat)
    (x y : VC) : I (CM L spin x) y = I x (CM L spin y) := by
  simp only [inner,complexMultiply,completedInner_multiplier_balance]

/-- Equal-time commutation is retained; no continuum spacelike locality is claimed. -/
theorem complexMultiply_comm {base other : Nat} (L : SourceLoop base) (R : SourceLoop other)
    (i j : Nat) (x : VC) : CM L i (CM R j x) = CM R j (CM L i x) := by
  apply Prod.ext
  · exact completedMultiply_comm hw0 hw1 hsmall hd hs L R i j x.1
  · exact completedMultiply_comm hw0 hw1 hsmall hd hs L R i j x.2

end CurrentCarrier

#print axioms valueAdd
#print axioms valueMul
#print axioms valueConj
#print axioms scalarValue
#print axioms valueConj_involutive
#print axioms valueConj_mul
#print axioms embedReal
#print axioms complexZero
#print axioms complexAdd
#print axioms inner
#print axioms complexSmul
#print axioms complexTime
#print axioms complexMultiply
#print axioms embedReal_injective
#print axioms complexAdd_assoc
#print axioms complexAdd_comm
#print axioms complexAdd_zero
#print axioms complexSmul_one
#print axioms complexSmul_i
#print axioms inner_embedReal
#print axioms inner_conj_symm
#print axioms inner_diagonal
#print axioms inner_nonnegative
#print axioms inner_posdef
#print axioms inner_add_right
#print axioms inner_add_left
#print axioms inner_smul_right
#print axioms inner_smul_left
#print axioms complexSmul_congr
#print axioms complexTime_embedReal
#print axioms complexTime_zero
#print axioms complexTime_add
#print axioms complexTime_addition
#print axioms complexTime_smul
#print axioms inner_time_balance
#print axioms complexMultiply_embedReal
#print axioms complexMultiply_addition
#print axioms complexMultiply_smul
#print axioms inner_multiplier_balance
#print axioms complexMultiply_comm

end YMGap.Continuum.BF4WilsonSpatialUnionComplexification
