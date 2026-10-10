/-
# Central-sign descent of the actual rational symmetric-power action

The scalar quaternion -1 acts on the complete degree-n tensor by its
degree parity, hence on all n+1 reconstructed symmetric coefficients.
At even degree this gives an actual action of the located sign-coset group
on representatives, with the existing multiplication and Hermitian laws.
Odd degree is detected by a concrete nonzero coefficient. This is only a
rational algebraic global-form leg: no compact SO(3), completed action,
continuous Haar, Yang--Mills action, or physical gap is inferred.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerAction
import YMGap.RepTheory.RationalQuaternionSignQuotient
import YMGap.RepTheory.CompactSimpleGlobalForm

namespace YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionTensorPowerAction
open YMGap.Continuum.SU2QuaternionSymmetricPowerAction

local infix:50 " ≃c " => RationalComplexEqv
local infixl:70 " ⊠ " => rationalComplexMul

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> ac_rfl))

private def negativeScalar : RationalComplex := (-1, 0)

/-- The central-sign scalar recorded without choosing a tensor basis. -/
def parityScalar (n : Nat) : RationalComplex :=
  (if n % 2 = 0 then 1 else -1, 0)

private theorem parityScalar_succ (n : Nat) :
    (negativeScalar ⊠ parityScalar n) ≃c parityScalar (n + 1) := by
  have hrange : n % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases heven : n % 2 = 0
  · have hodd : (n + 1) % 2 ≠ 0 := by omega
    simp only [parityScalar, negativeScalar, heven, hodd, ite_true, ite_false]
    unfold rationalComplexMul RationalComplexEqv
    constructor <;> ring_qeqv
  · have hnext : (n + 1) % 2 = 0 := by omega
    simp only [parityScalar, negativeScalar, heven, hnext, ite_true, ite_false]
    unfold rationalComplexMul RationalComplexEqv
    constructor <;> ring_qeqv

private theorem tensorScale_one : ∀ (n : Nat) (x : Tensor n),
    TensorEqv n (tensorScale n rationalComplexOne x) x
  | 0, x => by
      unfold TensorEqv tensorScale rationalComplexOne rationalComplexMul RationalComplexEqv
      constructor <;> ring_qeqv
  | n + 1, x => fun b => tensorScale_one n (x b)

private theorem tensorScale_scale (a b : RationalComplex) : ∀ (n : Nat) (x : Tensor n),
    TensorEqv n (tensorScale n a (tensorScale n b x))
      (tensorScale n (a ⊠ b) x)
  | 0, x => rationalComplexEqv_symm (rationalComplexMul_assoc a b x)
  | n + 1, x => fun bit => tensorScale_scale a b n (x bit)

private theorem negativeRow_false : ∀ (n : Nat) (x y : Tensor n),
    TensorEqv n
      (tensorAdd n (tensorScale n (fundamentalMatrixValue RationalQuaternion.unitNegativeOne.val false false) x)
        (tensorScale n (fundamentalMatrixValue RationalQuaternion.unitNegativeOne.val false true) y))
      (tensorScale n negativeScalar x)
  | 0, x, y => by
      change RationalComplexEqv
        (rationalComplexAdd (rationalComplexMul negativeScalar x)
          (rationalComplexMul rationalComplexZero y))
        (rationalComplexMul negativeScalar x)
      unfold rationalComplexAdd rationalComplexMul negativeScalar rationalComplexZero RationalComplexEqv
      constructor <;> ring_qeqv
  | n + 1, x, y => fun b => negativeRow_false n (x b) (y b)

private theorem negativeRow_true : ∀ (n : Nat) (x y : Tensor n),
    TensorEqv n
      (tensorAdd n (tensorScale n (fundamentalMatrixValue RationalQuaternion.unitNegativeOne.val true false) x)
        (tensorScale n (fundamentalMatrixValue RationalQuaternion.unitNegativeOne.val true true) y))
      (tensorScale n negativeScalar y)
  | 0, x, y => by
      change RationalComplexEqv
        (rationalComplexAdd (rationalComplexMul rationalComplexZero x)
          (rationalComplexMul negativeScalar y))
        (rationalComplexMul negativeScalar y)
      unfold rationalComplexAdd rationalComplexMul negativeScalar rationalComplexZero RationalComplexEqv
      constructor <;> ring_qeqv
  | n + 1, x, y => fun b => negativeRow_true n (x b) (y b)

/-- The ACTUAL tensor action of the negative central unit, on every fiber. -/
theorem negativeTensorParity : ∀ (n : Nat) (x : Tensor n),
    TensorEqv n (quaternionAction n RationalQuaternion.unitNegativeOne.val x)
      (tensorScale n (parityScalar n) x)
  | 0, x => tensorScale_one 0 x |>.symm
  | n + 1, x => by
      intro row
      have hm : TensorEqv n
          (matrixAction (n + 1) (fundamentalMatrixValue RationalQuaternion.unitNegativeOne.val) x row)
          (tensorScale n negativeScalar
            (matrixAction n (fundamentalMatrixValue RationalQuaternion.unitNegativeOne.val) (x row))) := by
        cases row
        · exact negativeRow_false n _ _
        · exact negativeRow_true n _ _
      exact hm.trans ((TensorEqv.scale (rationalComplexEqv_refl negativeScalar)
          (negativeTensorParity n (x row))).trans
        ((tensorScale_scale negativeScalar (parityScalar n) n (x row))
          |>.trans (TensorEqv.scale (parityScalar_succ n) (TensorEqv.refl n (x row)))))

private theorem coefficient_scale (a : RationalComplex) : ∀ (n : Nat)
    (x : Tensor n) (k : Nat),
    (coefficient n (tensorScale n a x) k) ≃c (a ⊠ coefficient n x k)
  | 0, _, _ => rationalComplexEqv_refl _
  | n + 1, x, 0 => coefficient_scale a n (x false) 0
  | n + 1, x, k + 1 => coefficient_scale a n (x true) k

/-- All n+1 concrete symmetric coefficients retain the central parity. -/
theorem symmetricAction_negative (n : Nat) (f : Nat → RationalComplex)
    (k : Nat) (hk : k ≤ n) :
    (symmetricAction n RationalQuaternion.unitNegativeOne.val f k) ≃c
      (parityScalar n ⊠ f k) :=
  rationalComplexEqv_trans
    (coefficient_congr (negativeTensorParity n (fromCoefficients n f)) k)
    (rationalComplexEqv_trans
      (coefficient_scale (parityScalar n) n (fromCoefficients n f) k)
      (rationalComplexMul_congr (rationalComplexEqv_refl _)
        (coefficient_fromCoefficients n f k hk)))

private theorem parityScalar_even {n : Nat} (hn : n % 2 = 0) :
    parityScalar n ≃c rationalComplexOne := by
  simp only [parityScalar, hn, ite_true, rationalComplexOne]
  exact rationalComplexEqv_refl _

/-- At even degree the negative unit is the identity on the full window. -/
theorem symmetricAction_negative_even {n : Nat} (hn : n % 2 = 0)
    (f : Nat → RationalComplex) (k : Nat) (hk : k ≤ n) :
    symmetricAction n RationalQuaternion.unitNegativeOne.val f k ≃c f k :=
  rationalComplexEqv_trans (symmetricAction_negative n f k hk)
    (rationalComplexEqv_trans
      (rationalComplexMul_congr (parityScalar_even hn) (rationalComplexEqv_refl _))
      (by unfold rationalComplexOne rationalComplexMul RationalComplexEqv
          constructor <;> ring_qeqv))

private theorem action_quaternion_congr (n : Nat) {p q : RationalQuaternion}
    (hpq : p.Equivalent q) (f : Nat → RationalComplex) (k : Nat) :
    symmetricAction n p f k ≃c symmetricAction n q f k :=
  coefficient_congr
    (matrixAction_congr (fundamentalMatrixValue_congr hpq)
      (TensorEqv.refl n (fromCoefficients n f))) k

private theorem action_input_congr (n : Nat) (q : RationalQuaternion)
    {f g : Nat → RationalComplex} (hfg : ∀ k, k ≤ n → f k ≃c g k) (k : Nat) :
    symmetricAction n q f k ≃c symmetricAction n q g k :=
  coefficient_congr
    (matrixAction_congr (fun _ _ => rationalComplexEqv_refl _)
      (fromCoefficients_congr n hfg)) k

/-- Concrete action on representatives of the actual located sign quotient. -/
def signQuotientAction (n : Nat)
    (q : RationalQuaternion.UnitNorm) (f : Nat → RationalComplex) : Nat → RationalComplex :=
  symmetricAction n q.val f

/-- At even degree this action is independent of the chosen sign-coset
representative. The output equality holds for all indices, even though the
identity law is only claimed on the coefficient window. -/
theorem signQuotientAction_congr {n : Nat} (hn : n % 2 = 0)
    {q r : RationalQuaternion.UnitNorm}
    (hqr : RationalQuaternion.UnitNorm.signLocatedQuotientGroup.Equivalent q r)
    (f : Nat → RationalComplex) (k : Nat) :
    signQuotientAction n q f k ≃c signQuotientAction n r f k := by
  cases (RationalQuaternion.UnitNorm.signCoset_iff q r).mp hqr with
  | inl h => exact action_quaternion_congr n h f k
  | inr h =>
      exact rationalComplexEqv_trans (action_quaternion_congr n h f k)
        (rationalComplexEqv_trans
          (symmetricAction_mul n r.val RationalQuaternion.unitNegativeOne.val f k)
          (action_input_congr n r.val
            (symmetricAction_negative_even hn f) k))

theorem signQuotientAction_one (n : Nat) (f : Nat → RationalComplex)
    (k : Nat) (hk : k ≤ n) :
    signQuotientAction n RationalQuaternion.unitOne f k ≃c f k :=
  symmetricAction_one n f k hk

theorem signQuotientAction_mul (n : Nat) (p q : RationalQuaternion.UnitNorm)
    (f : Nat → RationalComplex) (k : Nat) :
    signQuotientAction n (RationalQuaternion.UnitNorm.mul p q) f k ≃c
      signQuotientAction n p (signQuotientAction n q f) k :=
  symmetricAction_mul n p.val q.val f k

theorem signQuotientAction_unitary (n : Nat)
    (q : RationalQuaternion.UnitNorm) (f g : Nat → RationalComplex) :
    symmetricInner n (signQuotientAction n q f) (signQuotientAction n q g) ≃c
      symmetricInner n f g :=
  symmetricAction_unitary n q f g

/-- A single nonzero coefficient rules out odd-degree sign descent. -/
theorem symmetricAction_odd_rejected {n : Nat} (hn : n % 2 = 1) :
    ¬ (∀ (f : Nat → RationalComplex) (k : Nat), k ≤ n →
      symmetricAction n RationalQuaternion.unitNegativeOne.val f k ≃c f k) := by
  intro h
  let f : Nat → RationalComplex := fun _ => rationalComplexOne
  have hz := symmetricAction_negative n f 0 (Nat.zero_le n)
  have ho := h f 0 (Nat.zero_le n)
  have hp : parityScalar n ≃c negativeScalar := by
    have hn0 : n % 2 ≠ 0 := by omega
    simp only [parityScalar, negativeScalar, hn0, ite_false]
    exact rationalComplexEqv_refl _
  have he : negativeScalar ≃c rationalComplexOne :=
    (by
      have hm : (negativeScalar ⊠ rationalComplexOne) ≃c rationalComplexOne :=
        rationalComplexEqv_trans
          (rationalComplexMul_congr (rationalComplexEqv_symm hp)
            (rationalComplexEqv_refl _))
          (rationalComplexEqv_trans (rationalComplexEqv_symm hz) ho)
      have hleft : (negativeScalar ⊠ rationalComplexOne) ≃c negativeScalar := by
        unfold negativeScalar rationalComplexOne rationalComplexMul RationalComplexEqv
        constructor <;> ring_qeqv
      exact rationalComplexEqv_trans (rationalComplexEqv_symm hleft) hm)
  exact (by decide : ¬ Q'.eqv (-1 : Q') 1) he.1

/-- The code-level SO(3) parity rule is exactly the triviality criterion for
the ACTUAL degree-n rational action, not merely a label convention. -/
theorem so3DoubledSpin_descends_iff_action (n : Nat) :
    SO3DoubledSpinDescends n ↔
      ∀ (f : Nat → RationalComplex) (k : Nat), k ≤ n →
        symmetricAction n RationalQuaternion.unitNegativeOne.val f k ≃c f k := by
  constructor
  · intro h f k hk
    exact symmetricAction_negative_even
      ((so3DoubledSpin_descends_iff_even n).mp h) f k hk
  · intro h
    apply (so3DoubledSpin_descends_iff_even n).mpr
    change n % 2 = 0
    have hrange : n % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases heven : n % 2 = 0
    · exact heven
    · have hodd : n % 2 = 1 := by omega
      exact False.elim (symmetricAction_odd_rejected hodd h)

end YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent

#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.negativeTensorParity
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.symmetricAction_negative
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.symmetricAction_negative_even
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.signQuotientAction
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.signQuotientAction_congr
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.signQuotientAction_one
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.signQuotientAction_mul
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.signQuotientAction_unitary
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.symmetricAction_odd_rejected
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerSignDescent.so3DoubledSpin_descends_iff_action
