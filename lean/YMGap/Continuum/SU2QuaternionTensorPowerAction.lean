/-
# Actual quaternion matrix action on arbitrary finite tensor powers

The fundamental matrix is the existing complex matrix of the Hamilton
quaternion, not a dimension or multiplicity surrogate. This module lifts
that matrix to every finite tensor degree by structural recursion.

The full tensor power is reducible. Its symmetric sector and the identity
between its symmetric-sector trace and the literal characterPolynomial
remain separate from the tensor action itself. No character-kernel
positivity, slab OS positivity, transfer gap or continuum theorem follows
merely from this construction.
-/

import YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

namespace YMGap.Continuum.SU2QuaternionTensorPowerAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra

local infix:50 " ≈ " => Q'.eqv
local infix:50 " ≃c " => RationalComplexEqv
local infixl:65 " ⊞ " => rationalComplexAdd
local infixl:70 " ⊠ " => rationalComplexMul

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;> ac_rfl))

/-- Curried complex tensors; no list of all 2^n assignments is materialized. -/
def Tensor : Nat → Type
  | 0 => RationalComplex
  | n + 1 => Bool → Tensor n

/-- Componentwise rational-complex equality, with the degree retained. -/
def TensorEqv : (n : Nat) → Tensor n → Tensor n → Prop
  | 0, x, y => x ≃c y
  | n + 1, x, y => ∀ b, TensorEqv n (x b) (y b)

def tensorAdd : (n : Nat) → Tensor n → Tensor n → Tensor n
  | 0, x, y => x ⊞ y
  | n + 1, x, y => fun b => tensorAdd n (x b) (y b)

def tensorScale : (n : Nat) → RationalComplex → Tensor n → Tensor n
  | 0, a, x => a ⊠ x
  | n + 1, a, x => fun b => tensorScale n a (x b)

theorem TensorEqv.refl : ∀ (n : Nat) (x : Tensor n), TensorEqv n x x
  | 0, x => rationalComplexEqv_refl x
  | n + 1, x => fun b => TensorEqv.refl n (x b)

theorem TensorEqv.symm : ∀ {n : Nat} {x y : Tensor n}, TensorEqv n x y → TensorEqv n y x
  | 0, _, _, h => rationalComplexEqv_symm h
  | _ + 1, _, _, h => fun b => TensorEqv.symm (h b)

theorem TensorEqv.trans : ∀ {n : Nat} {x y z : Tensor n},
    TensorEqv n x y → TensorEqv n y z → TensorEqv n x z
  | 0, _, _, _, h, k => rationalComplexEqv_trans h k
  | _ + 1, _, _, _, h, k => fun b => TensorEqv.trans (h b) (k b)

theorem TensorEqv.add : ∀ {n : Nat} {x x' y y' : Tensor n},
    TensorEqv n x x' → TensorEqv n y y' → TensorEqv n (tensorAdd n x y) (tensorAdd n x' y')
  | 0, _, _, _, _, h, k => rationalComplexAdd_congr h k
  | _ + 1, _, _, _, _, h, k => fun b => TensorEqv.add (h b) (k b)

theorem TensorEqv.scale {a b : RationalComplex} (hab : a ≃c b) :
    ∀ {n : Nat} {x y : Tensor n}, TensorEqv n x y →
      TensorEqv n (tensorScale n a x) (tensorScale n b y)
  | 0, _, _, h => rationalComplexMul_congr hab h
  | _ + 1, _, _, h => fun bit => TensorEqv.scale hab (h bit)

private theorem scale_add (a : RationalComplex) : ∀ (n : Nat) (x y : Tensor n),
    TensorEqv n (tensorScale n a (tensorAdd n x y))
      (tensorAdd n (tensorScale n a x) (tensorScale n a y))
  | 0, x, y => rationalComplexMul_add a x y
  | n + 1, x, y => fun b => scale_add a n (x b) (y b)

private theorem add_scale (a b : RationalComplex) : ∀ (n : Nat) (x : Tensor n),
    TensorEqv n (tensorScale n (a ⊞ b) x)
      (tensorAdd n (tensorScale n a x) (tensorScale n b x))
  | 0, x => rationalComplexAdd_mul a b x
  | n + 1, x => fun bit => add_scale a b n (x bit)

private theorem scale_scale (a b : RationalComplex) : ∀ (n : Nat) (x : Tensor n),
    TensorEqv n (tensorScale n a (tensorScale n b x)) (tensorScale n (a ⊠ b) x)
  | 0, x => rationalComplexEqv_symm (rationalComplexMul_assoc a b x)
  | n + 1, x => fun bit => scale_scale a b n (x bit)

private theorem add_swap (n : Nat) (a b c d : Tensor n) :
    TensorEqv n (tensorAdd n (tensorAdd n a b) (tensorAdd n c d))
      (tensorAdd n (tensorAdd n a c) (tensorAdd n b d)) := by
  induction n with
  | zero => exact rationalComplexAdd_swap_inner a b c d
  | succ n ih => exact fun bit => ih (a bit) (b bit) (c bit) (d bit)

/-- The n-fold tensor action of the supplied actual 2x2 matrix. -/
def matrixAction : (n : Nat) → FundamentalMatrix → Tensor n → Tensor n
  | 0, _, x => x
  | n + 1, M, x => fun row =>
      tensorAdd n (tensorScale n (M row false) (matrixAction n M (x false)))
        (tensorScale n (M row true) (matrixAction n M (x true)))

theorem matrixAction_congr {M N : FundamentalMatrix} (hMN : FundamentalMatrixEqv M N) :
    ∀ {n : Nat} {x y : Tensor n}, TensorEqv n x y → TensorEqv n (matrixAction n M x) (matrixAction n N y)
  | 0, _, _, h => h
  | _ + 1, _, _, h => fun row =>
      (TensorEqv.scale (hMN row false) (matrixAction_congr hMN (h false))).add
        (TensorEqv.scale (hMN row true) (matrixAction_congr hMN (h true)))

theorem matrixAction_add (M : FundamentalMatrix) : ∀ (n : Nat) (x y : Tensor n),
    TensorEqv n (matrixAction n M (tensorAdd n x y))
      (tensorAdd n (matrixAction n M x) (matrixAction n M y))
  | 0, x, y => TensorEqv.refl 0 _
  | n + 1, x, y => by
    intro row
    exact ((TensorEqv.scale (rationalComplexEqv_refl _) (matrixAction_add M n (x false) (y false))).add
      (TensorEqv.scale (rationalComplexEqv_refl _) (matrixAction_add M n (x true) (y true)))).trans
      (((scale_add _ n _ _).add (scale_add _ n _ _)).trans (add_swap n _ _ _ _))

theorem matrixAction_scale (M : FundamentalMatrix) (a : RationalComplex) :
    ∀ (n : Nat) (x : Tensor n), TensorEqv n (matrixAction n M (tensorScale n a x))
      (tensorScale n a (matrixAction n M x))
  | 0, x => TensorEqv.refl 0 _
  | n + 1, x => by
    intro row
    have hs (b : Bool) : TensorEqv n
        (tensorScale n (M row b) (matrixAction n M (tensorScale n a (x b))))
        (tensorScale n a (tensorScale n (M row b) (matrixAction n M (x b)))) :=
      (TensorEqv.scale (rationalComplexEqv_refl _) (matrixAction_scale M a n (x b))).trans
        ((scale_scale _ _ n _).trans
          ((TensorEqv.scale (rationalComplexMul_comm _ _) (TensorEqv.refl n _)).trans
            (scale_scale _ _ n _).symm))
    exact ((hs false).add (hs true)).trans (scale_add a n _ _).symm

/-- Functoriality at EVERY degree; proof follows one Boolean fiber, not an
enumeration of matrix entries in dimension 2^n. -/
theorem matrixAction_mul (M N : FundamentalMatrix) : ∀ (n : Nat) (x : Tensor n),
    TensorEqv n (matrixAction n (fundamentalMatrixMul M N) x)
      (matrixAction n M (matrixAction n N x))
  | 0, x => TensorEqv.refl 0 x
  | n + 1, x => by
    intro row
    let y := fun b => matrixAction n M (matrixAction n N (x b))
    have hl (b : Bool) : TensorEqv n
        (tensorScale n (fundamentalMatrixMul M N row b)
          (matrixAction n (fundamentalMatrixMul M N) (x b)))
        (tensorAdd n (tensorScale n (M row false ⊠ N false b) (y b))
          (tensorScale n (M row true ⊠ N true b) (y b))) :=
      (TensorEqv.scale (rationalComplexEqv_refl _) (matrixAction_mul M N n (x b))).trans
        (add_scale _ _ n (y b))
    have hr (b : Bool) : TensorEqv n
        (tensorScale n (M row b) (matrixAction n M
          (tensorAdd n (tensorScale n (N b false) (matrixAction n N (x false)))
            (tensorScale n (N b true) (matrixAction n N (x true))))))
        (tensorAdd n (tensorScale n (M row b ⊠ N b false) (y false))
          (tensorScale n (M row b ⊠ N b true) (y true))) := by
      refine (TensorEqv.scale (rationalComplexEqv_refl _) (matrixAction_add M n _ _)).trans ?_
      refine (TensorEqv.scale (rationalComplexEqv_refl _)
        ((matrixAction_scale M _ n _).add (matrixAction_scale M _ n _))).trans ?_
      exact (scale_add _ n _ _).trans ((scale_scale _ _ n _).add (scale_scale _ _ n _))
    exact ((hl false).add (hl true)).trans ((add_swap n _ _ _ _).trans ((hr false).add (hr true)).symm)

/-- The actual Hamilton-quaternion action, at every tensor degree. -/
def quaternionAction (n : Nat) (q : RationalQuaternion) : Tensor n → Tensor n :=
  matrixAction n (fundamentalMatrixValue q)

theorem quaternionAction_mul (n : Nat) (p q : RationalQuaternion) (x : Tensor n) :
    TensorEqv n (quaternionAction n (RationalQuaternion.mul p q) x)
      (quaternionAction n p (quaternionAction n q x)) :=
  (matrixAction_congr (fundamentalMatrixValue_mul p q) (TensorEqv.refl n x)).trans
    (matrixAction_mul _ _ n x)

private theorem unit_mix : ∀ (n : Nat) (x y : Tensor n),
    TensorEqv n (tensorAdd n (tensorScale n rationalComplexOne x)
      (tensorScale n rationalComplexZero y)) x
  | 0, x, y => by
    change ((1, 0) ⊠ x) ⊞ ((0, 0) ⊠ y) ≃c x
    unfold rationalComplexAdd rationalComplexMul RationalComplexEqv
    constructor <;> ring_qeqv
  | n + 1, x, y => fun b => unit_mix n (x b) (y b)

private theorem zero_mix : ∀ (n : Nat) (x y : Tensor n),
    TensorEqv n (tensorAdd n (tensorScale n rationalComplexZero x)
      (tensorScale n rationalComplexOne y)) y
  | 0, x, y => by
    change ((0, 0) ⊠ x) ⊞ ((1, 0) ⊠ y) ≃c y
    unfold rationalComplexAdd rationalComplexMul RationalComplexEqv
    constructor <;> ring_qeqv
  | n + 1, x, y => fun b => zero_mix n (x b) (y b)

theorem quaternionAction_one : ∀ (n : Nat) (x : Tensor n),
    TensorEqv n (quaternionAction n RationalQuaternion.one x) x
  | 0, x => TensorEqv.refl 0 x
  | n + 1, x => by
    intro row
    cases row
    · exact (unit_mix n _ _).trans (quaternionAction_one n (x false))
    · exact (zero_mix n _ _).trans (quaternionAction_one n (x true))

/-- The inverse law is about the existing rational unit-quaternion group.
No compactness or completion of that group is asserted. -/
theorem quaternionAction_inverse (n : Nat) (q : RationalQuaternion.UnitNorm) (x : Tensor n) :
    TensorEqv n (quaternionAction n (RationalQuaternion.UnitNorm.inv q).val
      (quaternionAction n q.val x)) x :=
  (quaternionAction_mul n _ _ x).symm.trans
    ((matrixAction_congr (fundamentalMatrixValue_congr (RationalQuaternion.UnitNorm.inv_mul q))
      (TensorEqv.refl n x)).trans (quaternionAction_one n x))

/-- The standard Hermitian form, recursively summing every tensor coordinate. -/
def tensorInner : (n : Nat) → Tensor n → Tensor n → RationalComplex
  | 0, x, y => rationalComplexConj x ⊠ y
  | n + 1, x, y => tensorInner n (x false) (y false) ⊞ tensorInner n (x true) (y true)

private theorem conj_congr {x y : RationalComplex} (h : x ≃c y) :
    rationalComplexConj x ≃c rationalComplexConj y := ⟨h.1, Q'.neg_eqv_congr _ _ h.2⟩

theorem tensorInner_congr : ∀ {n : Nat} {x x' y y' : Tensor n},
    TensorEqv n x x' → TensorEqv n y y' → tensorInner n x y ≃c tensorInner n x' y'
  | 0, _, _, _, _, h, k => rationalComplexMul_congr (conj_congr h) k
  | _ + 1, _, _, _, _, h, k => rationalComplexAdd_congr
      (tensorInner_congr (h false) (k false)) (tensorInner_congr (h true) (k true))

private theorem inner_add_left : ∀ (n : Nat) (x y z : Tensor n),
    tensorInner n (tensorAdd n x y) z ≃c (tensorInner n x z ⊞ tensorInner n y z)
  | 0, x, y, z => by
    change (rationalComplexConj (x ⊞ y) ⊠ z) ≃c ((rationalComplexConj x ⊠ z) ⊞ (rationalComplexConj y ⊠ z))
    unfold rationalComplexConj rationalComplexAdd rationalComplexMul RationalComplexEqv
    constructor <;> ring_qeqv
  | n + 1, x, y, z => rationalComplexEqv_trans
      (rationalComplexAdd_congr (inner_add_left n (x false) (y false) (z false))
        (inner_add_left n (x true) (y true) (z true)))
      (rationalComplexAdd_swap_inner _ _ _ _)

private theorem inner_add_right : ∀ (n : Nat) (x y z : Tensor n),
    tensorInner n x (tensorAdd n y z) ≃c (tensorInner n x y ⊞ tensorInner n x z)
  | 0, _, _, _ => rationalComplexMul_add _ _ _
  | n + 1, x, y, z => rationalComplexEqv_trans
      (rationalComplexAdd_congr (inner_add_right n (x false) (y false) (z false))
        (inner_add_right n (x true) (y true) (z true)))
      (rationalComplexAdd_swap_inner _ _ _ _)

private theorem inner_scale_left (a : RationalComplex) : ∀ (n : Nat) (x y : Tensor n),
    tensorInner n (tensorScale n a x) y ≃c (rationalComplexConj a ⊠ tensorInner n x y)
  | 0, x, y => by
    change (rationalComplexConj (a ⊠ x) ⊠ y) ≃c (rationalComplexConj a ⊠ (rationalComplexConj x ⊠ y))
    unfold rationalComplexConj rationalComplexMul RationalComplexEqv
    constructor <;> ring_qeqv
  | n + 1, x, y => rationalComplexEqv_trans
      (rationalComplexAdd_congr (inner_scale_left a n (x false) (y false))
        (inner_scale_left a n (x true) (y true)))
      (rationalComplexEqv_symm (rationalComplexMul_add _ _ _))

private theorem inner_scale_right (a : RationalComplex) : ∀ (n : Nat) (x y : Tensor n),
    tensorInner n x (tensorScale n a y) ≃c (a ⊠ tensorInner n x y)
  | 0, x, y => by
    change (rationalComplexConj x ⊠ (a ⊠ y)) ≃c (a ⊠ (rationalComplexConj x ⊠ y))
    unfold rationalComplexConj rationalComplexMul RationalComplexEqv
    constructor <;> ring_qeqv
  | n + 1, x, y => rationalComplexEqv_trans
      (rationalComplexAdd_congr (inner_scale_right a n (x false) (y false))
        (inner_scale_right a n (x true) (y true)))
      (rationalComplexEqv_symm (rationalComplexMul_add _ _ _))

private theorem inner_mix_left (n : Nat) (a b : RationalComplex) (x y z : Tensor n) :
    tensorInner n (tensorAdd n (tensorScale n a x) (tensorScale n b y)) z ≃c
      ((rationalComplexConj a ⊠ tensorInner n x z) ⊞ (rationalComplexConj b ⊠ tensorInner n y z)) :=
  rationalComplexEqv_trans (inner_add_left n _ _ _)
    (rationalComplexAdd_congr (inner_scale_left a n x z) (inner_scale_left b n y z))

private theorem inner_mix_right (n : Nat) (a b : RationalComplex) (x y z : Tensor n) :
    tensorInner n x (tensorAdd n (tensorScale n a y) (tensorScale n b z)) ≃c
      ((a ⊠ tensorInner n x y) ⊞ (b ⊠ tensorInner n x z)) :=
  rationalComplexEqv_trans (inner_add_right n _ _ _)
    (rationalComplexAdd_congr (inner_scale_right a n x y) (inner_scale_right b n x z))

/-- The lifted adjoint is the actual conjugate transpose, at every degree. -/
theorem tensorInner_matrixAction (M : FundamentalMatrix) : ∀ (n : Nat) (x y : Tensor n),
    tensorInner n (matrixAction n M x) y ≃c
      tensorInner n x (matrixAction n (fundamentalMatrixAdjoint M) y)
  | 0, x, y => rationalComplexEqv_refl _
  | n + 1, x, y => by
    refine rationalComplexEqv_trans
      (rationalComplexAdd_congr (inner_mix_left n _ _ _ _ _) (inner_mix_left n _ _ _ _ _)) ?_
    refine rationalComplexEqv_trans
      (rationalComplexAdd_congr
        (rationalComplexAdd_congr
          (rationalComplexMul_congr (rationalComplexEqv_refl _) (tensorInner_matrixAction M n (x false) (y false)))
          (rationalComplexMul_congr (rationalComplexEqv_refl _) (tensorInner_matrixAction M n (x true) (y false))))
        (rationalComplexAdd_congr
          (rationalComplexMul_congr (rationalComplexEqv_refl _) (tensorInner_matrixAction M n (x false) (y true)))
          (rationalComplexMul_congr (rationalComplexEqv_refl _) (tensorInner_matrixAction M n (x true) (y true))))) ?_
    exact rationalComplexEqv_trans (rationalComplexAdd_swap_inner _ _ _ _)
      (rationalComplexEqv_symm (rationalComplexAdd_congr
        (inner_mix_right n _ _ _ _ _) (inner_mix_right n _ _ _ _ _)))

/-- Nonnegativity is the sum of the real and imaginary coordinate squares,
not a supplied positivity hypothesis. -/
theorem tensorInner_self_nonneg : ∀ (n : Nat) (x : Tensor n), (0 : Q') ≤ (tensorInner n x x).1
  | 0, x => by
    have h : (tensorInner 0 x x).1 ≈ x.1 * x.1 + x.2 * x.2 := by
      unfold tensorInner rationalComplexConj rationalComplexMul
      ring_qeqv
    exact Q'.le_trans' _ _ _
      (Q'.zero_le_add _ _ (SumOfSquares.q_mul_self_nonneg x.1) (SumOfSquares.q_mul_self_nonneg x.2))
      (Q'.le_of_eqv (Q'.eqv_symm h))
  | n + 1, x => Q'.zero_le_add _ _ (tensorInner_self_nonneg n (x false)) (tensorInner_self_nonneg n (x true))

theorem tensorInner_self_imag_zero : ∀ (n : Nat) (x : Tensor n), (tensorInner n x x).2 ≈ 0
  | 0, x => by
    have h : (tensorInner 0 x x).2 ≈ -(x.1 * x.2) + x.1 * x.2 := by
      unfold tensorInner rationalComplexConj rationalComplexMul
      ring_qeqv
    exact Q'.eqv_trans _ _ _ h (Q'.neg_add_self_eqv _)
  | n + 1, x => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (tensorInner_self_imag_zero n (x false)) (tensorInner_self_imag_zero n (x true)))
      (QPoly.q_zero_add_eqv 0)

/-- Exact Hermitian isometry for the existing rational unit-quaternion group,
on the full tensor carrier at every degree. -/
theorem quaternionAction_unitary (n : Nat) (q : RationalQuaternion.UnitNorm) (x y : Tensor n) :
    tensorInner n (quaternionAction n q.val x) (quaternionAction n q.val y) ≃c tensorInner n x y := by
  refine rationalComplexEqv_trans (tensorInner_matrixAction (fundamentalMatrixValue q.val) n x _) ?_
  apply tensorInner_congr (TensorEqv.refl n x)
  exact (matrixAction_congr
    (fun row column => rationalComplexEqv_symm (fundamentalMatrixValue_conj q.val row column))
    (TensorEqv.refl n _)).trans (quaternionAction_inverse n q y)

end YMGap.Continuum.SU2QuaternionTensorPowerAction

#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.Tensor
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.TensorEqv
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.tensorAdd
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.tensorScale
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.TensorEqv.refl
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.TensorEqv.symm
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.TensorEqv.trans
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.TensorEqv.add
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.TensorEqv.scale
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.matrixAction
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.matrixAction_congr
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.matrixAction_add
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.matrixAction_scale
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.matrixAction_mul
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.quaternionAction
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.quaternionAction_mul
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.quaternionAction_one
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.quaternionAction_inverse
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.tensorInner
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.tensorInner_congr
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.tensorInner_matrixAction
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.tensorInner_self_nonneg
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.tensorInner_self_imag_zero
#print axioms YMGap.Continuum.SU2QuaternionTensorPowerAction.quaternionAction_unitary
