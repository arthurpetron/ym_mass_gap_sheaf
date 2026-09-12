/-
# Constructive symmetric powers of the actual quaternion action

Symmetry is imposed by adjacent coordinate exchanges and inherited by every
Boolean fiber. Symmetric tensors are reconstructed from n+1 complex
coefficients, by a proved inverse to their explicit coefficient embedding.
The actual quaternion tensor action preserves this sector and its positive
Hermitian form. No binomial square roots or choice of a basis is assumed.

These are rational unit-quaternion representations. The all-spin trace
identity with characterPolynomial, its coefficient-retaining polynomial
version, and the positive reflected-channel resolution on the original slab
are NOT asserted here. No gap or continuum theorem is claimed.
-/

import YMGap.Continuum.SU2QuaternionTensorPowerAction

namespace YMGap.Continuum.SU2QuaternionSymmetricPowerAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionTensorPowerAction

local infix:50 " ≃c " => RationalComplexEqv
local infixl:65 " ⊞ " => rationalComplexAdd
local infixl:70 " ⊠ " => rationalComplexMul

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg]; ac_rfl))

/-- Adjacent-exchange symmetry. In degrees zero and one there is no pair
to exchange; at higher degrees the two fibers and their first mixed entries
must agree. This is a concrete subspace predicate, not a frontier premise. -/
def Symmetric : (n : Nat) → Tensor n → Prop
  | 0, _ => True
  | 1, _ => True
  | n + 2, x => Symmetric (n + 1) (x false) ∧ Symmetric (n + 1) (x true) ∧
      TensorEqv n (x false true) (x true false)

private theorem symmetric_tail : ∀ {n : Nat} {x : Tensor (n + 1)}, Symmetric (n + 1) x →
    ∀ b, Symmetric n (x b)
  | 0, _, _ => fun _ => True.intro
  | _ + 1, _, h => fun b => by cases b; exact h.1; exact h.2.1

private theorem symmetric_add : ∀ {n : Nat} {x y : Tensor n}, Symmetric n x → Symmetric n y →
    Symmetric n (tensorAdd n x y)
  | 0, _, _, _, _ => True.intro
  | 1, _, _, _, _ => True.intro
  | _ + 2, _, _, h, k => ⟨symmetric_add h.1 k.1, symmetric_add h.2.1 k.2.1, h.2.2.add k.2.2⟩

private theorem symmetric_scale (a : RationalComplex) : ∀ {n : Nat} {x : Tensor n}, Symmetric n x →
    Symmetric n (tensorScale n a x)
  | 0, _, _ => True.intro
  | 1, _, _ => True.intro
  | _ + 2, _, h => ⟨symmetric_scale a h.1, symmetric_scale a h.2.1,
      TensorEqv.scale (rationalComplexEqv_refl a) h.2.2⟩

private theorem mixed_value (a b c d x y z t : RationalComplex) (hyz : y ≃c z) :
    ((a ⊠ ((c ⊠ x) ⊞ (d ⊠ y))) ⊞ (b ⊠ ((c ⊠ z) ⊞ (d ⊠ t)))) ≃c
      ((c ⊠ ((a ⊠ x) ⊞ (b ⊠ y))) ⊞ (d ⊠ ((a ⊠ z) ⊞ (b ⊠ t)))) := by
  have hl := rationalComplexAdd_congr (rationalComplexEqv_refl (a ⊠ ((c ⊠ x) ⊞ (d ⊠ y))))
    (rationalComplexMul_congr (rationalComplexEqv_refl b)
      (rationalComplexAdd_congr (rationalComplexMul_congr (rationalComplexEqv_refl c)
        (rationalComplexEqv_symm hyz)) (rationalComplexEqv_refl (d ⊠ t))))
  have hr := rationalComplexAdd_congr (rationalComplexEqv_refl (c ⊠ ((a ⊠ x) ⊞ (b ⊠ y))))
    (rationalComplexMul_congr (rationalComplexEqv_refl d)
      (rationalComplexAdd_congr (rationalComplexMul_congr (rationalComplexEqv_refl a)
        (rationalComplexEqv_symm hyz)) (rationalComplexEqv_refl (b ⊠ t))))
  refine rationalComplexEqv_trans hl (rationalComplexEqv_trans ?_ (rationalComplexEqv_symm hr))
  unfold rationalComplexAdd rationalComplexMul RationalComplexEqv
  constructor <;> ring_qeqv

private theorem mixed_tensor (a b c d : RationalComplex) : ∀ (n : Nat) (x y z t : Tensor n),
    TensorEqv n y z →
    TensorEqv n
      (tensorAdd n (tensorScale n a (tensorAdd n (tensorScale n c x) (tensorScale n d y)))
        (tensorScale n b (tensorAdd n (tensorScale n c z) (tensorScale n d t))))
      (tensorAdd n (tensorScale n c (tensorAdd n (tensorScale n a x) (tensorScale n b y)))
        (tensorScale n d (tensorAdd n (tensorScale n a z) (tensorScale n b t))))
  | 0, x, y, z, t, h => mixed_value a b c d x y z t h
  | n + 1, x, y, z, t, h => fun bit => mixed_tensor a b c d n (x bit) (y bit) (z bit) (t bit) (h bit)

/-- The actual matrix tensor action preserves the concrete symmetric sector
at EVERY degree, without an irreducibility or character hypothesis. -/
theorem matrixAction_symmetric (M : FundamentalMatrix) : ∀ {n : Nat} {x : Tensor n},
    Symmetric n x → Symmetric n (matrixAction n M x)
  | 0, _, _ => True.intro
  | 1, _, _ => True.intro
  | n + 2, x, h => by
    refine ⟨symmetric_add (symmetric_scale _ (matrixAction_symmetric M h.1))
      (symmetric_scale _ (matrixAction_symmetric M h.2.1)),
      symmetric_add (symmetric_scale _ (matrixAction_symmetric M h.1))
      (symmetric_scale _ (matrixAction_symmetric M h.2.1)), ?_⟩
    exact mixed_tensor (M false false) (M false true) (M true false) (M true true) n _ _ _ _
      (matrixAction_congr (fun _ _ => rationalComplexEqv_refl _) h.2.2)

/-- Embed the n+1 coefficient values as a tensor depending only on the
number of true entries. Values above n are never read. -/
def fromCoefficients : (n : Nat) → (Nat → RationalComplex) → Tensor n
  | 0, f => f 0
  | n + 1, f => fun b => fromCoefficients n (fun k => if b then f (k + 1) else f k)

theorem fromCoefficients_congr : ∀ (n : Nat) {f g : Nat → RationalComplex},
    (∀ k, k ≤ n → f k ≃c g k) → TensorEqv n (fromCoefficients n f) (fromCoefficients n g)
  | 0, _, _, h => h 0 (by omega)
  | n + 1, f, g, h => by
    intro b
    cases b
    · exact fromCoefficients_congr n (fun k hk => h k (by omega))
    · exact fromCoefficients_congr n (fun k hk => h (k + 1) (by omega))

theorem fromCoefficients_symmetric : ∀ (n : Nat) (f : Nat → RationalComplex),
    Symmetric n (fromCoefficients n f)
  | 0, _ => True.intro
  | 1, _ => True.intro
  | n + 2, f => ⟨fromCoefficients_symmetric (n + 1) f,
      fromCoefficients_symmetric (n + 1) (fun k => f (k + 1)), TensorEqv.refl n _⟩

/-- Read the canonical coordinate with k initial true entries. Only k≤n
is a coefficient of the degree-n representation; the definition is total. -/
def coefficient : (n : Nat) → Tensor n → Nat → RationalComplex
  | 0, x, _ => x
  | n + 1, x, 0 => coefficient n (x false) 0
  | n + 1, x, k + 1 => coefficient n (x true) k

theorem coefficient_congr : ∀ {n : Nat} {x y : Tensor n}, TensorEqv n x y →
    ∀ k, coefficient n x k ≃c coefficient n y k
  | 0, _, _, h, _ => h
  | _ + 1, _, _, h, 0 => coefficient_congr (h false) 0
  | _ + 1, _, _, h, k + 1 => coefficient_congr (h true) k

/-- The explicit embedding has the advertised n+1 coordinates. -/
theorem coefficient_fromCoefficients : ∀ (n : Nat) (f : Nat → RationalComplex) (k : Nat), k ≤ n →
    coefficient n (fromCoefficients n f) k ≃c f k
  | 0, f, k, hk => by
    have : k = 0 := by omega
    subst k
    exact rationalComplexEqv_refl _
  | n + 1, f, 0, _ => coefficient_fromCoefficients n f 0 (by omega)
  | n + 1, f, k + 1, hk => coefficient_fromCoefficients n (fun j => f (j + 1)) k (by omega)

private theorem coefficient_false {n : Nat} {x : Tensor (n + 1)} (h : Symmetric (n + 1) x) :
    ∀ k, k ≤ n → coefficient (n + 1) x k ≃c coefficient n (x false) k := by
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    exact rationalComplexEqv_refl _
  | succ n ih =>
    intro k hk
    cases k with
    | zero => exact rationalComplexEqv_refl _
    | succ k =>
      exact rationalComplexEqv_trans (ih h.2.1 k (by omega))
        (coefficient_congr h.2.2.symm k)

/-- Every symmetric tensor is reconstructed from its n+1 explicit
coordinates. This is a constructive inverse, not an existential basis. -/
theorem fromCoefficients_coefficient : ∀ {n : Nat} {x : Tensor n}, Symmetric n x →
    TensorEqv n (fromCoefficients n (coefficient n x)) x
  | 0, _, _ => TensorEqv.refl 0 _
  | n + 1, x, h => by
    intro b
    cases b
    · exact (fromCoefficients_congr n (fun k hk => coefficient_false h k hk)).trans
        (fromCoefficients_coefficient (symmetric_tail h false))
    · exact fromCoefficients_coefficient (symmetric_tail h true)

/-- The symmetric-power action on its explicit coefficient window 0..n. -/
def symmetricAction (n : Nat) (q : RationalQuaternion) (f : Nat → RationalComplex) : Nat → RationalComplex :=
  coefficient n (quaternionAction n q (fromCoefficients n f))

private theorem fromCoefficients_add : ∀ (n : Nat) (f g : Nat → RationalComplex),
    TensorEqv n (fromCoefficients n (fun k => f k ⊞ g k))
      (tensorAdd n (fromCoefficients n f) (fromCoefficients n g))
  | 0, _, _ => TensorEqv.refl 0 _
  | n + 1, f, g => by
    intro b
    cases b
    · exact fromCoefficients_add n f g
    · exact fromCoefficients_add n (fun k => f (k + 1)) (fun k => g (k + 1))

private theorem fromCoefficients_scale (a : RationalComplex) : ∀ (n : Nat) (f : Nat → RationalComplex),
    TensorEqv n (fromCoefficients n (fun k => a ⊠ f k)) (tensorScale n a (fromCoefficients n f))
  | 0, _ => TensorEqv.refl 0 _
  | n + 1, f => by
    intro b
    cases b
    · exact fromCoefficients_scale a n f
    · exact fromCoefficients_scale a n (fun k => f (k + 1))

private theorem coefficient_add : ∀ (n : Nat) (x y : Tensor n) (k : Nat),
    coefficient n (tensorAdd n x y) k ≃c (coefficient n x k ⊞ coefficient n y k)
  | 0, _, _, _ => rationalComplexEqv_refl _
  | n + 1, x, y, 0 => coefficient_add n (x false) (y false) 0
  | n + 1, x, y, k + 1 => coefficient_add n (x true) (y true) k

private theorem coefficient_scale (a : RationalComplex) : ∀ (n : Nat) (x : Tensor n) (k : Nat),
    coefficient n (tensorScale n a x) k ≃c (a ⊠ coefficient n x k)
  | 0, _, _ => rationalComplexEqv_refl _
  | n + 1, x, 0 => coefficient_scale a n (x false) 0
  | n + 1, x, k + 1 => coefficient_scale a n (x true) k

theorem symmetricAction_add (n : Nat) (q : RationalQuaternion) (f g : Nat → RationalComplex) (k : Nat) :
    symmetricAction n q (fun j => f j ⊞ g j) k ≃c (symmetricAction n q f k ⊞ symmetricAction n q g k) :=
  rationalComplexEqv_trans (coefficient_congr
    ((matrixAction_congr (fun _ _ => rationalComplexEqv_refl _) (fromCoefficients_add n f g)).trans
      (matrixAction_add _ n _ _)) k) (coefficient_add n _ _ k)

theorem symmetricAction_scale (n : Nat) (q : RationalQuaternion) (a : RationalComplex)
    (f : Nat → RationalComplex) (k : Nat) :
    symmetricAction n q (fun j => a ⊠ f j) k ≃c (a ⊠ symmetricAction n q f k) :=
  rationalComplexEqv_trans (coefficient_congr
    ((matrixAction_congr (fun _ _ => rationalComplexEqv_refl _) (fromCoefficients_scale a n f)).trans
      (matrixAction_scale _ a n _)) k) (coefficient_scale a n _ k)

/-- The coefficient action is literally the restriction of the actual
quaternion tensor action, with a proved reconstruction pin. -/
theorem fromCoefficients_symmetricAction (n : Nat) (q : RationalQuaternion) (f : Nat → RationalComplex) :
    TensorEqv n (fromCoefficients n (symmetricAction n q f))
      (quaternionAction n q (fromCoefficients n f)) :=
  fromCoefficients_coefficient (matrixAction_symmetric _ (fromCoefficients_symmetric n f))

/-- The actual Hamilton multiplication law survives on all n+1 coefficients. -/
theorem symmetricAction_mul (n : Nat) (p q : RationalQuaternion) (f : Nat → RationalComplex) (k : Nat) :
    symmetricAction n (RationalQuaternion.mul p q) f k ≃c
      symmetricAction n p (symmetricAction n q f) k :=
  coefficient_congr ((quaternionAction_mul n p q _).trans
    (matrixAction_congr (fun _ _ => rationalComplexEqv_refl _)
      (fromCoefficients_symmetricAction n q f).symm)) k

theorem symmetricAction_one (n : Nat) (f : Nat → RationalComplex) (k : Nat) (hk : k ≤ n) :
    symmetricAction n RationalQuaternion.one f k ≃c f k :=
  rationalComplexEqv_trans (coefficient_congr (quaternionAction_one n _) k)
    (coefficient_fromCoefficients n f k hk)

/-- The positive Hermitian form inherited by the explicit coefficient
carrier. Its recursion encodes the binomial multiplicities without roots. -/
def symmetricInner (n : Nat) (f g : Nat → RationalComplex) : RationalComplex :=
  tensorInner n (fromCoefficients n f) (fromCoefficients n g)

theorem symmetricInner_self_nonneg (n : Nat) (f : Nat → RationalComplex) :
    (0 : Q') ≤ (symmetricInner n f f).1 := tensorInner_self_nonneg n _

/-- Positive Hermitian isometry of the concrete n+1-coefficient action for
every rational unit quaternion and every degree. -/
theorem symmetricAction_unitary (n : Nat) (q : RationalQuaternion.UnitNorm) (f g : Nat → RationalComplex) :
    symmetricInner n (symmetricAction n q.val f) (symmetricAction n q.val g) ≃c symmetricInner n f g :=
  rationalComplexEqv_trans (tensorInner_congr (fromCoefficients_symmetricAction n q.val f)
    (fromCoefficients_symmetricAction n q.val g)) (quaternionAction_unitary n q _ _)

end YMGap.Continuum.SU2QuaternionSymmetricPowerAction

#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.Symmetric
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.matrixAction_symmetric
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.fromCoefficients
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.fromCoefficients_congr
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.fromCoefficients_symmetric
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.coefficient
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.coefficient_congr
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.coefficient_fromCoefficients
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.fromCoefficients_coefficient
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.symmetricAction
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.symmetricAction_add
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.symmetricAction_scale
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.fromCoefficients_symmetricAction
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.symmetricAction_mul
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.symmetricAction_one
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.symmetricInner
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.symmetricInner_self_nonneg
#print axioms YMGap.Continuum.SU2QuaternionSymmetricPowerAction.symmetricAction_unitary
