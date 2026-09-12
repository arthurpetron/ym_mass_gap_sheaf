/-
# Coefficient-retaining tensor action and its actual Hermitian adjoint

The Boolean tensor recursion is lifted to the original complex rational
polynomials. Functoriality and the adjoint identity hold against every
coefficient probe, before evaluation or Haar integration. These identities
are inputs to a character-kernel Gram decomposition, not an assumed
positivity theorem and not a physical transfer or continuum construction.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerCoefficientTrace

namespace YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈c " => ComplexCoeffEqv
local infixl:65 " ⊞ " => complexRatPolyAdd
local infixl:70 " ⊠ " => complexRatPolyMul
local notation "star" => complexRatPolyConj

theorem conj_congr {x y : ComplexRatPoly} (h : x ≈c y) : star x ≈c star y :=
  ⟨h.1, RatPolyCoeffEqv.neg h.2⟩

private abbrev CExpr := PolyExpr × PolyExpr
private def v (i : Nat) : CExpr := (.var (2 * i), .var (2 * i + 1))
private def plus (x y : CExpr) : CExpr := (.add x.1 y.1, .add x.2 y.2)
private def times (x y : CExpr) : CExpr :=
  (.add (.mul x.1 y.1) (.neg (.mul x.2 y.2)), .add (.mul x.1 y.2) (.mul x.2 y.1))
private def bar (x : CExpr) : CExpr := (x.1, .neg x.2)
private def env (a b : ComplexRatPoly) : Nat → RatPoly
  | 0 => a.1 | 1 => a.2 | 2 => b.1 | 3 => b.2 | _ => polyZero
private theorem cert (l r : CExpr)
    (hr : normalize l.1 = normalize r.1) (hi : normalize l.2 = normalize r.2)
    (environment : Nat → RatPoly) :
    (coeffEvalExpr environment l.1, coeffEvalExpr environment l.2) ≈c
      (coeffEvalExpr environment r.1, coeffEvalExpr environment r.2) :=
  ⟨coeffEvalExpr_eqv_of_normalize_eq _ _ hr environment,
    coeffEvalExpr_eqv_of_normalize_eq _ _ hi environment⟩

theorem conj_add (a b : ComplexRatPoly) : star (a ⊞ b) ≈c (star a ⊞ star b) :=
  cert (bar (plus (v 0) (v 1))) (plus (bar (v 0)) (bar (v 1)))
    (by decide) (by decide) (env a b)

theorem conj_mul (a b : ComplexRatPoly) : star (a ⊠ b) ≈c (star a ⊠ star b) :=
  cert (bar (times (v 0) (v 1))) (times (bar (v 0)) (bar (v 1)))
    (by decide) (by decide) (env a b)

/-- Curried polynomial tensors retain raw real and imaginary coefficients. -/
def PolyTensor : Nat → Type
  | 0 => ComplexRatPoly
  | n + 1 => Bool → PolyTensor n

def PolyTensorEqv : (n : Nat) → PolyTensor n → PolyTensor n → Prop
  | 0, x, y => x ≈c y
  | n + 1, x, y => ∀ b, PolyTensorEqv n (x b) (y b)

def polyTensorAdd : (n : Nat) → PolyTensor n → PolyTensor n → PolyTensor n
  | 0, x, y => x ⊞ y
  | n + 1, x, y => fun b => polyTensorAdd n (x b) (y b)

def polyTensorScale : (n : Nat) → ComplexRatPoly → PolyTensor n → PolyTensor n
  | 0, a, x => a ⊠ x
  | n + 1, a, x => fun b => polyTensorScale n a (x b)

theorem PolyTensorEqv.refl : ∀ (n : Nat) (x : PolyTensor n), PolyTensorEqv n x x
  | 0, x => ComplexCoeffEqv.refl x
  | n + 1, x => fun b => PolyTensorEqv.refl n (x b)

theorem PolyTensorEqv.symm : ∀ {n : Nat} {x y : PolyTensor n}, PolyTensorEqv n x y → PolyTensorEqv n y x
  | 0, _, _, h => ComplexCoeffEqv.symm h
  | _ + 1, _, _, h => fun b => (h b).symm

theorem PolyTensorEqv.trans : ∀ {n : Nat} {x y z : PolyTensor n},
    PolyTensorEqv n x y → PolyTensorEqv n y z → PolyTensorEqv n x z
  | 0, _, _, _, h, k => ComplexCoeffEqv.trans h k
  | _ + 1, _, _, _, h, k => fun b => (h b).trans (k b)

theorem PolyTensorEqv.add : ∀ {n : Nat} {x x' y y' : PolyTensor n},
    PolyTensorEqv n x x' → PolyTensorEqv n y y' →
      PolyTensorEqv n (polyTensorAdd n x y) (polyTensorAdd n x' y')
  | 0, _, _, _, _, h, k => ComplexCoeffEqv.add h k
  | _ + 1, _, _, _, _, h, k => fun b => (h b).add (k b)

theorem PolyTensorEqv.scale {a b : ComplexRatPoly} (hab : a ≈c b) :
    ∀ {n : Nat} {x y : PolyTensor n}, PolyTensorEqv n x y →
      PolyTensorEqv n (polyTensorScale n a x) (polyTensorScale n b y)
  | 0, _, _, h => hab.mul h
  | _ + 1, _, _, h => fun bit => PolyTensorEqv.scale hab (h bit)

theorem scale_add (a : ComplexRatPoly) : ∀ (n : Nat) (x y : PolyTensor n),
    PolyTensorEqv n (polyTensorScale n a (polyTensorAdd n x y))
      (polyTensorAdd n (polyTensorScale n a x) (polyTensorScale n a y))
  | 0, x, y => mul_add a x y
  | n + 1, x, y => fun b => scale_add a n (x b) (y b)

private theorem add_scale (a b : ComplexRatPoly) : ∀ (n : Nat) (x : PolyTensor n),
    PolyTensorEqv n (polyTensorScale n (a ⊞ b) x)
      (polyTensorAdd n (polyTensorScale n a x) (polyTensorScale n b x))
  | 0, x => add_mul a b x
  | n + 1, x => fun bit => add_scale a b n (x bit)

private theorem scale_scale (a b : ComplexRatPoly) : ∀ (n : Nat) (x : PolyTensor n),
    PolyTensorEqv n (polyTensorScale n a (polyTensorScale n b x)) (polyTensorScale n (a ⊠ b) x)
  | 0, x => (mul_assoc a b x).symm
  | n + 1, x => fun bit => scale_scale a b n (x bit)

private theorem tensor_add_swap : ∀ (n : Nat) (a b c d : PolyTensor n),
    PolyTensorEqv n (polyTensorAdd n (polyTensorAdd n a b) (polyTensorAdd n c d))
      (polyTensorAdd n (polyTensorAdd n a c) (polyTensorAdd n b d))
  | 0, a, b, c, d => add_swap a b c d
  | n + 1, a, b, c, d => fun bit => tensor_add_swap n (a bit) (b bit) (c bit) (d bit)

abbrev PolynomialMatrix := Bool → Bool → ComplexRatPoly

def polynomialMatrixMul (M N : PolynomialMatrix) : PolynomialMatrix :=
  fun i j => (M i false ⊠ N false j) ⊞ (M i true ⊠ N true j)

def polynomialMatrixAdjoint (M : PolynomialMatrix) : PolynomialMatrix := fun i j => star (M j i)

def polyMatrixAction : (n : Nat) → PolynomialMatrix → PolyTensor n → PolyTensor n
  | 0, _, x => x
  | n + 1, M, x => fun row =>
      polyTensorAdd n (polyTensorScale n (M row false) (polyMatrixAction n M (x false)))
        (polyTensorScale n (M row true) (polyMatrixAction n M (x true)))

theorem polyMatrixAction_congr {M N : PolynomialMatrix} (hMN : ∀ i j, M i j ≈c N i j) :
    ∀ {n : Nat} {x y : PolyTensor n}, PolyTensorEqv n x y →
      PolyTensorEqv n (polyMatrixAction n M x) (polyMatrixAction n N y)
  | 0, _, _, h => h
  | _ + 1, _, _, h => fun row =>
      (PolyTensorEqv.scale (hMN row false) (polyMatrixAction_congr hMN (h false))).add
        (PolyTensorEqv.scale (hMN row true) (polyMatrixAction_congr hMN (h true)))

theorem polyMatrixAction_add (M : PolynomialMatrix) : ∀ (n : Nat) (x y : PolyTensor n),
    PolyTensorEqv n (polyMatrixAction n M (polyTensorAdd n x y))
      (polyTensorAdd n (polyMatrixAction n M x) (polyMatrixAction n M y))
  | 0, x, y => PolyTensorEqv.refl 0 (x ⊞ y)
  | n + 1, x, y => fun row =>
      ((PolyTensorEqv.scale (ComplexCoeffEqv.refl (M row false)) (polyMatrixAction_add M n (x false) (y false))).add
        (PolyTensorEqv.scale (ComplexCoeffEqv.refl (M row true)) (polyMatrixAction_add M n (x true) (y true)))).trans
      (((scale_add _ n _ _).add (scale_add _ n _ _)).trans (tensor_add_swap n _ _ _ _))

theorem polyMatrixAction_scale (M : PolynomialMatrix) (a : ComplexRatPoly) : ∀ (n : Nat) (x : PolyTensor n),
    PolyTensorEqv n (polyMatrixAction n M (polyTensorScale n a x))
      (polyTensorScale n a (polyMatrixAction n M x))
  | 0, x => PolyTensorEqv.refl 0 _
  | n + 1, x => by
    intro row
    have hs (b : Bool) : PolyTensorEqv n
        (polyTensorScale n (M row b) (polyMatrixAction n M (polyTensorScale n a (x b))))
        (polyTensorScale n a (polyTensorScale n (M row b) (polyMatrixAction n M (x b)))) :=
      (PolyTensorEqv.scale (ComplexCoeffEqv.refl _) (polyMatrixAction_scale M a n (x b))).trans
        ((scale_scale _ _ n _).trans
          ((PolyTensorEqv.scale (mul_comm _ _) (PolyTensorEqv.refl n _)).trans (scale_scale _ _ n _).symm))
    exact ((hs false).add (hs true)).trans (scale_add a n _ _).symm

/-- Functoriality of the original polynomial action with all probes retained. -/
theorem polyMatrixAction_mul (M N : PolynomialMatrix) : ∀ (n : Nat) (x : PolyTensor n),
    PolyTensorEqv n (polyMatrixAction n (polynomialMatrixMul M N) x)
      (polyMatrixAction n M (polyMatrixAction n N x))
  | 0, x => PolyTensorEqv.refl 0 x
  | n + 1, x => by
    intro row
    let y := fun b => polyMatrixAction n M (polyMatrixAction n N (x b))
    have hl (b : Bool) : PolyTensorEqv n
        (polyTensorScale n (polynomialMatrixMul M N row b)
          (polyMatrixAction n (polynomialMatrixMul M N) (x b)))
        (polyTensorAdd n (polyTensorScale n (M row false ⊠ N false b) (y b))
          (polyTensorScale n (M row true ⊠ N true b) (y b))) :=
      (PolyTensorEqv.scale (ComplexCoeffEqv.refl _) (polyMatrixAction_mul M N n (x b))).trans
        (add_scale _ _ n (y b))
    have hr (b : Bool) : PolyTensorEqv n
        (polyTensorScale n (M row b) (polyMatrixAction n M
          (polyTensorAdd n (polyTensorScale n (N b false) (polyMatrixAction n N (x false)))
            (polyTensorScale n (N b true) (polyMatrixAction n N (x true))))))
        (polyTensorAdd n (polyTensorScale n (M row b ⊠ N b false) (y false))
          (polyTensorScale n (M row b ⊠ N b true) (y true))) := by
      refine (PolyTensorEqv.scale (ComplexCoeffEqv.refl _) (polyMatrixAction_add M n _ _)).trans ?_
      refine (PolyTensorEqv.scale (ComplexCoeffEqv.refl _)
        ((polyMatrixAction_scale M _ n _).add (polyMatrixAction_scale M _ n _))).trans ?_
      exact (scale_add _ n _ _).trans ((scale_scale _ _ n _).add (scale_scale _ _ n _))
    exact ((hl false).add (hl true)).trans
      ((tensor_add_swap n _ _ _ _).trans ((hr false).add (hr true)).symm)

/-- Literal finite Hermitian pairing of polynomial tensors. -/
def polyTensorInner : (n : Nat) → PolyTensor n → PolyTensor n → ComplexRatPoly
  | 0, x, y => star x ⊠ y
  | n + 1, x, y => polyTensorInner n (x false) (y false) ⊞ polyTensorInner n (x true) (y true)

theorem polyTensorInner_congr : ∀ {n : Nat} {x x' y y' : PolyTensor n},
    PolyTensorEqv n x x' → PolyTensorEqv n y y' → polyTensorInner n x y ≈c polyTensorInner n x' y'
  | 0, _, _, _, _, h, k => (conj_congr h).mul k
  | _ + 1, _, _, _, _, h, k =>
      (polyTensorInner_congr (h false) (k false)).add (polyTensorInner_congr (h true) (k true))

theorem inner_add_left : ∀ (n : Nat) (x y z : PolyTensor n),
    polyTensorInner n (polyTensorAdd n x y) z ≈c (polyTensorInner n x z ⊞ polyTensorInner n y z)
  | 0, x, y, z => ((conj_add x y).mul (ComplexCoeffEqv.refl z)).trans (add_mul _ _ _)
  | n + 1, x, y, z => ((inner_add_left n (x false) (y false) (z false)).add
      (inner_add_left n (x true) (y true) (z true))).trans (add_swap _ _ _ _)

theorem inner_add_right : ∀ (n : Nat) (x y z : PolyTensor n),
    polyTensorInner n x (polyTensorAdd n y z) ≈c (polyTensorInner n x y ⊞ polyTensorInner n x z)
  | 0, _, _, _ => mul_add _ _ _
  | n + 1, x, y, z => ((inner_add_right n (x false) (y false) (z false)).add
      (inner_add_right n (x true) (y true) (z true))).trans (add_swap _ _ _ _)

theorem inner_scale_left (a : ComplexRatPoly) : ∀ (n : Nat) (x y : PolyTensor n),
    polyTensorInner n (polyTensorScale n a x) y ≈c (star a ⊠ polyTensorInner n x y)
  | 0, x, y => ((conj_mul a x).mul (ComplexCoeffEqv.refl y)).trans (mul_assoc _ _ _)
  | n + 1, x, y => ((inner_scale_left a n (x false) (y false)).add
      (inner_scale_left a n (x true) (y true))).trans (mul_add _ _ _).symm

theorem inner_scale_right (a : ComplexRatPoly) : ∀ (n : Nat) (x y : PolyTensor n),
    polyTensorInner n x (polyTensorScale n a y) ≈c (a ⊠ polyTensorInner n x y)
  | 0, x, y => (mul_assoc (star x) a y).symm.trans
      (((mul_comm _ _).mul (ComplexCoeffEqv.refl y)).trans (mul_assoc _ _ _))
  | n + 1, x, y => ((inner_scale_right a n (x false) (y false)).add
      (inner_scale_right a n (x true) (y true))).trans (mul_add _ _ _).symm

private theorem inner_mix_left (n : Nat) (a b : ComplexRatPoly) (x y z : PolyTensor n) :
    polyTensorInner n (polyTensorAdd n (polyTensorScale n a x) (polyTensorScale n b y)) z ≈c
      ((star a ⊠ polyTensorInner n x z) ⊞ (star b ⊠ polyTensorInner n y z)) :=
  (inner_add_left n _ _ _).trans ((inner_scale_left a n x z).add (inner_scale_left b n y z))

private theorem inner_mix_right (n : Nat) (a b : ComplexRatPoly) (x y z : PolyTensor n) :
    polyTensorInner n x (polyTensorAdd n (polyTensorScale n a y) (polyTensorScale n b z)) ≈c
      ((a ⊠ polyTensorInner n x y) ⊞ (b ⊠ polyTensorInner n x z)) :=
  (inner_add_right n _ _ _).trans ((inner_scale_right a n x y).add (inner_scale_right b n x z))

/-- Conjugate transpose is the actual adjoint at coefficient-probe strength. -/
theorem polyTensorInner_matrixAction (M : PolynomialMatrix) : ∀ (n : Nat) (x y : PolyTensor n),
    polyTensorInner n (polyMatrixAction n M x) y ≈c
      polyTensorInner n x (polyMatrixAction n (polynomialMatrixAdjoint M) y)
  | 0, x, y => ComplexCoeffEqv.refl _
  | n + 1, x, y => by
    refine ((inner_mix_left n _ _ _ _ _).add (inner_mix_left n _ _ _ _ _)).trans ?_
    refine ((((ComplexCoeffEqv.refl _).mul (polyTensorInner_matrixAction M n (x false) (y false))).add
      ((ComplexCoeffEqv.refl _).mul (polyTensorInner_matrixAction M n (x true) (y false)))).add
      (((ComplexCoeffEqv.refl _).mul (polyTensorInner_matrixAction M n (x false) (y true))).add
      ((ComplexCoeffEqv.refl _).mul (polyTensorInner_matrixAction M n (x true) (y true))))).trans ?_
    exact (add_swap _ _ _ _).trans
      ((inner_mix_right n _ _ _ _ _).add (inner_mix_right n _ _ _ _ _)).symm

end YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian

#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.conj_congr
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.conj_add
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.conj_mul
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.PolyTensor
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.PolyTensorEqv
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyTensorAdd
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyTensorScale
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.PolyTensorEqv.refl
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.PolyTensorEqv.symm
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.PolyTensorEqv.trans
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.PolyTensorEqv.add
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.PolyTensorEqv.scale
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.scale_add
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polynomialMatrixMul
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polynomialMatrixAdjoint
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyMatrixAction
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyMatrixAction_congr
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyMatrixAction_add
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyMatrixAction_scale
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyMatrixAction_mul
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyTensorInner
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyTensorInner_congr
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.inner_add_left
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.inner_add_right
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.inner_scale_left
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.inner_scale_right
#print axioms YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian.polyTensorInner_matrixAction
