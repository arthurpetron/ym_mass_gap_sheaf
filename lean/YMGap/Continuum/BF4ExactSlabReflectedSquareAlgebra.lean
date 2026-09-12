/-
# Explicit finite sums of reflected squares and their product closure

A finite tree stores every rational weight and real polynomial channel.
Multiplication constructs all cross-terms, preserving shared variables.
The evaluation is the original slab reflection, with common-padding
coefficient equality; no independence or Haar positivity is assumed.

The literal representation Gram kernel is identified with such a tree
at all degrees and extents. Half-carrier support and Haar factorization,
global slab positivity, transfer and continuum limits remain separate.
-/

import YMGap.Continuum.BF4ExactSlabSpatialChannelReflection

namespace YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.RingNormaliser

/-- Finite, computable channel data, not an existential positivity premise. -/
inductive SquareTree where
  | zero
  | term (weight : Q') (channel : RatPoly)
  | add (left right : SquareTree)

namespace SquareTree

def eval (extent : Nat) : SquareTree → RatPoly
  | .zero => polyZero
  | .term w p => polySmul w (polyMul (reflectCorrectedSlabPolynomial extent p) p)
  | .add p q => polyAdd (eval extent p) (eval extent q)

def Nonnegative : SquareTree → Prop
  | .zero => True
  | .term w _ => (0 : Q') ≤ w
  | .add p q => p.Nonnegative ∧ q.Nonnegative

def scale (s : Q') : SquareTree → SquareTree
  | .zero => .zero
  | .term w p => .term (s * w) p
  | .add p q => .add (scale s p) (scale s q)

def multiplyTerm (s : Q') (p : RatPoly) : SquareTree → SquareTree
  | .zero => .zero
  | .term w q => .term (s * w) (polyMul p q)
  | .add q r => .add (multiplyTerm s p q) (multiplyTerm s p r)

def product : SquareTree → SquareTree → SquareTree
  | .zero, _ => .zero
  | .term s p, q => multiplyTerm s p q
  | .add p q, r => .add (product p r) (product q r)

def sum {A : Type} (f : A → SquareTree) : List A → SquareTree
  | [] => .zero
  | a :: rest => .add (f a) (sum f rest)

def prefixSum (f : Nat → SquareTree) : Nat → SquareTree
  | 0 => .zero
  | n + 1 => .add (prefixSum f n) (f n)

theorem eval_scale (extent : Nat) (s : Q') : ∀ p : SquareTree,
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (polySmul s (p.eval extent)) ((p.scale s).eval extent)
  | .zero => .of_coeff (RatPolyCoeffEqv.smul_zero s)
  | .term w _ => .of_coeff (RatPolyCoeffEqv.smul_assoc s w _)
  | .add p q => (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.smul_add s _ _)).trans
      ((eval_scale extent s p).add (eval_scale extent s q))

private theorem term_product (extent : Nat) (s t : Q') (p q : RatPoly) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (polyMul ((.term s p : SquareTree).eval extent) ((.term t q : SquareTree).eval extent))
      ((.term (s * t) (polyMul p q) : SquareTree).eval extent) := by
  let rp := reflectCorrectedSlabPolynomial extent p
  let rq := reflectCorrectedSlabPolynomial extent q
  have h : RatPolyCoeffEqv
      (polyMul (polySmul s (polyMul rp p)) (polySmul t (polyMul rq q)))
      (polySmul (s * t) (polyMul (polyMul rp rq) (polyMul p q))) :=
    (RatPolyCoeffEqv.polyMul_smul_left s _ _).trans
      (((RatPolyCoeffEqv.polyMul_smul_right t _ _).smul s).trans
        ((RatPolyCoeffEqv.smul_assoc s t _).trans
          ((RatPolyCoeffEqv.mul_four_swap rp p rq q).smul (s * t))))
  exact (PaddedPolynomialCoeffEqv.of_coeff h).trans
    (((PaddedPolynomialCoeffEqv.of_prefix
      (reflectCorrectedSlabPolynomial_mul_prefix extent p q)).symm.mul
        (PaddedPolynomialCoeffEqv.refl _ (polyMul p q))).smul (s * t))

theorem eval_multiplyTerm (extent : Nat) (s : Q') (p : RatPoly) : ∀ q : SquareTree,
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (polyMul ((.term s p : SquareTree).eval extent) (q.eval extent))
      ((q.multiplyTerm s p).eval extent)
  | .zero => .of_coeff (RatPolyCoeffEqv.mul_zero_right _)
  | .term t q => term_product extent s t p q
  | .add q r => (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _)).trans
      ((eval_multiplyTerm extent s p q).add (eval_multiplyTerm extent s p r))

/-- Constructive distributivity into actual products of channels. No
disjointness is needed: all factors remain on the same polynomial carrier. -/
theorem eval_product (extent : Nat) : ∀ p q : SquareTree,
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (polyMul (p.eval extent) (q.eval extent)) ((p.product q).eval extent)
  | .zero, q => .of_coeff (RatPolyCoeffEqv.mul_zero_left _)
  | .term s p, q => eval_multiplyTerm extent s p q
  | .add p q, r => by
      change PaddedPolynomialCoeffEqv _ (polyMul (polyAdd _ _) _) _
      rw [polyMul_add_left_exact]
      exact (eval_product extent p r).add (eval_product extent q r)

theorem eval_sum {A : Type} (extent : Nat) (f : A → SquareTree) : ∀ xs : List A,
    finitePolySum (fun a => (f a).eval extent) xs = (sum f xs).eval extent
  | [] => rfl
  | _ :: xs => by simp only [finitePolySum, sum, eval, eval_sum extent f xs]

theorem scale_nonnegative (s : Q') (hs : (0 : Q') ≤ s) : ∀ p : SquareTree,
    p.Nonnegative → (p.scale s).Nonnegative
  | .zero, _ => True.intro
  | .term w _, h => Q'.mul_nonneg s w hs h
  | .add p q, h => ⟨scale_nonnegative s hs p h.1, scale_nonnegative s hs q h.2⟩

theorem multiplyTerm_nonnegative (s : Q') (p : RatPoly) (hs : (0 : Q') ≤ s) :
    ∀ q : SquareTree, q.Nonnegative → (q.multiplyTerm s p).Nonnegative
  | .zero, _ => True.intro
  | .term w _, h => Q'.mul_nonneg s w hs h
  | .add q r, h => ⟨multiplyTerm_nonnegative s p hs q h.1, multiplyTerm_nonnegative s p hs r h.2⟩

theorem product_nonnegative : ∀ p q : SquareTree,
    p.Nonnegative → q.Nonnegative → (p.product q).Nonnegative
  | .zero, _, _, _ => True.intro
  | .term s p, q, hp, hq => multiplyTerm_nonnegative s p hp q hq
  | .add p q, r, hp, hr => ⟨product_nonnegative p r hp.1 hr, product_nonnegative q r hp.2 hr⟩

theorem sum_nonnegative {A : Type} (f : A → SquareTree) : ∀ xs : List A,
    (∀ a, a ∈ xs → (f a).Nonnegative) → (sum f xs).Nonnegative
  | [], _ => True.intro
  | a :: xs, h => ⟨h a List.mem_cons_self,
      sum_nonnegative f xs (fun b hb => h b (List.mem_cons_of_mem a hb))⟩

theorem prefixSum_nonnegative (f : Nat → SquareTree) : ∀ n : Nat,
    (∀ k, k < n → (f k).Nonnegative) → (prefixSum f n).Nonnegative
  | 0, _ => True.intro
  | n + 1, h => ⟨prefixSum_nonnegative f n (fun k hk => h k (by omega)), h n (by omega)⟩

end SquareTree

/-- Both real components of each literal tensor channel are retained. -/
def tensorSquares : (n : Nat) → PolyTensor n → SquareTree
  | 0, x => .add (.term 1 x.1) (.term 1 x.2)
  | n + 1, x => .add (tensorSquares n (x false)) (tensorSquares n (x true))

theorem tensorSquares_nonnegative : ∀ (n : Nat) (x : PolyTensor n), (tensorSquares n x).Nonnegative
  | 0, _ => ⟨show (0 : Q') ≤ 1 by decide, show (0 : Q') ≤ 1 by decide⟩
  | n + 1, x => ⟨tensorSquares_nonnegative n (x false), tensorSquares_nonnegative n (x true)⟩

private theorem real_conj_mul (x y : ComplexRatPoly) :
    RatPolyCoeffEqv (complexRatPolyMul (complexRatPolyConj x) y).1
      (polyAdd (polyMul x.1 y.1) (polyMul x.2 y.2)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.neg (.var 1)) (.var 3))))
    (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
    (fun i => match i with | 0 => x.1 | 1 => x.2 | 2 => y.1 | 3 => y.2 | _ => polyZero)

theorem tensorInner_reflected_squares {extent : Nat} : ∀ {n : Nat} {lower upper : PolyTensor n},
    TensorReflectionImage extent n lower upper →
      PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
        (polyTensorInner n upper lower).1 ((tensorSquares n lower).eval extent)
  | 0, lower, upper, h => by
      have hr : PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
          (polyMul upper.1 lower.1)
          (polySmul 1 (polyMul (reflectCorrectedSlabPolynomial extent lower.1) lower.1)) :=
        ((PaddedPolynomialCoeffEqv.symm h.1).mul (.refl _ _)).trans
          (.of_coeff (RatPolyCoeffEqv.one_smul _).symm)
      have hi : PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
          (polyMul upper.2 lower.2)
          (polySmul 1 (polyMul (reflectCorrectedSlabPolynomial extent lower.2) lower.2)) :=
        ((PaddedPolynomialCoeffEqv.symm h.2).mul (.refl _ _)).trans
          (.of_coeff (RatPolyCoeffEqv.one_smul _).symm)
      exact (PaddedPolynomialCoeffEqv.of_coeff (real_conj_mul upper lower)).trans (hr.add hi)
  | _ + 1, _, _, h => (tensorInner_reflected_squares (h false)).add (tensorInner_reflected_squares (h true))

def gramSquares (lower : RationalQuaternionRatPoly.RatPolyQuaternion) (n : Nat) : SquareTree :=
  SquareTree.prefixSum (fun k => (tensorSquares n (polynomialColumn lower n k)).scale (basisInverseWeight n k)) (n + 1)

theorem gramSquares_nonnegative (lower : RationalQuaternionRatPoly.RatPolyQuaternion) (n : Nat) :
    (gramSquares lower n).Nonnegative :=
  SquareTree.prefixSum_nonnegative _ _ (fun k _ =>
    SquareTree.scale_nonnegative _ (Q'.le_of_lt (basisInverseWeight_pos n k)) _
      (tensorSquares_nonnegative n _))

private theorem prefix_image {extent : Nat} (f : Nat → ComplexRatPoly) (g : Nat → SquareTree) :
    ∀ m : Nat,
      (∀ k, k < m → PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length (f k).1 ((g k).eval extent)) →
      PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
        (polynomialSum m f).1 ((SquareTree.prefixSum g m).eval extent)
  | 0, _ => .refl _ _
  | m + 1, h => (prefix_image f g m (fun k hk => h k (by omega))).add (h m (by omega))

theorem gram_reflected_squares {extent : Nat}
    (lower upper : RationalQuaternionRatPoly.RatPolyQuaternion) (n : Nat)
    (h : ∀ k, TensorReflectionImage extent n (polynomialColumn lower n k) (polynomialColumn upper n k)) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (polynomialGramKernel upper lower n).1 ((gramSquares lower n).eval extent) :=
  prefix_image _ _ (n + 1) (fun k _ =>
    ((tensorInner_reflected_squares (h k)).smul (basisInverseWeight n k)).trans
      (SquareTree.eval_scale extent (basisInverseWeight n k) _))

/-- The actual reflected spatial Gram, uniformly over degree and extent,
has explicit positive rational channel weights. This is not yet positivity
of its integral against arbitrary observables. -/
theorem spatial_gram_reflected_squares {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hs : link.2 ≠ .x3) (n : Nat) :
    PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
      (reflectedSpatialLinkGram extent link n).1
      ((gramSquares (asRepresentationQuaternion (correctedSlabLinkPolynomial extent link)) n).eval extent) :=
  gram_reflected_squares _ _ n (spatial_column_image hl hs n)

end YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.eval
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.Nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.scale
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.multiplyTerm
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.product
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.sum
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.prefixSum
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.eval_scale
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.eval_multiplyTerm
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.eval_product
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.eval_sum
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.scale_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.multiplyTerm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.product_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.sum_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.SquareTree.prefixSum_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.tensorSquares
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.tensorSquares_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.tensorInner_reflected_squares
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.gramSquares
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.gramSquares_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.gram_reflected_squares
#print axioms YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra.spatial_gram_reflected_squares
