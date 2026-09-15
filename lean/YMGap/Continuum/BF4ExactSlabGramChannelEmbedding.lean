/-
# Every original representation channel follows the actual Haar block map

The image relation retains coefficients and finite coordinate prefixes.
The original complex matrix/tensor recursion commutes with the supplied
concrete block embedding, including its constant basis tensors. Applying
the existing same-branch transport therefore proves the polynomial image
of every selected Gram leaf, not merely preservation of its weight.

This is an algebraic naturality theorem. It does not identify interacting
amplitudes with different actions or prove a volume-uniform norm floor.
-/

import YMGap.Continuum.BF4ExactSlabGramChannelTransport
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingAlgebra

namespace YMGap.Continuum.BF4ExactSlabGramChannelEmbedding

set_option autoImplicit false

open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabGramChannelTransport
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram

variable {source target : Nat} (E : BlockEmbedding source target)

/-- Literal coefficient-sensitive image, allowing only coordinate padding. -/
def PolynomialImage (p q : RatPoly) : Prop :=
  QuaternionPrefixPolynomialEqv target (E.polynomial p) q

theorem image_zero : PolynomialImage E polyZero polyZero := .nil

theorem image_one : PolynomialImage E polyOne polyOne := E.polynomial_one_prefix

theorem image_add {p p' q q' : RatPoly} (hp : PolynomialImage E p p') (hq : PolynomialImage E q q') :
    PolynomialImage E (polyAdd p q) (polyAdd p' q') := by
  unfold PolynomialImage
  rw [E.polynomial_add]
  exact hp.append hq

theorem image_neg {p q : RatPoly} (h : PolynomialImage E p q) :
    PolynomialImage E (polyNeg p) (polyNeg q) := by
  unfold PolynomialImage
  rw [E.polynomial_neg]
  exact h.neg

theorem image_mul {p p' q q' : RatPoly} (hp : PolynomialImage E p p') (hq : PolynomialImage E q q') :
    PolynomialImage E (polyMul p q) (polyMul p' q') := by
  unfold PolynomialImage
  rw [E.polynomial_mul]
  exact hp.mul hq

def ComplexImage (x y : ComplexRatPoly) : Prop := PolynomialImage E x.1 y.1 ∧ PolynomialImage E x.2 y.2

private theorem complex_add {x x' y y' : ComplexRatPoly} (hx : ComplexImage E x x') (hy : ComplexImage E y y') :
    ComplexImage E (complexRatPolyAdd x y) (complexRatPolyAdd x' y') :=
  ⟨image_add E hx.1 hy.1, image_add E hx.2 hy.2⟩

private theorem complex_mul {x x' y y' : ComplexRatPoly} (hx : ComplexImage E x x') (hy : ComplexImage E y y') :
    ComplexImage E (complexRatPolyMul x y) (complexRatPolyMul x' y') :=
  ⟨image_add E (image_mul E hx.1 hy.1) (image_neg E (image_mul E hx.2 hy.2)),
    image_add E (image_mul E hx.1 hy.2) (image_mul E hx.2 hy.1)⟩

private theorem tensor_add : ∀ {n : Nat} {x x' y y' : PolyTensor n},
    TensorRelates (PolynomialImage E) n x x' → TensorRelates (PolynomialImage E) n y y' →
    TensorRelates (PolynomialImage E) n (polyTensorAdd n x y) (polyTensorAdd n x' y')
  | 0, _, _, _, _, hx, hy => complex_add E hx hy
  | _+1, _, _, _, _, hx, hy => fun b => tensor_add (hx b) (hy b)

private theorem tensor_scale {a b : ComplexRatPoly} (hab : ComplexImage E a b) :
    ∀ {n : Nat} {x y : PolyTensor n}, TensorRelates (PolynomialImage E) n x y →
      TensorRelates (PolynomialImage E) n (polyTensorScale n a x) (polyTensorScale n b y)
  | 0, _, _, h => complex_mul E hab h
  | _+1, _, _, h => fun bit => tensor_scale hab (h bit)

theorem matrixAction_image {M N : PolynomialMatrix} (hMN : ∀ i j, ComplexImage E (M i j) (N i j)) :
    ∀ {n : Nat} {x y : PolyTensor n}, TensorRelates (PolynomialImage E) n x y →
      TensorRelates (PolynomialImage E) n (polyMatrixAction n M x) (polyMatrixAction n N y)
  | 0, _, _, h => h
  | _+1, _, _, h => fun row => tensor_add E
      (tensor_scale E (hMN row false) (matrixAction_image hMN (h false)))
      (tensor_scale E (hMN row true) (matrixAction_image hMN (h true)))

private theorem embed_image : ∀ (n : Nat) (f g : Nat → ComplexRatPoly),
    (∀ k, ComplexImage E (f k) (g k)) →
    TensorRelates (PolynomialImage E) n (polyEmbed n f) (polyEmbed n g)
  | 0, _, _, h => h 0
  | n+1, f, g, h => by
      intro b
      cases b
      · exact embed_image n f g h
      · exact embed_image n (fun k => f (k+1)) (fun k => g (k+1)) (fun k => h (k+1))

private theorem basis_image (k j : Nat) : ComplexImage E (polynomialBasis k j) (polynomialBasis k j) := by
  unfold polynomialBasis
  split
  · exact ⟨image_one E, image_zero E⟩
  · exact ⟨image_zero E, image_zero E⟩

theorem fundamental_image {q r : PolyQuaternion}
    (h : QuaternionPrefixPolyQuaternionEqv target (E.quaternion q) r) :
    ∀ i j, ComplexImage E (fundamentalMatrixCoefficient (asRepresentationQuaternion q) i j)
      (fundamentalMatrixCoefficient (asRepresentationQuaternion r) i j)
  | false, false => ⟨h.scalar, h.iPart⟩
  | false, true => ⟨h.jPart, h.kPart⟩
  | true, false => ⟨image_neg E h.jPart, h.kPart⟩
  | true, true => ⟨h.scalar, image_neg E h.iPart⟩

/-- Every original matrix column and tensor row follows the same block map. -/
theorem polynomialColumn_image {q r : PolyQuaternion}
    (h : QuaternionPrefixPolyQuaternionEqv target (E.quaternion q) r) (spin k : Nat) :
    TensorRelates (PolynomialImage E) spin
      (polynomialColumn (asRepresentationQuaternion q) spin k)
      (polynomialColumn (asRepresentationQuaternion r) spin k) :=
  matrixAction_image E (fundamental_image E h) (embed_image E spin _ _ (basis_image E k))

/-- The transported leaf polynomial is the image of the SOURCE leaf polynomial. -/
theorem channel_image {q r : PolyQuaternion}
    (h : QuaternionPrefixPolyQuaternionEqv target (E.quaternion q) r)
    (c : GramChannel (asRepresentationQuaternion q)) :
    PolynomialImage E c.leaf.channel
      (transport (asRepresentationQuaternion q) (asRepresentationQuaternion r) c).leaf.channel :=
  transport_channel (PolynomialImage E) _ _ c (polynomialColumn_image E h c.spin)

end YMGap.Continuum.BF4ExactSlabGramChannelEmbedding

#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.PolynomialImage
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.image_zero
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.image_one
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.image_add
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.image_neg
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.image_mul
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.ComplexImage
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.matrixAction_image
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.fundamental_image
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.polynomialColumn_image
#print axioms YMGap.Continuum.BF4ExactSlabGramChannelEmbedding.channel_image
