/-
# Reflection of the actual spatial representation columns

The original slab pullback acts on both real polynomial components of each
complex channel. The representation action, tensor embedding and basis
are the existing ones. Structural recursion proves their reflection pin
at every degree and extent, retaining common carrier padding.

This supplies the literal channel input to reflected-square gluing.
It asserts neither Haar factorization nor slab positivity or a gap.
-/

import YMGap.Continuum.BF4ExactSlabSpatialLinkReflection

namespace YMGap.Continuum.BF4ExactSlabSpatialChannelReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationWordComposition
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram

def ReflectionImage (extent : Nat) (lower upper : RatPoly) : Prop :=
  PaddedPolynomialCoeffEqv (boundaryCompleteSlabLinks extent).length
    (reflectCorrectedSlabPolynomial extent lower) upper

namespace ReflectionImage

theorem zero (extent : Nat) : ReflectionImage extent polyZero polyZero := .refl _ _

theorem one (extent : Nat) : ReflectionImage extent polyOne polyOne :=
  .of_prefix (reflectCorrectedSlabPolynomial_character_prefix extent polyZero 0)

theorem add {extent : Nat} {p p' q q' : RatPoly}
    (hp : ReflectionImage extent p p') (hq : ReflectionImage extent q q') :
    ReflectionImage extent (polyAdd p q) (polyAdd p' q') := by
  unfold ReflectionImage
  rw [reflectCorrectedSlabPolynomial_add]
  exact PaddedPolynomialCoeffEqv.add hp hq

theorem mul {extent : Nat} {p p' q q' : RatPoly}
    (hp : ReflectionImage extent p p') (hq : ReflectionImage extent q q') :
    ReflectionImage extent (polyMul p q) (polyMul p' q') :=
  (PaddedPolynomialCoeffEqv.of_prefix
    (reflectCorrectedSlabPolynomial_mul_prefix extent p q)).trans (PaddedPolynomialCoeffEqv.mul hp hq)

theorem smul {extent : Nat} {p q : RatPoly} (h : ReflectionImage extent p q) (s : Q') :
    ReflectionImage extent (polySmul s p) (polySmul s q) :=
  (PaddedPolynomialCoeffEqv.of_prefix
    (reflectCorrectedSlabPolynomial_smul_prefix extent s p)).trans (PaddedPolynomialCoeffEqv.smul h s)

theorem neg {extent : Nat} {p q : RatPoly} (h : ReflectionImage extent p q) :
    ReflectionImage extent (polyNeg p) (polyNeg q) := by
  unfold ReflectionImage PaddedPolynomialCoeffEqv
  rw [reflectCorrectedSlabPolynomial_neg, reindexQuaternionPolynomial_neg,
    reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

end ReflectionImage

def ComplexReflectionImage (extent : Nat) (lower upper : ComplexRatPoly) : Prop :=
  ReflectionImage extent lower.1 upper.1 ∧ ReflectionImage extent lower.2 upper.2

namespace ComplexReflectionImage

theorem zero (extent : Nat) : ComplexReflectionImage extent complexRatPolyZero complexRatPolyZero :=
  ⟨ReflectionImage.zero extent, ReflectionImage.zero extent⟩

theorem one (extent : Nat) : ComplexReflectionImage extent complexRatPolyOne complexRatPolyOne :=
  ⟨ReflectionImage.one extent, ReflectionImage.zero extent⟩

theorem add {extent : Nat} {p p' q q' : ComplexRatPoly}
    (hp : ComplexReflectionImage extent p p') (hq : ComplexReflectionImage extent q q') :
    ComplexReflectionImage extent (complexRatPolyAdd p q) (complexRatPolyAdd p' q') :=
  ⟨hp.1.add hq.1, hp.2.add hq.2⟩

theorem mul {extent : Nat} {p p' q q' : ComplexRatPoly}
    (hp : ComplexReflectionImage extent p p') (hq : ComplexReflectionImage extent q q') :
    ComplexReflectionImage extent (complexRatPolyMul p q) (complexRatPolyMul p' q') :=
  ⟨(hp.1.mul hq.1).add (hp.2.mul hq.2).neg,
    (hp.1.mul hq.2).add (hp.2.mul hq.1)⟩

theorem conj {extent : Nat} {p q : ComplexRatPoly} (h : ComplexReflectionImage extent p q) :
    ComplexReflectionImage extent (complexRatPolyConj p) (complexRatPolyConj q) := ⟨h.1, h.2.neg⟩

end ComplexReflectionImage

theorem fundamental_image {extent : Nat} {p q : PolyQuaternion}
    (h : PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (reflectSlabQuaternion extent p) q) (row column : Bool) :
    ComplexReflectionImage extent
      (fundamentalMatrixCoefficient (asRepresentationQuaternion p) row column)
      (fundamentalMatrixCoefficient (asRepresentationQuaternion q) row column) := by
  have hs : ReflectionImage extent p.scalar q.scalar := h.scalar
  have hi : ReflectionImage extent p.iPart q.iPart := h.iPart
  have hj : ReflectionImage extent p.jPart q.jPart := h.jPart
  have hk : ReflectionImage extent p.kPart q.kPart := h.kPart
  cases row <;> cases column
  · exact ⟨hs, hi⟩
  · exact ⟨hj, hk⟩
  · exact ⟨hj.neg, hk⟩
  · exact ⟨hs, hi.neg⟩

def TensorReflectionImage (extent : Nat) : (n : Nat) → PolyTensor n → PolyTensor n → Prop
  | 0, p, q => ComplexReflectionImage extent p q
  | n + 1, p, q => ∀ b, TensorReflectionImage extent n (p b) (q b)

namespace TensorReflectionImage

theorem add {extent : Nat} : ∀ {n : Nat} {p p' q q' : PolyTensor n},
    TensorReflectionImage extent n p p' → TensorReflectionImage extent n q q' →
      TensorReflectionImage extent n (polyTensorAdd n p q) (polyTensorAdd n p' q')
  | 0, _, _, _, _, hp, hq => ComplexReflectionImage.add hp hq
  | _ + 1, _, _, _, _, hp, hq => fun b => add (hp b) (hq b)

theorem scale {extent : Nat} {a b : ComplexRatPoly} (hab : ComplexReflectionImage extent a b) :
    ∀ {n : Nat} {p q : PolyTensor n}, TensorReflectionImage extent n p q →
      TensorReflectionImage extent n (polyTensorScale n a p) (polyTensorScale n b q)
  | 0, _, _, hp => hab.mul hp
  | _ + 1, _, _, hp => fun c => scale hab (hp c)

end TensorReflectionImage

theorem matrixAction_image {extent : Nat} {M N : Bool → Bool → ComplexRatPoly}
    (hMN : ∀ i j, ComplexReflectionImage extent (M i j) (N i j)) :
    ∀ {n : Nat} {p q : PolyTensor n}, TensorReflectionImage extent n p q →
      TensorReflectionImage extent n (polyMatrixAction n M p) (polyMatrixAction n N q)
  | 0, _, _, h => h
  | _ + 1, _, _, h => fun row =>
      (TensorReflectionImage.scale (hMN row false) (matrixAction_image hMN (h false))).add
        (TensorReflectionImage.scale (hMN row true) (matrixAction_image hMN (h true)))

theorem embed_image {extent : Nat} : ∀ (n : Nat) {f g : Nat → ComplexRatPoly},
    (∀ k, ComplexReflectionImage extent (f k) (g k)) →
      TensorReflectionImage extent n (polyEmbed n f) (polyEmbed n g)
  | 0, _, _, h => h 0
  | n + 1, _, _, h => by
      intro b
      cases b
      · exact embed_image n h
      · exact embed_image n (fun k => h (k + 1))

theorem basis_image (extent k j : Nat) :
    ComplexReflectionImage extent (polynomialBasis k j) (polynomialBasis k j) := by
  unfold polynomialBasis
  by_cases h : j = k
  · rw [if_pos h]; exact ComplexReflectionImage.one extent
  · rw [if_neg h]; exact ComplexReflectionImage.zero extent

theorem column_image {extent : Nat} {p q : PolyQuaternion}
    (h : PaddedQuaternionCoeffEqv (boundaryCompleteSlabLinks extent).length
      (reflectSlabQuaternion extent p) q) (n k : Nat) :
    TensorReflectionImage extent n
      (polynomialColumn (asRepresentationQuaternion p) n k)
      (polynomialColumn (asRepresentationQuaternion q) n k) :=
  matrixAction_image (fundamental_image h) (embed_image n (basis_image extent k))

/-- All actual spatial-link columns, not an abstract replacement matrix. -/
theorem spatial_column_image {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hs : link.2 ≠ .x3) (n k : Nat) :
    TensorReflectionImage extent n
      (polynomialColumn (asRepresentationQuaternion (correctedSlabLinkPolynomial extent link)) n k)
      (polynomialColumn (asRepresentationQuaternion
        (correctedSlabLinkPolynomial extent (timeReflectLink extent link))) n k) :=
  column_image (spatial_link_reflection hl hs) n k

end YMGap.Continuum.BF4ExactSlabSpatialChannelReflection

#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ReflectionImage
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ReflectionImage.zero
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ReflectionImage.one
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ReflectionImage.add
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ReflectionImage.mul
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ReflectionImage.smul
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ReflectionImage.neg
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ComplexReflectionImage
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ComplexReflectionImage.zero
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ComplexReflectionImage.one
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ComplexReflectionImage.add
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ComplexReflectionImage.mul
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.ComplexReflectionImage.conj
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.fundamental_image
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.TensorReflectionImage
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.TensorReflectionImage.add
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.TensorReflectionImage.scale
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.matrixAction_image
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.embed_image
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.basis_image
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.column_image
#print axioms YMGap.Continuum.BF4ExactSlabSpatialChannelReflection.spatial_column_image
