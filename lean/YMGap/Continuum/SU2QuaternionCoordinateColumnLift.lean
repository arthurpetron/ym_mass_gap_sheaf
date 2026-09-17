/-
# The actual coordinate representation columns on two ordered Haar halves

Every component of the original degree-n polynomial column at slot i is
supported in its declared lower carrier. Adjoining N fresh head blocks
maps that column to the actual column at N+i, with common 2N padding.
Both real and imaginary components and every tensor index are retained.

These are algebraic inputs to the positive Gram expansion of the actual
selected-pair kinetic kernel. No positivity of a kernel, transfer bound,
OS-carrier identification, or continuum construction is assumed or proved.
-/

import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.SU2QuaternionPolynomialGramPositivity
import YMGap.Continuum.BF4ExactSlabPlaquettePathGram

namespace YMGap.Continuum.SU2QuaternionCoordinateColumnLift

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
open YMGap.Continuum.SU2QuaternionPolynomialTensorHermitian
open YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomialBasis
open YMGap.Continuum.SU2QuaternionSymmetricPowerKernelGram
open YMGap.Continuum.SU2QuaternionPolynomialGramPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_add)

private abbrev CSupported (blocks : Nat) (p : ComplexRatPoly) :=
  PolyTensorSupported blocks 0 p

private theorem support_zero (blocks : Nat) : SupportedQuaternionBlocks blocks polyZero :=
  fun _ h => False.elim (List.not_mem_nil h)

private theorem support_one (blocks : Nat) : SupportedQuaternionBlocks blocks polyOne := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  exact Nat.zero_le _

private theorem support_var {blocks coordinate : Nat} (h : coordinate < 4 * blocks) :
    SupportedQuaternionBlocks blocks (polyVar coordinate) := by
  intro t ht
  have he := List.mem_singleton.mp ht
  subst t
  simp only [varMono, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  omega

private theorem support_neg {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) : SupportedQuaternionBlocks blocks (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem complex_zero_support (blocks : Nat) : CSupported blocks complexRatPolyZero :=
  ⟨support_zero blocks, support_zero blocks⟩

private theorem complex_one_support (blocks : Nat) : CSupported blocks complexRatPolyOne :=
  ⟨support_one blocks, support_zero blocks⟩

private theorem complex_add_support {blocks : Nat} {p q : ComplexRatPoly}
    (hp : CSupported blocks p) (hq : CSupported blocks q) :
    CSupported blocks (complexRatPolyAdd p q) :=
  ⟨supported_add hp.1 hq.1, supported_add hp.2 hq.2⟩

private theorem complex_mul_support {blocks : Nat} {p q : ComplexRatPoly}
    (hp : CSupported blocks p) (hq : CSupported blocks q) :
    CSupported blocks (complexRatPolyMul p q) :=
  ⟨supported_add (supported_polyMul hp.1 hq.1) (support_neg (supported_polyMul hp.2 hq.2)),
    supported_add (supported_polyMul hp.1 hq.2) (supported_polyMul hp.2 hq.1)⟩

private theorem tensor_add_support {blocks : Nat} : ∀ {degree : Nat} {p q : PolyTensor degree},
    PolyTensorSupported blocks degree p → PolyTensorSupported blocks degree q →
      PolyTensorSupported blocks degree (polyTensorAdd degree p q)
  | 0, _, _, hp, hq => complex_add_support hp hq
  | _ + 1, _, _, hp, hq => fun b => tensor_add_support (hp b) (hq b)

private theorem tensor_scale_support {blocks : Nat} {a : ComplexRatPoly}
    (ha : CSupported blocks a) : ∀ {degree : Nat} {p : PolyTensor degree},
    PolyTensorSupported blocks degree p →
      PolyTensorSupported blocks degree (polyTensorScale degree a p)
  | 0, _, hp => complex_mul_support ha hp
  | _ + 1, _, hp => fun b => tensor_scale_support ha (hp b)

private theorem matrix_support {blocks : Nat} {M : Bool → Bool → ComplexRatPoly}
    (hM : ∀ i j, CSupported blocks (M i j)) :
    ∀ {degree : Nat} {p : PolyTensor degree}, PolyTensorSupported blocks degree p →
      PolyTensorSupported blocks degree (polyMatrixAction degree M p)
  | 0, _, hp => hp
  | _ + 1, _, hp => fun b =>
      tensor_add_support (tensor_scale_support (hM b false) (matrix_support hM (hp false)))
        (tensor_scale_support (hM b true) (matrix_support hM (hp true)))

private theorem embed_support {blocks : Nat} : ∀ degree {f : Nat → ComplexRatPoly},
    (∀ k, CSupported blocks (f k)) → PolyTensorSupported blocks degree (polyEmbed degree f)
  | 0, _, h => h 0
  | degree + 1, _, h => by
      intro b
      cases b
      · exact embed_support degree h
      · exact embed_support degree (fun k => h (k + 1))

private theorem basis_support (blocks k j : Nat) : CSupported blocks (polynomialBasis k j) := by
  unfold polynomialBasis
  split
  · exact complex_one_support blocks
  · exact complex_zero_support blocks

private theorem fundamental_supported {blocks slot : Nat} (hslot : slot < blocks)
    (row column : Bool) : CSupported blocks
      (fundamentalMatrixCoefficient (asRepresentationQuaternion
        (PolyQuaternion.coordinateVariable slot)) row column) := by
  cases row <;> cases column
  · exact ⟨support_var (by omega), support_var (by omega)⟩
  · exact ⟨support_var (by omega), support_var (by omega)⟩
  · exact ⟨support_neg (support_var (by omega)), support_var (by omega)⟩
  · exact ⟨support_var (by omega), support_neg (support_var (by omega))⟩

/-- Every original representation-column component is supported on the
declared coordinate carrier, at arbitrary degree and column index. -/
theorem coordinateColumn_supported {blocks slot : Nat} (hslot : slot < blocks)
    (degree k : Nat) : PolyTensorSupported blocks degree
      (polynomialColumn (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k) :=
  matrix_support (fundamental_supported hslot) (embed_support degree (basis_support blocks k))

private def LiftImage (blocks : Nat) (lower upper : RatPoly) : Prop :=
  PaddedPolynomialCoeffEqv (blocks + blocks) (liftBoundary blocks lower) upper

private theorem lift_zero : ∀ blocks, liftBoundary blocks polyZero = polyZero
  | 0 => rfl
  | blocks + 1 => by rw [liftBoundary, lift_zero blocks]; rfl

private theorem lift_neg : ∀ (blocks : Nat) (p : RatPoly),
    liftBoundary blocks (polyNeg p) = polyNeg (liftBoundary blocks p)
  | 0, _ => rfl
  | blocks + 1, p => by
      rw [liftBoundary, lift_neg blocks p, liftBoundary]
      simp only [liftHead, polyNeg, List.map_map]
      rfl

private theorem lift_var : ∀ (blocks coordinate : Nat),
    liftBoundary blocks (polyVar coordinate) = polyVar (4 * blocks + coordinate)
  | 0, _ => by simp only [liftBoundary, Nat.mul_zero, Nat.zero_add]
  | blocks + 1, coordinate => by
      rw [liftBoundary, lift_var blocks coordinate]
      rw [show 4 * (blocks + 1) + coordinate =
        (4 * blocks + coordinate) + 1 + 1 + 1 + 1 by omega]
      simp only [liftHead, polyVar, varMono, List.map_cons, List.map_nil,
        List.replicate_succ, List.cons_append]

private theorem image_zero (blocks : Nat) : LiftImage blocks polyZero polyZero := by
  unfold LiftImage
  rw [lift_zero]
  exact .refl _ _

private theorem image_one (blocks : Nat) : LiftImage blocks polyOne polyOne :=
  lift_one (blocks + blocks) blocks

private theorem image_add {blocks : Nat} {p p' q q' : RatPoly}
    (hp : LiftImage blocks p p') (hq : LiftImage blocks q q') :
    LiftImage blocks (polyAdd p q) (polyAdd p' q') := by
  unfold LiftImage
  rw [lift_add]
  exact PaddedPolynomialCoeffEqv.add hp hq

private theorem image_mul {blocks : Nat} {p p' q q' : RatPoly}
    (hp : LiftImage blocks p p') (hq : LiftImage blocks q q') :
    LiftImage blocks (polyMul p q) (polyMul p' q') := by
  unfold LiftImage
  rw [lift_product]
  exact PaddedPolynomialCoeffEqv.mul hp hq

private theorem image_neg {blocks : Nat} {p q : RatPoly} (h : LiftImage blocks p q) :
    LiftImage blocks (polyNeg p) (polyNeg q) := by
  unfold LiftImage PaddedPolynomialCoeffEqv at h ⊢
  rw [lift_neg, reindexQuaternionPolynomial_neg, reindexQuaternionPolynomial_neg]
  exact RatPolyCoeffEqv.neg h

private def ComplexLiftImage (blocks : Nat) (lower upper : ComplexRatPoly) : Prop :=
  LiftImage blocks lower.1 upper.1 ∧ LiftImage blocks lower.2 upper.2

private theorem complex_image_zero (blocks : Nat) :
    ComplexLiftImage blocks complexRatPolyZero complexRatPolyZero :=
  ⟨image_zero blocks, image_zero blocks⟩

private theorem complex_image_one (blocks : Nat) :
    ComplexLiftImage blocks complexRatPolyOne complexRatPolyOne :=
  ⟨image_one blocks, image_zero blocks⟩

private theorem complex_image_add {blocks : Nat} {p p' q q' : ComplexRatPoly}
    (hp : ComplexLiftImage blocks p p') (hq : ComplexLiftImage blocks q q') :
    ComplexLiftImage blocks (complexRatPolyAdd p q) (complexRatPolyAdd p' q') :=
  ⟨image_add hp.1 hq.1, image_add hp.2 hq.2⟩

private theorem complex_image_mul {blocks : Nat} {p p' q q' : ComplexRatPoly}
    (hp : ComplexLiftImage blocks p p') (hq : ComplexLiftImage blocks q q') :
    ComplexLiftImage blocks (complexRatPolyMul p q) (complexRatPolyMul p' q') :=
  ⟨image_add (image_mul hp.1 hq.1) (image_neg (image_mul hp.2 hq.2)),
    image_add (image_mul hp.1 hq.2) (image_mul hp.2 hq.1)⟩

/-- Literal lower-to-upper coordinate lifting on each complex tensor
component, compared on common 2N padding. No Haar equality is assumed. -/
def TensorLiftImage (blocks : Nat) : (degree : Nat) → PolyTensor degree → PolyTensor degree → Prop
  | 0, lower, upper =>
      PaddedPolynomialCoeffEqv (blocks + blocks) (liftBoundary blocks lower.1) upper.1 ∧
      PaddedPolynomialCoeffEqv (blocks + blocks) (liftBoundary blocks lower.2) upper.2
  | degree + 1, lower, upper => ∀ b, TensorLiftImage blocks degree (lower b) (upper b)

private theorem tensor_image_add {blocks : Nat} :
    ∀ {degree : Nat} {p p' q q' : PolyTensor degree},
    TensorLiftImage blocks degree p p' → TensorLiftImage blocks degree q q' →
      TensorLiftImage blocks degree (polyTensorAdd degree p q) (polyTensorAdd degree p' q')
  | 0, _, _, _, _, hp, hq => complex_image_add hp hq
  | _ + 1, _, _, _, _, hp, hq => fun b => tensor_image_add (hp b) (hq b)

private theorem tensor_image_scale {blocks : Nat} {a b : ComplexRatPoly}
    (hab : ComplexLiftImage blocks a b) : ∀ {degree : Nat} {p q : PolyTensor degree},
    TensorLiftImage blocks degree p q →
      TensorLiftImage blocks degree (polyTensorScale degree a p) (polyTensorScale degree b q)
  | 0, _, _, hp => complex_image_mul hab hp
  | _ + 1, _, _, hp => fun bit => tensor_image_scale hab (hp bit)

private theorem matrix_image {blocks : Nat} {M N : Bool → Bool → ComplexRatPoly}
    (hMN : ∀ i j, ComplexLiftImage blocks (M i j) (N i j)) :
    ∀ {degree : Nat} {p q : PolyTensor degree}, TensorLiftImage blocks degree p q →
      TensorLiftImage blocks degree (polyMatrixAction degree M p) (polyMatrixAction degree N q)
  | 0, _, _, hp => hp
  | _ + 1, _, _, hp => fun row =>
      tensor_image_add (tensor_image_scale (hMN row false) (matrix_image hMN (hp false)))
        (tensor_image_scale (hMN row true) (matrix_image hMN (hp true)))

private theorem embed_image {blocks : Nat} : ∀ degree {f g : Nat → ComplexRatPoly},
    (∀ k, ComplexLiftImage blocks (f k) (g k)) →
      TensorLiftImage blocks degree (polyEmbed degree f) (polyEmbed degree g)
  | 0, _, _, h => h 0
  | degree + 1, _, _, h => by
      intro b
      cases b
      · exact embed_image degree h
      · exact embed_image degree (fun k => h (k + 1))

private theorem basis_image (blocks k j : Nat) :
    ComplexLiftImage blocks (polynomialBasis k j) (polynomialBasis k j) := by
  unfold polynomialBasis
  split
  · exact complex_image_one blocks
  · exact complex_image_zero blocks

private theorem coordinate_image (blocks slot offset : Nat) :
    LiftImage blocks (polyVar (4 * slot + offset)) (polyVar (4 * (blocks + slot) + offset)) := by
  unfold LiftImage
  rw [lift_var, Nat.mul_add, Nat.add_assoc]
  exact .refl _ _

private theorem fundamental_image (blocks slot : Nat) (row column : Bool) :
    ComplexLiftImage blocks
      (fundamentalMatrixCoefficient (asRepresentationQuaternion
        (PolyQuaternion.coordinateVariable slot)) row column)
      (fundamentalMatrixCoefficient (asRepresentationQuaternion
        (PolyQuaternion.coordinateVariable (blocks + slot))) row column) := by
  have hs := coordinate_image blocks slot 0
  have hi := coordinate_image blocks slot 1
  have hj := coordinate_image blocks slot 2
  have hk := coordinate_image blocks slot 3
  simp only [Nat.add_zero] at hs
  cases row <;> cases column
  · exact ⟨hs, hi⟩
  · exact ⟨hj, hk⟩
  · exact ⟨image_neg hj, hk⟩
  · exact ⟨hs, image_neg hi⟩

/-- The original column at N+i is exactly the lower column with N fresh
head blocks adjoined. This is polynomial algebra, so no slot guard is needed;
consumers removing padding must separately supply their carrier support. -/
theorem coordinateColumn_lift (blocks slot degree k : Nat) :
    TensorLiftImage blocks degree
      (polynomialColumn (asRepresentationQuaternion (PolyQuaternion.coordinateVariable slot)) degree k)
      (polynomialColumn (asRepresentationQuaternion
        (PolyQuaternion.coordinateVariable (blocks + slot))) degree k) :=
  matrix_image (fundamental_image blocks slot) (embed_image degree (basis_image blocks k))

end YMGap.Continuum.SU2QuaternionCoordinateColumnLift

#print axioms YMGap.Continuum.SU2QuaternionCoordinateColumnLift.coordinateColumn_supported
#print axioms YMGap.Continuum.SU2QuaternionCoordinateColumnLift.TensorLiftImage
#print axioms YMGap.Continuum.SU2QuaternionCoordinateColumnLift.coordinateColumn_lift
