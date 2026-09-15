/-
# The common vertex assignment preserves the ORIGINAL full action

Every original physical plaquette character is invariant under the same
all-link auxiliary gauge ledger. The proof composes over the original heat
sum, the complete physical face list and the original upper observable.
All neighboring action factors are retained. Equality holds with any further
supported insertion on the augmented original carrier.

These finite identities do not yet integrate the scalar image or identify
its cutoff/volume/completed limits. No transfer or mass-gap claim is made.
-/

import YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
import YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabVertexGaugeAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabAuxiliaryVertexGauge
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAdjacentPlaquetteGluing
open YMGap.Continuum.SU2QuaternionScalarVertexGaugeAverage
open YMGap.Continuum.SU2QuaternionAuxiliaryVertexGaugeLedger
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.QuaternionHaarSquareCertificate

private abbrev Lift (p : RatPoly) := liftBoundary 3 p
private abbrev G (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) := slabGaugePolynomial extent tags

/-- A proved property of the original polynomial and its actual ledger image.
This is not an assumed analytic certificate or a new observable algebra. -/
structure Invariant (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (p : RatPoly) : Prop where
  support : SupportedQuaternionBlocks (linkCount extent) p
  image : SupportedHaarEqv (linkCount extent+3) (G extent tags (Lift p)) (Lift p)

namespace Invariant

theorem lifted_support {extent : Nat} {tags : Z4Vertex → Option (Fin 3)} {p : RatPoly}
    (h : Invariant extent tags p) : SupportedQuaternionBlocks (linkCount extent+3) (Lift p) :=
  lift_supported h.support 3

theorem image_support {extent : Nat} {tags : Z4Vertex → Option (Fin 3)} {p : RatPoly}
    (h : Invariant extent tags p) : SupportedQuaternionBlocks (linkCount extent+3) (G extent tags (Lift p)) :=
  gaugePolynomial_supported _ _ _ h.lifted_support

theorem one (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) : Invariant extent tags polyOne := by
  refine ⟨supported_one _, ?_⟩
  let steps := gaugeLedger (startTag extent tags) (finishTag extent tags)
  have hpos : 0 < linkCount extent+2 := by omega
  have h := (padded_apply hpos steps (lift_one (linkCount extent+3) 3)).trans
    ((applySteps_character hpos steps polyOne 0).trans (lift_one (linkCount extent+3) 3).symm)
  exact .of_padded h (gaugePolynomial_supported _ _ _ (lift_supported (supported_one _) 3))
    (lift_supported (supported_one _) 3)

theorem zero (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) : Invariant extent tags polyZero := by
  refine ⟨fun _ h => False.elim (List.not_mem_nil h), ?_⟩
  change SupportedHaarEqv _ (applySelectedTranslationSteps _ _ polyZero) polyZero
  rw [applySteps_zero]
  exact .refl _ _

theorem add {extent : Nat} {tags : Z4Vertex → Option (Fin 3)} {p q : RatPoly}
    (hp : Invariant extent tags p) (hq : Invariant extent tags q) :
    Invariant extent tags (polyAdd p q) := by
  refine ⟨supported_add hp.support hq.support, ?_⟩
  change SupportedHaarEqv _ (applySelectedTranslationSteps _ _ (liftBoundary 3 (polyAdd p q))) _
  simp only [Lift, lift_add, applySelectedTranslationSteps_add]
  exact hp.image.add hq.image

theorem mul {extent : Nat} {tags : Z4Vertex → Option (Fin 3)} {p q : RatPoly}
    (hp : Invariant extent tags p) (hq : Invariant extent tags q) :
    Invariant extent tags (polyMul p q) := by
  refine ⟨supported_polyMul hp.support hq.support, ?_⟩
  change SupportedHaarEqv _ (applySelectedTranslationSteps _ _ (liftBoundary 3 (polyMul p q))) _
  simp only [Lift, lift_product]
  exact (SupportedHaarEqv.of_padded (.of_coeff (applySelectedTranslationSteps_mul _ _ _ _))
    (gaugePolynomial_supported _ _ _ (supported_polyMul hp.lifted_support hq.lifted_support))
    (supported_polyMul hp.image_support hq.image_support)).trans
      (hp.image.mul hq.image hq.image_support hp.lifted_support)

theorem smul {extent : Nat} {tags : Z4Vertex → Option (Fin 3)} {p : RatPoly}
    (h : Invariant extent tags p) (a : Q') : Invariant extent tags (polySmul a p) := by
  refine ⟨supported_smul h.support a, ?_⟩
  change SupportedHaarEqv _ (applySelectedTranslationSteps _ _ (liftBoundary 3 (polySmul a p))) _
  simp only [Lift, lift_smul]
  exact (SupportedHaarEqv.of_padded (.of_coeff (applySelectedTranslationSteps_smul _ _ _ _))
    (gaugePolynomial_supported _ _ _ (supported_smul h.lifted_support a))
    (supported_smul h.image_support a)).trans (h.image.smul a)

theorem finiteSum {A : Type} {extent : Nat} {tags : Z4Vertex → Option (Fin 3)} (f : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → Invariant extent tags (f a)) →
      Invariant extent tags (finitePolySum f xs)
  | [], _ => zero _ _
  | a::xs, h => (h a List.mem_cons_self).add (finiteSum f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem product {A : Type} {extent : Nat} {tags : Z4Vertex → Option (Fin 3)} (f : A → RatPoly) :
    ∀ xs : List A, (∀ a, a ∈ xs → Invariant extent tags (f a)) →
      Invariant extent tags (polynomialProduct f xs)
  | [], _ => one _ _
  | a::xs, h => (h a List.mem_cons_self).mul (product f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

end Invariant

private theorem qone (blocks : Nat) : QuaternionSupported blocks PolyQuaternion.one :=
  ⟨supported_one blocks, fun _ h => False.elim (List.not_mem_nil h),
    fun _ h => False.elim (List.not_mem_nil h), fun _ h => False.elim (List.not_mem_nil h)⟩

private theorem original_link_support (extent : Nat) (link : Z4Link) :
    QuaternionSupported (linkCount extent) (correctedSlabLinkPolynomial extent link) := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks extent
  · rw [correctedSlabLinkPolynomial_of_mem hl]
    exact .coordinate (List.idxOf_lt_length_of_mem hl)
  · rw [correctedSlabLinkPolynomial_of_not_mem hl]
    exact qone _

theorem lifted_link_support (extent : Nat) (link : Z4Link) :
    QuaternionSupported (linkCount extent+3) (liftedLink extent link) := by
  have h := original_link_support extent link
  exact ⟨lift_supported h.scalar 3, lift_supported h.iPart 3,
    lift_supported h.jPart 3, lift_supported h.kPart 3⟩

private theorem auxiliary_support (extent : Nat) (tag : Option (Fin 3)) :
    QuaternionSupported (linkCount extent+3) (auxiliaryGauge tag) := by
  cases tag with
  | none => exact qone _
  | some j => exact .coordinate (by have := j.isLt; omega)

private theorem vertex_link_support (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (link : Z4Link) :
    QuaternionSupported (linkCount extent+3) (vertexLink extent tags link) :=
  (((auxiliary_support extent _).conj).mul (lifted_link_support extent link)).mul (auxiliary_support extent _)

private theorem character_support {blocks : Nat} {p : RatPoly} (h : SupportedQuaternionBlocks blocks p) :
    ∀ spin, SupportedQuaternionBlocks blocks (characterPolynomial p spin)
  | 0 => supported_one _
  | 1 => supported_smul h 2
  | spin+2 => supported_add (supported_polyMul (supported_smul h 2) (character_support h (spin+1)))
      (supported_smul (character_support h spin) (-1))

private theorem lifted_character_support (extent : Nat) (face : Z4Plaq) (spin : Nat) :
    SupportedQuaternionBlocks (linkCount extent+3) (characterPolynomial (liftedFaceWord extent face).scalar spin) :=
  character_support ((((lifted_link_support extent _).mul (lifted_link_support extent _)).mul
    (lifted_link_support extent _).conj).mul (lifted_link_support extent _).conj).scalar spin

private theorem vertex_character_support (extent : Nat) (tags : Z4Vertex → Option (Fin 3)) (face : Z4Plaq) (spin : Nat) :
    SupportedQuaternionBlocks (linkCount extent+3) (characterPolynomial (vertexFaceWord extent tags face).scalar spin) :=
  character_support ((((vertex_link_support extent tags _).mul (vertex_link_support extent tags _)).mul
    (vertex_link_support extent tags _).conj).mul (vertex_link_support extent tags _).conj).scalar spin

private def rawWord (extent : Nat) (face : Z4Plaq) : PolyQuaternion :=
  plaquetteWord (correctedSlabLinkPolynomial extent (faceLinkA face))
    (correctedSlabLinkPolynomial extent (faceLinkB face))
    (correctedSlabLinkPolynomial extent (faceLinkC face))
    (correctedSlabLinkPolynomial extent (faceLinkD face))

private theorem raw_word_pin (extent : Nat) (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (correctedSlabPlaquettePolynomial extent face) (rawWord extent face) :=
  (((PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)).mul
    (PolyQuaternionCoeffEqv.refl _)).mul (PolyQuaternionCoeffEqv.refl _)

private theorem lifted_scalar (q : PolyQuaternion) : Lift q.scalar = (liftThree q).scalar := rfl

private theorem lift3_word (a b c d : PolyQuaternion) :
    liftThree (plaquetteWord a b c d) =
      plaquetteWord (liftThree a) (liftThree b) (liftThree c) (liftThree d) := by
  simp only [liftThree, plaquetteWord, lift_mul, lift_conj]

private theorem lifted_word_pin (extent : Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (Lift (correctedSlabPlaquettePolynomial extent face).scalar) (liftedFaceWord extent face).scalar := by
  have h := lift_coeff 3 (raw_word_pin extent face).scalar
  have pin : Lift (rawWord extent face).scalar = (liftedFaceWord extent face).scalar :=
    (lifted_scalar (rawWord extent face)).trans (congrArg PolyQuaternion.scalar
      (lift3_word (correctedSlabLinkPolynomial extent (faceLinkA face))
        (correctedSlabLinkPolynomial extent (faceLinkB face))
        (correctedSlabLinkPolynomial extent (faceLinkC face))
        (correctedSlabLinkPolynomial extent (faceLinkD face))))
  unfold Lift at pin
  rw [pin] at h
  exact h

/-- The ORIGINAL physical face character, not a substituted local model. -/
theorem character_invariant {extent : Nat} (tags : Z4Vertex → Option (Fin 3)) {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    Invariant extent tags (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) := by
  let p := (correctedSlabPlaquettePolynomial extent face).scalar
  let steps := gaugeLedger (startTag extent tags) (finishTag extent tags)
  have hpos : 0 < linkCount extent+2 := by omega
  have hp := original_character_support extent face spin
  have hword : PaddedPolynomialCoeffEqv (linkCount extent+3)
      (G extent tags (Lift p)) (vertexFaceWord extent tags face).scalar :=
    (PaddedPolynomialCoeffEqv.of_coeff (applySelectedTranslationSteps_coeffEqv hpos steps
      (lifted_word_pin extent face))).trans (slabGauge_face_word tags hf).scalar
  have image := (padded_apply hpos steps (lift_character (linkCount extent+3) 3 p spin)).trans
    ((applySteps_character hpos steps (Lift p) spin).trans (hword.character spin))
  have back := (lift_character (linkCount extent+3) 3 p spin).trans
    ((PaddedPolynomialCoeffEqv.of_coeff (lifted_word_pin extent face)).character spin)
  refine ⟨hp, ?_⟩
  exact (SupportedHaarEqv.of_padded image (gaugePolynomial_supported _ _ _ (lift_supported hp 3))
    (vertex_character_support extent tags face spin)).trans
      ((SupportedHaarEqv.of_carrier (vertexFace_character extent tags face spin)).trans
        (SupportedHaarEqv.of_padded back (lift_supported hp 3) (lifted_character_support extent face spin)).symm)

theorem faceHeat_invariant {extent : Nat} (tags : Z4Vertex → Option (Fin 3)) (w : Q') (K : Nat)
    {id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) : Invariant extent tags (faceHeatPolynomial w K extent id) :=
  Invariant.finiteSum _ _ (fun spin _ => (character_invariant tags (slabPlaquetteAt_mem hi) spin).smul _)

/-- Every supplied physical face factor is retained, at every heat cutoff. -/
theorem heatProduct_invariant {extent : Nat} (tags : Z4Vertex → Option (Fin 3)) (w : Q') (K : Nat)
    (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Invariant extent tags (polynomialProduct (faceHeatPolynomial w K extent) ids) :=
  Invariant.product _ _ (fun id hid => faceHeat_invariant tags w K (hi id hid))

private theorem expression_invariant {extent half : Nat} (tags : Z4Vertex → Option (Fin 3))
    (f : Nat → Nat → RatPoly) (hf : ∀ id, id ∈ centralLowerFaceIds half → ∀ spin, Invariant extent tags (f id spin)) :
    ∀ e : PlaquetteExpression half, Invariant extent tags (evaluate f e)
  | .unit => Invariant.one _ _
  | .character id hi spin => hf id hi spin
  | .add p q => (expression_invariant tags f hf p).add (expression_invariant tags f hf q)
  | .mul p q => (expression_invariant tags f hf p).mul (expression_invariant tags f hf q)
  | .smul a p => (expression_invariant tags f hf p).smul a

theorem lower_invariant {half : Nat} (tags : Z4Vertex → Option (Fin 3)) (e : PlaquetteExpression half) :
    Invariant (centralExtent half) tags (lower e) :=
  expression_invariant tags _ (fun _ hi spin => character_invariant tags
    (slabPlaquetteAt_mem (mem_centralLowerFaceIds.mp hi).1) spin) e

theorem upper_invariant {half : Nat} (tags : Z4Vertex → Option (Fin 3)) (e : PlaquetteExpression half) :
    Invariant (centralExtent half) tags (upper e) :=
  expression_invariant tags _ (fun _ hi spin => character_invariant tags
    (slabPlaquetteAt_mem (mem_centralUpperFaceIds.mp (upper_id hi)).1) spin) e

/-- Full ORIGINAL action and upper insertion, under one common vertex field.
No factor is treated as independent of the original probe links. -/
theorem fullActionInsertion_invariant {half : Nat} (tags : Z4Vertex → Option (Fin 3))
    (w : Q') (K : Nat) (e : PlaquetteExpression half) :
    Invariant (centralExtent half) tags (polyMul (upper e)
      (polynomialProduct (faceHeatPolynomial w K (centralExtent half)) (slabPhysicalFaceEdges (centralExtent half)))) :=
  (upper_invariant tags e).mul (heatProduct_invariant tags w K _ (fun _ h => h))

end YMGap.Continuum.BF4ExactSlabVertexGaugeAction

#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.lifted_support
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.image_support
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.one
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.zero
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.add
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.mul
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.smul
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.finiteSum
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.Invariant.product
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.lifted_link_support
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.character_invariant
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.faceHeat_invariant
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.heatProduct_invariant
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.lower_invariant
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.upper_invariant
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaugeAction.fullActionInsertion_invariant
