/-
# The actual vertex Gauss sum annihilates the full original heat action

Raw coefficient equalities identify each literal four-edge plaquette with
its closed Wilson word BEFORE differentiation. The checked endpoint
telescope then kills every character. Raw linearity and Leibniz retain
every spatial and temporal heat factor at every finite cutoff and extent.

No action positivity, nome range, inverse, gauge fixing, static restriction,
or continuum assumption is used. This is a finite all-link statement, not
fixed-slice transfer preservation or a horizontal signed-cost estimate.
-/

import YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
import YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit

namespace YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabVertexGaussWilsonWord
open YMGap.Continuum.BF4ExactSlabVertexGaussClosedCharacter
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionLeftRightAngularAction
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "SlabB" extent:arg => List.length (boundaryCompleteSlabLinks extent)
attribute [local irreducible] boundaryCompleteSlabLinks

private theorem directions (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

private theorem frame_congr (right : Bool) (b : Nat) (i : Fin 3)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (frameDerivativeAt right b i p) (frameDerivativeAt right b i q) := by
  have hd (a d : Nat) := angularDerivative_congr (4*b+a) (4*b+d) h
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact (hd 0 1).add (hd 2 3)
    · exact (hd 0 1).add (RatPolyCoeffEqv.neg (hd 2 3))
  · cases right
    · exact (hd 0 2).add (RatPolyCoeffEqv.neg (hd 1 3))
    · exact (hd 0 2).add (hd 1 3)
  · cases right
    · exact (hd 0 3).add (hd 1 2)
    · exact (hd 0 3).add (RatPolyCoeffEqv.neg (hd 1 2))

private theorem choose_congr (c : Prop) [Decidable c] {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (if c then p else polyZero) (if c then q else polyZero) := by
  split
  · exact h
  · exact .refl _

private theorem sum_congr {A : Type} (f g : A → RatPoly)
    (h : ∀ a, RatPolyCoeffEqv (f a) (g a)) : ∀ xs : List A,
    RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum g xs)
  | [] => .refl _
  | a::xs => (h a).add (sum_congr f g h xs)

/-- Only RAW coefficient equality is differentiated here; no padded pin is
used as an input to a derivative. -/
theorem vertexGauss_congr (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (vertexGauss extent v i p) (vertexGauss extent v i q) := by
  apply sum_congr
  intro l
  exact (choose_congr (v=l.1) (RatPolyCoeffEqv.neg (frame_congr false _ i h))).add
    (choose_congr (v=addE l.1 l.2) (frame_congr true _ i h))

private theorem neg_supported {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) : SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem zero_supported (n : Nat) : SupportedQuaternionBlocks n polyZero :=
  fun _ h => False.elim (List.not_mem_nil h)

private theorem frame_supported {n b : Nat} (right : Bool) (hb : b<n) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (frameDerivativeAt right b i p) := by
  have hd (a d : Nat) (ha : a<4) (hda : d<4) :
      SupportedQuaternionBlocks n (blockAngularDerivative b a d p) :=
    angularDerivative_supported_at (by omega) (by omega) hp
  rcases directions i with rfl | rfl | rfl
  · cases right
    · exact supported_add (hd 0 1 (by decide) (by decide)) (hd 2 3 (by decide) (by decide))
    · exact supported_add (hd 0 1 (by decide) (by decide))
        (neg_supported (hd 2 3 (by decide) (by decide)))
  · cases right
    · exact supported_add (hd 0 2 (by decide) (by decide))
        (neg_supported (hd 1 3 (by decide) (by decide)))
    · exact supported_add (hd 0 2 (by decide) (by decide)) (hd 1 3 (by decide) (by decide))
  · cases right
    · exact supported_add (hd 0 3 (by decide) (by decide)) (hd 1 2 (by decide) (by decide))
    · exact supported_add (hd 0 3 (by decide) (by decide))
        (neg_supported (hd 1 2 (by decide) (by decide)))

private theorem sum_supported {A : Type} {n : Nat} (f : A → RatPoly) :
    ∀ xs : List A, (∀ a, a∈xs → SupportedQuaternionBlocks n (f a)) →
    SupportedQuaternionBlocks n (finitePolySum f xs)
  | [], _ => zero_supported n
  | a::xs, h => supported_add (h a List.mem_cons_self)
      (sum_supported f xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- Every summand is differentiated at its actual in-range physical link. -/
theorem vertexGauss_supported (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (SlabB extent) p) :
    SupportedQuaternionBlocks (SlabB extent) (vertexGauss extent v i p) := by
  apply sum_supported
  intro l hl
  have hb := List.idxOf_lt_length_of_mem hl
  apply supported_add
  · split
    · exact neg_supported (frame_supported false hb i hp)
    · exact zero_supported _
  · split
    · exact frame_supported true hb i hp
    · exact zero_supported _

private theorem boundary_compatible (face : Z4Plaq) :
    Compatible face.1 (orientedPlaquetteBoundary face) := by
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;>
    simp [Compatible, orientedPlaquetteBoundary, entryStart, entryFinish, dirsOf, addE]

private theorem plaquette_character_zero {extent : Nat} (v : Z4Vertex) (i : Fin 3)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) (spin : Nat) :
    PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i
        (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin))
      polyZero :=
  (PaddedPolynomialCoeffEqv.of_coeff
    (vertexGauss_congr extent v i (character_plaquette extent face spin)).symm).trans
      (closedCharacter_gauss_zero extent v i face.1 (orientedPlaquetteBoundary face)
        (boundary_compatible face) rfl
        (fun _ he => orientedPlaquetteBoundary_link_mem_slab hf he) spin)

private theorem sum_gauss_zero {A : Type} (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (f : A → RatPoly) : ∀ xs : List A,
    (∀ a, a∈xs → PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i (f a)) polyZero) →
    PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i (finitePolySum f xs)) polyZero
  | [], _ => .of_coeff (vertexGauss_zero extent v i)
  | a::xs, h => (PaddedPolynomialCoeffEqv.of_coeff (vertexGauss_add extent v i _ _)).trans
      ((h a List.mem_cons_self).add
        (sum_gauss_zero extent v i f xs (fun b hb => h b (List.mem_cons_of_mem a hb))))

/-- Every spin of an ORIGINAL physical plaquette is retained in its heat
prefix, including K=0 and arbitrary rational nome. -/
theorem faceHeatPolynomial_gauss_zero {extent id : Nat} (w : Q') (K : Nat)
    (hi : id ∈ slabPhysicalFaceEdges extent) (v : Z4Vertex) (i : Fin 3) :
    PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i (faceHeatPolynomial w K extent id)) polyZero := by
  apply sum_gauss_zero
  intro spin _
  exact (PaddedPolynomialCoeffEqv.of_coeff (vertexGauss_smul extent v i _ _)).trans
    (((plaquette_character_zero v i (slabPlaquetteAt_mem hi) spin).smul _).trans
      (.of_coeff (RatPolyCoeffEqv.smul_zero _)))

private theorem product_gauss_zero {A : Type} (extent : Nat) (v : Z4Vertex) (i : Fin 3)
    (f : A → RatPoly) : ∀ xs : List A,
    (∀ a, a∈xs → PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i (f a)) polyZero) →
    PaddedPolynomialCoeffEqv (SlabB extent)
      (vertexGauss extent v i (polynomialProduct f xs)) polyZero
  | [], _ => .of_coeff (vertexGauss_one extent v i)
  | a::xs, h =>
      (PaddedPolynomialCoeffEqv.of_coeff (vertexGauss_mul extent v i _ _)).trans
        ((((h a List.mem_cons_self).mul (.refl _ _)).add
          ((PaddedPolynomialCoeffEqv.refl _ _).mul
            (product_gauss_zero extent v i f xs (fun b hb => h b (List.mem_cons_of_mem a hb))))).trans
          (.of_coeff ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.mul_zero_right _))))

/-- The complete ORIGINAL finite action, spatial and temporal faces alike,
is annihilated by the actual all-link vertex Gauss generator. -/
theorem fullHeatProduct_gauss_zero (w : Q') (K half : Nat) (v : Z4Vertex) (i : Fin 3) :
    PaddedPolynomialCoeffEqv (SlabB (centralExtent half))
      (vertexGauss (centralExtent half) v i (fullHeatProduct w K half)) polyZero :=
  product_gauss_zero _ v i _ _ (fun _ hi => faceHeatPolynomial_gauss_zero w K hi v i)

end YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction

#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction.vertexGauss_congr
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction.vertexGauss_supported
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction.faceHeatPolynomial_gauss_zero
#print axioms YMGap.Continuum.BF4ExactSlabVertexGaussHeatAction.fullHeatProduct_gauss_zero
