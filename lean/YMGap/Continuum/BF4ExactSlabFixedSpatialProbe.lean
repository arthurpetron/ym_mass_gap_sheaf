/-
# Signed original spatial probes on the fixed width-only slice

Evaluate a finite list of signed face-character factors on the SAME ordered
source plaquettes used by the spatial action. Time placement changes only
the faces: every coefficient, spin, repeated factor and list order is kept.
The existing ordered plaquette pin then identifies the placed source probe
with its original unswept face polynomial, coefficient-sensitively up to
zero padding.

The consumer is the original finite-chain pairing with spatial probes on
its two endpoints. No positivity, stationary normalization, completion or
mass-gap estimate is asserted. Arbitrary source polynomials are not being
identified with original gauge-invariant probes.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialProbe

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- Finite signed face factors on the width-only source slice. -/
def sourceProbe (width : Nat) (fs : List FaceFactor) : RatPoly :=
  product (fun face spin => characterPolynomial (plaquette width face).scalar spin) fs

/-- Translate only the face; its entire signed character list is unchanged. -/
def placeProbes (time : Nat) (fs : List FaceFactor) : List FaceFactor :=
  fs.map (fun f => (timeShiftPlaquette time f.1, f.2))

theorem placeProbes_face_mem {width : Nat} (time : Nat) (fs : List FaceFactor)
    (hfaces : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    ∀ f, f ∈ placeProbes time fs →
      f.1 ∈ (spatialFaces width).map (timeShiftPlaquette time) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact List.mem_map.mpr ⟨g.1, hfaces g hg, rfl⟩

theorem placeProbes_physical {width time extent : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent) (fs : List FaceFactor)
    (hfaces : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    ∀ f, f ∈ placeProbes time fs →
      f.1 ∈ boundaryCompleteSlabPlaquettes extent := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact spatialFaces_shift_physical (by omega) ht (hfaces g hg)

theorem placeProbes_spatial {width : Nat} (time : Nat) (fs : List FaceFactor)
    (hfaces : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    ∀ f, f ∈ placeProbes time fs → (dirsOf f.1.2).2 ≠ Dir4.x3 := by
  intro f hf
  exact ((spatialFaces_shift_mem_iff width time f.1).mp
    (placeProbes_face_mem time fs hfaces f hf)).2.2.2.2

theorem placeProbes_time {width : Nat} (time : Nat) (fs : List FaceFactor)
    (hfaces : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    ∀ f, f ∈ placeProbes time fs → f.1.1.2.2.2 = time := by
  intro f hf
  exact ((spatialFaces_shift_mem_iff width time f.1).mp
    (placeProbes_face_mem time fs hfaces f hf)).2.2.2.1

private theorem imageSum {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (finitePolySum f xs)) (finitePolySum g xs)
  | [], _ => .nil
  | a::xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyAdd _ _)) _
      rw [E.polynomial_add]
      exact (h a List.mem_cons_self).append
        (imageSum E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem imageProduct {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (polynomialProduct f xs)) (polynomialProduct g xs)
  | [], _ => E.polynomial_one_prefix
  | a::xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyMul _ _)) _
      rw [E.polynomial_mul]
      exact (h a List.mem_cons_self).mul
        (imageProduct E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem factor_pin {width time extent : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent)
    (f : FaceFactor) (hf : f.1 ∈ spatialFaces width) :
    QuaternionPrefixPolynomialEqv (B extent)
      ((embedding hw ht).polynomial (factor
        (fun face spin => characterPolynomial (plaquette width face).scalar spin) f))
      (factor (fun face spin =>
        characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin)
        (timeShiftPlaquette time f.1, f.2)) := by
  apply imageSum
  intro term _
  rw [BlockEmbedding.polynomial_smul]
  exact ((embedding hw ht).character_of_quaternion (plaquette_pin hw ht hf) term.1).smul term.2

private theorem product_place (characters : Z4Plaq → Nat → RatPoly)
    (time : Nat) (fs : List FaceFactor) :
    product characters (placeProbes time fs) =
      polynomialProduct (fun f => factor characters (timeShiftPlaquette time f.1, f.2)) fs := by
  simp only [product, placeProbes, polynomialProduct, List.foldr_map]

/-- All original signed terms are preserved by the already-proved ordered word pin. -/
theorem sourceProbe_prefix_pin {width time extent : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent) (fs : List FaceFactor)
    (hfaces : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    QuaternionPrefixPolynomialEqv (B extent)
      ((embedding hw ht).polynomial (sourceProbe width fs))
      (sweptProduct extent 0 (placeProbes time fs)) := by
  rw [swept_zero, product_place]
  exact imageProduct (embedding hw ht) _ _ fs
    (fun f hf => factor_pin hw ht f (hfaces f hf))

/-- Coefficient-sensitive endpoint pin, usable inside the entire original action. -/
theorem sourceProbe_pin {width time extent : Nat}
    (hw : width ≤ extent) (ht : time ≤ extent) (fs : List FaceFactor)
    (hfaces : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) :
    PaddedPolynomialCoeffEqv (B extent)
      ((embedding hw ht).polynomial (sourceProbe width fs))
      (sweptProduct extent 0 (placeProbes time fs)) :=
  PaddedPolynomialCoeffEqv.of_prefix (sourceProbe_prefix_pin hw ht fs hfaces)

private theorem support_one (n : Nat) : QuaternionSupported n PolyQuaternion.one :=
  ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h)), (fun _ h => False.elim (List.not_mem_nil h))⟩

private theorem link_supported (width : Nat) (l : Z4Link) :
    QuaternionSupported (N width) (link width l) := by
  unfold link
  split
  · exact QuaternionSupported.coordinate (List.idxOf_lt_length_of_mem ‹_›)
  · exact support_one _

private theorem oriented_supported (width : Nat) (entry : OrientedBF4Link) :
    QuaternionSupported (N width) (orientedLink width entry) := by
  unfold orientedLink
  split
  · exact (link_supported width entry.link).conj
  · exact link_supported width entry.link

private theorem word_supported (width : Nat) : ∀ word : List OrientedBF4Link,
    ∀ p, QuaternionSupported (N width) p → QuaternionSupported (N width)
      (word.foldl (fun q e => PolyQuaternion.mul q (orientedLink width e)) p)
  | [], _, hp => hp
  | e::es, _, hp => word_supported width es _ (hp.mul (oriented_supported width e))

private theorem sum_supported {A : Type} {n : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks n (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks n (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a::xs => supported_add (h a) (sum_supported f h xs)

private theorem polynomialProduct_supported {A : Type} {n : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks n (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks n (polynomialProduct f xs)
  | [] => supported_one n
  | a::xs => supported_polyMul (h a) (polynomialProduct_supported f h xs)

/-- Support holds for all finite syntax; valid-face hypotheses are needed only for its physical pin. -/
theorem sourceProbe_supported (width : Nat) (fs : List FaceFactor) :
    SupportedQuaternionBlocks (N width) (sourceProbe width fs) := by
  apply polynomialProduct_supported
  intro f
  apply sum_supported
  intro term
  exact supported_smul (SU2QuaternionRelativeHeatPairGeometry.character_supported
    (word_supported width _ _ (support_one _)).scalar term.1) term.2

end YMGap.Continuum.BF4ExactSlabFixedSpatialProbe

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.sourceProbe
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.placeProbes
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.placeProbes_face_mem
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.placeProbes_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.placeProbes_spatial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.placeProbes_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.sourceProbe_prefix_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.sourceProbe_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.sourceProbe_supported
