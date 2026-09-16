/-
# One and the same original spatial weight on every placed time slice

Construct the ordered plaquette words directly on the width-only spatial
link carrier. Their complete finite heat product is independent of ambient
extent and time. Every placement sends this fixed polynomial to the actual
original `spatialHeat`, up to coefficient-sensitive zero padding. The exact
Haar pairing with any supported source insertion is consequently unchanged.

This supplies the V factor for finite weighted time composition. It does
not identify the kinetic factor, transfer powers, or a stationary vacuum,
and needs no positivity or coupling assumption.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
import YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
import YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
import YMGap.Continuum.QuaternionHaarHeatCertificate

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarHeatCertificate
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation "N" width => List.length (baseLinks width)
local notation "B" extent => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

/-- A literal source link variable, with the same identity convention off-carrier. -/
def link (width : Nat) (l : Z4Link) : PolyQuaternion :=
  if l ∈ baseLinks width then PolyQuaternion.coordinateVariable ((baseLinks width).idxOf l)
  else PolyQuaternion.one

def orientedLink (width : Nat) (entry : OrientedBF4Link) : PolyQuaternion :=
  if entry.reverse then PolyQuaternion.conj (link width entry.link) else link width entry.link

def plaquette (width : Nat) (face : Z4Plaq) : PolyQuaternion :=
  (orientedPlaquetteBoundary face).foldl
    (fun q entry => PolyQuaternion.mul q (orientedLink width entry)) PolyQuaternion.one

def spatialWeight (w : Q') (K width : Nat) : RatPoly :=
  polynomialProduct (fun face => heatPrefix w K (plaquette width face).scalar) (spatialFaces width)

private theorem face_links {width : Nat} {face : Z4Plaq} (hf : face ∈ spatialFaces width)
    {l : Z4Link} (hl : l ∈ edgesOf face) : l ∈ baseLinks width := by
  obtain ⟨hx,hy,hz,ht,hsp⟩ := (spatialFaces_mem_iff width face).mp hf
  have hb := face_edge_box hx hy hz hl
  have he := spatial_face_edge face hsp l hl
  exact (baseLinks_mem_iff width l).mpr ⟨he.1,hb.1,hb.2.1,hb.2.2,he.2.trans ht⟩

private def shiftEntry (time : Nat) (entry : OrientedBF4Link) : OrientedBF4Link :=
  ⟨timeShiftLink time entry.link,entry.reverse⟩

private theorem boundary_shift (time : Nat) (face : Z4Plaq) :
    orientedPlaquetteBoundary (timeShiftPlaquette time face) =
      (orientedPlaquetteBoundary face).map (shiftEntry time) := by
  simp only [orientedPlaquetteBoundary,timeShiftPlaquette,timeShiftLink,shiftEntry,
    List.map_cons,List.map_nil,timeShiftVertex_addE]

private theorem oriented_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    {entry : OrientedBF4Link} (hl : entry.link ∈ baseLinks width) :
    QuaternionPrefixPolyQuaternionEqv (B extent)
      ((embedding hw ht).quaternion (orientedLink width entry))
      (orientedCorrectedSlabLinkPolynomial extent (shiftEntry time entry)) := by
  unfold orientedLink orientedCorrectedSlabLinkPolynomial shiftEntry
  simp only [link,if_pos hl]
  cases h : entry.reverse
  · exact link_pin hw ht hl
  · simp only [ite_true]
    rw [BlockEmbedding.quaternion_conj]
    exact (link_pin hw ht hl).conj

private theorem word_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent) :
    ∀ word : List OrientedBF4Link, (∀ e, e ∈ word → e.link ∈ baseLinks width) →
    ∀ p q : PolyQuaternion,
    QuaternionPrefixPolyQuaternionEqv (B extent) ((embedding hw ht).quaternion p) q →
    QuaternionPrefixPolyQuaternionEqv (B extent)
      ((embedding hw ht).quaternion (word.foldl (fun a e => PolyQuaternion.mul a (orientedLink width e)) p))
      ((word.map (shiftEntry time)).foldl
        (fun a e => PolyQuaternion.mul a (orientedCorrectedSlabLinkPolynomial extent e)) q)
  | [], _, _, _, hp => hp
  | e::es, he, p, q, hp => by
      apply word_pin hw ht es (fun e hm => he e (List.mem_cons_of_mem _ hm))
      rw [BlockEmbedding.quaternion_mul]
      exact hp.mul (oriented_pin hw ht (he e List.mem_cons_self))

/-- Ordered quaternion multiplication and every original edge are preserved. -/
theorem plaquette_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    {face : Z4Plaq} (hf : face ∈ spatialFaces width) :
    QuaternionPrefixPolyQuaternionEqv (B extent)
      ((embedding hw ht).quaternion (plaquette width face))
      (correctedSlabPlaquettePolynomial extent (timeShiftPlaquette time face)) := by
  unfold plaquette correctedSlabPlaquettePolynomial
  rw [boundary_shift]
  exact word_pin hw ht _ (fun e he => face_links hf (orientedPlaquetteBoundary_link_mem_edgesOf he))
    _ _ (embedding hw ht).quaternion_one

private theorem imageSum {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (finitePolySum f xs)) (finitePolySum g xs)
  | [], _ => .nil
  | a::xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyAdd _ _)) _
      rw [E.polynomial_add]
      exact (h a List.mem_cons_self).append (imageSum E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem imageProduct {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (polynomialProduct f xs)) (polynomialProduct g xs)
  | [], _ => E.polynomial_one_prefix
  | a::xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyMul _ _)) _
      rw [E.polynomial_mul]
      exact (h a List.mem_cons_self).mul (imageProduct E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private def literalHeat (w : Q') (K extent : Nat) (face : Z4Plaq) : RatPoly :=
  heatPrefix w K (correctedSlabPlaquettePolynomial extent face).scalar

private theorem literalHeat_at (w : Q') (K extent id : Nat) :
    literalHeat w K extent (slabPlaquetteAt extent id) = faceHeatPolynomial w K extent id := by
  rw [faceHeatPolynomial_eq_sum]
  rfl

/-- The full heat prefix, not only one spin or its scalar coefficient. -/
theorem heatFace_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    (w : Q') (K : Nat) {face : Z4Plaq} (hf : face ∈ spatialFaces width) :
    QuaternionPrefixPolynomialEqv (B extent)
      ((embedding hw ht).polynomial (heatPrefix w K (plaquette width face).scalar))
      (heatPrefix w K (correctedSlabPlaquettePolynomial extent (timeShiftPlaquette time face)).scalar) := by
  apply imageSum
  intro spin _
  rw [BlockEmbedding.polynomial_smul]
  exact ((embedding hw ht).character_of_quaternion (plaquette_pin hw ht hf) spin).smul _

/-- ONE width-only spatial action is placed at any admissible time/extent.
Padding and face enumeration permutations are both coefficient-sensitive. -/
theorem spatialWeight_pin {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    (w : Q') (K : Nat) :
    PaddedPolynomialCoeffEqv (B extent) ((embedding hw ht).polynomial (spatialWeight w K width))
      (spatialHeat w K extent width time) := by
  have hi := imageProduct (embedding hw ht) _ _ (spatialFaces width)
    (fun face hf => heatFace_pin hw ht w K hf)
  have hp := polynomialProduct_perm (literalHeat w K extent)
    (spatialFaces_shift_perm extent width time (by omega) ht)
  simp only [polynomialProduct,List.foldr_map,literalHeat_at] at hp
  exact (PaddedPolynomialCoeffEqv.of_prefix hi).trans (PaddedPolynomialCoeffEqv.of_coeff hp)

private theorem support_one (n : Nat) : QuaternionSupported n PolyQuaternion.one :=
  ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h)), (fun _ h => False.elim (List.not_mem_nil h))⟩

private theorem link_supported (width : Nat) (l : Z4Link) : QuaternionSupported (N width) (link width l) := by
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
  | e::es, p, hp => word_supported width es _ (hp.mul (oriented_supported width e))

private theorem sum_supported {A : Type} {n : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks n (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks n (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a::xs => supported_add (h a) (sum_supported f h xs)

private theorem product_supported {A : Type} {n : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks n (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks n (polynomialProduct f xs)
  | [] => supported_one n
  | a::xs => supported_polyMul (h a) (product_supported f h xs)

theorem spatialWeight_supported (w : Q') (K width : Nat) :
    SupportedQuaternionBlocks (N width) (spatialWeight w K width) := by
  apply product_supported
  intro face
  apply sum_supported
  intro spin
  exact supported_smul (SU2QuaternionRelativeHeatPairGeometry.character_supported
    (word_supported width _ _ (support_one _)).scalar spin) _

/-- All source insertions share the same ORIGINAL spatial-weighted Haar law. -/
theorem spatialWeight_haar {width time extent : Nat} (hw : width ≤ extent) (ht : time ≤ extent)
    (w : Q') (K : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (N width) p) :
    quaternionHaar (B extent) (polyMul ((embedding hw ht).polynomial p) (spatialHeat w K extent width time)) ≈
      quaternionHaar (N width) (polyMul p (spatialWeight w K width)) := by
  have h := (spatialWeight_pin hw ht w K).haar_insert
    ((embedding hw ht).polynomial_supported _) (BF4ExactSlabFaceLinkLocality.heatProduct_supported w K extent _)
    ((embedding hw ht).polynomial p) ((embedding hw ht).polynomial_supported p)
  rw [← BlockEmbedding.polynomial_mul] at h
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm h)
    ((embedding hw ht).haar _ (supported_polyMul hp (spatialWeight_supported w K width)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.link
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.orientedLink
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.plaquette
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.spatialWeight
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.plaquette_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.heatFace_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat.spatialWeight_haar
