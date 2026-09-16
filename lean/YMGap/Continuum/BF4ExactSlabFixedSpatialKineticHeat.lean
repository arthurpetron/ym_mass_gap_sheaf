/-
# One original kinetic factor on two ordered copies of a spatial slice

Every temporal face couples the lower spatial link to the conjugate of
the SAME spatial link on the next slice. Construct that ordered relative
quaternion on the N+N carrier, retain every finite heat-character term,
and place the resulting width/nome/cutoff-only polynomial into the actual
original swept kinetic heat. No spatial action factor is absorbed into K.

This supplies the kinetic factor for exact finite weighted composition.
It is not a stationary transfer, positivity, contraction or mass-gap claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier
import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabSpatialSliceFactors
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGluing
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairCarrier
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPlaquetteHeatPropagation
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)
local infix:50 " ≈ " => Q'.eqv

def lowerLink (width : Nat) (link : Z4Link) : PolyQuaternion :=
  if link ∈ baseLinks width then PolyQuaternion.coordinateVariable ((baseLinks width).idxOf link)
  else PolyQuaternion.one

def upperLink (width : Nat) (link : Z4Link) : PolyQuaternion :=
  if link ∈ baseLinks width then PolyQuaternion.coordinateVariable (N width+(baseLinks width).idxOf link)
  else PolyQuaternion.one

/-- Original lower times inverse-upper order, not a diagonal surrogate. -/
def relative (width : Nat) (face : Z4Plaq) : PolyQuaternion :=
  PolyQuaternion.mul (lowerLink width (faceLinkA face))
    (PolyQuaternion.conj (upperLink width (faceLinkA face)))

def kineticWeight (w : Q') (K width : Nat) : RatPoly :=
  polynomialProduct (fun face => factor
    (fun f spin => characterPolynomial (relative width f).scalar spin)
    (face,heatWeights w K)) (temporalFaces width)

private theorem lower_member {width : Nat} {face : Z4Plaq}
    (hf : face ∈ temporalFaces width) : faceLinkA face ∈ baseLinks width := by
  obtain ⟨hx,hy,hz,ht,hd⟩ := (temporalFaces_mem_iff width face).mp hf
  apply (baseLinks_mem_iff width _).mpr
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;> simp only [dirsOf] at hd <;> try cases hd
  all_goals dsimp only at hx hy hz ht
  all_goals simp only [SliceLink, faceLinkA, dirsOf]
  all_goals refine ⟨(by intro h; cases h), ?_, ?_, ?_, ?_⟩ <;> omega

private theorem lower_shift (time : Nat) (face : Z4Plaq) :
    faceLinkA (timeShiftPlaquette time face) = timeShiftLink time (faceLinkA face) := rfl

private theorem upper_shift {face : Z4Plaq} (hd : (dirsOf face.2).2 = .x3) (time : Nat) :
    faceLinkC (timeShiftPlaquette time face) = timeShiftLink (time+1) (faceLinkA face) := by
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;> simp only [dirsOf] at hd <;> try cases hd
  all_goals simp only [faceLinkC, faceLinkA, timeShiftPlaquette, timeShiftLink,
    timeShiftVertex, dirsOf, addE, Nat.add_assoc]

/-- The placed relative quaternion is the actual original kinetic word. -/
theorem relative_pin {width start extent : Nat} (hw : width ≤ extent) (ht : start+1 ≤ extent)
    {face : Z4Plaq} (hf : face ∈ temporalFaces width) :
    QuaternionPrefixPolyQuaternionEqv (B extent) ((embedding hw ht).quaternion (relative width face))
      (PolyQuaternion.mul (correctedSlabLinkPolynomial extent (faceLinkA (timeShiftPlaquette start face)))
        (PolyQuaternion.conj (correctedSlabLinkPolynomial extent (faceLinkC (timeShiftPlaquette start face))))) := by
  have hm := lower_member hf
  rw [relative, BlockEmbedding.quaternion_mul, lowerLink, upperLink, if_pos hm, if_pos hm,
    BlockEmbedding.quaternion_conj, lower_shift,
    upper_shift ((temporalFaces_mem_iff width face).mp hf).2.2.2.2]
  exact (lower_link_pin hw ht hm).mul (upper_link_pin hw ht hm).conj

theorem character_pin {width start extent : Nat} (hw : width ≤ extent) (ht : start+1 ≤ extent)
    {face : Z4Plaq} (hf : face ∈ temporalFaces width) (spin : Nat) :
    QuaternionPrefixPolynomialEqv (B extent)
      ((embedding hw ht).polynomial (characterPolynomial (relative width face).scalar spin))
      (relativeCharacter extent (timeShiftPlaquette start face) spin) :=
  (embedding hw ht).character_of_quaternion (relative_pin hw ht hf) spin

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

/-- Full finite heat sum, with every original coefficient retained. -/
theorem heatFace_pin {width start extent : Nat} (hw : width ≤ extent) (ht : start+1 ≤ extent)
    (w : Q') (K : Nat) {face : Z4Plaq} (hf : face ∈ temporalFaces width) :
    QuaternionPrefixPolynomialEqv (B extent)
      ((embedding hw ht).polynomial (factor
        (fun f spin => characterPolynomial (relative width f).scalar spin) (face,heatWeights w K)))
      (factor (relativeCharacter extent) (timeShiftPlaquette start face,heatWeights w K)) := by
  apply imageSum
  intro term _
  rw [BlockEmbedding.polynomial_smul]
  exact (character_pin hw ht hf term.1).smul term.2

private theorem product_map {A C : Type} (f : C → RatPoly) (g : A → C) (xs : List A) :
    polynomialProduct f (xs.map g) = polynomialProduct (fun a => f (g a)) xs := by
  simp only [polynomialProduct,List.foldr_map]

/-- One fixed K polynomial is the original swept kinetic layer at every placement. -/
theorem kineticWeight_pin {width start extent : Nat} (hw : width ≤ extent) (ht : start+1 ≤ extent)
    (w : Q') (K : Nat) :
    PaddedPolynomialCoeffEqv (B extent) ((embedding hw ht).polynomial (kineticWeight w K width))
      (kineticHeat w K extent width start) := by
  rw [kineticHeat,product,heatFactors,product_map]
  have hi := imageProduct (embedding hw ht) _ _ (temporalFaces width)
    (fun face hf => heatFace_pin hw ht w K hf)
  have hp := polynomialProduct_perm (fun face => factor (relativeCharacter extent) (face,heatWeights w K))
    (temporalFaces_shift_perm extent width start (by omega) ht)
  rw [product_map,product_map] at hp
  exact (PaddedPolynomialCoeffEqv.of_prefix hi).trans (PaddedPolynomialCoeffEqv.of_coeff hp)

private theorem support_one (n : Nat) : QuaternionSupported n PolyQuaternion.one :=
  ⟨supported_one n, (fun _ h => False.elim (List.not_mem_nil h)),
    (fun _ h => False.elim (List.not_mem_nil h)), (fun _ h => False.elim (List.not_mem_nil h))⟩

private theorem lower_supported (width : Nat) (link : Z4Link) :
    QuaternionSupported (N width+N width) (lowerLink width link) := by
  unfold lowerLink
  split
  · have hi := List.idxOf_lt_length_of_mem ‹link ∈ baseLinks width›
    exact QuaternionSupported.coordinate (by omega)
  · exact support_one _

private theorem upper_supported (width : Nat) (link : Z4Link) :
    QuaternionSupported (N width+N width) (upperLink width link) := by
  unfold upperLink
  split
  · have hi := List.idxOf_lt_length_of_mem ‹link ∈ baseLinks width›
    exact QuaternionSupported.coordinate (by omega)
  · exact support_one _

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

theorem kineticWeight_supported (w : Q') (K width : Nat) :
    SupportedQuaternionBlocks (N width+N width) (kineticWeight w K width) := by
  apply product_supported
  intro face
  apply sum_supported
  intro term
  exact supported_smul (SU2QuaternionRelativeHeatPairGeometry.character_supported
    ((lower_supported width _).mul (upper_supported width _).conj).scalar term.1) term.2

/-- All supported two-slice insertions keep their original kinetic-weighted Haar pairing. -/
theorem kineticWeight_haar {width start extent : Nat} (hw : width ≤ extent) (ht : start+1 ≤ extent)
    (w : Q') (K : Nat) (p : RatPoly) (hp : SupportedQuaternionBlocks (N width+N width) p) :
    quaternionHaar (B extent) (polyMul ((embedding hw ht).polynomial p) (kineticHeat w K extent width start)) ≈
      quaternionHaar (N width+N width) (polyMul p (kineticWeight w K width)) := by
  have h := (kineticWeight_pin hw ht w K).haar_insert
    ((embedding hw ht).polynomial_supported _) (kineticHeat_supported w K extent width start)
    ((embedding hw ht).polynomial p) ((embedding hw ht).polynomial_supported p)
  rw [← BlockEmbedding.polynomial_mul] at h
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm h)
    ((embedding hw ht).haar _ (supported_polyMul hp (kineticWeight_supported w K width)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.lowerLink
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.upperLink
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.relative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.kineticWeight
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.relative_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.character_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.heatFace_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.kineticWeight_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.kineticWeight_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat.kineticWeight_haar
