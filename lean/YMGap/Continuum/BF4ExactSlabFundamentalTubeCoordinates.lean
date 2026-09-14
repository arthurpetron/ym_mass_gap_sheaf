/-
# Literal corrected-slab coordinates of the fundamental tube

The compact tube's lower and upper links embed into the ORIGINAL 116-link
slab carrier. Its four relative characters are exactly the temporal-gauge
images of crossing faces 2,40,20,4. Faces 0 and 6 are its two ends.

The embedded conditional Haar identity retains arbitrary boundary and
spectator insertions. This is a bare selected-channel identity, NOT an
estimate for the complete original interacting covariance; no other face
weight, centering term, cutoff or volume limit is silently included.
-/

import YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
import YMGap.Continuum.SU2QuaternionHaarBlockEmbeddingAlgebra
import YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces

namespace YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeFaces
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTube
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.SU2QuaternionHaarGaugeCancellation
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.ClusterCount4DProgress

local infix:50 " ≈ " => Q'.eqv

def tubeLinks : List Nat := [0,3,2,1,8,17,16,12]

/-- Put the eight displayed spatial links first, retaining EVERY other link. -/
def tubeOrder : List Nat := tubeLinks ++ (List.range 116).filter (fun i => !tubeLinks.contains i)

def tubeEmbedding : BlockEmbedding 116 116 where
  image := tubeOrder
  length := by decide +kernel
  nodup := by decide +kernel
  physical := by
    intro i hi
    have h : tubeOrder.all (fun j => decide (j < 116)) = true := by decide +kernel
    exact of_decide_eq_true (List.all_eq_true.mp h i hi)

def lowerPlaquette : RatPoly := plaquette 0 3 2 1
def upperPlaquette : RatPoly := plaquette 8 17 16 12

def crossingIds : List Nat := [2,40,20,4]

def literalSide (i : Fin 4) : RatPoly :=
  sideCharacter (tubeLinks.getD i.val 0) (tubeLinks.getD (i.val + 4) 0)

def literalFactors : List RatPoly :=
  [lowerPlaquette, literalSide ⟨0,by decide⟩, literalSide ⟨1,by decide⟩,
    literalSide ⟨2,by decide⟩, literalSide ⟨3,by decide⟩]

private theorem embed_plaquette {a b c d : Nat}
    (ha : a < 116) (hb : b < 116) (hc : c < 116) (hd : d < 116) :
    QuaternionPrefixPolynomialEqv 116 (tubeEmbedding.polynomial (plaquette a b c d))
      (plaquette (tubeEmbedding.block a) (tubeEmbedding.block b)
        (tubeEmbedding.block c) (tubeEmbedding.block d)) := by
  apply tubeEmbedding.character_of_quaternion
  rw [tubeEmbedding.quaternion_mul, tubeEmbedding.quaternion_mul,
    tubeEmbedding.quaternion_mul, tubeEmbedding.quaternion_conj, tubeEmbedding.quaternion_conj]
  exact (((tubeEmbedding.quaternion_coordinate ha).mul
    (tubeEmbedding.quaternion_coordinate hb)).mul
    (tubeEmbedding.quaternion_coordinate hc).conj).mul
    (tubeEmbedding.quaternion_coordinate hd).conj

private theorem embed_side {a b : Nat} (ha : a < 116) (hb : b < 116) :
    QuaternionPrefixPolynomialEqv 116 (tubeEmbedding.polynomial (sideCharacter a b))
      (sideCharacter (tubeEmbedding.block a) (tubeEmbedding.block b)) := by
  apply tubeEmbedding.character_of_quaternion
  rw [tubeEmbedding.quaternion_mul, tubeEmbedding.quaternion_conj]
  exact (tubeEmbedding.quaternion_coordinate ha).mul (tubeEmbedding.quaternion_coordinate hb).conj

theorem lower_embedding_pin :
    QuaternionPrefixPolynomialEqv 116 (tubeEmbedding.polynomial (plaquette 0 1 2 3)) lowerPlaquette :=
  embed_plaquette (by decide) (by decide) (by decide) (by decide)

theorem upper_embedding_pin :
    QuaternionPrefixPolynomialEqv 116 (tubeEmbedding.polynomial (plaquette 4 5 6 7)) upperPlaquette :=
  embed_plaquette (by decide) (by decide) (by decide) (by decide)

theorem side_embedding_pin (i : Fin 4) :
    QuaternionPrefixPolynomialEqv 116
      (tubeEmbedding.polynomial (sideCharacter i.val (i.val + 4))) (literalSide i) := by
  have h := embed_side (a := i.val) (b := i.val + 4) (by omega) (by omega)
  rcases i with ⟨i,hi⟩
  have his : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases his with rfl | rfl | rfl | rfl <;> exact h

private theorem face_word (face : Z4Plaq) :
    PolyQuaternionCoeffEqv (correctedSlabPlaquettePolynomial 1 face)
      (plaquetteWord (correctedSlabLinkPolynomial 1 (faceLinkA face))
        (correctedSlabLinkPolynomial 1 (faceLinkB face))
        (correctedSlabLinkPolynomial 1 (faceLinkC face))
        (correctedSlabLinkPolynomial 1 (faceLinkD face))) := by
  simp only [correctedSlabPlaquettePolynomial, orientedPlaquetteBoundary,
    List.foldl_cons, List.foldl_nil, orientedCorrectedSlabLinkPolynomial,
    Bool.false_eq_true, if_false, if_true, plaquetteWord, faceLinkA, faceLinkB,
    faceLinkC, faceLinkD]
  exact (((PolyQuaternionCoeffEqv.one_mul _).mul (PolyQuaternionCoeffEqv.refl _)).mul
    (PolyQuaternionCoeffEqv.refl _)).mul (PolyQuaternionCoeffEqv.refl _)

private def LinkData (link : Z4Link) (index : Nat) : Prop :=
  link ∈ boundaryCompleteSlabLinks 1 ∧ (boundaryCompleteSlabLinks 1).idxOf link = index

private instance (link : Z4Link) (index : Nat) : Decidable (LinkData link index) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem link_of_data {link : Z4Link} {index : Nat} (h : LinkData link index) :
    correctedSlabLinkPolynomial 1 link = PolyQuaternion.coordinateVariable index := by
  rw [correctedSlabLinkPolynomial_of_mem h.1, h.2]

private theorem face_from_data (id a b c d : Nat)
    (ha : LinkData (faceLinkA (slabPlaquetteAt 1 id)) a)
    (hb : LinkData (faceLinkB (slabPlaquetteAt 1 id)) b)
    (hc : LinkData (faceLinkC (slabPlaquetteAt 1 id)) c)
    (hd : LinkData (faceLinkD (slabPlaquetteAt 1 id)) d) :
    RatPolyCoeffEqv (characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 id)).scalar 1)
      (plaquette a b c d) := by
  have h := face_word (slabPlaquetteAt 1 id)
  rw [link_of_data ha, link_of_data hb, link_of_data hc, link_of_data hd] at h
  exact characterPolynomial_coeffEqv h.scalar 1

/-- ORIGINAL lower face, with its redundant initial unit removed coefficientwise. -/
theorem lower_face_pin : RatPolyCoeffEqv
    (characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 0)).scalar 1)
    lowerPlaquette := by
  exact face_from_data 0 0 3 2 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem upper_face_pin : RatPolyCoeffEqv
    (characterPolynomial (correctedSlabPlaquettePolynomial 1 (slabPlaquetteAt 1 6)).scalar 1)
    upperPlaquette := by
  exact face_from_data 6 8 17 16 12 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The side kernel is pinned to the actual crossing face after the common
temporal gauge assignment, not to independently chosen link variables. -/
theorem temporal_side_pin (i : Fin 4) : HaarCarrierEqv 116
    (characterPolynomial (temporalFaceWord 1 0
      (slabPlaquetteAt 1 (crossingIds.getD i.val 0))).scalar 1) (literalSide i) := by
  have hf : ∀ j : Fin 4,
      plaquetteHalfSide 0 (slabPlaquetteAt 1 (crossingIds.getD j.val 0)) = .fixed := by decide +kernel
  have hd : ∀ j : Fin 4,
      LinkData (faceLinkA (slabPlaquetteAt 1 (crossingIds.getD j.val 0))) (tubeLinks.getD j.val 0) ∧
      LinkData (faceLinkC (slabPlaquetteAt 1 (crossingIds.getD j.val 0))) (tubeLinks.getD (j.val+4) 0) := by decide +kernel
  have hlen : (boundaryCompleteSlabLinks 1).length = 116 := by decide +kernel
  have h := crossing_face_character 1 0 (slabPlaquetteAt 1 (crossingIds.getD i.val 0)) (hf i) 1
  rw [hlen, link_of_data (hd i).1, link_of_data (hd i).2] at h
  exact h

theorem tube_embedding_pin :
    QuaternionPrefixPolynomialEqv 116 (tubeEmbedding.polynomial (factorProduct tubeFactors))
      (factorProduct literalFactors) := by
  simp only [tubeFactors, literalFactors, factorProduct, tubeEmbedding.polynomial_mul]
  exact lower_embedding_pin.mul ((side_embedding_pin ⟨0,by decide⟩).mul
    ((side_embedding_pin ⟨1,by decide⟩).mul ((side_embedding_pin ⟨2,by decide⟩).mul
      ((side_embedding_pin ⟨3,by decide⟩).mul tubeEmbedding.polynomial_one_prefix))))

/-- Transport the exact conditional contraction to the ORIGINAL link carrier.
The support guard prevents dropping any coordinate from the inserted polynomial.
No interaction/centering/limit estimate is assumed or inferred. -/
theorem embedded_tube_boundary_haar (boundary : RatPoly)
    (hs : SupportedQuaternionBlocks 116
      (factorProduct (tubeFactors ++ [liftBoundary 4 boundary]))) :
    quaternionHaar 116 (tubeEmbedding.polynomial
        (factorProduct (tubeFactors ++ [liftBoundary 4 boundary]))) ≈
      quaternionHaar 112 (polyMul propagatedPlaquette boundary) :=
  Q'.eqv_trans _ _ _ (tubeEmbedding.haar _ hs) (tube_boundary_haar 112 boundary)

private theorem lift_supported (n blocks : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks (blocks+n) (liftBoundary n p) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
      intro t ht
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
      have h := ih s hs
      change s.1.length + 1 + 1 + 1 + 1 ≤ 4 * (blocks + (n+1))
      omega

private theorem factors_supported (blocks : Nat) (fs : List RatPoly)
    (h : ∀ p, p ∈ fs → SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks blocks (factorProduct fs) := by
  induction fs with
  | nil => intro t ht; simp [factorProduct, polyOne] at ht; subst t; exact Nat.zero_le _
  | cons p ps ih =>
      exact supported_polyMul (h p List.mem_cons_self)
        (ih (fun q hq => h q (List.mem_cons_of_mem p hq)))

private theorem checked_support {fs : List RatPoly}
    (h : fs.all (fun p => p.all (fun t => decide (t.1.length ≤ 4*116))) = true) :
    ∀ p, p ∈ fs → SupportedQuaternionBlocks 116 p := by
  intro p hp t ht
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h p hp) t ht)

private theorem source_support {boundary : RatPoly} (hb : SupportedQuaternionBlocks 112 boundary) :
    SupportedQuaternionBlocks 116 (factorProduct (tubeFactors ++ [liftBoundary 4 boundary])) := by
  apply factors_supported
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact checked_support (fs := tubeFactors) (by decide +kernel) p hp
  · simp only [List.mem_singleton] at hp
    subst p
    exact lift_supported 4 112 hb

/-- The full spectator insertion is mapped too. Its coordinates cannot
accidentally refer to one of the four eliminated original lower links. -/
def literalBoundary (boundary : RatPoly) : RatPoly := tubeEmbedding.polynomial (liftBoundary 4 boundary)

theorem literal_boundary_source_pin (boundary : RatPoly) (hb : SupportedQuaternionBlocks 112 boundary) :
    quaternionHaar 116 (factorProduct (literalFactors ++ [literalBoundary boundary])) ≈
      quaternionHaar 116 (factorProduct (tubeFactors ++ [liftBoundary 4 boundary])) := by
  have hp : QuaternionPrefixPolynomialEqv 116
      (tubeEmbedding.polynomial (factorProduct (tubeFactors ++ [liftBoundary 4 boundary])))
      (factorProduct (literalFactors ++ [literalBoundary boundary])) := by
    simp only [tubeFactors, literalFactors, List.cons_append, List.nil_append,
      factorProduct, tubeEmbedding.polynomial_mul]
    exact lower_embedding_pin.mul ((side_embedding_pin ⟨0,by decide⟩).mul
      ((side_embedding_pin ⟨1,by decide⟩).mul ((side_embedding_pin ⟨2,by decide⟩).mul
        ((side_embedding_pin ⟨3,by decide⟩).mul
          ((QuaternionPrefixPolynomialEqv.refl _ _).mul tubeEmbedding.polynomial_one_prefix)))))
  have hl : SupportedQuaternionBlocks 116 (factorProduct (literalFactors ++ [literalBoundary boundary])) := by
    apply factors_supported
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact checked_support (fs := literalFactors) (by decide +kernel) p hp
    · simp only [List.mem_singleton] at hp
      subst p
      exact tubeEmbedding.polynomial_supported _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv 116 hp (tubeEmbedding.polynomial_supported _) hl))
    (tubeEmbedding.haar _ (source_support hb))

/-- Bare tube contraction directly on the original slab's literal link indices. -/
theorem literal_tube_boundary_haar (boundary : RatPoly) (hb : SupportedQuaternionBlocks 112 boundary) :
    quaternionHaar 116 (factorProduct (literalFactors ++ [literalBoundary boundary])) ≈
      quaternionHaar 112 (polyMul propagatedPlaquette boundary) :=
  Q'.eqv_trans _ _ _ (literal_boundary_source_pin boundary hb) (tube_boundary_haar 112 boundary)

/-- The selected original four-face heat term, with all other 112 link
coordinates retained: exact w^12 propagation, not an interacting lower bound. -/
theorem literal_weighted_tube_boundary_haar (w : Q') (boundary : RatPoly)
    (hb : SupportedQuaternionBlocks 112 boundary) :
    quaternionHaar 116 (polySmul (fourHeatCoefficients w)
        (factorProduct (literalFactors ++ [literalBoundary boundary]))) ≈
      qpow w 12 * quaternionHaar 112 (polyMul (plaquette 0 1 2 3) boundary) := by
  refine Q'.eqv_trans _ _ _ (quaternionHaar_polySmul _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (literal_boundary_source_pin boundary hb)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_polySmul _ _ _))
    (weighted_tube_boundary_haar w 112 boundary)

end YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates

#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.tubeEmbedding
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.lower_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.upper_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.side_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.lower_face_pin
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.upper_face_pin
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.temporal_side_pin
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.tube_embedding_pin
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.embedded_tube_boundary_haar
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.literalBoundary
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.literal_boundary_source_pin
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.literal_tube_boundary_haar
#print axioms YMGap.Continuum.BF4ExactSlabFundamentalTubeCoordinates.literal_weighted_tube_boundary_haar
