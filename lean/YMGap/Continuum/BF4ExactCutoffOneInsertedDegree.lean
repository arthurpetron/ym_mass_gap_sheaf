/-
# Literal fundamental insertions in the cutoff-one corrected BF4 slab

The insertion list is a list of occurrences, not a set: repeated faces retain
their character factors and their full block degree.  The original action
factor on each inserted face remains in the weighted 72-face integrand.

This module supplies exact block homogeneity, actual 116-block support, and
odd-link Haar annihilation.  It does not prove charged-mask completeness,
an active-carrier reduction, or the value of a charged tensor contraction.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier

namespace YMGap.Continuum.BF4ExactCutoffOneInsertedDegree

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceActiveCarrier
open YMGap.Continuum.BF4ExactCutoffOneTransmittedDegree
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- The actual fundamental character is twice the scalar part, not a
scalar-part insertion with the character normalization omitted. -/
theorem fundamentalFaceFactor_eq_two_scalar (face : Z4Plaq) :
    bf4SurfaceActiveSpinFactor face 1 =
      polySmul 2 (correctedSlabPlaquettePolynomial 1 face).scalar := rfl

/-- Literal product of fundamental characters, retaining list multiplicity. -/
def insertedFundamentalProduct (faces : List Z4Plaq) : RatPoly :=
  faces.foldr
    (fun face total => polyMul (bf4SurfaceActiveSpinFactor face 1) total)
    polyOne

/-- Every factor uses the original corrected-slab carrier, including its
literal fallback convention.  Physical membership is required below for
the exact incidence-degree interpretation, not supplied as a support axiom. -/
theorem insertedFundamentalProduct_supported_116 (faces : List Z4Plaq) :
    SupportedQuaternionBlocks 116 (insertedFundamentalProduct faces) := by
  have h := correctedSlabSpinNetworkFaces_support 1 (fun _ => 1) faces
  rw [correctedSlabLinks_extent_one_length] at h
  simpa only [insertedFundamentalProduct, bf4SurfaceActiveSpinFactor,
    correctedSlabPlaquetteSpinFactor] using h

/-- Insertion degree is exactly the existing occurrence-counted face degree.
No `Nodup` premise or parity-mask replacement of the polynomial is used. -/
theorem insertedFundamentalProduct_blockDegree (block : Nat) :
    ∀ faces : List Z4Plaq,
      (∀ face, face ∈ faces → face ∈ boundaryCompleteSlabPlaquettes 1) →
      HasQuaternionBlockDegree block (slabFacesBlockDegree block faces)
        (insertedFundamentalProduct faces)
  | [], _ => by
      simpa only [insertedFundamentalProduct, List.foldr,
        slabFacesBlockDegree] using hasQuaternionBlockDegree_one block
  | face :: rest, hfaces => by
      simp only [insertedFundamentalProduct, List.foldr,
        slabFacesBlockDegree]
      have hface :
          HasQuaternionBlockDegree block (slabFaceBlockDegree block face)
            (bf4SurfaceActiveSpinFactor face 1) := by
        rw [fundamentalFaceFactor_eq_two_scalar]
        exact (correctedSlabPlaquetteScalar_blockDegree block
          (hfaces face List.mem_cons_self)).smul 2
      exact hface.mul
        (insertedFundamentalProduct_blockDegree block rest
          (fun other hother =>
            hfaces other (List.mem_cons_of_mem face hother)))

/-- Original heat-weighted cutoff-one action times the literal insertions.
The inserted face's original action factor is not removed or differentiated. -/
def exactCutoffOneInsertedIntegrand
    (w : Q') (faceLabel : EdgeLabelling) (faces : List Z4Plaq) : RatPoly :=
  polyMul (exactCorrectedSlabWeightedIntegrand w 1 faceLabel)
    (insertedFundamentalProduct faces)

theorem exactCutoffOneInsertedIntegrand_supported_116
    (w : Q') (faceLabel : EdgeLabelling) (faces : List Z4Plaq) :
    SupportedQuaternionBlocks 116
      (exactCutoffOneInsertedIntegrand w faceLabel faces) :=
  supported_polyMul
    (exactCorrectedSlabWeightedIntegrand_supported_116 w 1 faceLabel)
    (insertedFundamentalProduct_supported_116 faces)

/-- Total degree is selected-action incidence PLUS inserted occurrence
incidence.  This is an actual polynomial homogeneity theorem. -/
theorem exactCutoffOneInsertedIntegrand_blockDegree
    (block : Nat) (w : Q') (faceLabel : EdgeLabelling)
    (faces : List Z4Plaq)
    (hlabel : ∀ id, faceLabel id ≤ 1)
    (hfaces : ∀ face, face ∈ faces →
      face ∈ boundaryCompleteSlabPlaquettes 1) :
    HasQuaternionBlockDegree block
      (cutoffOneSlabSelectedBlockDegree block faceLabel +
        slabFacesBlockDegree block faces)
      (exactCutoffOneInsertedIntegrand w faceLabel faces) :=
  (exactCorrectedSlabWeightedIntegrand_cutoffOne_blockDegree
    block w faceLabel hlabel).mul
    (insertedFundamentalProduct_blockDegree block faces hfaces)

/-- Odd total incidence at any actual slab link annihilates the literal
inserted 116-link Haar summand.  Support and degree are produced above. -/
theorem exactCutoffOneInsertedHaar_eq_zero_of_odd_degree
    (w : Q') (faceLabel : EdgeLabelling) (faces : List Z4Plaq)
    (block : Nat) (hblock : block < 116)
    (hlabel : ∀ id, faceLabel id ≤ 1)
    (hfaces : ∀ face, face ∈ faces →
      face ∈ boundaryCompleteSlabPlaquettes 1)
    (hodd : (cutoffOneSlabSelectedBlockDegree block faceLabel +
      slabFacesBlockDegree block faces) % 2 = 1) :
    quaternionHaar 116
        (exactCutoffOneInsertedIntegrand w faceLabel faces) ≈ 0 :=
  quaternionHaar_116_eq_zero_of_odd_blockDegree block
    (cutoffOneSlabSelectedBlockDegree block faceLabel +
      slabFacesBlockDegree block faces) hblock hodd
    (exactCutoffOneInsertedIntegrand w faceLabel faces)
    (exactCutoffOneInsertedIntegrand_supported_116 w faceLabel faces)
    (exactCutoffOneInsertedIntegrand_blockDegree
      block w faceLabel faces hlabel hfaces)

/-- Two equal insertions contribute twice the incidence degree although their
parity is zero.  Zero charge does not mean an absent insertion factor. -/
theorem repeatedFace_degree_and_parity (block : Nat) (face : Z4Plaq) :
    slabFacesBlockDegree block [face, face] =
        2 * slabFaceBlockDegree block face ∧
      slabFacesBlockDegree block [face, face] % 2 = 0 := by
  simp only [slabFacesBlockDegree]
  constructor <;> omega

#print axioms fundamentalFaceFactor_eq_two_scalar
#print axioms insertedFundamentalProduct
#print axioms insertedFundamentalProduct_supported_116
#print axioms insertedFundamentalProduct_blockDegree
#print axioms exactCutoffOneInsertedIntegrand
#print axioms exactCutoffOneInsertedIntegrand_supported_116
#print axioms exactCutoffOneInsertedIntegrand_blockDegree
#print axioms exactCutoffOneInsertedHaar_eq_zero_of_odd_degree
#print axioms repeatedFace_degree_and_parity

end YMGap.Continuum.BF4ExactCutoffOneInsertedDegree
