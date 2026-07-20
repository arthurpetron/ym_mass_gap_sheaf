/-
# Outward elementary-cube face-product bridge

This leaf packages the audited radius-zero cube boundary into six genuinely
named plaquette trace summands.  The alternating outward orientation is kept
literally: reversed, standard, reversed, standard, reversed, standard.

For one opaque vertex-major Boolean assignment, the six left-associated
four-coefficient trace terms are first certified against the existing
face-major descriptor word.  The generic prefix/suffix four-row theorem then
reassociates their outer product to that word after finite-product Haar.  The
result composes with the exact twelve-link Schur contraction endpoint.

Only the six descriptor rows are checked concretely.  The depth-twenty-four
Boolean sum and the twenty-four-factor polynomial product remain opaque.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping
import YMGap.Continuum.SU2QuaternionElementaryCubeTaggedProductReconciliation

namespace YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFourFactorGrouping
open YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedFundamentalContraction
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedOccurrenceCoverage
open YMGap.Continuum.SU2QuaternionElementaryCubeTaggedProductReconciliation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence

/-! ## 1. Six oriented face rows -/

/-- One production plaquette, its selected outward orientation, and its four
cyclic vertex-major trace tags. -/
structure TaggedOrientedPlaquetteRow where
  plaquette : Z4Plaq
  orientation : FundamentalFaceOrientation
  firstTag : Nat
  secondTag : Nat
  thirdTag : Nat
  fourthTag : Nat
  deriving DecidableEq

def TaggedOrientedPlaquetteRow.tags
    (row : TaggedOrientedPlaquetteRow) : List Nat :=
  [row.firstTag, row.secondTag, row.thirdTag, row.fourthTag]

/-- Canonical `edgesOf` slot zero. -/
def TaggedOrientedPlaquetteRow.link0
    (row : TaggedOrientedPlaquetteRow) : Z4Link :=
  (row.plaquette.1, (dirsOf row.plaquette.2).1)

/-- Canonical `edgesOf` slot one. -/
def TaggedOrientedPlaquetteRow.link1
    (row : TaggedOrientedPlaquetteRow) : Z4Link :=
  (row.plaquette.1, (dirsOf row.plaquette.2).2)

/-- Canonical `edgesOf` slot two. -/
def TaggedOrientedPlaquetteRow.link2
    (row : TaggedOrientedPlaquetteRow) : Z4Link :=
  (addE row.plaquette.1 (dirsOf row.plaquette.2).2,
    (dirsOf row.plaquette.2).1)

/-- Canonical `edgesOf` slot three. -/
def TaggedOrientedPlaquetteRow.link3
    (row : TaggedOrientedPlaquetteRow) : Z4Link :=
  (addE row.plaquette.1 (dirsOf row.plaquette.2).1,
    (dirsOf row.plaquette.2).2)

def TaggedOrientedPlaquetteRow.block0
    (row : TaggedOrientedPlaquetteRow) : Nat :=
  adjacentEvenActiveLinkIndex 0 row.link0

def TaggedOrientedPlaquetteRow.block1
    (row : TaggedOrientedPlaquetteRow) : Nat :=
  adjacentEvenActiveLinkIndex 0 row.link1

def TaggedOrientedPlaquetteRow.block2
    (row : TaggedOrientedPlaquetteRow) : Nat :=
  adjacentEvenActiveLinkIndex 0 row.link2

def TaggedOrientedPlaquetteRow.block3
    (row : TaggedOrientedPlaquetteRow) : Nat :=
  adjacentEvenActiveLinkIndex 0 row.link3

/-- The bottom `p01` face, outward-reversed. -/
def radiusZeroElementaryCubeOutwardFaceRow0 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 0, 0, 1), .p01), .reversed, 0, 9, 6, 3⟩

/-- The bottom `p02` face, outward-standard. -/
def radiusZeroElementaryCubeOutwardFaceRow1 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 0, 0, 1), .p02), .standard, 1, 4, 15, 12⟩

/-- The bottom `p12` face, outward-reversed. -/
def radiusZeroElementaryCubeOutwardFaceRow2 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 0, 0, 1), .p12), .reversed, 2, 13, 21, 10⟩

/-- The translated `p01` face, outward-standard. -/
def radiusZeroElementaryCubeOutwardFaceRow3 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 0, 1, 1), .p01), .standard, 14, 16, 18, 22⟩

/-- The translated `p02` face, outward-reversed. -/
def radiusZeroElementaryCubeOutwardFaceRow4 :
    TaggedOrientedPlaquetteRow :=
  ⟨((0, 1, 0, 1), .p02), .reversed, 11, 23, 19, 7⟩

/-- The translated `p12` face, outward-standard. -/
def radiusZeroElementaryCubeOutwardFaceRow5 :
    TaggedOrientedPlaquetteRow :=
  ⟨((1, 0, 0, 1), .p12), .standard, 5, 8, 20, 17⟩

/-- The six face rows in the audited production face order. -/
def radiusZeroElementaryCubeOutwardFaceRows :
    List TaggedOrientedPlaquetteRow :=
  [radiusZeroElementaryCubeOutwardFaceRow0,
   radiusZeroElementaryCubeOutwardFaceRow1,
   radiusZeroElementaryCubeOutwardFaceRow2,
   radiusZeroElementaryCubeOutwardFaceRow3,
   radiusZeroElementaryCubeOutwardFaceRow4,
   radiusZeroElementaryCubeOutwardFaceRow5]

theorem radiusZeroElementaryCubeOutwardFaceRows_length :
    radiusZeroElementaryCubeOutwardFaceRows.length = 6 := by
  decide

/-- The row metadata is literally the previously audited outward face list. -/
theorem radiusZeroElementaryCubeOutwardFaceRows_faces :
    radiusZeroElementaryCubeOutwardFaceRows.map (fun row =>
        (row.plaquette, row.orientation)) =
      radiusZeroElementaryCubeOutwardFaces := by
  decide

/-- The row tags are literally the previously audited six cyclic tag rows. -/
theorem radiusZeroElementaryCubeOutwardFaceRows_tags :
    radiusZeroElementaryCubeOutwardFaceRows.map
        TaggedOrientedPlaquetteRow.tags =
      radiusZeroElementaryCubeFaceTagCycles := by
  decide

/-! ## 2. Named trace terms and exact descriptor chunks -/

def TaggedOrientedPlaquetteRow.firstCoefficient
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      forwardFundamentalCoefficient row.block0
        (cubeTagValue assignment row.firstTag)
        (cubeTagValue assignment row.secondTag)
  | .reversed =>
      forwardFundamentalCoefficient row.block1
        (cubeTagValue assignment row.firstTag)
        (cubeTagValue assignment row.secondTag)

def TaggedOrientedPlaquetteRow.secondCoefficient
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      forwardFundamentalCoefficient row.block3
        (cubeTagValue assignment row.secondTag)
        (cubeTagValue assignment row.thirdTag)
  | .reversed =>
      forwardFundamentalCoefficient row.block2
        (cubeTagValue assignment row.secondTag)
        (cubeTagValue assignment row.thirdTag)

def TaggedOrientedPlaquetteRow.thirdCoefficient
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      reverseFundamentalCoefficient row.block2
        (cubeTagValue assignment row.thirdTag)
        (cubeTagValue assignment row.fourthTag)
  | .reversed =>
      reverseFundamentalCoefficient row.block3
        (cubeTagValue assignment row.thirdTag)
        (cubeTagValue assignment row.fourthTag)

def TaggedOrientedPlaquetteRow.fourthCoefficient
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    ComplexRatPoly :=
  match row.orientation with
  | .standard =>
      reverseFundamentalCoefficient row.block1
        (cubeTagValue assignment row.fourthTag)
        (cubeTagValue assignment row.firstTag)
  | .reversed =>
      reverseFundamentalCoefficient row.block0
        (cubeTagValue assignment row.fourthTag)
        (cubeTagValue assignment row.firstTag)

/-- One outward face as the established left-associated four-factor trace
summand. -/
def TaggedOrientedPlaquetteRow.traceTerm
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    ComplexRatPoly :=
  complexRatPolyFourFactorRowPolynomial
    (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
    (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
    (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
    (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)
    row

/-- Each abstract row term is definitionally the already established named
standard or reversed plaquette trace term with the canonical four edge
blocks. -/
theorem TaggedOrientedPlaquetteRow.traceTerm_eq_named
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    row.traceTerm assignment =
      match row.orientation with
      | .standard =>
          standardPlaquetteTraceTerm
            row.block0 row.block1 row.block2 row.block3
            (cubeTagValue assignment row.firstTag)
            (cubeTagValue assignment row.secondTag)
            (cubeTagValue assignment row.thirdTag)
            (cubeTagValue assignment row.fourthTag)
      | .reversed =>
          reversedPlaquetteTraceTerm
            row.block0 row.block1 row.block2 row.block3
            (cubeTagValue assignment row.firstTag)
            (cubeTagValue assignment row.secondTag)
            (cubeTagValue assignment row.thirdTag)
            (cubeTagValue assignment row.fourthTag) := by
  obtain ⟨plaquette, orientation, firstTag, secondTag, thirdTag, fourthTag⟩ := row
  cases orientation <;> rfl

/-- The four descriptor slots belonging to one face row. -/
def TaggedOrientedPlaquetteRow.coefficientDescriptors
    (row : TaggedOrientedPlaquetteRow) : List CubeCoefficientDescriptor :=
  match row.orientation with
  | .standard =>
      [⟨row.link0, true, row.firstTag, row.secondTag⟩,
       ⟨row.link3, true, row.secondTag, row.thirdTag⟩,
       ⟨row.link2, false, row.thirdTag, row.fourthTag⟩,
       ⟨row.link1, false, row.fourthTag, row.firstTag⟩]
  | .reversed =>
      [⟨row.link1, true, row.firstTag, row.secondTag⟩,
       ⟨row.link2, true, row.secondTag, row.thirdTag⟩,
       ⟨row.link3, false, row.thirdTag, row.fourthTag⟩,
       ⟨row.link0, false, row.fourthTag, row.firstTag⟩]

/-- Mapping one face's four descriptors through an opaque assignment gives
exactly its standard/reversed coefficient row. -/
theorem TaggedOrientedPlaquetteRow.factors_eq_descriptors_map
    (assignment : List Bool) (row : TaggedOrientedPlaquetteRow) :
    complexRatPolyFourFactorRowFactors
        (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
        (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
        (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
        (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)
        row =
      row.coefficientDescriptors.map
        (fun descriptor => descriptor.coefficient assignment) := by
  obtain ⟨plaquette, orientation, firstTag, secondTag, thirdTag, fourthTag⟩ := row
  cases orientation <;> rfl

/-- Descriptor-level face-chunk audit.  Flattening the six four-slot rows is
literally the previously certified face-major descriptor list. -/
theorem radiusZeroElementaryCubeOutwardFaceDescriptorRows_flatten :
    radiusZeroElementaryCubeOutwardFaceRows.flatMap
        TaggedOrientedPlaquetteRow.coefficientDescriptors =
      radiusZeroElementaryCubeFaceMajorCoefficientDescriptors := by
  decide

private theorem flatMap_fourFactorRows_eq_map_flatMap_descriptors
    (assignment : List Bool) :
    ∀ rows : List TaggedOrientedPlaquetteRow,
      rows.flatMap
          (complexRatPolyFourFactorRowFactors
            (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
            (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
            (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
            (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)) =
        (rows.flatMap
            TaggedOrientedPlaquetteRow.coefficientDescriptors).map
          (fun descriptor => descriptor.coefficient assignment)
  | [] => rfl
  | row :: rows => by
      simp only [List.flatMap_cons, List.map_append]
      rw [TaggedOrientedPlaquetteRow.factors_eq_descriptors_map,
        flatMap_fourFactorRows_eq_map_flatMap_descriptors assignment rows]

/-- The flattened six-row coefficient word is exactly the face-major word
already reconciled with the twelve-link contraction schedule. -/
theorem radiusZeroElementaryCubeOutwardFaceCoefficientRows_eq_faceMajorWord
    (assignment : List Bool) :
    radiusZeroElementaryCubeOutwardFaceRows.flatMap
        (complexRatPolyFourFactorRowFactors
          (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
          (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
          (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
          (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)) =
      radiusZeroElementaryCubeFaceMajorCoefficientWord assignment := by
  rw [flatMap_fourFactorRows_eq_map_flatMap_descriptors assignment,
    radiusZeroElementaryCubeOutwardFaceDescriptorRows_flatten]
  rfl

/-! ## 3. Six-face Haar endpoint -/

/-- The six orientation-specific, left-associated plaquette trace summands. -/
def radiusZeroElementaryCubeOutwardFaceTraceTerms
    (assignment : List Bool) : List ComplexRatPoly :=
  radiusZeroElementaryCubeOutwardFaceRows.map
    (TaggedOrientedPlaquetteRow.traceTerm assignment)

/-- Their chosen tail-first outer product. -/
def radiusZeroElementaryCubeOutwardFaceTraceProduct
    (assignment : List Bool) : ComplexRatPoly :=
  complexRatPolyProduct
    (radiusZeroElementaryCubeOutwardFaceTraceTerms assignment)

/-- Grouping the face-major word into the six established left-associated
plaquette terms preserves finite-product Haar. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutwardFaceTraceProduct_eq_faceMajor
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubeOutwardFaceTraceProduct assignment))
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (complexRatPolyProduct
          (radiusZeroElementaryCubeFaceMajorCoefficientWord assignment))) := by
  have h :=
    finiteProductHaarComplex_fourFactorRowProducts_eq_flatMap
      (adjacentEvenActiveLinks 0).length
      (TaggedOrientedPlaquetteRow.firstCoefficient assignment)
      (TaggedOrientedPlaquetteRow.secondCoefficient assignment)
      (TaggedOrientedPlaquetteRow.thirdCoefficient assignment)
      (TaggedOrientedPlaquetteRow.fourthCoefficient assignment)
      radiusZeroElementaryCubeOutwardFaceRows
  rw [radiusZeroElementaryCubeOutwardFaceCoefficientRows_eq_faceMajorWord
    assignment] at h
  exact h

/-- **Exact outward six-face fixed-assignment endpoint.**  The product of the
six orientation-specific named plaquette summands contracts to the resolved
crossed-Schur-delta value. -/
theorem finiteProductHaarComplex_radiusZeroElementaryCubeOutwardFaceTraceProduct_eq_schurDeltaValue
    (assignment : List Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex
        (adjacentEvenActiveLinks 0).length
        (radiusZeroElementaryCubeOutwardFaceTraceProduct assignment))
      (radiusZeroElementaryCubeSchurDeltaValue assignment) :=
  rationalComplexEqv_trans
    (finiteProductHaarComplex_radiusZeroElementaryCubeOutwardFaceTraceProduct_eq_faceMajor
      assignment)
    (finiteProductHaarComplex_radiusZeroElementaryCubeFaceMajorCoefficientProduct_eq_schurDeltaValue
      assignment)

#print axioms radiusZeroElementaryCubeOutwardFaceRows_faces
#print axioms radiusZeroElementaryCubeOutwardFaceRows_tags
#print axioms TaggedOrientedPlaquetteRow.traceTerm_eq_named
#print axioms radiusZeroElementaryCubeOutwardFaceDescriptorRows_flatten
#print axioms radiusZeroElementaryCubeOutwardFaceCoefficientRows_eq_faceMajorWord
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutwardFaceTraceProduct_eq_faceMajor
#print axioms finiteProductHaarComplex_radiusZeroElementaryCubeOutwardFaceTraceProduct_eq_schurDeltaValue

end YMGap.Continuum.SU2QuaternionElementaryCubeOutwardFaceProductBridge
