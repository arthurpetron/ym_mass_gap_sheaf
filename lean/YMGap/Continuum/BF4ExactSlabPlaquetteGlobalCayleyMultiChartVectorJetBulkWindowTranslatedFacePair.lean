/-
# Literal target transport of one selected vector-jet face pair

The two local factors in the exact selected covariance expansion are moved
through the arbitrary-extent slab placement and then represented by the
literal shifted target plaquette characters.  Each target factor retains the
same explicit interval cap and its exact four-link locality.  Finite and
cutoff-removed covariances are pinned under the translated selected action.

This does not add any exterior target action face.  It constructs no common
connected carrier for the separated pair, no insertion telescope, no summed
boundary estimate, and no continuum or mass-gap conclusion.
-/

import YMGap.Continuum.BF4ExactSlabTranslatedSelectedCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
  (sweptProduct_interval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTranslatedProbe
  (sweptProduct_zero_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval (probeCap)
open YMGap.Continuum.BF4ExactSlabTemporalSweep (sweptProduct swept_zero)
open YMGap.Continuum.BF4ExactSlabTranslatedHaarEmbedding
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedAction
open YMGap.Continuum.BF4ExactSlabTranslatedSelectedCovariance
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
  (bulkSourceFaces)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-- Concrete placement at the origin of a larger arbitrary target slab. -/
def zeroPlacement (s n L target : Nat)
    (hroom : originalBulkVectorQuadraticJetExtent s n L ≤ target) : Placement where
  source := originalBulkVectorQuadraticJetExtent s n L
  target := target
  space := 0
  time := 0
  space_room := by simpa only [Nat.add_zero] using hroom
  time_room := by simpa only [Nat.add_zero] using hroom

/-- The literal target face supporting one translated local vector factor. -/
def translatedOriginalBulkVectorQuadraticJetPlacedFace
    (P : Placement) (n offset : Nat) (face : Z4Plaq) : Z4Plaq :=
  shiftFace P.space P.time
    (originalBulkVectorQuadraticJetPlacedFace n offset face)

/-- One literal translated target vector-character factor. -/
def translatedOriginalBulkVectorQuadraticJetFacePlaced
    (P : Placement) (n offset : Nat) (face : Z4Plaq) : RatPoly :=
  sweptProduct P.target 0
    [(translatedOriginalBulkVectorQuadraticJetPlacedFace P n offset face,
      vectorQuadraticJetTerms)]

/-- The canonical selected source IDs, viewed in a placement whose source is
the canonical vector-jet slab. -/
theorem originalBulkVectorQuadraticJetIds_physical_at_placement
    (P : Placement) (s n L : Nat)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L) :
    ∀ id, id ∈ originalBulkVectorQuadraticJetIds s n L →
      id ∈ slabPhysicalFaceEdges P.source := by
  intro id hid
  rw [hsource]
  exact originalBulkVectorQuadraticJetIds_physical s n L id hid

/-- The shifted local face is a physical target plaquette. -/
theorem translatedOriginalBulkVectorQuadraticJetPlacedFace_physical
    (P : Placement) (s n offset L : Nat) (face : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hface : face ∈ bulkSourceFaces s) (hoffset : offset ≤ L) :
    translatedOriginalBulkVectorQuadraticJetPlacedFace P n offset face ∈
      boundaryCompleteSlabPlaquettes P.target := by
  apply shiftFace_mem P.space_room P.time_room
  rw [hsource]
  exact originalBulkVectorQuadraticJetPlacedFace_physical
    s n offset L face hface hoffset

/-- The block-map image is represented by the literal shifted target factor. -/
theorem translatedOriginalBulkVectorQuadraticJetFace_pin
    (P : Placement) (s n offset L : Nat) (face : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hface : face ∈ bulkSourceFaces s) (hoffset : offset ≤ L) :
    QuaternionPrefixPolynomialEqv
      (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial
        (originalBulkVectorQuadraticJetFacePlaced s n offset L face))
      (translatedOriginalBulkVectorQuadraticJetFacePlaced P n offset face) := by
  rw [originalBulkVectorQuadraticJetFacePlaced_eq_sweptProduct]
  have hpin := sweptProduct_zero_pin P
    [(originalBulkVectorQuadraticJetPlacedFace n offset face,
      vectorQuadraticJetTerms)] (by
        intro factor hfactor
        have hfactorEq := List.mem_singleton.mp hfactor
        subst factor
        rw [hsource]
        exact originalBulkVectorQuadraticJetPlacedFace_physical
          s n offset L face hface hoffset)
  rw [← hsource]
  change QuaternionPrefixPolynomialEqv
    (boundaryCompleteSlabLinks P.target).length
    (P.embedding.polynomial
      (sweptProduct P.source 0
        [(originalBulkVectorQuadraticJetPlacedFace n offset face,
          vectorQuadraticJetTerms)]))
    (sweptProduct P.target 0
      [(shiftFace P.space P.time
          (originalBulkVectorQuadraticJetPlacedFace n offset face),
        vectorQuadraticJetTerms)])
  exact hpin

/-- The translated target factor retains the exact source cap. -/
def translatedOriginalBulkVectorQuadraticJetFace_interval
    (P : Placement) (s n offset L : Nat) (face : Z4Plaq)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hface : face ∈ bulkSourceFaces s) (hoffset : offset ≤ L) :
    Interval (boundaryCompleteSlabLinks P.target).length
      (translatedOriginalBulkVectorQuadraticJetFacePlaced P n offset face)
      (originalBulkVectorQuadraticJetFaceCap n offset face) := by
  have hinterval := sweptProduct_interval P.target
    [(translatedOriginalBulkVectorQuadraticJetPlacedFace P n offset face,
      vectorQuadraticJetTerms)] (by
        intro factor hfactor
        have hfactorEq := List.mem_singleton.mp hfactor
        subst factor
        exact translatedOriginalBulkVectorQuadraticJetPlacedFace_physical
          P s n offset L face hsource hface hoffset)
  simpa [translatedOriginalBulkVectorQuadraticJetFacePlaced,
    originalBulkVectorQuadraticJetFaceCap, probeCap] using hinterval

/-- The translated factor is local to exactly the shifted face's four links. -/
theorem translatedOriginalBulkVectorQuadraticJetFace_local
    (P : Placement) (n offset : Nat) (face : Z4Plaq) :
    LinkLocal P.target
      (edgesOf
        (translatedOriginalBulkVectorQuadraticJetPlacedFace P n offset face))
      (translatedOriginalBulkVectorQuadraticJetFacePlaced P n offset face) := by
  unfold translatedOriginalBulkVectorQuadraticJetFacePlaced
  rw [swept_zero]
  apply BlockLocal.fold
  intro factor hfactor
  have hfactorEq := List.mem_singleton.mp hfactor
  subst factor
  apply BlockLocal.finiteSum
  intro term _
  exact ((face_scalar_local P.target
    (translatedOriginalBulkVectorQuadraticJetPlacedFace P n offset face)).character
      term.1).smul term.2

/-- Exact finite selected covariance transport for two literal local target
factors. -/
theorem finiteCovariance_translatedFacePair_pin
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s n L leftOffset rightOffset : Nat)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s)
    (stage : Nat) :
    finiteCovariance w hw0 hw1 P.target
        (selectedIds P (originalBulkVectorQuadraticJetIds s n L))
        (selectedIds_physical P (originalBulkVectorQuadraticJetIds s n L)
          (originalBulkVectorQuadraticJetIds_physical_at_placement
            P s n L hsource))
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n rightOffset rightFace)
        stage ≈
      finiteCovariance w hw0 hw1 P.source
        (originalBulkVectorQuadraticJetIds s n L)
        (originalBulkVectorQuadraticJetIds_physical_at_placement
          P s n L hsource)
        (originalBulkVectorQuadraticJetFacePlaced
          s n leftOffset L leftFace)
        (originalBulkVectorQuadraticJetFacePlaced
          s n rightOffset L rightFace)
        stage := by
  have hleftSource := originalBulkVectorQuadraticJetFace_interval
    s n leftOffset L leftFace hleftFace hleftOffset
  have hrightSource := originalBulkVectorQuadraticJetFace_interval
    s n rightOffset L rightFace hrightFace hrightOffset
  have hleftSourceP : Interval (boundaryCompleteSlabLinks P.source).length
      (originalBulkVectorQuadraticJetFacePlaced s n leftOffset L leftFace)
      (originalBulkVectorQuadraticJetFaceCap n leftOffset leftFace) := by
    simpa only [hsource] using hleftSource
  have hrightSourceP : Interval (boundaryCompleteSlabLinks P.source).length
      (originalBulkVectorQuadraticJetFacePlaced s n rightOffset L rightFace)
      (originalBulkVectorQuadraticJetFaceCap n rightOffset rightFace) := by
    simpa only [hsource] using hrightSource
  have hleftTarget := translatedOriginalBulkVectorQuadraticJetFace_interval
    P s n leftOffset L leftFace hsource hleftFace hleftOffset
  have hrightTarget := translatedOriginalBulkVectorQuadraticJetFace_interval
    P s n rightOffset L rightFace hsource hrightFace hrightOffset
  exact finiteCovariance_pin_of_prefix P hw0 hw1
    (originalBulkVectorQuadraticJetIds s n L)
    (originalBulkVectorQuadraticJetIds_physical_at_placement P s n L hsource)
    (originalBulkVectorQuadraticJetFacePlaced s n leftOffset L leftFace)
    (originalBulkVectorQuadraticJetFacePlaced s n rightOffset L rightFace)
    hleftSourceP.support hrightSourceP.support
    (translatedOriginalBulkVectorQuadraticJetFacePlaced P n leftOffset leftFace)
    (translatedOriginalBulkVectorQuadraticJetFacePlaced P n rightOffset rightFace)
    hleftTarget.support hrightTarget.support
    (translatedOriginalBulkVectorQuadraticJetFace_pin
      P s n leftOffset L leftFace hsource hleftFace hleftOffset)
    (translatedOriginalBulkVectorQuadraticJetFace_pin
      P s n rightOffset L rightFace hsource hrightFace hrightOffset)
    stage

/-- The same literal pair transport after fixed-volume cutoff removal. -/
theorem covariance_translatedFacePair_pin
    (P : Placement) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (s n L leftOffset rightOffset : Nat)
    (hsource : P.source = originalBulkVectorQuadraticJetExtent s n L)
    (hleftOffset : leftOffset ≤ L) (hrightOffset : rightOffset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleftFace : leftFace ∈ bulkSourceFaces s)
    (hrightFace : rightFace ∈ bulkSourceFaces s) :
    Equiv
      (covariance w hw0 hw1 P.target
        (selectedIds P (originalBulkVectorQuadraticJetIds s n L))
        (selectedIds_physical P (originalBulkVectorQuadraticJetIds s n L)
          (originalBulkVectorQuadraticJetIds_physical_at_placement
            P s n L hsource))
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n leftOffset leftFace)
        (translatedOriginalBulkVectorQuadraticJetFacePlaced
          P n rightOffset rightFace))
      (covariance w hw0 hw1 P.source
        (originalBulkVectorQuadraticJetIds s n L)
        (originalBulkVectorQuadraticJetIds_physical_at_placement
          P s n L hsource)
        (originalBulkVectorQuadraticJetFacePlaced
          s n leftOffset L leftFace)
        (originalBulkVectorQuadraticJetFacePlaced
          s n rightOffset L rightFace)) := by
  have hleftSource := originalBulkVectorQuadraticJetFace_interval
    s n leftOffset L leftFace hleftFace hleftOffset
  have hrightSource := originalBulkVectorQuadraticJetFace_interval
    s n rightOffset L rightFace hrightFace hrightOffset
  have hleftSourceP : Interval (boundaryCompleteSlabLinks P.source).length
      (originalBulkVectorQuadraticJetFacePlaced s n leftOffset L leftFace)
      (originalBulkVectorQuadraticJetFaceCap n leftOffset leftFace) := by
    simpa only [hsource] using hleftSource
  have hrightSourceP : Interval (boundaryCompleteSlabLinks P.source).length
      (originalBulkVectorQuadraticJetFacePlaced s n rightOffset L rightFace)
      (originalBulkVectorQuadraticJetFaceCap n rightOffset rightFace) := by
    simpa only [hsource] using hrightSource
  have hleftTarget := translatedOriginalBulkVectorQuadraticJetFace_interval
    P s n leftOffset L leftFace hsource hleftFace hleftOffset
  have hrightTarget := translatedOriginalBulkVectorQuadraticJetFace_interval
    P s n rightOffset L rightFace hsource hrightFace hrightOffset
  exact covariance_pin_of_prefix P hw0 hw1
    (originalBulkVectorQuadraticJetIds s n L)
    (originalBulkVectorQuadraticJetIds_physical_at_placement P s n L hsource)
    (originalBulkVectorQuadraticJetFacePlaced s n leftOffset L leftFace)
    (originalBulkVectorQuadraticJetFacePlaced s n rightOffset L rightFace)
    hleftSourceP.support hrightSourceP.support
    (translatedOriginalBulkVectorQuadraticJetFacePlaced P n leftOffset leftFace)
    (translatedOriginalBulkVectorQuadraticJetFacePlaced P n rightOffset rightFace)
    hleftTarget.support hrightTarget.support
    (translatedOriginalBulkVectorQuadraticJetFace_pin
      P s n leftOffset L leftFace hsource hleftFace hleftOffset)
    (translatedOriginalBulkVectorQuadraticJetFace_pin
      P s n rightOffset L rightFace hsource hrightFace hrightOffset)

end YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.zeroPlacement
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.translatedOriginalBulkVectorQuadraticJetPlacedFace
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.translatedOriginalBulkVectorQuadraticJetFacePlaced
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.originalBulkVectorQuadraticJetIds_physical_at_placement
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.translatedOriginalBulkVectorQuadraticJetPlacedFace_physical
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.translatedOriginalBulkVectorQuadraticJetFace_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.translatedOriginalBulkVectorQuadraticJetFace_interval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.translatedOriginalBulkVectorQuadraticJetFace_local
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.finiteCovariance_translatedFacePair_pin
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGlobalCayleyMultiChartVectorJetBulkWindowTranslatedFacePair.covariance_translatedFacePair_pin
