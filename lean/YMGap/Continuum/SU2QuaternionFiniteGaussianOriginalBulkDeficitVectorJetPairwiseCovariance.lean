/-
# Pairwise selected covariance and endpoint mismatch for the original vector jet

The physical-character vector-jet schedule is expanded into its exact finite
face-pair covariance sum.  Each local factor has a checked interval and literal
four-link support, so the existing selected two-probe distance estimate applies
without changing the ORIGINAL action.  A sharp global interval

  0 <= vectorJet <= sum bulk coefficients

also pays both selected-mean mismatches by endpoint mixing.

No absolute geometric convolution, ORIGINAL-to-FREE response comparison,
neighboring sign, cutoff removal, continuum Hamiltonian, or Clay mass gap is
proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
import YMGap.Continuum.QuaternionHaarPolynomialInterval

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate (adjustedCoreRate)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal face_scalar_local)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds_nodup)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (middleRatio_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl (sweptProduct_interval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
  (endpoint_mean_lags_commonTail endpoint_means_eqv lower_endpoint_mean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
  (windowRatio_carrier_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (placeWindowProbes)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
  (placedSpan sourceSpan)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (singletonCarrier)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance
  (finite_covariance_distance_bound)
open YMGap.Continuum.BF4ExactSlabTemporalSweep (sweptProduct swept_zero)
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (distanceBudget)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval (probeCap)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSizeGeometricSum (entropyRate)
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRatio heatRemainderBound)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCentering
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitCenteredRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPhysicalFaceEdges)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Literal quarter profile weight multiplying one local vector character. -/
def originalBulkVectorQuadraticJetFaceWeight
    (s : Nat) (hs : 0 < s) (face : Z4Plaq) : Q' :=
  Q'.mkPos 1 4 (by decide) * bulkSourceCoefficient s hs face

/-- One unscaled local vector-character factor in the canonical slab. -/
def originalBulkVectorQuadraticJetFacePlaced
    (s n offset L : Nat) (face : Z4Plaq) : RatPoly :=
  sweptProduct (originalBulkVectorQuadraticJetExtent s n L) 0
    (placeWindowProbes n (vectorQuadraticJetSchedule offset face))

/-- The complete placed vector jet is its literal weighted face sum. -/
theorem originalBulkVectorQuadraticJetPlaced_face_sum
    (s : Nat) (hs : 0 < s) (n offset L : Nat) :
    originalBulkVectorQuadraticJetPlaced s hs n offset L =
      finitePolySum
        (fun face => polySmul
          (originalBulkVectorQuadraticJetFaceWeight s hs face)
          (originalBulkVectorQuadraticJetFacePlaced s n offset L face))
        (bulkSourceFaces s) := by
  unfold originalBulkVectorQuadraticJetPlaced placedSpan
    originalBulkVectorQuadraticJetSchedule
    originalBulkVectorQuadraticJetFaceWeight
    originalBulkVectorQuadraticJetFacePlaced
  rw [YMGap.Continuum.PolynomialWeightedSumBounds.sum_map]
  rfl

/-- Actual chronological face supporting one local vector factor. -/
def originalBulkVectorQuadraticJetPlacedFace
    (n offset : Nat) (face : Z4Plaq) : Z4Plaq :=
  timeShiftPlaquette (n + offset) face

/-- Exact interval cap generated by the fixed local character list. -/
def originalBulkVectorQuadraticJetFaceCap
    (n offset : Nat) (face : Z4Plaq) : Q' :=
  probeCap
    [(originalBulkVectorQuadraticJetPlacedFace n offset face,
      vectorQuadraticJetTerms)]

private theorem facePlaced_schedule
    (s n offset L : Nat) (face : Z4Plaq) :
    originalBulkVectorQuadraticJetFacePlaced s n offset L face =
      sweptProduct (originalBulkVectorQuadraticJetExtent s n L) 0
        [(originalBulkVectorQuadraticJetPlacedFace n offset face,
          vectorQuadraticJetTerms)] := by
  unfold originalBulkVectorQuadraticJetFacePlaced
    vectorQuadraticJetSchedule originalBulkVectorQuadraticJetPlacedFace
    placeWindowProbes YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.placeProbes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_singleton]

/-- Literal singleton schedule for one local vector factor. -/
theorem originalBulkVectorQuadraticJetFacePlaced_eq_sweptProduct
    (s n offset L : Nat) (face : Z4Plaq) :
    originalBulkVectorQuadraticJetFacePlaced s n offset L face =
      sweptProduct (originalBulkVectorQuadraticJetExtent s n L) 0
        [(originalBulkVectorQuadraticJetPlacedFace n offset face,
          vectorQuadraticJetTerms)] :=
  facePlaced_schedule s n offset L face

/-- The chronological face used by one local vector factor is physical in
the canonical source slab. -/
theorem originalBulkVectorQuadraticJetPlacedFace_physical
    (s n offset L : Nat) (face : Z4Plaq)
    (hface : face ∈ bulkSourceFaces s) (hoffset : offset ≤ L) :
    originalBulkVectorQuadraticJetPlacedFace n offset face ∈
      boundaryCompleteSlabPlaquettes
        (originalBulkVectorQuadraticJetExtent s n L) := by
  apply YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_shift_physical
      (width := s * s) (time := n + offset)
  · unfold originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  · unfold originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  · exact bulkSourceFace_mem_spatialFaces_square hface

/-- Volume-independent interval for one actual placed vector factor. -/
def originalBulkVectorQuadraticJetFace_interval
    (s n offset L : Nat) (face : Z4Plaq)
    (hface : face ∈ bulkSourceFaces s) (hoffset : offset ≤ L) :
    Interval
      (boundaryCompleteSlabLinks
        (originalBulkVectorQuadraticJetExtent s n L)).length
      (originalBulkVectorQuadraticJetFacePlaced s n offset L face)
      (originalBulkVectorQuadraticJetFaceCap n offset face) := by
  rw [facePlaced_schedule]
  apply sweptProduct_interval
  intro factor hfactor
  have hfactorEq := List.mem_singleton.mp hfactor
  subst factor
  apply YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe.placeWindowProbes_physical
      (width := s * s) (start := n) (L := L)
      (extent := originalBulkVectorQuadraticJetExtent s n L)
      (fs := vectorQuadraticJetSchedule offset face)
  · unfold originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  · unfold originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  · intro entry hentry
    have hentryEq := List.mem_singleton.mp hentry
    subst entry
    exact hoffset
  · intro entry hentry localFactor hlocalFactor
    have hentryEq := List.mem_singleton.mp hentry
    subst entry
    have hlocalEq := List.mem_singleton.mp hlocalFactor
    subst localFactor
    exact bulkSourceFace_mem_spatialFaces_square hface
  · exact List.mem_singleton.mpr rfl

/-- Literal support of one local vector factor is its placed face's four
links. -/
theorem originalBulkVectorQuadraticJetFace_local
    (s n offset L : Nat) (face : Z4Plaq) :
    LinkLocal (originalBulkVectorQuadraticJetExtent s n L)
      (edgesOf (originalBulkVectorQuadraticJetPlacedFace n offset face))
      (originalBulkVectorQuadraticJetFacePlaced s n offset L face) := by
  rw [facePlaced_schedule, swept_zero]
  apply BlockLocal.fold
  intro factor hfactor
  have hfactorEq := List.mem_singleton.mp hfactor
  subst factor
  apply BlockLocal.finiteSum
  intro term _
  exact ((face_scalar_local
    (originalBulkVectorQuadraticJetExtent s n L)
    (originalBulkVectorQuadraticJetPlacedFace n offset face)).character term.1).smul term.2

/-- Every pair in the exact vector expansion satisfies the selected-action
distance estimate with singleton plaquette carriers. -/
theorem originalBulkVectorQuadraticJetFace_covariance_distance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hsRate : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s : Nat) (stage n L offset : Nat) (hoffset : offset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleft : leftFace ∈ bulkSourceFaces s)
    (hright : rightFace ∈ bulkSourceFaces s) :
    Q'.abs
        (finiteCovariance w hw0 hw1
          (originalBulkVectorQuadraticJetExtent s n L)
          (originalBulkVectorQuadraticJetIds s n L)
          (originalBulkVectorQuadraticJetIds_physical s n L)
          (originalBulkVectorQuadraticJetFacePlaced s n offset L leftFace)
          (originalBulkVectorQuadraticJetFacePlaced s n offset L rightFace)
          stage) ≤
      distanceBudget
        (singletonCarrier
          (originalBulkVectorQuadraticJetPlacedFace n offset leftFace))
        (singletonCarrier
          (originalBulkVectorQuadraticJetPlacedFace n offset rightFace))
        w hd hsRate
        (originalBulkVectorQuadraticJetFaceCap n offset leftFace)
        (originalBulkVectorQuadraticJetFaceCap n offset rightFace) := by
  apply finite_covariance_distance_bound hw0 hw1 hsmall hd hsRate
    (originalBulkVectorQuadraticJetExtent s n L)
    (originalBulkVectorQuadraticJetIds s n L)
    (by
      unfold originalBulkVectorQuadraticJetIds
        originalBulkScalarSquareRemainderIds
      exact chainIds_nodup _ _ _ _)
    (originalBulkVectorQuadraticJetIds_physical s n L)
    (originalBulkVectorQuadraticJetFacePlaced s n offset L leftFace)
    (originalBulkVectorQuadraticJetFacePlaced s n offset L rightFace)
    (originalBulkVectorQuadraticJetFaceCap n offset leftFace)
    (originalBulkVectorQuadraticJetFaceCap n offset rightFace)
    (originalBulkVectorQuadraticJetFace_interval
      s n offset L leftFace hleft hoffset)
    (originalBulkVectorQuadraticJetFace_interval
      s n offset L rightFace hright hoffset)
    (edgesOf (originalBulkVectorQuadraticJetPlacedFace n offset leftFace))
    (edgesOf (originalBulkVectorQuadraticJetPlacedFace n offset rightFace))
    (singletonCarrier
      (originalBulkVectorQuadraticJetPlacedFace n offset leftFace))
    (singletonCarrier
      (originalBulkVectorQuadraticJetPlacedFace n offset rightFace))
    (originalBulkVectorQuadraticJetFace_local s n offset L leftFace)
    (originalBulkVectorQuadraticJetFace_local s n offset L rightFace)
    stage

/-- Sharp cap for the complete vector jet. -/
def originalBulkVectorQuadraticJetCap (s : Nat) (hs : 0 < s) : Q' :=
  originalBulkCoefficientSum s hs

/-- One plaquette vector jet lies constructively in `[0,1]`. -/
def plaquetteVectorQuadraticJet_interval
    (width : Nat) (face : Z4Plaq) :
    Interval (N width) (plaquetteVectorQuadraticJet width face) 1 := by
  let q := plaquette width face
  let jet := plaquetteVectorQuadraticJet width face
  have hq := plaquette_supported width (N width) (Nat.le_refl _) face
  have hjetSupport : SupportedQuaternionBlocks (N width) jet := by
    unfold jet plaquetteVectorQuadraticJet
    exact supported_add (supported_polyMul hq.iPart hq.iPart)
      (supported_add (supported_polyMul hq.jPart hq.jPart)
        (supported_polyMul hq.kPart hq.kPart))
  have hjetCertificate : Certificate (N width) jet := by
    unfold jet plaquetteVectorQuadraticJet
    exact (Certificate.square _ hq.iPart).add
      ((Certificate.square _ hq.jPart).add
        (Certificate.square _ hq.kPart))
  refine
    { support := hjetSupport
      nonnegative := by decide
      upper := ?_
      lower := ?_ }
  · have hcap : RatPolyCoeffEqv
        (polyAdd (cap 1) (polyNeg jet))
        (polyAdd polyOne (polyNeg jet)) :=
      (RatPolyCoeffEqv.one_smul polyOne).add (RatPolyCoeffEqv.refl _)
    exact Certificate.transport
      ((RatPolyCoeffEqv.haarCarrier hcap).trans
        (by
          simpa only [jet] using
            (plaquetteVectorQuadraticJet_complement width face)))
      (Certificate.square q.scalar hq.scalar)
  · exact (Certificate.constant (N width) 1 (by decide)).add hjetCertificate

private def weightedVectorJetInterval
    (s : Nat) (hs : 0 < s) (face : Z4Plaq)
    (hface : face ∈ bulkSourceFaces s) :
    Interval (N (s * s))
      (polySmul (bulkSourceCoefficient s hs face)
        (plaquetteVectorQuadraticJet (s * s) face))
      (bulkSourceCoefficient s hs face) := by
  exact Interval.changeCap
    (Q'.mul_one_eqv (bulkSourceCoefficient s hs face))
    (Interval.smul (bulkSourceCoefficient s hs face)
      (Q'.le_of_lt (bulkSourceCoefficient_pos hs hface))
      (plaquetteVectorQuadraticJet_interval (s * s) face))

private def finiteVectorJetInterval (s : Nat) (hs : 0 < s) :
    ∀ items : List Z4Plaq,
      (∀ face, face ∈ items → face ∈ bulkSourceFaces s) →
      Interval (N (s * s))
        (finitePolySum
          (fun face => polySmul (bulkSourceCoefficient s hs face)
            (plaquetteVectorQuadraticJet (s * s) face)) items)
        (listQSum (bulkSourceCoefficient s hs) items)
  | [], _ => Interval.zero _
  | face :: items, hitems =>
      (weightedVectorJetInterval s hs face (hitems face List.mem_cons_self)).add
        (finiteVectorJetInterval s hs items
          (fun next hnext => hitems next (List.mem_cons_of_mem face hnext)))

/-- The complete vector jet lies in the sharp interval
`[0,sum bulk coefficients]` on the ORIGINAL one-slice carrier. -/
def originalBulkVectorQuadraticJet_interval (s : Nat) (hs : 0 < s) :
    Interval (N (s * s)) (originalBulkVectorQuadraticJet s hs)
      (originalBulkVectorQuadraticJetCap s hs) := by
  unfold originalBulkVectorQuadraticJet originalBulkVectorQuadraticJetCap
    originalBulkCoefficientSum
  exact finiteVectorJetInterval s hs (bulkSourceFaces s)
    (fun _ hface => hface)

/-- The selected finite mean is the ORIGINAL window mean of the lifted
physical vector jet. -/
theorem originalBulkVectorQuadraticJetSelectedMean_windowRatio {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat)
    (hoffset : offset ≤ L) :
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (liftBoundary (offset * N (s * s))
          (originalBulkVectorQuadraticJet s hs)) ≈
      originalBulkVectorQuadraticJetSelectedMean
        hw0 hw1 s hs stage n L offset := by
  let extent := originalBulkVectorQuadraticJetExtent s n L
  let schedule := originalBulkVectorQuadraticJetSchedule s hs offset
  let source := sourceSpan (s * s) schedule
  let placed := originalBulkVectorQuadraticJetPlaced s hs n offset L
  let ids := originalBulkVectorQuadraticJetIds s n L
  let hids := originalBulkVectorQuadraticJetIds_physical s n L
  have hsource := originalBulkVectorQuadraticJetSchedule_source_full
    s hs offset L hoffset
  have hwithin : ∀ x, x ∈ schedule → ∀ entry, entry ∈ x.2 → entry.1 ≤ L := by
    intro x hx entry hentry
    exact Nat.le_trans
      (originalBulkVectorQuadraticJetSchedule_within
        s hs offset x hx entry hentry)
      hoffset
  have hfaces : ∀ x, x ∈ schedule → ∀ entry, entry ∈ x.2 →
      ∀ factor, factor ∈ entry.2 → factor.1 ∈ spatialFaces (s * s) :=
    originalBulkVectorQuadraticJetSchedule_faces s hs offset
  have hwidth : s * s ≤ extent := by
    unfold extent originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  have htime : 0 + (n + (L + n)) ≤ extent := by
    unfold extent originalBulkVectorQuadraticJetExtent
      originalBulkScalarSquareRemainderExtent
    omega
  have hmeanRaw := windowRatio_span_originalFiniteValue hw0 hw1 hwidth htime
    schedule hwithin hfaces stage
  have hmean : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n source ≈
      finiteValue w hw0 hw1 extent ids hids placed stage := by
    simpa only [Nat.zero_add, source, placed, ids, extent,
      originalBulkVectorQuadraticJetPlaced,
      originalBulkVectorQuadraticJetIds,
      originalBulkVectorQuadraticJetExtent] using hmeanRaw
  exact Q'.eqv_trans _ _ _
    (windowRatio_carrier_congr hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n hsource.symm)
    (by
      simpa only [originalBulkVectorQuadraticJetSelectedMean,
        originalBulkVectorQuadraticJetPlaced,
        originalBulkVectorQuadraticJetIds,
        originalBulkVectorQuadraticJetExtent,
        source, extent, placed, ids] using hmean)

/-- The actual finite OWN vector-jet center is its lower one-step endpoint. -/
theorem originalBulkVectorQuadraticJetOwnMean_endpoint_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n ≈
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n 1 n
        (originalBulkVectorQuadraticJet s hs) := by
  unfold originalBulkVectorQuadraticJetOwnMean
  have hsupport := (originalBulkVectorQuadraticJet_interval s hs).support
  exact Q'.eqv_trans _ _ _
    (middleRatio_swap hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) (n + 1) n
      (originalBulkVectorQuadraticJet s hs))
    (Q'.eqv_symm
      (lower_endpoint_mean hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n 1 hsupport))

/-- Explicit endpoint-mixing error for the selected vector-jet mean. -/
def originalBulkVectorQuadraticJetSelectedMeanError {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (n : Nat) : Q' :=
  mixRate hw0 hw1 (s * s) ^ n *
    (originalBulkVectorQuadraticJetCap s hs +
      originalBulkVectorQuadraticJetCap s hs)

theorem originalBulkVectorQuadraticJetSelectedMean_zero_close {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let selected := originalBulkVectorQuadraticJetSelectedMean
      hw0 hw1 s hs stage n L 0
    let own := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
    let error := originalBulkVectorQuadraticJetSelectedMeanError
      hw0 hw1 s hs n
    selected ≤ own + error ∧ own ≤ selected + error := by
  dsimp only
  let jet := originalBulkVectorQuadraticJet s hs
  let selected := originalBulkVectorQuadraticJetSelectedMean
    hw0 hw1 s hs stage n L 0
  let own := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
  let error := originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n
  let lagged := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n L n jet
  let oneStep := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n 1 n jet
  have hselected : lagged ≈ selected := by
    simpa only [lagged, selected, jet, Nat.zero_mul, liftBoundary] using
      (originalBulkVectorQuadraticJetSelectedMean_windowRatio
        hw0 hw1 s hs stage n L 0 (Nat.zero_le _))
  have hone : own ≈ oneStep := by
    simpa only [own, oneStep, jet] using
      (originalBulkVectorQuadraticJetOwnMean_endpoint_one
        hw0 hw1 s hs stage n)
  have hlag := endpoint_mean_lags_commonTail hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L 1
    (originalBulkVectorQuadraticJet_interval s hs)
  change lagged ≤ oneStep + error ∧ oneStep ≤ lagged + error at hlag
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hselected.symm)
      (Q'.le_trans' _ _ _ hlag.1
        (Q'.le_of_eqv (Q'.add_eqv_congr' hone.symm (Q'.eqv_refl _)))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hone)
      (Q'.le_trans' _ _ _ hlag.2
        (Q'.le_of_eqv (Q'.add_eqv_congr' hselected (Q'.eqv_refl _))))⟩

theorem originalBulkVectorQuadraticJetSelectedMean_L_close {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let selected := originalBulkVectorQuadraticJetSelectedMean
      hw0 hw1 s hs stage n L L
    let own := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
    let error := originalBulkVectorQuadraticJetSelectedMeanError
      hw0 hw1 s hs n
    selected ≤ own + error ∧ own ≤ selected + error := by
  dsimp only
  let jet := originalBulkVectorQuadraticJet s hs
  let selected := originalBulkVectorQuadraticJetSelectedMean
    hw0 hw1 s hs stage n L L
  let own := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
  let error := originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n
  let lagged := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n L n jet
  let lifted := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n L n
    (liftBoundary (L * N (s * s)) jet)
  let oneStep := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n 1 n jet
  have hlifted : lifted ≈ selected := by
    simpa only [lifted, selected, jet] using
      (originalBulkVectorQuadraticJetSelectedMean_windowRatio
        hw0 hw1 s hs stage n L L (Nat.le_refl _))
  have hendpoint : lagged ≈ lifted := by
    simpa only [lagged, lifted, jet] using
      (endpoint_means_eqv hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L
        (originalBulkVectorQuadraticJet_interval s hs).support)
  have hselected : lagged ≈ selected := Q'.eqv_trans _ _ _ hendpoint hlifted
  have hone : own ≈ oneStep := by
    simpa only [own, oneStep, jet] using
      (originalBulkVectorQuadraticJetOwnMean_endpoint_one
        hw0 hw1 s hs stage n)
  have hlag := endpoint_mean_lags_commonTail hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L 1
    (originalBulkVectorQuadraticJet_interval s hs)
  change lagged ≤ oneStep + error ∧ oneStep ≤ lagged + error at hlag
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hselected.symm)
      (Q'.le_trans' _ _ _ hlag.1
        (Q'.le_of_eqv (Q'.add_eqv_congr' hone.symm (Q'.eqv_refl _)))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hone)
      (Q'.le_trans' _ _ _ hlag.2
        (Q'.le_of_eqv (Q'.add_eqv_congr' hselected (Q'.eqv_refl _))))⟩

/-- Lower selected-mean mismatch square paid by endpoint mixing. -/
theorem originalBulkVectorQuadraticJetSelectedMean_zero_mismatch_square_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let mismatch :=
      originalBulkVectorQuadraticJetSelectedMean hw0 hw1 s hs stage n L 0 +
        -originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
    let error := originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n
    mismatch * mismatch ≤ error * error := by
  dsimp only
  let selected := originalBulkVectorQuadraticJetSelectedMean
    hw0 hw1 s hs stage n L 0
  let own := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
  let error := originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n
  have hclose := originalBulkVectorQuadraticJetSelectedMean_zero_close
    hw0 hw1 s hs stage n L
  change selected ≤ own + error ∧ own ≤ selected + error at hclose
  have habs : Q'.abs (selected + -own) ≤ error :=
    CReal.abs_sub_le_of_bounds hclose.1 hclose.2
  have hsquare := YMGap.Continuum.BondMovingQuadratic.sq_le_sq
    (Q'.abs_nonneg (selected + -own)) habs
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_mul_self_eqv (selected + -own))) hsquare

/-- Lifted upper selected-mean mismatch square with the same payment. -/
theorem originalBulkVectorQuadraticJetSelectedMean_L_mismatch_square_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let mismatch :=
      originalBulkVectorQuadraticJetSelectedMean hw0 hw1 s hs stage n L L +
        -originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
    let error := originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n
    mismatch * mismatch ≤ error * error := by
  dsimp only
  let selected := originalBulkVectorQuadraticJetSelectedMean
    hw0 hw1 s hs stage n L L
  let own := originalBulkVectorQuadraticJetOwnMean hw0 hw1 s hs stage n
  let error := originalBulkVectorQuadraticJetSelectedMeanError hw0 hw1 s hs n
  have hclose := originalBulkVectorQuadraticJetSelectedMean_L_close
    hw0 hw1 s hs stage n L
  change selected ≤ own + error ∧ own ≤ selected + error at hclose
  have habs : Q'.abs (selected + -own) ≤ error :=
    CReal.abs_sub_le_of_bounds hclose.1 hclose.2
  have hsquare := YMGap.Continuum.BondMovingQuadratic.sq_le_sq
    (Q'.abs_nonneg (selected + -own)) habs
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_mul_self_eqv (selected + -own))) hsquare

/-- Exact coefficient-product pair sum for one vector-jet placement. -/
def originalBulkVectorQuadraticJetPairwiseCovariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat) : Q' :=
  listQSum
    (fun leftFace => listQSum
      (fun rightFace =>
        (originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
          originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
        finiteCovariance w hw0 hw1
          (originalBulkVectorQuadraticJetExtent s n L)
          (originalBulkVectorQuadraticJetIds s n L)
          (originalBulkVectorQuadraticJetIds_physical s n L)
          (originalBulkVectorQuadraticJetFacePlaced s n offset L leftFace)
          (originalBulkVectorQuadraticJetFacePlaced s n offset L rightFace)
          stage)
      (bulkSourceFaces s))
    (bulkSourceFaces s)

/-- Exact pairwise expansion of the SAME selected vector-jet covariance. -/
theorem originalBulkVectorQuadraticJetSelectedCovariance_pairwise {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat) :
    originalBulkVectorQuadraticJetSelectedCovariance
        hw0 hw1 s hs stage n L offset ≈
      originalBulkVectorQuadraticJetPairwiseCovariance
        hw0 hw1 s hs stage n L offset := by
  let extent := originalBulkVectorQuadraticJetExtent s n L
  let ids := originalBulkVectorQuadraticJetIds s n L
  let hids := originalBulkVectorQuadraticJetIds_physical s n L
  let weight := originalBulkVectorQuadraticJetFaceWeight s hs
  let localFactor := originalBulkVectorQuadraticJetFacePlaced s n offset L
  have hsum : originalBulkVectorQuadraticJetPlaced s hs n offset L =
      finitePolySum
        (fun face => polySmul (weight face) (localFactor face))
        (bulkSourceFaces s) := by
    simpa only [weight, localFactor] using
      (originalBulkVectorQuadraticJetPlaced_face_sum s hs n offset L)
  unfold originalBulkVectorQuadraticJetSelectedCovariance
    originalBulkVectorQuadraticJetPairwiseCovariance
  rw [hsum]
  simpa only [extent, ids, hids, weight, localFactor] using
    (finiteCovariance_weightedSum_pairwise hw0 hw1 extent ids hids stage
      weight localFactor (bulkSourceFaces s))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetPlaced_face_sum
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetFacePlaced_eq_sweptProduct
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetPlacedFace_physical
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetFace_interval
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetFace_local
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetFace_covariance_distance_bound
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.plaquetteVectorQuadraticJet_interval
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJet_interval
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetSelectedMean_windowRatio
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetOwnMean_endpoint_one
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetSelectedMean_zero_mismatch_square_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetSelectedMean_L_mismatch_square_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance.originalBulkVectorQuadraticJetSelectedCovariance_pairwise
