/-
# Pairwise expansion of the original bulk scalar-remainder covariance

The selected original-action covariance of the complete weighted bulk
scalar-square remainder is exactly the double finite sum of its local
face-pair covariances.  Both outer source coefficients pass through the
covariance, so every summand carries their product.  This is the finite
coefficient-square identity required before applying the existing local
two-probe distance estimate face by face.

No absolute-value summation, geometric spatial collapse, cutoff removal,
continuum Hamiltonian, or Clay mass gap is proved here.  The two endpoint
mean-mismatch squares are bounded below, but are not summed over the bulk
source in this module.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.ClusterCount4DProgress
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
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
  (endpoint_mean_lags_commonTail endpoint_means_eqv lower_endpoint_mean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
  (placedSpan sourceSpan)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (singletonCarrier)
open YMGap.Continuum.BF4ExactSlabTemporalSweep (sweptProduct swept_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (placeWindowProbes)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval (probeCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabSelectedTwoProbeCovariance
  (finiteValue_coeff_congr finite_covariance_distance_bound)
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (distanceBudget)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSizeGeometricSum (entropyRate)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderDiagonal
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkSourceBridge
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRatio heatRemainderBound)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabPhysicalFaceEdges)

local infix:50 " ≈ " => Q'.eqv

/-- The literal rational coefficient multiplying one local character factor. -/
def originalBulkScalarSquareRemainderFaceWeight
    (s : Nat) (hs : 0 < s) (face : Z4Plaq) : Q' :=
  Q'.mkPos 1 4 (by decide) * bulkSourceCoefficient s hs face

/-- One unscaled local placed factor in the canonical selected slab. -/
def originalBulkScalarSquareRemainderFacePlaced
    (s n offset L : Nat) (face : Z4Plaq) : RatPoly :=
  sweptProduct (originalBulkScalarSquareRemainderExtent s n L) 0
    (placeWindowProbes n (scalarSquareRemainderSchedule offset face))

/-- The complete placed remainder is the weighted sum of its local faces. -/
theorem originalBulkScalarSquareRemainderPlaced_face_sum
    (s : Nat) (hs : 0 < s) (n offset L : Nat) :
    originalBulkScalarSquareRemainderPlaced s hs n offset L =
      finitePolySum
        (fun face => polySmul
          (originalBulkScalarSquareRemainderFaceWeight s hs face)
          (originalBulkScalarSquareRemainderFacePlaced s n offset L face))
        (bulkSourceFaces s) := by
  unfold originalBulkScalarSquareRemainderPlaced placedSpan
    originalBulkScalarSquareRemainderSchedule
    originalBulkScalarSquareRemainderFaceWeight
    originalBulkScalarSquareRemainderFacePlaced
  rw [YMGap.Continuum.PolynomialWeightedSumBounds.sum_map]
  rfl

/-- The actual chronological face supporting one local factor. -/
def originalBulkScalarSquareRemainderPlacedFace
    (n offset : Nat) (face : Z4Plaq) : Z4Plaq :=
  timeShiftPlaquette (n + offset) face

/-- The interval cap of one local character factor.  Its value depends only
on the fixed coefficient list; the face occurs only in the singleton syntax. -/
def originalBulkScalarSquareRemainderFaceCap
    (n offset : Nat) (face : Z4Plaq) : Q' :=
  probeCap
    [(originalBulkScalarSquareRemainderPlacedFace n offset face,
      scalarSquareRemainderTerms)]

private theorem facePlaced_schedule
    (s n offset L : Nat) (face : Z4Plaq) :
    originalBulkScalarSquareRemainderFacePlaced s n offset L face =
      sweptProduct (originalBulkScalarSquareRemainderExtent s n L) 0
        [(originalBulkScalarSquareRemainderPlacedFace n offset face,
          scalarSquareRemainderTerms)] := by
  unfold originalBulkScalarSquareRemainderFacePlaced
    scalarSquareRemainderSchedule originalBulkScalarSquareRemainderPlacedFace
    placeWindowProbes YMGap.Continuum.BF4ExactSlabFixedSpatialProbe.placeProbes
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_singleton]

/-- The existing polynomial interval machinery gives a volume-independent
cap for the actual local placed factor. -/
def originalBulkScalarSquareRemainderFace_interval
    (s n offset L : Nat) (face : Z4Plaq)
    (hface : face ∈ bulkSourceFaces s) (hoffset : offset ≤ L) :
    Interval
      (boundaryCompleteSlabLinks
        (originalBulkScalarSquareRemainderExtent s n L)).length
      (originalBulkScalarSquareRemainderFacePlaced s n offset L face)
      (originalBulkScalarSquareRemainderFaceCap n offset face) := by
  rw [facePlaced_schedule]
  apply sweptProduct_interval
  intro factor hfactor
  have hfactorEq := List.mem_singleton.mp hfactor
  subst factor
  apply YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe.placeWindowProbes_physical
      (width := s * s) (start := n) (L := L)
      (extent := originalBulkScalarSquareRemainderExtent s n L)
      (fs := scalarSquareRemainderSchedule offset face)
  · unfold originalBulkScalarSquareRemainderExtent
    omega
  · unfold originalBulkScalarSquareRemainderExtent
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

/-- Literal support of one local factor is exactly its placed face's four
links.  No coefficient-equivalence transport is used. -/
theorem originalBulkScalarSquareRemainderFace_local
    (s n offset L : Nat) (face : Z4Plaq) :
    LinkLocal (originalBulkScalarSquareRemainderExtent s n L)
      (edgesOf (originalBulkScalarSquareRemainderPlacedFace n offset face))
      (originalBulkScalarSquareRemainderFacePlaced s n offset L face) := by
  rw [facePlaced_schedule, swept_zero]
  apply BlockLocal.fold
  intro factor hfactor
  have hfactorEq := List.mem_singleton.mp hfactor
  subst factor
  apply BlockLocal.finiteSum
  intro term _
  exact ((face_scalar_local
    (originalBulkScalarSquareRemainderExtent s n L)
    (originalBulkScalarSquareRemainderPlacedFace n offset face)).character term.1).smul term.2

/-- Each pair in the exact expansion satisfies the existing geometric
selected-action covariance estimate with singleton plaquette carriers. -/
theorem originalBulkScalarSquareRemainderFace_covariance_distance_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hsRate : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (s : Nat) (stage n L offset : Nat) (hoffset : offset ≤ L)
    (leftFace rightFace : Z4Plaq)
    (hleft : leftFace ∈ bulkSourceFaces s)
    (hright : rightFace ∈ bulkSourceFaces s) :
    Q'.abs
        (finiteCovariance w hw0 hw1
          (originalBulkScalarSquareRemainderExtent s n L)
          (originalBulkScalarSquareRemainderIds s n L)
          (originalBulkScalarSquareRemainderIds_physical s n L)
          (originalBulkScalarSquareRemainderFacePlaced s n offset L leftFace)
          (originalBulkScalarSquareRemainderFacePlaced s n offset L rightFace)
          stage) ≤
      distanceBudget
        (singletonCarrier
          (originalBulkScalarSquareRemainderPlacedFace n offset leftFace))
        (singletonCarrier
          (originalBulkScalarSquareRemainderPlacedFace n offset rightFace))
        w hd hsRate
        (originalBulkScalarSquareRemainderFaceCap n offset leftFace)
        (originalBulkScalarSquareRemainderFaceCap n offset rightFace) := by
  apply finite_covariance_distance_bound hw0 hw1 hsmall hd hsRate
    (originalBulkScalarSquareRemainderExtent s n L)
    (originalBulkScalarSquareRemainderIds s n L)
    (by
      unfold originalBulkScalarSquareRemainderIds
      exact chainIds_nodup _ _ _ _)
    (originalBulkScalarSquareRemainderIds_physical s n L)
    (originalBulkScalarSquareRemainderFacePlaced s n offset L leftFace)
    (originalBulkScalarSquareRemainderFacePlaced s n offset L rightFace)
    (originalBulkScalarSquareRemainderFaceCap n offset leftFace)
    (originalBulkScalarSquareRemainderFaceCap n offset rightFace)
    (originalBulkScalarSquareRemainderFace_interval
      s n offset L leftFace hleft hoffset)
    (originalBulkScalarSquareRemainderFace_interval
      s n offset L rightFace hright hoffset)
    (edgesOf (originalBulkScalarSquareRemainderPlacedFace n offset leftFace))
    (edgesOf (originalBulkScalarSquareRemainderPlacedFace n offset rightFace))
    (singletonCarrier
      (originalBulkScalarSquareRemainderPlacedFace n offset leftFace))
    (singletonCarrier
      (originalBulkScalarSquareRemainderPlacedFace n offset rightFace))
    (originalBulkScalarSquareRemainderFace_local s n offset L leftFace)
    (originalBulkScalarSquareRemainderFace_local s n offset L rightFace)
    stage

/-- The selected finite mean is exactly the original-window mean of the
chronologically lifted bulk remainder. -/
theorem originalBulkScalarSquareRemainderSelectedMean_windowRatio {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat)
    (hoffset : offset ≤ L) :
    windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L n
        (liftBoundary (offset * (baseLinks (s * s)).length)
          (originalBulkScalarSquareRemainder s hs)) ≈
      originalBulkScalarSquareRemainderSelectedMean
        hw0 hw1 s hs stage n L offset := by
  let extent := originalBulkScalarSquareRemainderExtent s n L
  let schedule := originalBulkScalarSquareRemainderSchedule s hs offset
  let source := sourceSpan (s * s) schedule
  let placed := originalBulkScalarSquareRemainderPlaced s hs n offset L
  let ids := originalBulkScalarSquareRemainderIds s n L
  let hids := originalBulkScalarSquareRemainderIds_physical s n L
  have hsource := originalBulkScalarSquareRemainderSchedule_source s hs offset
  have hwithin : ∀ x, x ∈ schedule → ∀ entry, entry ∈ x.2 → entry.1 ≤ L := by
    intro x hx entry hentry
    exact Nat.le_trans
      (originalBulkScalarSquareRemainderSchedule_within
        s hs offset x hx entry hentry)
      hoffset
  have hfaces : ∀ x, x ∈ schedule → ∀ entry, entry ∈ x.2 →
      ∀ factor, factor ∈ entry.2 → factor.1 ∈ spatialFaces (s * s) :=
    originalBulkScalarSquareRemainderSchedule_faces s hs offset
  have hwidth : s * s ≤ extent := by
    unfold extent originalBulkScalarSquareRemainderExtent
    omega
  have htime : 0 + (n + (L + n)) ≤ extent := by
    unfold extent originalBulkScalarSquareRemainderExtent
    omega
  have hmeanRaw := windowRatio_span_originalFiniteValue hw0 hw1 hwidth htime
    schedule hwithin hfaces stage
  have hmean : windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n source ≈
      finiteValue w hw0 hw1 extent ids hids placed stage := by
    simpa only [Nat.zero_add, source, placed, ids, extent,
      originalBulkScalarSquareRemainderPlaced,
      originalBulkScalarSquareRemainderIds] using hmeanRaw
  exact Q'.eqv_trans _ _ _
    (windowRatio_congr hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) n L n hsource.symm)
    (by
      simpa only [originalBulkScalarSquareRemainderSelectedMean,
        originalBulkScalarSquareRemainderPlaced,
        originalBulkScalarSquareRemainderIds,
        originalBulkScalarSquareRemainderExtent,
        source, extent, placed, ids] using hmean)

/-- The actual finite OWN remainder center is the lower one-step endpoint. -/
theorem originalBulkScalarSquareRemainderOwnMean_endpoint_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n : Nat) :
    originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n ≈
      windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n 1 n
        (originalBulkScalarSquareRemainder s hs) := by
  unfold originalBulkScalarSquareRemainderOwnMean
  have hsupport := (originalBulkScalarSquareRemainder_interval s hs).support
  exact Q'.eqv_trans _ _ _
    (middleRatio_swap hw0 hw1 (headCutoff w + stage) (s * s)
      (Nat.le_add_right _ _) (n + 1) n
      (originalBulkScalarSquareRemainder s hs))
    (Q'.eqv_symm
      (lower_endpoint_mean hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n 1 hsupport))

/-- Explicit endpoint-mixing payment for a selected remainder mean. -/
def originalBulkScalarSquareRemainderSelectedMeanError {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (n : Nat) : Q' :=
  mixRate hw0 hw1 (s * s) ^ n *
    (originalBulkScalarSquareRemainderCap s hs +
      originalBulkScalarSquareRemainderCap s hs)

/-- Both orders of the lower selected-mean comparison with the finite OWN
center, uniformly in the chronological lag. -/
theorem originalBulkScalarSquareRemainderSelectedMean_zero_close {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let selected := originalBulkScalarSquareRemainderSelectedMean
      hw0 hw1 s hs stage n L 0
    let own := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let error := originalBulkScalarSquareRemainderSelectedMeanError
      hw0 hw1 s hs n
    selected ≤ own + error ∧ own ≤ selected + error := by
  dsimp only
  let remainder := originalBulkScalarSquareRemainder s hs
  let selected := originalBulkScalarSquareRemainderSelectedMean
    hw0 hw1 s hs stage n L 0
  let own := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  let error := originalBulkScalarSquareRemainderSelectedMeanError
    hw0 hw1 s hs n
  let lagged := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n L n remainder
  let oneStep := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n 1 n remainder
  have hselected : lagged ≈ selected := by
    simpa only [lagged, selected, remainder, Nat.zero_mul, liftBoundary] using
      (originalBulkScalarSquareRemainderSelectedMean_windowRatio
        hw0 hw1 s hs stage n L 0 (Nat.zero_le _))
  have hone : own ≈ oneStep := by
    simpa only [own, oneStep, remainder] using
      (originalBulkScalarSquareRemainderOwnMean_endpoint_one
        hw0 hw1 s hs stage n)
  have hlag := endpoint_mean_lags_commonTail hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L 1
    (originalBulkScalarSquareRemainder_interval s hs)
  change lagged ≤ oneStep + error ∧ oneStep ≤ lagged + error at hlag
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hselected.symm)
      (Q'.le_trans' _ _ _ hlag.1
        (Q'.le_of_eqv (Q'.add_eqv_congr' hone.symm (Q'.eqv_refl _)))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hone)
      (Q'.le_trans' _ _ _ hlag.2
        (Q'.le_of_eqv (Q'.add_eqv_congr' hselected (Q'.eqv_refl _))))⟩

/-- Both orders of the upper selected-mean comparison.  Exact endpoint
symmetry first removes the chronological lift. -/
theorem originalBulkScalarSquareRemainderSelectedMean_L_close {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let selected := originalBulkScalarSquareRemainderSelectedMean
      hw0 hw1 s hs stage n L L
    let own := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let error := originalBulkScalarSquareRemainderSelectedMeanError
      hw0 hw1 s hs n
    selected ≤ own + error ∧ own ≤ selected + error := by
  dsimp only
  let remainder := originalBulkScalarSquareRemainder s hs
  let selected := originalBulkScalarSquareRemainderSelectedMean
    hw0 hw1 s hs stage n L L
  let own := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  let error := originalBulkScalarSquareRemainderSelectedMeanError
    hw0 hw1 s hs n
  let lagged := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n L n remainder
  let lifted := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n L n
    (liftBoundary (L * (baseLinks (s * s)).length) remainder)
  let oneStep := windowRatio hw0 hw1 (headCutoff w + stage) (s * s)
    (Nat.le_add_right _ _) n 1 n remainder
  have hlifted : lifted ≈ selected := by
    simpa only [lifted, selected, remainder] using
      (originalBulkScalarSquareRemainderSelectedMean_windowRatio
        hw0 hw1 s hs stage n L L (Nat.le_refl _))
  have hendpoint : lagged ≈ lifted := by
    simpa only [lagged, lifted, remainder] using
      (endpoint_means_eqv hw0 hw1 (headCutoff w + stage) (s * s)
        (Nat.le_add_right _ _) n L
        (originalBulkScalarSquareRemainder_interval s hs).support)
  have hselected : lagged ≈ selected := Q'.eqv_trans _ _ _ hendpoint hlifted
  have hone : own ≈ oneStep := by
    simpa only [own, oneStep, remainder] using
      (originalBulkScalarSquareRemainderOwnMean_endpoint_one
        hw0 hw1 s hs stage n)
  have hlag := endpoint_mean_lags_commonTail hw0 hw1
    (headCutoff w + stage) (s * s) (Nat.le_add_right _ _) n L 1
    (originalBulkScalarSquareRemainder_interval s hs)
  change lagged ≤ oneStep + error ∧ oneStep ≤ lagged + error at hlag
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hselected.symm)
      (Q'.le_trans' _ _ _ hlag.1
        (Q'.le_of_eqv (Q'.add_eqv_congr' hone.symm (Q'.eqv_refl _)))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hone)
      (Q'.le_trans' _ _ _ hlag.2
        (Q'.le_of_eqv (Q'.add_eqv_congr' hselected (Q'.eqv_refl _))))⟩

/-- The lower selected-mean mismatch square pays only the squared endpoint
mixing error. -/
theorem originalBulkScalarSquareRemainderSelectedMean_zero_mismatch_square_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let mismatch :=
      originalBulkScalarSquareRemainderSelectedMean hw0 hw1 s hs stage n L 0 +
        -originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let error := originalBulkScalarSquareRemainderSelectedMeanError
      hw0 hw1 s hs n
    mismatch * mismatch ≤ error * error := by
  dsimp only
  let selected := originalBulkScalarSquareRemainderSelectedMean
    hw0 hw1 s hs stage n L 0
  let own := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  let error := originalBulkScalarSquareRemainderSelectedMeanError
    hw0 hw1 s hs n
  have hclose := originalBulkScalarSquareRemainderSelectedMean_zero_close
    hw0 hw1 s hs stage n L
  change selected ≤ own + error ∧ own ≤ selected + error at hclose
  have habs : Q'.abs (selected + -own) ≤ error :=
    CReal.abs_sub_le_of_bounds hclose.1 hclose.2
  have hsquare := YMGap.Continuum.BondMovingQuadratic.sq_le_sq
    (Q'.abs_nonneg (selected + -own)) habs
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_mul_self_eqv (selected + -own))) hsquare

/-- The lifted upper selected-mean mismatch has the same square budget. -/
theorem originalBulkScalarSquareRemainderSelectedMean_L_mismatch_square_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L : Nat) :
    let mismatch :=
      originalBulkScalarSquareRemainderSelectedMean hw0 hw1 s hs stage n L L +
        -originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
    let error := originalBulkScalarSquareRemainderSelectedMeanError
      hw0 hw1 s hs n
    mismatch * mismatch ≤ error * error := by
  dsimp only
  let selected := originalBulkScalarSquareRemainderSelectedMean
    hw0 hw1 s hs stage n L L
  let own := originalBulkScalarSquareRemainderOwnMean hw0 hw1 s hs stage n
  let error := originalBulkScalarSquareRemainderSelectedMeanError
    hw0 hw1 s hs n
  have hclose := originalBulkScalarSquareRemainderSelectedMean_L_close
    hw0 hw1 s hs stage n L
  change selected ≤ own + error ∧ own ≤ selected + error at hclose
  have habs : Q'.abs (selected + -own) ≤ error :=
    CReal.abs_sub_le_of_bounds hclose.1 hclose.2
  have hsquare := YMGap.Continuum.BondMovingQuadratic.sq_le_sq
    (Q'.abs_nonneg (selected + -own)) habs
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_mul_self_eqv (selected + -own))) hsquare

section FiniteCovarianceAlgebra

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent : Nat) (ids : List Nat)
  (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (stage : Nat)

private theorem finite_zero :
    finiteValue w hw0 hw1 extent ids hids polyZero stage ≈ 0 :=
  Q'.zero_mul_eqv _

private theorem finite_add (p q : RatPoly) :
    finiteValue w hw0 hw1 extent ids hids (polyAdd p q) stage ≈
      finiteValue w hw0 hw1 extent ids hids p stage +
        finiteValue w hw0 hw1 extent ids hids q stage := by
  unfold finiteValue YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numerator
  rw [polyMul_add_left_exact]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (quaternionHaar_append _ _ _))
    (Q'.add_mul_eqv _ _ _)

private theorem finite_smul (coefficient : Q') (p : RatPoly) :
    finiteValue w hw0 hw1 extent ids hids (polySmul coefficient p) stage ≈
      coefficient * finiteValue w hw0 hw1 extent ids hids p stage := by
  unfold finiteValue YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numerator
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_trans _ _ _
          (quaternionHaar_polyMul_smul_right _ coefficient _ p)
          (Q'.mul_eqv_congr_left coefficient _ _
            (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))))
    (Q'.mul_assoc_eqv _ _ _)

private theorem finite_covariance_zero_left (q : RatPoly) :
    finiteCovariance w hw0 hw1 extent ids hids polyZero q stage ≈ 0 := by
  unfold finiteCovariance
  have hproduct := finiteValue_coeff_congr w hw0 hw1 extent ids hids
    (polyMul polyZero q) polyZero
    (RatPolyCoeffEqv.mul_zero_left q) stage
  have hzero := finite_zero hw0 hw1 extent ids hids stage
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hproduct
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _ hzero)))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hzero
        (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv _)))
      (by decide))

private theorem finite_covariance_add_left (p r q : RatPoly) :
    finiteCovariance w hw0 hw1 extent ids hids (polyAdd p r) q stage ≈
      finiteCovariance w hw0 hw1 extent ids hids p q stage +
        finiteCovariance w hw0 hw1 extent ids hids r q stage := by
  unfold finiteCovariance
  have hproduct := finiteValue_coeff_congr w hw0 hw1 extent ids hids
    (polyMul (polyAdd p r) q)
    (polyAdd (polyMul p q) (polyMul r q))
    (by rw [polyMul_add_left_exact]; exact RatPolyCoeffEqv.refl _) stage
  have hproductAdd := finite_add hw0 hw1 extent ids hids stage
    (polyMul p q) (polyMul r q)
  have hmeanAdd := finite_add hw0 hw1 extent ids hids stage p r
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hproduct hproductAdd)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _ hmeanAdd))) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1))
      (.neg (.mul (.add (.var 2) (.var 3)) (.var 4))))
    (.add
      (.add (.var 0) (.neg (.mul (.var 2) (.var 4))))
      (.add (.var 1) (.neg (.mul (.var 3) (.var 4)))))
    (by decide)
    (fun index =>
      if index = 0 then finiteValue w hw0 hw1 extent ids hids (polyMul p q) stage
      else if index = 1 then finiteValue w hw0 hw1 extent ids hids (polyMul r q) stage
      else if index = 2 then finiteValue w hw0 hw1 extent ids hids p stage
      else if index = 3 then finiteValue w hw0 hw1 extent ids hids r stage
      else finiteValue w hw0 hw1 extent ids hids q stage)

private theorem finite_covariance_add_right (p q r : RatPoly) :
    finiteCovariance w hw0 hw1 extent ids hids p (polyAdd q r) stage ≈
      finiteCovariance w hw0 hw1 extent ids hids p q stage +
        finiteCovariance w hw0 hw1 extent ids hids p r stage := by
  unfold finiteCovariance
  have hproduct := finiteValue_coeff_congr w hw0 hw1 extent ids hids
    (polyMul p (polyAdd q r))
    (polyAdd (polyMul p q) (polyMul p r))
    (RatPolyCoeffEqv.mul_add_right p q r) stage
  have hproductAdd := finite_add hw0 hw1 extent ids hids stage
    (polyMul p q) (polyMul p r)
  have hmeanAdd := finite_add hw0 hw1 extent ids hids stage q r
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hproduct hproductAdd)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hmeanAdd))) ?_
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1))
      (.neg (.mul (.var 2) (.add (.var 3) (.var 4)))))
    (.add
      (.add (.var 0) (.neg (.mul (.var 2) (.var 3))))
      (.add (.var 1) (.neg (.mul (.var 2) (.var 4)))))
    (by decide)
    (fun index =>
      if index = 0 then finiteValue w hw0 hw1 extent ids hids (polyMul p q) stage
      else if index = 1 then finiteValue w hw0 hw1 extent ids hids (polyMul p r) stage
      else if index = 2 then finiteValue w hw0 hw1 extent ids hids p stage
      else if index = 3 then finiteValue w hw0 hw1 extent ids hids q stage
      else finiteValue w hw0 hw1 extent ids hids r stage)

private theorem finite_covariance_smul_left
    (coefficient : Q') (p q : RatPoly) :
    finiteCovariance w hw0 hw1 extent ids hids (polySmul coefficient p) q stage ≈
      coefficient * finiteCovariance w hw0 hw1 extent ids hids p q stage := by
  unfold finiteCovariance
  have hproduct := finiteValue_coeff_congr w hw0 hw1 extent ids hids
    (polyMul (polySmul coefficient p) q)
    (polySmul coefficient (polyMul p q))
    (RatPolyCoeffEqv.polyMul_smul_left coefficient p q) stage
  have hproductScale := finite_smul hw0 hw1 extent ids hids stage coefficient (polyMul p q)
  have hmeanScale := finite_smul hw0 hw1 extent ids hids stage coefficient p
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hproduct hproductScale)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _ hmeanScale))) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1))
      (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3))))
    (.mul (.var 0)
      (.add (.var 1) (.neg (.mul (.var 2) (.var 3)))))
    (by decide)
    (fun index =>
      if index = 0 then coefficient
      else if index = 1 then finiteValue w hw0 hw1 extent ids hids (polyMul p q) stage
      else if index = 2 then finiteValue w hw0 hw1 extent ids hids p stage
      else finiteValue w hw0 hw1 extent ids hids q stage)

private theorem finite_covariance_smul_right
    (coefficient : Q') (p q : RatPoly) :
    finiteCovariance w hw0 hw1 extent ids hids p (polySmul coefficient q) stage ≈
      coefficient * finiteCovariance w hw0 hw1 extent ids hids p q stage := by
  unfold finiteCovariance
  have hproduct := finiteValue_coeff_congr w hw0 hw1 extent ids hids
    (polyMul p (polySmul coefficient q))
    (polySmul coefficient (polyMul p q))
    (RatPolyCoeffEqv.polyMul_smul_right coefficient p q) stage
  have hproductScale := finite_smul hw0 hw1 extent ids hids stage coefficient (polyMul p q)
  have hmeanScale := finite_smul hw0 hw1 extent ids hids stage coefficient q
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hproduct hproductScale)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hmeanScale))) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1))
      (.neg (.mul (.var 2) (.mul (.var 0) (.var 3)))))
    (.mul (.var 0)
      (.add (.var 1) (.neg (.mul (.var 2) (.var 3)))))
    (by decide)
    (fun index =>
      if index = 0 then coefficient
      else if index = 1 then finiteValue w hw0 hw1 extent ids hids (polyMul p q) stage
      else if index = 2 then finiteValue w hw0 hw1 extent ids hids p stage
      else finiteValue w hw0 hw1 extent ids hids q stage)

private theorem finite_covariance_weighted
    (leftWeight rightWeight : Q') (p q : RatPoly) :
    finiteCovariance w hw0 hw1 extent ids hids
        (polySmul leftWeight p) (polySmul rightWeight q) stage ≈
      (leftWeight * rightWeight) *
        finiteCovariance w hw0 hw1 extent ids hids p q stage := by
  exact Q'.eqv_trans _ _ _
    (finite_covariance_smul_left hw0 hw1 extent ids hids stage
      leftWeight p (polySmul rightWeight q))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left leftWeight _ _
        (finite_covariance_smul_right hw0 hw1 extent ids hids stage
          rightWeight p q))
      (Q'.eqv_symm (Q'.mul_assoc_eqv leftWeight rightWeight _)))

private theorem finite_covariance_sum_left {A : Type}
    (polynomial : A → RatPoly) (items : List A) (q : RatPoly) :
    finiteCovariance w hw0 hw1 extent ids hids
        (finitePolySum polynomial items) q stage ≈
      listQSum
        (fun item => finiteCovariance w hw0 hw1 extent ids hids
          (polynomial item) q stage)
        items := by
  induction items with
  | nil => exact finite_covariance_zero_left hw0 hw1 extent ids hids stage q
  | cons head tail ih =>
      exact Q'.eqv_trans _ _ _
        (finite_covariance_add_left hw0 hw1 extent ids hids stage
          (polynomial head) (finitePolySum polynomial tail) q)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)

private theorem finite_covariance_sum_right {A : Type}
    (p : RatPoly) (polynomial : A → RatPoly) (items : List A) :
    finiteCovariance w hw0 hw1 extent ids hids
        p (finitePolySum polynomial items) stage ≈
      listQSum
        (fun item => finiteCovariance w hw0 hw1 extent ids hids
          p (polynomial item) stage)
        items := by
  induction items with
  | nil =>
      change finiteCovariance w hw0 hw1 extent ids hids p polyZero stage ≈ 0
      have hcomm := finiteValue_coeff_congr w hw0 hw1 extent ids hids
        (polyMul p polyZero) polyZero
        (RatPolyCoeffEqv.mul_zero_right p) stage
      unfold finiteCovariance
      have hzero := finite_zero hw0 hw1 extent ids hids stage
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hcomm
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left _ _ _ hzero)))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' hzero
            (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv _)))
          (by decide))
  | cons head tail ih =>
      exact Q'.eqv_trans _ _ _
        (finite_covariance_add_right hw0 hw1 extent ids hids stage
          p (polynomial head) (finitePolySum polynomial tail))
        (Q'.add_eqv_congr' (Q'.eqv_refl _) ih)

private theorem finite_covariance_double_sum {A B : Type}
    (left : A → RatPoly) (leftItems : List A)
    (right : B → RatPoly) (rightItems : List B) :
    finiteCovariance w hw0 hw1 extent ids hids
        (finitePolySum left leftItems) (finitePolySum right rightItems) stage ≈
      listQSum
        (fun leftItem => listQSum
          (fun rightItem => finiteCovariance w hw0 hw1 extent ids hids
            (left leftItem) (right rightItem) stage)
          rightItems)
        leftItems := by
  refine Q'.eqv_trans _ _ _
    (finite_covariance_sum_left hw0 hw1 extent ids hids stage
      left leftItems (finitePolySum right rightItems)) ?_
  apply listQSum_congr_on
  intro leftItem _
  exact finite_covariance_sum_right hw0 hw1 extent ids hids stage
    (left leftItem) right rightItems

end FiniteCovarianceAlgebra

/-- Reusable exact pairwise expansion for a finite weighted polynomial sum
under one selected original action. -/
theorem finiteCovariance_weightedSum_pairwise {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (stage : Nat) {Index : Type}
    (weight : Index → Q') (localFactor : Index → RatPoly)
    (items : List Index) :
    finiteCovariance w hw0 hw1 extent ids hids
        (finitePolySum
          (fun item => polySmul (weight item) (localFactor item)) items)
        (finitePolySum
          (fun item => polySmul (weight item) (localFactor item)) items)
        stage ≈
      listQSum
        (fun leftItem => listQSum
          (fun rightItem =>
            (weight leftItem * weight rightItem) *
              finiteCovariance w hw0 hw1 extent ids hids
                (localFactor leftItem) (localFactor rightItem) stage)
          items)
        items := by
  let weighted := fun item : Index =>
    polySmul (weight item) (localFactor item)
  refine Q'.eqv_trans _ _ _
    (finite_covariance_double_sum hw0 hw1 extent ids hids stage
      weighted items weighted items) ?_
  apply listQSum_congr_on
  intro leftItem _
  apply listQSum_congr_on
  intro rightItem _
  simpa only [weighted] using
    (finite_covariance_weighted hw0 hw1 extent ids hids stage
      (weight leftItem) (weight rightItem)
      (localFactor leftItem) (localFactor rightItem))

/-- Reusable exact pairwise expansion for two independently placed finite
weighted polynomial sums under one selected original action. -/
theorem finiteCovariance_twoWeightedSums_pairwise {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (stage : Nat) {LeftIndex RightIndex : Type}
    (leftWeight : LeftIndex → Q') (leftFactor : LeftIndex → RatPoly)
    (leftItems : List LeftIndex)
    (rightWeight : RightIndex → Q') (rightFactor : RightIndex → RatPoly)
    (rightItems : List RightIndex) :
    finiteCovariance w hw0 hw1 extent ids hids
        (finitePolySum
          (fun item => polySmul (leftWeight item) (leftFactor item)) leftItems)
        (finitePolySum
          (fun item => polySmul (rightWeight item) (rightFactor item)) rightItems)
        stage ≈
      listQSum
        (fun leftItem => listQSum
          (fun rightItem =>
            (leftWeight leftItem * rightWeight rightItem) *
              finiteCovariance w hw0 hw1 extent ids hids
                (leftFactor leftItem) (rightFactor rightItem) stage)
          rightItems)
        leftItems := by
  let leftWeighted := fun item : LeftIndex =>
    polySmul (leftWeight item) (leftFactor item)
  let rightWeighted := fun item : RightIndex =>
    polySmul (rightWeight item) (rightFactor item)
  refine Q'.eqv_trans _ _ _
    (finite_covariance_double_sum hw0 hw1 extent ids hids stage
      leftWeighted leftItems rightWeighted rightItems) ?_
  apply listQSum_congr_on
  intro leftItem _
  apply listQSum_congr_on
  intro rightItem _
  simpa only [leftWeighted, rightWeighted] using
    (finite_covariance_weighted hw0 hw1 extent ids hids stage
      (leftWeight leftItem) (rightWeight rightItem)
      (leftFactor leftItem) (rightFactor rightItem))

/-- The exact coefficient-product pair sum for one chronological placement. -/
def originalBulkScalarSquareRemainderPairwiseCovariance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat) : Q' :=
  listQSum
    (fun leftFace => listQSum
      (fun rightFace =>
        (originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
          originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
        finiteCovariance w hw0 hw1
          (originalBulkScalarSquareRemainderExtent s n L)
          (originalBulkScalarSquareRemainderIds s n L)
          (originalBulkScalarSquareRemainderIds_physical s n L)
          (originalBulkScalarSquareRemainderFacePlaced s n offset L leftFace)
          (originalBulkScalarSquareRemainderFacePlaced s n offset L rightFace)
          stage)
      (bulkSourceFaces s))
    (bulkSourceFaces s)

/-- Exact pairwise expansion of the SAME selected-action bulk covariance.
Every local pair carries the product of its two original source weights. -/
theorem originalBulkScalarSquareRemainderSelectedCovariance_pairwise {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat) :
    originalBulkScalarSquareRemainderSelectedCovariance
        hw0 hw1 s hs stage n L offset ≈
      originalBulkScalarSquareRemainderPairwiseCovariance
        hw0 hw1 s hs stage n L offset := by
  let extent := originalBulkScalarSquareRemainderExtent s n L
  let ids := originalBulkScalarSquareRemainderIds s n L
  let hids := originalBulkScalarSquareRemainderIds_physical s n L
  let weight := originalBulkScalarSquareRemainderFaceWeight s hs
  let localFactor := originalBulkScalarSquareRemainderFacePlaced s n offset L
  let weighted := fun face : Z4Plaq => polySmul (weight face) (localFactor face)
  have hsum : originalBulkScalarSquareRemainderPlaced s hs n offset L =
      finitePolySum weighted (bulkSourceFaces s) := by
    simpa only [weight, localFactor, weighted] using
      (originalBulkScalarSquareRemainderPlaced_face_sum s hs n offset L)
  unfold originalBulkScalarSquareRemainderSelectedCovariance
    originalBulkScalarSquareRemainderPairwiseCovariance
  rw [hsum]
  refine Q'.eqv_trans _ _ _
    (finite_covariance_double_sum hw0 hw1 extent ids hids stage
      weighted (bulkSourceFaces s) weighted (bulkSourceFaces s)) ?_
  apply listQSum_congr_on
  intro leftFace _
  apply listQSum_congr_on
  intro rightFace _
  simpa only [weight, localFactor, weighted] using
    (finite_covariance_weighted hw0 hw1 extent ids hids stage
      (weight leftFace) (weight rightFace)
      (localFactor leftFace) (localFactor rightFace))

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderPlaced_face_sum
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderFace_interval
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderFace_local
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderFace_covariance_distance_bound
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderSelectedMean_windowRatio
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderOwnMean_endpoint_one
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderSelectedMean_zero_mismatch_square_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderSelectedMean_L_mismatch_square_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.finiteCovariance_weightedSum_pairwise
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.finiteCovariance_twoWeightedSums_pairwise
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance.originalBulkScalarSquareRemainderSelectedCovariance_pairwise
