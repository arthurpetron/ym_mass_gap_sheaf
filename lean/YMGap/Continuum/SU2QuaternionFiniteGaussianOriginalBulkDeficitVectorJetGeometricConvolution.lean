/-
# Width-uniform geometric convolution for the original vector jet

The exact vector face-pair covariance expansion is bounded by one universal
local amplitude times a symmetric geometric kernel.  The existing finite
Young inequality and four-dimensional L-infinity row cap collapse the full
double sum to the exact quarter-weight coefficient-square mass without a
face-count factor.

This is a SAME-ORIGINAL selected-covariance bound.  It does not compare the
pure lagged jet response with the FREE Gaussian law, prove a neighboring
margin, remove a cutoff, construct a continuum Hamiltonian, or prove the Clay
mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval (probeCap)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (singletonCarrier)
open YMGap.Continuum.BF4ExactSlabSummedCouplingDefects (amplitude singleton_budget)
open YMGap.Continuum.BF4ExactSlabTwoProbeDistanceDecay (distanceBudget)
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse (finiteCovariance)
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSizeGeometricSum (entropyRate)
open YMGap.Continuum.FiniteWeightedGramSOS (listQSum_mul_right)
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRatio heatRemainderBound)
open YMGap.Continuum.SepLatticeZ4Linf (cPlaq linfDist natDist vComp)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution
  (weighted_symmetric_kernel_pair_sum_le linfDist_comm linfDist_timeShiftPlaquette)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetPairwiseCovariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinfGeometricSum

local infix:50 " ≈ " => Q'.eqv

/-- Face-independent interval cap of the fixed local vector character. -/
def originalBulkVectorQuadraticJetLocalCap : Q' :=
  probeCap [(((0, 0, 0, 0), Z4Plane.p01), vectorQuadraticJetTerms)]

theorem originalBulkVectorQuadraticJetFaceCap_eq_localCap
    (n offset : Nat) (face : Z4Plaq) :
    originalBulkVectorQuadraticJetFaceCap n offset face =
      originalBulkVectorQuadraticJetLocalCap := by
  rfl

theorem originalBulkVectorQuadraticJetLocalCap_nonnegative :
    (0 : Q') ≤ originalBulkVectorQuadraticJetLocalCap := by
  simp only [originalBulkVectorQuadraticJetLocalCap, probeCap,
    YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval.factorCap,
    YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval.termCap,
    vectorQuadraticJetTerms,
    YMGap.Continuum.QuaternionHaarPolynomialSquareBound.characterBound,
    YMGap.Continuum.QuaternionHaarPolynomialSquareBound.sumBound]
  decide

/-- Translation-independent amplitude for two singleton vector factors. -/
def originalBulkVectorQuadraticJetPairAmplitude
    (w : Q') (hd : heatRemainderBound w < 1)
    (hsRate : entropyRate 625 (adjustedCoreRate w hd) < 1) : Q' :=
  ((((originalBulkVectorQuadraticJetLocalCap *
        originalBulkVectorQuadraticJetLocalCap +
      originalBulkVectorQuadraticJetLocalCap *
        originalBulkVectorQuadraticJetLocalCap) *
      probePrefactor w hd 8) * Q'.ofNat 1562500) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd))
      (HKPos.one_sub_pos hsRate))

theorem originalBulkVectorQuadraticJetPairAmplitude_nonnegative
    (w : Q') (hd : heatRemainderBound w < 1)
    (hsRate : entropyRate 625 (adjustedCoreRate w hd) < 1) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetPairAmplitude w hd hsRate := by
  unfold originalBulkVectorQuadraticJetPairAmplitude
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _
            originalBulkVectorQuadraticJetLocalCap_nonnegative
            originalBulkVectorQuadraticJetLocalCap_nonnegative)
          (Q'.mul_nonneg _ _
            originalBulkVectorQuadraticJetLocalCap_nonnegative
            originalBulkVectorQuadraticJetLocalCap_nonnegative))
        (probePrefactor_nonnegative w hd 8))
      (ClusterCount.ofNat_nonneg 1562500))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- Exact factorization of the singleton distance budget after removing the
common chronological translation. -/
theorem originalBulkVectorQuadraticJetFace_distanceBudget_factor
    (w : Q') (hd : heatRemainderBound w < 1)
    (hsRate : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (n offset : Nat) (leftFace rightFace : Z4Plaq) :
    distanceBudget
        (singletonCarrier
          (originalBulkVectorQuadraticJetPlacedFace n offset leftFace))
        (singletonCarrier
          (originalBulkVectorQuadraticJetPlacedFace n offset rightFace))
        w hd hsRate
        (originalBulkVectorQuadraticJetFaceCap n offset leftFace)
        (originalBulkVectorQuadraticJetFaceCap n offset rightFace) ≈
      originalBulkVectorQuadraticJetPairAmplitude w hd hsRate *
        (entropyRate 625 (adjustedCoreRate w hd)) ^
          (linfDist leftFace rightFace - 1) := by
  rw [originalBulkVectorQuadraticJetFaceCap_eq_localCap,
    originalBulkVectorQuadraticJetFaceCap_eq_localCap]
  refine Q'.eqv_trans _ _ _
    (singleton_budget
      (singletonCarrier
        (originalBulkVectorQuadraticJetPlacedFace n offset leftFace))
      (originalBulkVectorQuadraticJetPlacedFace n offset rightFace)
      w hd hsRate originalBulkVectorQuadraticJetLocalCap
      originalBulkVectorQuadraticJetLocalCap) ?_
  unfold amplitude originalBulkVectorQuadraticJetPairAmplitude
    originalBulkVectorQuadraticJetPlacedFace
  simp only [singletonCarrier, List.length_cons, List.length_nil, edgesOf]
  rw [linfDist_timeShiftPlaquette]
  rfl

def originalBulkVectorQuadraticJetGeometricRate
    (w : Q') (hd : heatRemainderBound w < 1) : Q' :=
  entropyRate 625 (adjustedCoreRate w hd)

theorem originalBulkVectorQuadraticJetGeometricRate_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetGeometricRate w hd := by
  unfold originalBulkVectorQuadraticJetGeometricRate entropyRate
  exact Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg 625)
    (adjustedCoreRate_nonnegative (Q'.le_of_lt hw0) hd)

def originalBulkVectorQuadraticJetGeometricKernel
    (w : Q') (hd : heatRemainderBound w < 1)
    (leftFace rightFace : Z4Plaq) : Q' :=
  (originalBulkVectorQuadraticJetGeometricRate w hd) ^
    (linfDist leftFace rightFace - 1)

theorem originalBulkVectorQuadraticJetGeometricKernel_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (leftFace rightFace : Z4Plaq) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetGeometricKernel
      w hd leftFace rightFace := by
  unfold originalBulkVectorQuadraticJetGeometricKernel
  exact Q'.pow_nonneg _
    (originalBulkVectorQuadraticJetGeometricRate_nonnegative hw0 hd) _

theorem originalBulkVectorQuadraticJetGeometricKernel_comm
    (w : Q') (hd : heatRemainderBound w < 1)
    (leftFace rightFace : Z4Plaq) :
    originalBulkVectorQuadraticJetGeometricKernel w hd leftFace rightFace =
      originalBulkVectorQuadraticJetGeometricKernel w hd rightFace leftFace := by
  unfold originalBulkVectorQuadraticJetGeometricKernel
  rw [linfDist_comm]

def originalBulkVectorQuadraticJetGeometricRowCap
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1) : Q' :=
  tailCap
    (originalBulkVectorQuadraticJetGeometricRate_nonnegative hw0 hd)
    hsRate 1 0

theorem originalBulkVectorQuadraticJetGeometricRow_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (leftFace : Z4Plaq) :
    listQSum
        (originalBulkVectorQuadraticJetGeometricKernel w hd leftFace)
        (bulkSourceFaces s) ≤
      originalBulkVectorQuadraticJetGeometricRowCap hw0 hd hsRate := by
  unfold originalBulkVectorQuadraticJetGeometricKernel
    originalBulkVectorQuadraticJetGeometricRowCap
  exact finite_sum_bound
    (originalBulkVectorQuadraticJetGeometricRate_nonnegative hw0 hd)
    hsRate leftFace 1 (bulkSourceFaces s) (bulkSourceFaces_nodup s)

def originalBulkVectorQuadraticJetFaceWeightSquareMass
    (s : Nat) (hs : 0 < s) : Q' :=
  listQSum
    (fun face =>
      originalBulkVectorQuadraticJetFaceWeight s hs face *
        originalBulkVectorQuadraticJetFaceWeight s hs face)
    (bulkSourceFaces s)

def originalBulkVectorQuadraticJetWeightedGeometricPairSum
    (w : Q') (hd : heatRemainderBound w < 1)
    (s : Nat) (hs : 0 < s) : Q' :=
  listQSum
    (fun leftFace => listQSum
      (fun rightFace =>
        (originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
          originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
        originalBulkVectorQuadraticJetGeometricKernel
          w hd leftFace rightFace)
      (bulkSourceFaces s))
    (bulkSourceFaces s)

theorem originalBulkVectorQuadraticJetFaceWeight_nonnegative
    (s : Nat) (hs : 0 < s) (face : Z4Plaq)
    (hface : face ∈ bulkSourceFaces s) :
    (0 : Q') ≤ originalBulkVectorQuadraticJetFaceWeight s hs face := by
  unfold originalBulkVectorQuadraticJetFaceWeight
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (bulkSourceCoefficient_pos hs hface))

theorem originalBulkVectorQuadraticJetWeightedGeometricPairSum_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) :
    originalBulkVectorQuadraticJetWeightedGeometricPairSum w hd s hs ≤
      originalBulkVectorQuadraticJetGeometricRowCap hw0 hd hsRate *
          originalBulkVectorQuadraticJetFaceWeightSquareMass s hs +
        originalBulkVectorQuadraticJetGeometricRowCap hw0 hd hsRate *
          originalBulkVectorQuadraticJetFaceWeightSquareMass s hs := by
  unfold originalBulkVectorQuadraticJetWeightedGeometricPairSum
    originalBulkVectorQuadraticJetFaceWeightSquareMass
  apply weighted_symmetric_kernel_pair_sum_le
  · exact originalBulkVectorQuadraticJetFaceWeight_nonnegative s hs
  · intro leftFace _ rightFace _
    exact originalBulkVectorQuadraticJetGeometricKernel_nonnegative
      hw0 hd leftFace rightFace
  · exact originalBulkVectorQuadraticJetGeometricKernel_comm w hd
  · intro leftFace _
    exact originalBulkVectorQuadraticJetGeometricRow_le
      hw0 hd hsRate s leftFace

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' _
  | head :: tail, h =>
      Q'.add_le_add (h head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => h item (List.mem_cons_of_mem head hitem)))

private theorem abs_listQSum_le_sum_abs_local {A : Type}
    (value : A → Q') : ∀ items : List A,
    Q'.abs (listQSum value items) ≤
      listQSum (fun item => Q'.abs (value item)) items
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail))
        (Q'.add_le_add
          (Q'.le_refl' (Q'.abs (value head)))
          (abs_listQSum_le_sum_abs_local value tail))

private theorem weightedFaceCovarianceTerm_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat)
    (hoffset : offset ≤ L) (leftFace rightFace : Z4Plaq)
    (hleft : leftFace ∈ bulkSourceFaces s)
    (hright : rightFace ∈ bulkSourceFaces s) :
    Q'.abs
        ((originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
            originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
          finiteCovariance w hw0 hw1
            (originalBulkVectorQuadraticJetExtent s n L)
            (originalBulkVectorQuadraticJetIds s n L)
            (originalBulkVectorQuadraticJetIds_physical s n L)
            (originalBulkVectorQuadraticJetFacePlaced
              s n offset L leftFace)
            (originalBulkVectorQuadraticJetFacePlaced
              s n offset L rightFace)
            stage) ≤
      originalBulkVectorQuadraticJetPairAmplitude w hd hsRate *
        ((originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
            originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
          originalBulkVectorQuadraticJetGeometricKernel
            w hd leftFace rightFace) := by
  let leftWeight := originalBulkVectorQuadraticJetFaceWeight s hs leftFace
  let rightWeight := originalBulkVectorQuadraticJetFaceWeight s hs rightFace
  let covariance := finiteCovariance w hw0 hw1
    (originalBulkVectorQuadraticJetExtent s n L)
    (originalBulkVectorQuadraticJetIds s n L)
    (originalBulkVectorQuadraticJetIds_physical s n L)
    (originalBulkVectorQuadraticJetFacePlaced s n offset L leftFace)
    (originalBulkVectorQuadraticJetFacePlaced s n offset L rightFace) stage
  have hweightProduct : (0 : Q') ≤ leftWeight * rightWeight :=
    Q'.mul_nonneg _ _
      (originalBulkVectorQuadraticJetFaceWeight_nonnegative
        s hs leftFace hleft)
      (originalBulkVectorQuadraticJetFaceWeight_nonnegative
        s hs rightFace hright)
  have hcovariance : Q'.abs covariance ≤
      distanceBudget
        (singletonCarrier
          (originalBulkVectorQuadraticJetPlacedFace n offset leftFace))
        (singletonCarrier
          (originalBulkVectorQuadraticJetPlacedFace n offset rightFace))
        w hd hsRate
        (originalBulkVectorQuadraticJetFaceCap n offset leftFace)
        (originalBulkVectorQuadraticJetFaceCap n offset rightFace) :=
    originalBulkVectorQuadraticJetFace_covariance_distance_bound
      hw0 hw1 hsmall hd hsRate s stage n L offset hoffset
      leftFace rightFace hleft hright
  refine Q'.le_trans' _ _ _
    (YMGap.Constructive.ExpNeg.abs_mul_le
      (leftWeight * rightWeight) covariance) ?_
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hweightProduct]
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcovariance hweightProduct) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (leftWeight * rightWeight) _ _
      (originalBulkVectorQuadraticJetFace_distanceBudget_factor
        w hd hsRate n offset leftFace rightFace)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (leftWeight * rightWeight)
      (originalBulkVectorQuadraticJetPairAmplitude w hd hsRate)
      (originalBulkVectorQuadraticJetGeometricKernel
        w hd leftFace rightFace))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv
        (leftWeight * rightWeight)
        (originalBulkVectorQuadraticJetPairAmplitude w hd hsRate))) ?_
  exact Q'.mul_assoc_eqv
    (originalBulkVectorQuadraticJetPairAmplitude w hd hsRate)
    (leftWeight * rightWeight)
    (originalBulkVectorQuadraticJetGeometricKernel w hd leftFace rightFace)

/-- SAME-selected vector-jet covariance bounded by a width-independent
geometric constant times the exact quarter-weight square mass. -/
theorem originalBulkVectorQuadraticJetSelectedCovariance_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkVectorQuadraticJetGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat)
    (hoffset : offset ≤ L) :
    Q'.abs
        (originalBulkVectorQuadraticJetSelectedCovariance
          hw0 hw1 s hs stage n L offset) ≤
      originalBulkVectorQuadraticJetPairAmplitude w hd hsRate *
        (originalBulkVectorQuadraticJetGeometricRowCap hw0 hd hsRate *
            originalBulkVectorQuadraticJetFaceWeightSquareMass s hs +
          originalBulkVectorQuadraticJetGeometricRowCap hw0 hd hsRate *
            originalBulkVectorQuadraticJetFaceWeightSquareMass s hs) := by
  let amplitude := originalBulkVectorQuadraticJetPairAmplitude w hd hsRate
  let geometricPairSum :=
    originalBulkVectorQuadraticJetWeightedGeometricPairSum w hd s hs
  have hpairwise := originalBulkVectorQuadraticJetSelectedCovariance_pairwise
    hw0 hw1 s hs stage n L offset
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hpairwise)) ?_
  unfold originalBulkVectorQuadraticJetPairwiseCovariance
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local _ (bulkSourceFaces s)) ?_
  refine Q'.le_trans' _ _ _
    (listQSum_le_termwise_local _ _ (bulkSourceFaces s)
      (fun leftFace _ =>
        abs_listQSum_le_sum_abs_local _ (bulkSourceFaces s))) ?_
  have htermwise :
      listQSum
          (fun leftFace => listQSum
            (fun rightFace =>
              Q'.abs
                ((originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
                    originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
                  finiteCovariance w hw0 hw1
                    (originalBulkVectorQuadraticJetExtent s n L)
                    (originalBulkVectorQuadraticJetIds s n L)
                    (originalBulkVectorQuadraticJetIds_physical s n L)
                    (originalBulkVectorQuadraticJetFacePlaced
                      s n offset L leftFace)
                    (originalBulkVectorQuadraticJetFacePlaced
                      s n offset L rightFace)
                    stage))
            (bulkSourceFaces s))
          (bulkSourceFaces s) ≤
        listQSum
          (fun leftFace => listQSum
            (fun rightFace =>
              amplitude *
                ((originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
                    originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
                  originalBulkVectorQuadraticJetGeometricKernel
                    w hd leftFace rightFace))
            (bulkSourceFaces s))
          (bulkSourceFaces s) := by
    apply listQSum_le_termwise_local
    intro leftFace hleft
    apply listQSum_le_termwise_local
    intro rightFace hright
    exact weightedFaceCovarianceTerm_abs_le
      hw0 hw1 hsmall hd hsRate s hs stage n L offset hoffset
      leftFace rightFace hleft hright
  refine Q'.le_trans' _ _ _ htermwise ?_
  have hfactor :
      listQSum
          (fun leftFace => listQSum
            (fun rightFace =>
              amplitude *
                ((originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
                    originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
                  originalBulkVectorQuadraticJetGeometricKernel
                    w hd leftFace rightFace))
            (bulkSourceFaces s))
          (bulkSourceFaces s) ≈
        amplitude * geometricPairSum := by
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_on _ _ (bulkSourceFaces s) (fun leftFace _ =>
        listQSum_mul_left amplitude
          (fun rightFace =>
            (originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
              originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
            originalBulkVectorQuadraticJetGeometricKernel
              w hd leftFace rightFace)
          (bulkSourceFaces s))) ?_
    exact listQSum_mul_left amplitude
      (fun leftFace => listQSum
        (fun rightFace =>
          (originalBulkVectorQuadraticJetFaceWeight s hs leftFace *
            originalBulkVectorQuadraticJetFaceWeight s hs rightFace) *
          originalBulkVectorQuadraticJetGeometricKernel
            w hd leftFace rightFace)
        (bulkSourceFaces s))
      (bulkSourceFaces s)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (originalBulkVectorQuadraticJetWeightedGeometricPairSum_le
      hw0 hd hsRate s hs)
    (originalBulkVectorQuadraticJetPairAmplitude_nonnegative w hd hsRate)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetLocalCap
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetFaceCap_eq_localCap
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetPairAmplitude
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetPairAmplitude_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetFace_distanceBudget_factor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetGeometricRate_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetGeometricKernel_comm
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetGeometricRow_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetFaceWeightSquareMass
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetWeightedGeometricPairSum_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitVectorJetGeometricConvolution.originalBulkVectorQuadraticJetSelectedCovariance_geometric_le
