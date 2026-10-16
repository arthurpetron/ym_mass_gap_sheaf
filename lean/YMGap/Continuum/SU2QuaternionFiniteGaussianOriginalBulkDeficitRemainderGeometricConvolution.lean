/-
# Geometric convolution for the original bulk scalar remainder

The exact face-pair covariance expansion is converted into a genuinely
volume-independent spatial convolution.  The key finite inequality is the
symmetric-kernel Young bound

  sum_x sum_y a_x a_y K(x,y)
    <= 2 C sum_x a_x^2

when the weights and kernel are nonnegative, the kernel is symmetric, and
every row sum is at most C.  This avoids the false `(3*s^3)^2` face-pair
cardinality loss.  The existing four-dimensional L-infinity geometric sum
supplies C for the actual bulk-source face list.

This remains a finite selected-action estimate.  It does not compare the
shifted vector jet with the FREE law, remove the cutoff, construct a
Hamiltonian, or prove the Clay mass gap.
-/

import YMGap.Constructive.CRealAlg
import YMGap.Continuum.BF4ExactSlabSummedCouplingDefects
import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance
import YMGap.Continuum.Z4LinfGeometricSum

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution

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
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSizeGeometricSum (entropyRate)
open YMGap.Continuum.FiniteWeightedGramSOS (listQSum_mul_right)
open YMGap.Continuum.QuaternionHaarCharacterInterval (heatRemainderBound)
open YMGap.Continuum.SepLatticeZ4Linf (cPlaq linfDist natDist vComp)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum)
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitJetRemainder
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderPairwiseCovariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinfGeometricSum

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm =>
      Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hterm item (List.mem_cons_of_mem head hitem)))

/-- Finite symmetric-kernel Young inequality.  Its constant is independent
of the number of items; only a uniform row-sum cap is paid. -/
theorem weighted_symmetric_kernel_pair_sum_le {A : Type}
    (items : List A) (weight : A → Q') (kernel : A → A → Q') (cap : Q')
    (hweight : ∀ item, item ∈ items → (0 : Q') ≤ weight item)
    (hkernel : ∀ left, left ∈ items → ∀ right, right ∈ items →
      (0 : Q') ≤ kernel left right)
    (hsymmetric : ∀ left right, kernel left right = kernel right left)
    (hrow : ∀ left, left ∈ items →
      listQSum (kernel left) items ≤ cap) :
    listQSum
        (fun left => listQSum
          (fun right => (weight left * weight right) * kernel left right)
          items)
        items ≤
      cap * listQSum (fun item => weight item * weight item) items +
        cap * listQSum (fun item => weight item * weight item) items := by
  let squareMass := listQSum (fun item => weight item * weight item) items
  let leftPart := listQSum
    (fun left => listQSum
      (fun right => (weight left * weight left) * kernel left right)
      items)
    items
  let rightPart := listQSum
    (fun left => listQSum
      (fun right => (weight right * weight right) * kernel left right)
      items)
    items
  have hpointwise : ∀ left, left ∈ items → ∀ right, right ∈ items →
      (weight left * weight right) * kernel left right ≤
        ((weight left * weight left) + (weight right * weight right)) *
          kernel left right := by
    intro left hleft right hright
    have hproduct : (0 : Q') ≤ weight left * weight right :=
      Q'.mul_nonneg _ _ (hweight left hleft) (hweight right hright)
    have hyoung : weight left * weight right ≤
        weight left * weight left + weight right * weight right :=
      Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg
          (weight left * weight right) (weight left * weight right) hproduct)
        (amgm_two (weight left) (weight right))
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hyoung
      (hkernel left hleft right hright)
  have hmajor :
      listQSum
          (fun left => listQSum
            (fun right => (weight left * weight right) * kernel left right)
            items)
          items ≤
        listQSum
          (fun left => listQSum
            (fun right =>
              ((weight left * weight left) + (weight right * weight right)) *
                kernel left right)
            items)
          items := by
    apply listQSum_le_termwise_local
    intro left hleft
    apply listQSum_le_termwise_local
    intro right hright
    exact hpointwise left hleft right hright
  have hsplit :
      listQSum
          (fun left => listQSum
            (fun right =>
              ((weight left * weight left) + (weight right * weight right)) *
                kernel left right)
            items)
          items ≈
        leftPart + rightPart := by
    dsimp only [leftPart, rightPart]
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_on
        (fun left => listQSum
          (fun right =>
            ((weight left * weight left) + (weight right * weight right)) *
              kernel left right)
          items)
        (fun left =>
          listQSum
              (fun right => (weight left * weight left) * kernel left right)
              items +
            listQSum
              (fun right => (weight right * weight right) * kernel left right)
              items)
        items (fun left _ => ?_)) ?_
    · refine Q'.eqv_trans _ _ _
        (listQSum_congr_on _ _ items (fun right _ =>
          Q'.add_mul_eqv
            (weight left * weight left)
            (weight right * weight right)
            (kernel left right))) ?_
      exact listQSum_add
        (fun right => (weight left * weight left) * kernel left right)
        (fun right => (weight right * weight right) * kernel left right)
        items
    · exact listQSum_add
        (fun left => listQSum
          (fun right => (weight left * weight left) * kernel left right) items)
        (fun left => listQSum
          (fun right => (weight right * weight right) * kernel left right) items)
        items
  have hleft : leftPart ≤ cap * squareMass := by
    dsimp only [leftPart, squareMass]
    refine Q'.le_trans' _ _ _
      (listQSum_le_termwise_local
        (fun left => listQSum
          (fun right => (weight left * weight left) * kernel left right)
          items)
        (fun left => (weight left * weight left) * cap)
        items (fun left hleft => ?_)) ?_
    · refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (listQSum_mul_left
          (weight left * weight left) (kernel left) items)) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ (hrow left hleft)
        (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg (weight left))
    · refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (listQSum_mul_right
          (fun item => weight item * weight item) cap items) ?_
      exact Q'.mul_comm_eqv squareMass cap
  have hright : rightPart ≤ cap * squareMass := by
    dsimp only [rightPart, squareMass]
    let swapped := listQSum
      (fun right => listQSum
        (fun left => (weight right * weight right) * kernel right left)
        items)
      items
    have hswap : rightPart ≈ swapped := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (listQSum_swap
          (fun left right => (weight right * weight right) * kernel left right)
          items items)) ?_
      apply listQSum_congr_on
      intro right _
      apply listQSum_congr_on
      intro left _
      rw [hsymmetric left right]
      exact Q'.eqv_refl _
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hswap) ?_
    refine Q'.le_trans' _ _ _
      (listQSum_le_termwise_local
        (fun right => listQSum
          (fun left => (weight right * weight right) * kernel right left)
          items)
        (fun right => (weight right * weight right) * cap)
        items (fun right hright => ?_)) ?_
    · refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (listQSum_mul_left
          (weight right * weight right) (kernel right) items)) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ (hrow right hright)
        (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg (weight right))
    · refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (listQSum_mul_right
          (fun item => weight item * weight item) cap items) ?_
      exact Q'.mul_comm_eqv squareMass cap
  exact Q'.le_trans' _ _ _ hmajor
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.add_le_add hleft hright))

private theorem natDist_comm (left right : Nat) :
    natDist left right = natDist right left := by
  unfold natDist
  omega

theorem linfDist_comm (left right : Z4Plaq) :
    linfDist left right = linfDist right left := by
  unfold linfDist
  rw [natDist_comm (cPlaq left Dir4.x0) (cPlaq right Dir4.x0),
    natDist_comm (cPlaq left Dir4.x1) (cPlaq right Dir4.x1),
    natDist_comm (cPlaq left Dir4.x2) (cPlaq right Dir4.x2),
    natDist_comm (cPlaq left Dir4.x3) (cPlaq right Dir4.x3)]

theorem linfDist_timeShiftPlaquette (shift : Nat) (left right : Z4Plaq) :
    linfDist (timeShiftPlaquette shift left) (timeShiftPlaquette shift right) =
      linfDist left right := by
  obtain ⟨⟨leftX, leftY, leftZ, leftT⟩, leftPlane⟩ := left
  obtain ⟨⟨rightX, rightY, rightZ, rightT⟩, rightPlane⟩ := right
  simp only [linfDist, cPlaq, vComp, timeShiftPlaquette, timeShiftVertex,
    natDist, Nat.add_sub_add_right]

/-- The face-independent interval cap of the fixed local remainder word. -/
def originalBulkScalarSquareRemainderLocalCap : Q' :=
  probeCap [(((0, 0, 0, 0), Z4Plane.p01), scalarSquareRemainderTerms)]

theorem originalBulkScalarSquareRemainderFaceCap_eq_localCap
    (n offset : Nat) (face : Z4Plaq) :
    originalBulkScalarSquareRemainderFaceCap n offset face =
      originalBulkScalarSquareRemainderLocalCap := by
  rfl

theorem originalBulkScalarSquareRemainderLocalCap_nonnegative :
    (0 : Q') ≤ originalBulkScalarSquareRemainderLocalCap := by
  simp only [originalBulkScalarSquareRemainderLocalCap, probeCap,
    YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval.factorCap,
    YMGap.Continuum.BF4ExactSlabFixedSpatialProbeInterval.termCap,
    scalarSquareRemainderTerms,
    YMGap.Continuum.QuaternionHaarPolynomialSquareBound.characterBound,
    YMGap.Continuum.QuaternionHaarPolynomialSquareBound.sumBound]
  decide

/-- Translation-independent amplitude for two singleton local remainder
factors. -/
def originalBulkScalarSquareRemainderPairAmplitude
    (w : Q') (hd : heatRemainderBound w < 1)
    (hsRate : entropyRate 625 (adjustedCoreRate w hd) < 1) : Q' :=
  ((((originalBulkScalarSquareRemainderLocalCap *
        originalBulkScalarSquareRemainderLocalCap +
      originalBulkScalarSquareRemainderLocalCap *
        originalBulkScalarSquareRemainderLocalCap) *
      probePrefactor w hd 8) * Q'.ofNat 1562500) *
    Q'.recipPos (1 + -entropyRate 625 (adjustedCoreRate w hd))
      (HKPos.one_sub_pos hsRate))

theorem originalBulkScalarSquareRemainderPairAmplitude_nonnegative
    (w : Q') (hd : heatRemainderBound w < 1)
    (hsRate : entropyRate 625 (adjustedCoreRate w hd) < 1) :
    (0 : Q') ≤
      originalBulkScalarSquareRemainderPairAmplitude w hd hsRate := by
  unfold originalBulkScalarSquareRemainderPairAmplitude
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.zero_le_add _ _
          (Q'.mul_nonneg _ _
            originalBulkScalarSquareRemainderLocalCap_nonnegative
            originalBulkScalarSquareRemainderLocalCap_nonnegative)
          (Q'.mul_nonneg _ _
            originalBulkScalarSquareRemainderLocalCap_nonnegative
            originalBulkScalarSquareRemainderLocalCap_nonnegative))
        (probePrefactor_nonnegative w hd 8))
      (ClusterCount.ofNat_nonneg 1562500))
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

/-- The existing singleton distance budget is exactly one universal
amplitude times the unshifted L-infinity kernel. -/
theorem originalBulkScalarSquareRemainderFace_distanceBudget_factor
    (w : Q') (hd : heatRemainderBound w < 1)
    (hsRate : entropyRate 625 (adjustedCoreRate w hd) < 1)
    (n offset : Nat) (leftFace rightFace : Z4Plaq) :
    distanceBudget
        (singletonCarrier
          (originalBulkScalarSquareRemainderPlacedFace n offset leftFace))
        (singletonCarrier
          (originalBulkScalarSquareRemainderPlacedFace n offset rightFace))
        w hd hsRate
        (originalBulkScalarSquareRemainderFaceCap n offset leftFace)
        (originalBulkScalarSquareRemainderFaceCap n offset rightFace) ≈
      originalBulkScalarSquareRemainderPairAmplitude w hd hsRate *
        (entropyRate 625 (adjustedCoreRate w hd)) ^
          (linfDist leftFace rightFace - 1) := by
  rw [originalBulkScalarSquareRemainderFaceCap_eq_localCap,
    originalBulkScalarSquareRemainderFaceCap_eq_localCap]
  refine Q'.eqv_trans _ _ _
    (singleton_budget
      (singletonCarrier
        (originalBulkScalarSquareRemainderPlacedFace n offset leftFace))
      (originalBulkScalarSquareRemainderPlacedFace n offset rightFace)
      w hd hsRate originalBulkScalarSquareRemainderLocalCap
      originalBulkScalarSquareRemainderLocalCap) ?_
  unfold amplitude originalBulkScalarSquareRemainderPairAmplitude
    originalBulkScalarSquareRemainderPlacedFace
  simp only [singletonCarrier, List.length_cons, List.length_nil, edgesOf]
  rw [linfDist_timeShiftPlaquette]
  rfl

/-- The positive geometric rate already present in the selected-action
two-probe estimate. -/
def originalBulkScalarSquareRemainderGeometricRate
    (w : Q') (hd : heatRemainderBound w < 1) : Q' :=
  entropyRate 625 (adjustedCoreRate w hd)

theorem originalBulkScalarSquareRemainderGeometricRate_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderGeometricRate w hd := by
  unfold originalBulkScalarSquareRemainderGeometricRate entropyRate
  exact Q'.mul_nonneg _ _ (ClusterCount.ofNat_nonneg 625)
    (adjustedCoreRate_nonnegative (Q'.le_of_lt hw0) hd)

/-- Symmetric spatial kernel after removing the common chronological shift. -/
def originalBulkScalarSquareRemainderGeometricKernel
    (w : Q') (hd : heatRemainderBound w < 1)
    (leftFace rightFace : Z4Plaq) : Q' :=
  (originalBulkScalarSquareRemainderGeometricRate w hd) ^
    (linfDist leftFace rightFace - 1)

theorem originalBulkScalarSquareRemainderGeometricKernel_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (leftFace rightFace : Z4Plaq) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderGeometricKernel
      w hd leftFace rightFace := by
  unfold originalBulkScalarSquareRemainderGeometricKernel
  exact Q'.pow_nonneg _
    (originalBulkScalarSquareRemainderGeometricRate_nonnegative hw0 hd) _

theorem originalBulkScalarSquareRemainderGeometricKernel_comm
    (w : Q') (hd : heatRemainderBound w < 1)
    (leftFace rightFace : Z4Plaq) :
    originalBulkScalarSquareRemainderGeometricKernel
        w hd leftFace rightFace =
      originalBulkScalarSquareRemainderGeometricKernel
        w hd rightFace leftFace := by
  unfold originalBulkScalarSquareRemainderGeometricKernel
  rw [linfDist_comm]

/-- Uniform row cap for the actual bulk-source face list.  No side length or
face count appears in the cap. -/
def originalBulkScalarSquareRemainderGeometricRowCap
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1) : Q' :=
  tailCap
    (originalBulkScalarSquareRemainderGeometricRate_nonnegative hw0 hd)
    hsRate 1 0

theorem originalBulkScalarSquareRemainderGeometricRow_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (leftFace : Z4Plaq) :
    listQSum
        (originalBulkScalarSquareRemainderGeometricKernel w hd leftFace)
        (bulkSourceFaces s) ≤
      originalBulkScalarSquareRemainderGeometricRowCap hw0 hd hsRate := by
  unfold originalBulkScalarSquareRemainderGeometricKernel
    originalBulkScalarSquareRemainderGeometricRowCap
  exact finite_sum_bound
    (originalBulkScalarSquareRemainderGeometricRate_nonnegative hw0 hd)
    hsRate leftFace 1 (bulkSourceFaces s) (bulkSourceFaces_nodup s)

/-- Exact quarter-weight coefficient-square mass of the bulk remainder. -/
def originalBulkScalarSquareRemainderFaceWeightSquareMass
    (s : Nat) (hs : 0 < s) : Q' :=
  listQSum
    (fun face =>
      originalBulkScalarSquareRemainderFaceWeight s hs face *
        originalBulkScalarSquareRemainderFaceWeight s hs face)
    (bulkSourceFaces s)

/-- The positive weighted geometric pair sum that majorizes the absolute
face-pair covariance expansion after the universal amplitude is removed. -/
def originalBulkScalarSquareRemainderWeightedGeometricPairSum
    (w : Q') (hd : heatRemainderBound w < 1)
    (s : Nat) (hs : 0 < s) : Q' :=
  listQSum
    (fun leftFace => listQSum
      (fun rightFace =>
        (originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
          originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
        originalBulkScalarSquareRemainderGeometricKernel
          w hd leftFace rightFace)
      (bulkSourceFaces s))
    (bulkSourceFaces s)

theorem originalBulkScalarSquareRemainderFaceWeight_nonnegative
    (s : Nat) (hs : 0 < s) (face : Z4Plaq)
    (hface : face ∈ bulkSourceFaces s) :
    (0 : Q') ≤ originalBulkScalarSquareRemainderFaceWeight s hs face := by
  unfold originalBulkScalarSquareRemainderFaceWeight
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.le_of_lt (bulkSourceCoefficient_pos hs hface))

/-- Width-uniform coefficient-square convolution.  The full double sum pays
twice one geometric row cap, not the square of the number of source faces. -/
theorem originalBulkScalarSquareRemainderWeightedGeometricPairSum_le
    {w : Q'} (hw0 : (0 : Q') < w)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) :
    originalBulkScalarSquareRemainderWeightedGeometricPairSum w hd s hs ≤
      originalBulkScalarSquareRemainderGeometricRowCap hw0 hd hsRate *
          originalBulkScalarSquareRemainderFaceWeightSquareMass s hs +
        originalBulkScalarSquareRemainderGeometricRowCap hw0 hd hsRate *
          originalBulkScalarSquareRemainderFaceWeightSquareMass s hs := by
  unfold originalBulkScalarSquareRemainderWeightedGeometricPairSum
    originalBulkScalarSquareRemainderFaceWeightSquareMass
  apply weighted_symmetric_kernel_pair_sum_le
  · exact originalBulkScalarSquareRemainderFaceWeight_nonnegative s hs
  · intro leftFace _ rightFace _
    exact originalBulkScalarSquareRemainderGeometricKernel_nonnegative
      hw0 hd leftFace rightFace
  · exact originalBulkScalarSquareRemainderGeometricKernel_comm w hd
  · intro leftFace _
    exact originalBulkScalarSquareRemainderGeometricRow_le
      hw0 hd hsRate s leftFace

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

/-- Absolute value of one weighted local covariance term, with all
face-dependence reduced to the symmetric geometric kernel. -/
private theorem weightedFaceCovarianceTerm_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : YMGap.Continuum.QuaternionHaarCharacterInterval.heatRatio w ≤
      HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat)
    (hoffset : offset ≤ L) (leftFace rightFace : Z4Plaq)
    (hleft : leftFace ∈ bulkSourceFaces s)
    (hright : rightFace ∈ bulkSourceFaces s) :
    Q'.abs
        ((originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
            originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
          YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.finiteCovariance
            w hw0 hw1
            (originalBulkScalarSquareRemainderExtent s n L)
            (originalBulkScalarSquareRemainderIds s n L)
            (originalBulkScalarSquareRemainderIds_physical s n L)
            (originalBulkScalarSquareRemainderFacePlaced
              s n offset L leftFace)
            (originalBulkScalarSquareRemainderFacePlaced
              s n offset L rightFace)
            stage) ≤
      originalBulkScalarSquareRemainderPairAmplitude w hd hsRate *
        ((originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
            originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
          originalBulkScalarSquareRemainderGeometricKernel
            w hd leftFace rightFace) := by
  let leftWeight :=
    originalBulkScalarSquareRemainderFaceWeight s hs leftFace
  let rightWeight :=
    originalBulkScalarSquareRemainderFaceWeight s hs rightFace
  let covariance :=
    YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.finiteCovariance
      w hw0 hw1
      (originalBulkScalarSquareRemainderExtent s n L)
      (originalBulkScalarSquareRemainderIds s n L)
      (originalBulkScalarSquareRemainderIds_physical s n L)
      (originalBulkScalarSquareRemainderFacePlaced s n offset L leftFace)
      (originalBulkScalarSquareRemainderFacePlaced s n offset L rightFace)
      stage
  have hweightProduct : (0 : Q') ≤ leftWeight * rightWeight :=
    Q'.mul_nonneg _ _
      (originalBulkScalarSquareRemainderFaceWeight_nonnegative
        s hs leftFace hleft)
      (originalBulkScalarSquareRemainderFaceWeight_nonnegative
        s hs rightFace hright)
  have hcovariance : Q'.abs covariance ≤
      distanceBudget
        (singletonCarrier
          (originalBulkScalarSquareRemainderPlacedFace n offset leftFace))
        (singletonCarrier
          (originalBulkScalarSquareRemainderPlacedFace n offset rightFace))
        w hd hsRate
        (originalBulkScalarSquareRemainderFaceCap n offset leftFace)
        (originalBulkScalarSquareRemainderFaceCap n offset rightFace) :=
    originalBulkScalarSquareRemainderFace_covariance_distance_bound
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
      (originalBulkScalarSquareRemainderFace_distanceBudget_factor
        w hd hsRate n offset leftFace rightFace)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (leftWeight * rightWeight)
      (originalBulkScalarSquareRemainderPairAmplitude w hd hsRate)
      (originalBulkScalarSquareRemainderGeometricKernel
        w hd leftFace rightFace))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv
        (leftWeight * rightWeight)
        (originalBulkScalarSquareRemainderPairAmplitude w hd hsRate))) ?_
  exact Q'.mul_assoc_eqv
    (originalBulkScalarSquareRemainderPairAmplitude w hd hsRate)
    (leftWeight * rightWeight)
    (originalBulkScalarSquareRemainderGeometricKernel
      w hd leftFace rightFace)

/-- The SAME selected original-action bulk covariance is bounded by a
volume-independent geometric constant times the exact quarter-weight
coefficient-square mass. -/
theorem originalBulkScalarSquareRemainderSelectedCovariance_geometric_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : YMGap.Continuum.QuaternionHaarCharacterInterval.heatRatio w ≤
      HalfPow.half)
    (hd : heatRemainderBound w < 1)
    (hsRate : originalBulkScalarSquareRemainderGeometricRate w hd < 1)
    (s : Nat) (hs : 0 < s) (stage n L offset : Nat)
    (hoffset : offset ≤ L) :
    Q'.abs
        (YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderCovariance.originalBulkScalarSquareRemainderSelectedCovariance
          hw0 hw1 s hs stage n L offset) ≤
      originalBulkScalarSquareRemainderPairAmplitude w hd hsRate *
        (originalBulkScalarSquareRemainderGeometricRowCap
              hw0 hd hsRate *
            originalBulkScalarSquareRemainderFaceWeightSquareMass s hs +
          originalBulkScalarSquareRemainderGeometricRowCap
              hw0 hd hsRate *
            originalBulkScalarSquareRemainderFaceWeightSquareMass s hs) := by
  let amplitude :=
    originalBulkScalarSquareRemainderPairAmplitude w hd hsRate
  let geometricPairSum :=
    originalBulkScalarSquareRemainderWeightedGeometricPairSum w hd s hs
  have hpairwise :=
    originalBulkScalarSquareRemainderSelectedCovariance_pairwise
      hw0 hw1 s hs stage n L offset
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hpairwise)) ?_
  unfold originalBulkScalarSquareRemainderPairwiseCovariance
  refine Q'.le_trans' _ _ _
    (abs_listQSum_le_sum_abs_local _ (bulkSourceFaces s)) ?_
  refine Q'.le_trans' _ _ _
    (listQSum_le_termwise_local _ _ (bulkSourceFaces s)
      (fun leftFace hleft =>
        abs_listQSum_le_sum_abs_local _ (bulkSourceFaces s))) ?_
  have htermwise :
      listQSum
          (fun leftFace => listQSum
            (fun rightFace =>
              Q'.abs
                ((originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
                    originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
                  YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.finiteCovariance
                    w hw0 hw1
                    (originalBulkScalarSquareRemainderExtent s n L)
                    (originalBulkScalarSquareRemainderIds s n L)
                    (originalBulkScalarSquareRemainderIds_physical s n L)
                    (originalBulkScalarSquareRemainderFacePlaced
                      s n offset L leftFace)
                    (originalBulkScalarSquareRemainderFacePlaced
                      s n offset L rightFace)
                    stage))
            (bulkSourceFaces s))
          (bulkSourceFaces s) ≤
        listQSum
          (fun leftFace => listQSum
            (fun rightFace =>
              amplitude *
                ((originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
                    originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
                  originalBulkScalarSquareRemainderGeometricKernel
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
                ((originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
                    originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
                  originalBulkScalarSquareRemainderGeometricKernel
                    w hd leftFace rightFace))
            (bulkSourceFaces s))
          (bulkSourceFaces s) ≈
        amplitude * geometricPairSum := by
    refine Q'.eqv_trans _ _ _
      (listQSum_congr_on _ _ (bulkSourceFaces s) (fun leftFace _ =>
        listQSum_mul_left amplitude
          (fun rightFace =>
            (originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
              originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
            originalBulkScalarSquareRemainderGeometricKernel
              w hd leftFace rightFace)
          (bulkSourceFaces s))) ?_
    exact listQSum_mul_left amplitude
      (fun leftFace => listQSum
        (fun rightFace =>
          (originalBulkScalarSquareRemainderFaceWeight s hs leftFace *
            originalBulkScalarSquareRemainderFaceWeight s hs rightFace) *
          originalBulkScalarSquareRemainderGeometricKernel
            w hd leftFace rightFace)
        (bulkSourceFaces s))
      (bulkSourceFaces s)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (originalBulkScalarSquareRemainderWeightedGeometricPairSum_le
      hw0 hd hsRate s hs)
    (originalBulkScalarSquareRemainderPairAmplitude_nonnegative
      w hd hsRate)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.weighted_symmetric_kernel_pair_sum_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.linfDist_comm
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.linfDist_timeShiftPlaquette
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderLocalCap
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderFaceCap_eq_localCap
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderPairAmplitude
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderPairAmplitude_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderFace_distanceBudget_factor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderGeometricRate_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderGeometricKernel_comm
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderGeometricRow_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderFaceWeightSquareMass
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderWeightedGeometricPairSum_le
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOriginalBulkDeficitRemainderGeometricConvolution.originalBulkScalarSquareRemainderSelectedCovariance_geometric_le
