/-
# Positive definiteness of the finite comb FREE-history precision

The flattened FREE-history quadratic splits into the sum of spatial-slice
quadratics and temporal-path quadratics.  A nonzero flattened coordinate lies
in one explicit spatial slice, whose comb-gauge quadratic is strictly
positive; every other spatial slice and every temporal fiber is nonnegative.

This yields constructive strict positivity of the complete finite comb-history
precision at every width and time cutoff.  The generic Schur recursion then
produces exact positive LDL data and an exact rational two-sided inverse.  No
Gaussian law, continuum limit, Hamiltonian, or mass-gap statement is proved.
-/

import YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite
import YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalFreeHistoryQuadratic
open YMGap.Continuum.FiniteRationalFreeTemporalPositiveSemidefinite
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombCurlMatrix
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQSum_positive_of_mem
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      (0 : Q') < value witness →
      (0 : Q') < listQSum value items
  | [], _, _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem, hwitness => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.pos_of_lt_of_le hwitness
          (Q'.add_le_self_of_nonneg
            (value head) (listQSum value tail)
            (listQSum_nonnegative_on value tail
              (fun item hitem =>
                hnonnegative item
                  (List.mem_cons_of_mem head hitem))))
      · have htailPositive := listQSum_positive_of_mem
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail hwitness
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.pos_of_lt_of_le htailPositive htailLe

private theorem historyIndex_decode
    {spatialSize index : Nat} :
    historyIndex spatialSize
        (historyTime spatialSize index)
        (historySpatial spatialSize index) = index := by
  unfold historyIndex historyTime historySpatial
  exact Nat.div_add_mod index spatialSize

/-- The complete finite comb-gauge FREE-history precision is strictly positive
on every coefficient vector carrying an explicit nonzero in-range entry. -/
theorem combGaugeFreeHistoryPrecision_strictlyPositive
    (timeBonds width : Nat) :
    FiniteMatrixStrictlyPositive
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeFreeHistoryPrecision timeBonds width) := by
  intro coefficient index hindex hcoordinate
  let spatialSize := combGaugeEdgeCount width
  have hspatialSize : 0 < spatialSize := by
    change 0 < combGaugeEdgeCount width
    apply Nat.pos_of_ne_zero
    intro hzero
    unfold historyCoordinateCount at hindex
    rw [hzero, Nat.mul_zero] at hindex
    exact Nat.not_lt_zero index hindex
  have htime :
      historyTime spatialSize index < historySliceCount timeBonds := by
    unfold historyTime
    apply (Nat.div_lt_iff_lt_mul hspatialSize).2
    simpa only [historyCoordinateCount] using hindex
  have hspatial : historySpatial spatialSize index < spatialSize := by
    unfold historySpatial
    exact Nat.mod_lt index hspatialSize
  have hdecode :
      historyIndex spatialSize
          (historyTime spatialSize index)
          (historySpatial spatialSize index) = index :=
    historyIndex_decode
  let spatialValue := fun time =>
    finiteMatrixQuadratic spatialSize
      (combGaugeSpatialPrecision width)
      (historySpatialSlice spatialSize coefficient time)
  have hspatialNonnegative :
      ∀ time, time ∈ List.range (historySliceCount timeBonds) →
        (0 : Q') ≤ spatialValue time := by
    intro time _htime
    exact combGaugeSpatialQuadratic_nonnegative width
      (historySpatialSlice spatialSize coefficient time)
  have hselectedPositive :
      (0 : Q') < spatialValue (historyTime spatialSize index) := by
    apply combGaugeSpatialQuadratic_positive_of_coordinate_not_eqv_zero
      width (historySpatialSlice spatialSize coefficient
        (historyTime spatialSize index)) hspatial
    unfold historySpatialSlice
    rw [hdecode]
    exact hcoordinate
  have hspatialSumPositive :
      (0 : Q') < listQSum spatialValue
        (List.range (historySliceCount timeBonds)) := by
    exact listQSum_positive_of_mem spatialValue
      (List.range (historySliceCount timeBonds))
      hspatialNonnegative (List.mem_range.mpr htime) hselectedPositive
  have htemporalSumNonnegative :
      (0 : Q') ≤
        listQSum
          (fun spatial =>
            finiteMatrixQuadratic (historySliceCount timeBonds)
              (freeTemporalPrecision timeBonds)
              (historyTemporalFiber spatialSize coefficient spatial))
          (List.range spatialSize) := by
    apply listQSum_nonnegative_on
    intro spatial _hspatial
    exact freeTemporalQuadratic_nonnegative timeBonds
      (historyTemporalFiber spatialSize coefficient spatial)
  have hsumPositive :
      (0 : Q') <
        listQSum spatialValue
            (List.range (historySliceCount timeBonds)) +
          listQSum
            (fun spatial =>
              finiteMatrixQuadratic (historySliceCount timeBonds)
                (freeTemporalPrecision timeBonds)
                (historyTemporalFiber spatialSize coefficient spatial))
            (List.range spatialSize) :=
    Q'.pos_of_lt_of_le hspatialSumPositive
      (Q'.add_le_self_of_nonneg _ _ htemporalSumNonnegative)
  have hdecomposition :=
    finiteMatrixQuadratic_freeHistoryPrecision
      timeBonds spatialSize (combGaugeSpatialPrecision width) coefficient
  exact Q'.pos_of_lt_of_le hsumPositive
    (Q'.ge_of_eqv (by
      simpa only [spatialValue, spatialSize, combGaugeFreeHistoryPrecision,
        freeHistoryCurlPrecision, combGaugeSpatialPrecision]
        using hdecomposition))

/-- The complete finite comb-gauge FREE-history precision is symmetric. -/
theorem combGaugeFreeHistoryPrecision_symmetric
    (timeBonds width : Nat) :
    FiniteMatrixSymmetric
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeFreeHistoryPrecision timeBonds width) := by
  intro left right _hleft _hright
  exact combGaugeFreeHistoryPrecision_symm
    timeBonds width left right

/-- Exact positive LDL data for the complete finite comb FREE-history
precision at every width and time cutoff. -/
def combGaugeFreeHistoryPositiveLDL (timeBonds width : Nat) :
    PositiveLDLData
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeFreeHistoryPrecision timeBonds width) :=
  positiveLDLDataOfStrictPositive
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeFreeHistoryPrecision timeBonds width)
    (combGaugeFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeFreeHistoryPrecision_strictlyPositive timeBonds width)

/-- The produced complete-history factors pass the exact finite LDL checker. -/
theorem combGaugeFreeHistoryPositiveLDL_check (timeBonds width : Nat) :
    finiteLDLCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeFreeHistoryPrecision timeBonds width)
        (combGaugeFreeHistoryPositiveLDL timeBonds width).lower
        (combGaugeFreeHistoryPositiveLDL timeBonds width).diagonal = true :=
  (combGaugeFreeHistoryPositiveLDL timeBonds width).finiteLDLCheck_eq_true

/-- Every produced complete-history pivot passes the strict-positive Boolean
checker used by the rational coordinate-factor construction. -/
theorem combGaugeFreeHistoryPositiveLDL_diagonal_check
    (timeBonds width : Nat) :
    finiteLDLPositiveDiagonalCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeFreeHistoryPositiveLDL timeBonds width).diagonal = true := by
  unfold finiteLDLPositiveDiagonalCheck
  apply List.all_eq_true.mpr
  intro index hindex
  exact decide_eq_true
    ((combGaugeFreeHistoryPositiveLDL timeBonds width).diagonal_pos
      (List.mem_range.mp hindex))

/-- Exact two-sided rational inverse data for the complete finite comb
FREE-history precision at every width and time cutoff. -/
def combGaugeFreeHistoryInverseData (timeBonds width : Nat) :
    FiniteMatrixInverseData
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeFreeHistoryPrecision timeBonds width) :=
  finiteMatrixInverseDataOfStrictPositive
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeFreeHistoryPrecision timeBonds width)
    (combGaugeFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeFreeHistoryPrecision_strictlyPositive timeBonds width)

/-- Canonical exact rational covariance for the complete finite comb
FREE-history precision. -/
def combGaugeFreeHistoryCovariance
    (timeBonds width : Nat) : Nat → Nat → Q' :=
  (combGaugeFreeHistoryInverseData timeBonds width).inverse

/-- Exact positive LDL data for the canonical complete-history covariance.
The factors are the transposed inverse spatial-history lower factor and the
positive reciprocal precision pivots. -/
def combGaugeFreeHistoryCovariancePositiveLDL
    (timeBonds width : Nat) :
    PositiveLDLData
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeFreeHistoryCovariance timeBonds width) :=
  finiteMatrixInversePositiveLDLDataOfStrictPositive
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeFreeHistoryPrecision timeBonds width)
    (combGaugeFreeHistoryPrecision_symmetric timeBonds width)
    (combGaugeFreeHistoryPrecision_strictlyPositive timeBonds width)

/-- Concrete rational Heron factor for the exact comb-history covariance at a
requested finite stage. -/
def combGaugeFreeHistoryHeronTransform
    (timeBonds width stage : Nat) : Nat → Nat → Q' :=
  heronLDLTransform
    (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).lower
    (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).diagonal
    stage

/-- Literal finite Gaussian polynomial for one comb-history coordinate under
the concrete rational Heron factor. -/
def combGaugeFreeHistoryHeronCoordinate
    (timeBonds width stage physicalIndex : Nat) : RatPoly :=
  finiteGaussianLinearCoordinate
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeFreeHistoryHeronTransform timeBonds width stage)
    physicalIndex

/-- Literal finite Gaussian polynomial for an arbitrary finite comb-history
physical row under the concrete rational Heron factor. -/
def combGaugeFreeHistoryHeronObservable
    (timeBonds width stage : Nat) (physicalRow : Nat → Q') : RatPoly :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteGaussianLinearObservable coordinateCount coordinateCount
    (combGaugeFreeHistoryHeronTransform timeBonds width stage)
    physicalRow

/-- Exact covariance bilinear form of the canonical rational comb-history
covariance matrix. -/
def combGaugeFreeHistoryCovarianceBilinear
    (timeBonds width : Nat) (leftRow rightRow : Nat → Q') : Q' :=
  finiteMatrixBilinear
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeFreeHistoryCovariance timeBonds width)
    leftRow rightRow

/-- Literal physical row for one oriented internal comb-gauge face curl on a
specified FREE-history time slice. The finite covariance bilinear restricts
this row to the complete flattened history prefix. -/
def combGaugeFreeHistoryCurlRow
    (width time faceIndex coordinate : Nat) : Q' :=
  if historyTime (combGaugeEdgeCount width) coordinate = time then
    combGaugeCurl width faceIndex
      (historySpatial (combGaugeEdgeCount width) coordinate)
  else 0

/-- On an encoded in-range comb coordinate, the literal history curl row is
exactly the corresponding comb-curl matrix coefficient. -/
theorem combGaugeFreeHistoryCurlRow_historyIndex
    {width time faceIndex gaugeIndex : Nat}
    (hgauge : gaugeIndex < combGaugeEdgeCount width) :
    combGaugeFreeHistoryCurlRow width time faceIndex
        (historyIndex (combGaugeEdgeCount width) time gaugeIndex) =
      combGaugeCurl width faceIndex gaugeIndex := by
  have hsize : 0 < combGaugeEdgeCount width :=
    Nat.pos_of_ne_zero (fun hzero => by
      rw [hzero] at hgauge
      exact Nat.not_lt_zero gaugeIndex hgauge)
  unfold combGaugeFreeHistoryCurlRow
  rw [historyTime_index hsize hgauge, if_pos rfl,
    historySpatial_index hgauge]

/-- One row of an explicitly placed three-color comb-curl family after the
certified Heron coordinate pullback. `rowIndex / 3` selects the placed face
and `rowIndex % 3` selects its color block. -/
def combGaugeFreeHistoryHeronColorCurlRow
    (timeBonds width stage : Nat)
    (times faceIndices : Nat → Nat) (rowIndex coordinate : Nat) : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  threeColorRows coordinateCount
    (pulledRow coordinateCount
      (combGaugeFreeHistoryHeronTransform timeBonds width stage)
      (combGaugeFreeHistoryCurlRow width
        (times (rowIndex / 3)) (faceIndices (rowIndex / 3))))
    (rowIndex % 3) coordinate

/-- Literal weighted radial square for a finite family of placed internal
comb-curl faces. Each rational face weight is copied to its three color rows;
no square root of a source coefficient is used. -/
def combGaugeFreeHistoryHeronWeightedCurlRadialSquare
    (timeBonds width stage familyCount : Nat)
    (weights : Nat → Q') (times faceIndices : Nat → Nat) : RatPoly :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteGaussianWeightedRadialSquare
    (coordinateCount + (coordinateCount + coordinateCount))
    (3 * familyCount)
    (fun rowIndex => weights (rowIndex / 3))
    (combGaugeFreeHistoryHeronColorCurlRow
      timeBonds width stage times faceIndices)

/-- Literal coefficient-weighted aggregate of the entrywise Heron residual
envelopes for two finite comb-history rows. -/
def combGaugeFreeHistoryHeronBilinearResidualEnvelope
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  physicalCovarianceBilinearResidualEnvelope coordinateCount
    (ldlFactorResidualEnvelope coordinateCount
      (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).lower
      (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).diagonal
      stage)
    leftRow rightRow

/-- The actual finite product-Gaussian second moment of two concrete
comb-history coordinate polynomials is exactly the staged Heron factor Gram.
This is a polynomial-functional statement, not a density or measure-level
pushforward theorem. -/
theorem combGaugeFreeHistoryHeronCoordinate_pair
    (timeBonds width stage left right : Nat) :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    finiteProductGaussian coordinateCount
        (polyMul
          (combGaugeFreeHistoryHeronCoordinate
            timeBonds width stage left)
          (combGaugeFreeHistoryHeronCoordinate
            timeBonds width stage right)) ≈
      factorCovariance coordinateCount
        (combGaugeFreeHistoryHeronTransform timeBonds width stage)
        left right := by
  exact finiteProductGaussian_linearCoordinate_pair
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (combGaugeFreeHistoryHeronTransform timeBonds width stage)
    left right

/-- The canonical covariance factors pass the exact finite LDL checker. -/
theorem combGaugeFreeHistoryCovariancePositiveLDL_check
    (timeBonds width : Nat) :
    finiteLDLCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeFreeHistoryCovariance timeBonds width)
        (combGaugeFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal = true :=
  (combGaugeFreeHistoryCovariancePositiveLDL
    timeBonds width).finiteLDLCheck_eq_true

/-- Every covariance pivot passes the strict-positive Boolean checker. -/
theorem combGaugeFreeHistoryCovariancePositiveLDL_diagonal_check
    (timeBonds width : Nat) :
    finiteLDLPositiveDiagonalCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal = true := by
  unfold finiteLDLPositiveDiagonalCheck
  apply List.all_eq_true.mpr
  intro index hindex
  exact decide_eq_true
    ((combGaugeFreeHistoryCovariancePositiveLDL
      timeBonds width).diagonal_pos (List.mem_range.mp hindex))

/-- The canonical complete-history covariance passes the repository's
executable two-sided inverse checker. -/
theorem combGaugeFreeHistoryCovariance_inverse_check
    (timeBonds width : Nat) :
    finiteMatrixInverseCheck
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeFreeHistoryPrecision timeBonds width)
        (combGaugeFreeHistoryCovariance timeBonds width) = true :=
  (combGaugeFreeHistoryInverseData timeBonds width).finiteMatrixInverseCheck_eq_true

/-- The same inverse certificate in the exact checker interface consumed by
the finite Gaussian Heron-factor theorem. -/
theorem combGaugeFreeHistoryCovariance_freeHistoryInverseCheck
    (timeBonds width : Nat) :
    freeHistoryCovarianceInverseCheck timeBonds
        (combGaugeEdgeCount width) (internalOpenCubeFaceCount width)
        (combGaugeCurl width)
        (combGaugeFreeHistoryCovariance timeBonds width) = true := by
  exact combGaugeFreeHistoryCovariance_inverse_check timeBonds width

/-- The exact comb-history covariance and its positive LDL factors satisfy the
explicit finite Heron factor residual theorem consumed by the Gaussian row
construction. -/
theorem combGaugeFreeHistoryCovariance_heronFactor
    {timeBonds width stage left right : Nat}
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    (finiteMatrixProduct
        (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
        (combGaugeFreeHistoryPrecision timeBonds width)
        (combGaugeFreeHistoryCovariance timeBonds width) left right ≈
          finiteIdentityMatrix left right) ∧
      Q'.abs
          (factorCovariance
              (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
              (heronLDLTransform
                (combGaugeFreeHistoryCovariancePositiveLDL
                  timeBonds width).lower
                (combGaugeFreeHistoryCovariancePositiveLDL
                  timeBonds width).diagonal
                stage)
              left right +
            -combGaugeFreeHistoryCovariance timeBonds width left right) ≤
        ldlFactorResidualEnvelope
          (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
          (combGaugeFreeHistoryCovariancePositiveLDL
            timeBonds width).lower
          (combGaugeFreeHistoryCovariancePositiveLDL
            timeBonds width).diagonal
          stage left right := by
  exact freeHistoryCovariance_heronFactor
    (combGaugeFreeHistoryCovariance_freeHistoryInverseCheck
      timeBonds width)
    (combGaugeFreeHistoryCovariancePositiveLDL_check timeBonds width)
    (combGaugeFreeHistoryCovariancePositiveLDL_diagonal_check
      timeBonds width)
    hleft hright

/-- The certified Heron residual controls the actual finite Gaussian
polynomial second moment of the concrete coordinate generators relative to
the exact comb-history covariance entry. -/
theorem combGaugeFreeHistoryHeronCoordinate_pair_error
    {timeBonds width stage left right : Nat}
    (hleft : left <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width))
    (hright : right <
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)) :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    Q'.abs
        (finiteProductGaussian coordinateCount
            (polyMul
              (combGaugeFreeHistoryHeronCoordinate
                timeBonds width stage left)
              (combGaugeFreeHistoryHeronCoordinate
                timeBonds width stage right)) +
          -combGaugeFreeHistoryCovariance timeBonds width left right) ≤
      ldlFactorResidualEnvelope coordinateCount
        (combGaugeFreeHistoryCovariancePositiveLDL
          timeBonds width).lower
        (combGaugeFreeHistoryCovariancePositiveLDL
          timeBonds width).diagonal
        stage left right := by
  have hmoment := combGaugeFreeHistoryHeronCoordinate_pair
    timeBonds width stage left right
  have herror := (combGaugeFreeHistoryCovariance_heronFactor
    (timeBonds := timeBonds) (width := width) (stage := stage)
    hleft hright).2
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (ExpNeg.abs_eqv_congr
        (Q'.add_eqv_congr_right _ _ _ hmoment)))
    herror

/-- Arbitrary finite comb-history rows inherit a checked Gaussian pair-moment
error by summing the certified entrywise Heron envelopes with their literal
pair coefficients. -/
theorem combGaugeFreeHistoryHeronObservable_pair_error
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    Q'.abs
        (finiteProductGaussian coordinateCount
            (polyMul
              (combGaugeFreeHistoryHeronObservable
                timeBonds width stage leftRow)
              (combGaugeFreeHistoryHeronObservable
                timeBonds width stage rightRow)) +
          -combGaugeFreeHistoryCovarianceBilinear
            timeBonds width leftRow rightRow) ≤
      combGaugeFreeHistoryHeronBilinearResidualEnvelope
        timeBonds width stage leftRow rightRow := by
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  exact finiteProductGaussian_linearObservable_pair_error
    coordinateCount coordinateCount
    (combGaugeFreeHistoryHeronTransform timeBonds width stage)
    (combGaugeFreeHistoryCovariance timeBonds width)
    (ldlFactorResidualEnvelope coordinateCount
      (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).lower
      (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).diagonal
      stage)
    leftRow rightRow
    (fun left right hleft hright =>
      (combGaugeFreeHistoryCovariance_heronFactor
        (timeBonds := timeBonds) (width := width) (stage := stage)
        hleft hright).2)

/-- The staged physical covariance bilinear itself differs from the exact
comb-history covariance bilinear by the same coefficient-weighted Heron
envelope. -/
theorem combGaugeFreeHistoryHeronBilinear_error
    (timeBonds width stage : Nat) (leftRow rightRow : Nat → Q') :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    Q'.abs
        (physicalCovarianceBilinear coordinateCount coordinateCount
            (combGaugeFreeHistoryHeronTransform timeBonds width stage)
            leftRow rightRow +
          -combGaugeFreeHistoryCovarianceBilinear
            timeBonds width leftRow rightRow) ≤
      combGaugeFreeHistoryHeronBilinearResidualEnvelope
        timeBonds width stage leftRow rightRow := by
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  exact physicalCovarianceBilinear_error
    coordinateCount coordinateCount
    (combGaugeFreeHistoryHeronTransform timeBonds width stage)
    (combGaugeFreeHistoryCovariance timeBonds width)
    (ldlFactorResidualEnvelope coordinateCount
      (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).lower
      (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).diagonal
      stage)
    leftRow rightRow
    (fun left right hleft hright =>
      (combGaugeFreeHistoryCovariance_heronFactor
        (timeBonds := timeBonds) (width := width) (stage := stage)
        hleft hright).2)

/-- Every concrete comb-history Heron stage feeds the exact three-color finite
Gaussian radial covariance identity with no supplied independence or covariance
premise. -/
theorem combGaugeFreeHistoryHeronRows_radialCovariance
    (timeBonds width stage : Nat) (b d : Nat → Q') :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    finiteGaussianCovariance
        (coordinateCount + (coordinateCount + coordinateCount))
        (polyMul
          (finiteGaussianRadialSquare
            (coordinateCount + (coordinateCount + coordinateCount)) 3
            (threeColorRows coordinateCount
              (pulledRow coordinateCount
                (combGaugeFreeHistoryHeronTransform
                  timeBonds width stage) b)))
          (finiteGaussianRadialSquare
            (coordinateCount + (coordinateCount + coordinateCount)) 3
            (threeColorRows coordinateCount
              (pulledRow coordinateCount
                (combGaugeFreeHistoryHeronTransform
                  timeBonds width stage) b))))
        (finiteGaussianRadialSquare
          (coordinateCount + (coordinateCount + coordinateCount)) 3
          (threeColorRows coordinateCount
            (pulledRow coordinateCount
              (combGaugeFreeHistoryHeronTransform
                timeBonds width stage) d))) ≈
      60 *
        physicalCovarianceBilinear coordinateCount coordinateCount
          (combGaugeFreeHistoryHeronTransform timeBonds width stage) b b *
        (physicalCovarianceBilinear coordinateCount coordinateCount
            (combGaugeFreeHistoryHeronTransform timeBonds width stage) b d *
          physicalCovarianceBilinear coordinateCount coordinateCount
            (combGaugeFreeHistoryHeronTransform
              timeBonds width stage) b d) := by
  exact finiteGaussianRadialCovariance_threeColorHeronLDLRows
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width)) stage
    (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).lower
    (combGaugeFreeHistoryCovariancePositiveLDL timeBonds width).diagonal
    b d

/-- Exact weighted covariance identity for two finite placed comb-curl
families at one certified Heron stage. This assembles the rational source
weights, face indices, time placements and three color blocks required by the
BOX denominator. Identifying a particular original face list with the
internal comb carrier and proving a positive lower bound remain separate. -/
theorem combGaugeFreeHistoryHeronWeightedCurlRadialPairCovariance_trace
    (timeBonds width stage sourceCount directionCount : Nat)
    (sourceWeights directionWeights : Nat → Q')
    (sourceTimes sourceFaces directionTimes directionFaces : Nat → Nat) :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    finiteGaussianCovariance
        (coordinateCount + (coordinateCount + coordinateCount))
        (combGaugeFreeHistoryHeronWeightedCurlRadialSquare
          timeBonds width stage sourceCount
          sourceWeights sourceTimes sourceFaces)
        (combGaugeFreeHistoryHeronWeightedCurlRadialSquare
          timeBonds width stage directionCount
          directionWeights directionTimes directionFaces) ≈
      2 * finiteWeightedCrossGramSquareTrace
        (coordinateCount + (coordinateCount + coordinateCount))
        (3 * sourceCount) (3 * directionCount)
        (fun rowIndex => sourceWeights (rowIndex / 3))
        (fun rowIndex => directionWeights (rowIndex / 3))
        (combGaugeFreeHistoryHeronColorCurlRow
          timeBonds width stage sourceTimes sourceFaces)
        (combGaugeFreeHistoryHeronColorCurlRow
          timeBonds width stage directionTimes directionFaces) := by
  exact finiteGaussianWeightedRadialPairCovariance_trace
    (historyCoordinateCount timeBonds (combGaugeEdgeCount width) +
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width) +
        historyCoordinateCount timeBonds (combGaugeEdgeCount width)))
    (3 * sourceCount) (3 * directionCount)
    (fun rowIndex => sourceWeights (rowIndex / 3))
    (fun rowIndex => directionWeights (rowIndex / 3))
    (combGaugeFreeHistoryHeronColorCurlRow
      timeBonds width stage sourceTimes sourceFaces)
    (combGaugeFreeHistoryHeronColorCurlRow
      timeBonds width stage directionTimes directionFaces)

/-- Actual three-color finite Gaussian radial covariance for the concrete
comb-history Heron rows. -/
def combGaugeFreeHistoryHeronRadialCovariance
    (timeBonds width stage : Nat) (b d : Nat → Q') : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteGaussianCovariance
    (coordinateCount + (coordinateCount + coordinateCount))
    (polyMul
      (finiteGaussianRadialSquare
        (coordinateCount + (coordinateCount + coordinateCount)) 3
        (threeColorRows coordinateCount
          (pulledRow coordinateCount
            (combGaugeFreeHistoryHeronTransform
              timeBonds width stage) b)))
      (finiteGaussianRadialSquare
        (coordinateCount + (coordinateCount + coordinateCount)) 3
        (threeColorRows coordinateCount
          (pulledRow coordinateCount
            (combGaugeFreeHistoryHeronTransform
              timeBonds width stage) b))))
    (finiteGaussianRadialSquare
      (coordinateCount + (coordinateCount + coordinateCount)) 3
      (threeColorRows coordinateCount
        (pulledRow coordinateCount
          (combGaugeFreeHistoryHeronTransform
            timeBonds width stage) d)))

/-- Exact factor-60 target formed from the canonical rational comb-history
covariance matrix. -/
def combGaugeFreeHistoryExactRadialCovariance
    (timeBonds width : Nat) (b d : Nat → Q') : Q' :=
  factor60RadialExpression
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b b)
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d)

/-- Actual three-color quadratic radial pair covariance for the concrete
comb-history Heron rows. This is the denominator paired with the sixth-order
radial covariance above. -/
def combGaugeFreeHistoryHeronRadialPairCovariance
    (timeBonds width stage : Nat) (b d : Nat → Q') : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  finiteGaussianCovariance
    (coordinateCount + (coordinateCount + coordinateCount))
    (finiteGaussianRadialSquare
      (coordinateCount + (coordinateCount + coordinateCount)) 3
      (threeColorRows coordinateCount
        (pulledRow coordinateCount
          (combGaugeFreeHistoryHeronTransform timeBonds width stage) b)))
    (finiteGaussianRadialSquare
      (coordinateCount + (coordinateCount + coordinateCount)) 3
      (threeColorRows coordinateCount
        (pulledRow coordinateCount
          (combGaugeFreeHistoryHeronTransform timeBonds width stage) d)))

/-- Exact factor-6 quadratic denominator formed from the canonical rational
comb-history covariance bilinear. -/
def combGaugeFreeHistoryExactRadialPairCovariance
    (timeBonds width : Nat) (b d : Nat → Q') : Q' :=
  factor6RadialPairExpression
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d)

/-- Explicit propagation of the mixed row-bilinear Heron error through the
factor-6 quadratic radial denominator. -/
def combGaugeFreeHistoryHeronRadialPairResidualEnvelope
    (timeBonds width stage : Nat) (b d : Nat → Q') : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  factor6RadialPairResidualEnvelope
    (physicalCovarianceBilinear coordinateCount coordinateCount
      (combGaugeFreeHistoryHeronTransform timeBonds width stage) b d)
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d)
    (combGaugeFreeHistoryHeronBilinearResidualEnvelope
      timeBonds width stage b d)

/-- Explicit nonlinear propagation of the diagonal and mixed row-bilinear
Heron errors through the factor-60 radial covariance expression. -/
def combGaugeFreeHistoryHeronRadialResidualEnvelope
    (timeBonds width stage : Nat) (b d : Nat → Q') : Q' :=
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  factor60RadialResidualEnvelope
    (physicalCovarianceBilinear coordinateCount coordinateCount
      (combGaugeFreeHistoryHeronTransform timeBonds width stage) b b)
    (physicalCovarianceBilinear coordinateCount coordinateCount
      (combGaugeFreeHistoryHeronTransform timeBonds width stage) b d)
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d)
    (combGaugeFreeHistoryHeronBilinearResidualEnvelope
      timeBonds width stage b b)
    (combGaugeFreeHistoryHeronBilinearResidualEnvelope
      timeBonds width stage b d)

/-- The actual finite Gaussian quadratic radial pair covariance is exactly the
staged factor-6 denominator. -/
theorem combGaugeFreeHistoryHeronRadialPairCovariance_factor6
    (timeBonds width stage : Nat) (b d : Nat → Q') :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    combGaugeFreeHistoryHeronRadialPairCovariance
        timeBonds width stage b d ≈
      factor6RadialPairExpression
        (physicalCovarianceBilinear coordinateCount coordinateCount
          (combGaugeFreeHistoryHeronTransform timeBonds width stage) b d) := by
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  have hgram := finiteRowGram_pulledRow coordinateCount coordinateCount
    (combGaugeFreeHistoryHeronTransform timeBonds width stage) b d
  unfold combGaugeFreeHistoryHeronRadialPairCovariance
    factor6RadialPairExpression
  exact Q'.eqv_trans _ _ _
    (finiteGaussianRadialPairCovariance_threeColorRows coordinateCount
      (pulledRow coordinateCount
        (combGaugeFreeHistoryHeronTransform timeBonds width stage) b)
      (pulledRow coordinateCount
        (combGaugeFreeHistoryHeronTransform timeBonds width stage) d))
    (Q'.mul_eqv_congr_left 6 _ _ (qmul_congr hgram hgram))

/-- The exact sixth-order radial target is ten times its exact diagonal
bilinear times the exact quadratic radial denominator. -/
theorem combGaugeFreeHistoryExactRadialCovariance_normalization
    (timeBonds width : Nat) (b d : Nat → Q') :
    combGaugeFreeHistoryExactRadialCovariance timeBonds width b d ≈
      10 * combGaugeFreeHistoryCovarianceBilinear timeBonds width b b *
        combGaugeFreeHistoryExactRadialPairCovariance
          timeBonds width b d := by
  unfold combGaugeFreeHistoryExactRadialCovariance
    combGaugeFreeHistoryExactRadialPairCovariance
  exact factor60RadialExpression_eq_ten_mul_factor6
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b b)
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d)

/-- A positive exact mixed covariance makes the exact quadratic radial
denominator strictly positive. -/
theorem combGaugeFreeHistoryExactRadialPairCovariance_pos
    (timeBonds width : Nat) (b d : Nat → Q')
    (hmixed : (0 : Q') <
      combGaugeFreeHistoryCovarianceBilinear timeBonds width b d) :
    (0 : Q') <
      combGaugeFreeHistoryExactRadialPairCovariance timeBonds width b d := by
  unfold combGaugeFreeHistoryExactRadialPairCovariance
  exact factor6RadialPairExpression_pos
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d) hmixed

/-- Any explicit positive floor on the exact mixed covariance gives the
corresponding squared floor on the exact quadratic radial denominator. -/
theorem combGaugeFreeHistoryExactRadialPairCovariance_floor
    (timeBonds width : Nat) (b d : Nat → Q') (floor : Q')
    (hfloor : (0 : Q') < floor)
    (hfloorMixed : floor ≤
      combGaugeFreeHistoryCovarianceBilinear timeBonds width b d) :
    6 * (floor * floor) ≤
      combGaugeFreeHistoryExactRadialPairCovariance
        timeBonds width b d := by
  unfold combGaugeFreeHistoryExactRadialPairCovariance
  exact factor6RadialPairExpression_floor
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d)
    floor hfloor hfloorMixed

/-- The actual finite Gaussian radial covariance is exactly the staged
factor-60 expression. -/
theorem combGaugeFreeHistoryHeronRadialCovariance_factor60
    (timeBonds width stage : Nat) (b d : Nat → Q') :
    let coordinateCount :=
      historyCoordinateCount timeBonds (combGaugeEdgeCount width)
    combGaugeFreeHistoryHeronRadialCovariance
        timeBonds width stage b d ≈
      factor60RadialExpression
        (physicalCovarianceBilinear coordinateCount coordinateCount
          (combGaugeFreeHistoryHeronTransform timeBonds width stage) b b)
        (physicalCovarianceBilinear coordinateCount coordinateCount
          (combGaugeFreeHistoryHeronTransform timeBonds width stage) b d) := by
  unfold combGaugeFreeHistoryHeronRadialCovariance
    factor60RadialExpression
  exact combGaugeFreeHistoryHeronRows_radialCovariance
    timeBonds width stage b d

/-- The checked mixed row-bilinear Heron error propagates through the actual
finite Gaussian quadratic radial denominator. -/
theorem combGaugeFreeHistoryHeronRadialPairCovariance_error
    (timeBonds width stage : Nat) (b d : Nat → Q') :
    Q'.abs
        (combGaugeFreeHistoryHeronRadialPairCovariance
            timeBonds width stage b d +
          -combGaugeFreeHistoryExactRadialPairCovariance
            timeBonds width b d) ≤
      combGaugeFreeHistoryHeronRadialPairResidualEnvelope
        timeBonds width stage b d := by
  have hpair := combGaugeFreeHistoryHeronRadialPairCovariance_factor6
    timeBonds width stage b d
  have hmixed := combGaugeFreeHistoryHeronBilinear_error
    timeBonds width stage b d
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (ExpNeg.abs_eqv_congr
        (Q'.add_eqv_congr_right _ _ _ hpair))) ?_
  exact factor6RadialPairExpression_error
    (physicalCovarianceBilinear
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (historyCoordinateCount timeBonds (combGaugeEdgeCount width))
      (combGaugeFreeHistoryHeronTransform timeBonds width stage) b d)
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d)
    (combGaugeFreeHistoryHeronBilinearResidualEnvelope
      timeBonds width stage b d)
    hmixed

/-- The checked row-bilinear Heron errors propagate through the complete
nonlinear factor-60 radial covariance identity for the actual finite Gaussian
polynomial functional. -/
theorem combGaugeFreeHistoryHeronRadialCovariance_error
    (timeBonds width stage : Nat) (b d : Nat → Q') :
    Q'.abs
        (combGaugeFreeHistoryHeronRadialCovariance
            timeBonds width stage b d +
          -combGaugeFreeHistoryExactRadialCovariance
            timeBonds width b d) ≤
      combGaugeFreeHistoryHeronRadialResidualEnvelope
        timeBonds width stage b d := by
  let coordinateCount :=
    historyCoordinateCount timeBonds (combGaugeEdgeCount width)
  have hradial := combGaugeFreeHistoryHeronRadialCovariance_factor60
    timeBonds width stage b d
  have hdiagonal := combGaugeFreeHistoryHeronBilinear_error
    timeBonds width stage b b
  have hmixed := combGaugeFreeHistoryHeronBilinear_error
    timeBonds width stage b d
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (ExpNeg.abs_eqv_congr
        (Q'.add_eqv_congr_right _ _ _ hradial))) ?_
  exact factor60RadialExpression_error
    (physicalCovarianceBilinear coordinateCount coordinateCount
      (combGaugeFreeHistoryHeronTransform timeBonds width stage) b b)
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b b)
    (physicalCovarianceBilinear coordinateCount coordinateCount
      (combGaugeFreeHistoryHeronTransform timeBonds width stage) b d)
    (combGaugeFreeHistoryCovarianceBilinear timeBonds width b d)
    (combGaugeFreeHistoryHeronBilinearResidualEnvelope
      timeBonds width stage b b)
    (combGaugeFreeHistoryHeronBilinearResidualEnvelope
      timeBonds width stage b d)
    hdiagonal hmixed

/-- The quadratic radial denominator error specialized to literal internal
comb-curl rows on two FREE-history time slices. -/
theorem combGaugeFreeHistoryHeronCurlRadialPairCovariance_error
    (timeBonds width stage sourceTime sourceFace directionTime directionFace : Nat) :
    Q'.abs
        (combGaugeFreeHistoryHeronRadialPairCovariance
            timeBonds width stage
            (combGaugeFreeHistoryCurlRow width sourceTime sourceFace)
            (combGaugeFreeHistoryCurlRow width directionTime directionFace) +
          -combGaugeFreeHistoryExactRadialPairCovariance
            timeBonds width
            (combGaugeFreeHistoryCurlRow width sourceTime sourceFace)
            (combGaugeFreeHistoryCurlRow width directionTime directionFace)) ≤
      combGaugeFreeHistoryHeronRadialPairResidualEnvelope
        timeBonds width stage
        (combGaugeFreeHistoryCurlRow width sourceTime sourceFace)
        (combGaugeFreeHistoryCurlRow width directionTime directionFace) := by
  exact combGaugeFreeHistoryHeronRadialPairCovariance_error
    timeBonds width stage
    (combGaugeFreeHistoryCurlRow width sourceTime sourceFace)
    (combGaugeFreeHistoryCurlRow width directionTime directionFace)

/-- The sixth-order radial covariance error specialized to the same literal
internal comb-curl row pair. -/
theorem combGaugeFreeHistoryHeronCurlRadialCovariance_error
    (timeBonds width stage sourceTime sourceFace directionTime directionFace : Nat) :
    Q'.abs
        (combGaugeFreeHistoryHeronRadialCovariance
            timeBonds width stage
            (combGaugeFreeHistoryCurlRow width sourceTime sourceFace)
            (combGaugeFreeHistoryCurlRow width directionTime directionFace) +
          -combGaugeFreeHistoryExactRadialCovariance
            timeBonds width
            (combGaugeFreeHistoryCurlRow width sourceTime sourceFace)
            (combGaugeFreeHistoryCurlRow width directionTime directionFace)) ≤
      combGaugeFreeHistoryHeronRadialResidualEnvelope
        timeBonds width stage
        (combGaugeFreeHistoryCurlRow width sourceTime sourceFace)
        (combGaugeFreeHistoryCurlRow width directionTime directionFace) := by
  exact combGaugeFreeHistoryHeronRadialCovariance_error
    timeBonds width stage
    (combGaugeFreeHistoryCurlRow width sourceTime sourceFace)
    (combGaugeFreeHistoryCurlRow width directionTime directionFace)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryPrecision_strictlyPositive
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryPrecision_symmetric
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryPositiveLDL
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryPositiveLDL_check
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryPositiveLDL_diagonal_check
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryInverseData
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryCovariancePositiveLDL
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronCoordinate
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronObservable
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryCovarianceBilinear
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryCurlRow_historyIndex
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronBilinearResidualEnvelope
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronCoordinate_pair
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronTransform
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryCovariancePositiveLDL_check
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryCovariancePositiveLDL_diagonal_check
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryCovariance_inverse_check
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryCovariance_freeHistoryInverseCheck
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryCovariance_heronFactor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronCoordinate_pair_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronObservable_pair_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronBilinear_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRows_radialCovariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRadialCovariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryExactRadialCovariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRadialPairCovariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronWeightedCurlRadialPairCovariance_trace
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryExactRadialPairCovariance
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRadialPairResidualEnvelope
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRadialResidualEnvelope
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRadialPairCovariance_factor6
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryExactRadialCovariance_normalization
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryExactRadialPairCovariance_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryExactRadialPairCovariance_floor
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRadialCovariance_factor60
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRadialPairCovariance_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronRadialCovariance_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronCurlRadialPairCovariance_error
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite.combGaugeFreeHistoryHeronCurlRadialCovariance_error
