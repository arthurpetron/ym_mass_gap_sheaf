/-
# A positive finite Heron stage for the open-cube bulk source

The exact one-bond lower-face curl covariance is strictly positive.  The
entrywise Heron residual envelope factors as one explicit nonnegative rational
coefficient times a dyadic power.  A constructive geometric modulus therefore
selects a finite Heron stage at which the staged lower-face mixed covariance
retains at least half of its exact value.

The selected color-zero lower-face square is then a strictly positive summand
of the complete weighted cross-Gram-square trace.  This proves positivity of
the literal finite Gaussian bulk-source denominator at that explicit stage.

The stage and lower bound depend on the finite side.  No side-uniform Heron
stage, original-law comparison, continuum limit, Hamiltonian gap, or Clay
theorem is proved here.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor
import YMGap.Continuum.RegularLinearGeometricModulus
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalFreeHistoryQuadratic
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.RegularLinearGeometricModulus
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianCoordinatePullback
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision
open YMGap.Continuum.SU2QuaternionFiniteGaussianLDLCoordinateFactor
open YMGap.Continuum.SU2QuaternionFiniteGaussianLinearCoordinateRealization
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkCrossCovarianceFloor
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkSource
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombFreeHistoryPositiveDefinite
open YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeCombGauge
open YMGap.Continuum.SU2QuaternionFiniteGaussianRadialCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianThreeColorRows
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

local infix:50 " ≈ " => Q'.eqv

theorem qListSum_map_eq_listQSum_local {A : Type}
    (value : A → Q') : ∀ items : List A,
    qListSum (items.map value) = listQSum value items
  | [] => rfl
  | _ :: items => by
      simp only [List.map, qListSum, listQSum]
      rw [qListSum_map_eq_listQSum_local value items]

def ldlFactorResidualCoefficient
    (n : Nat) (lower : Nat → Nat → Q') (diagonal : Nat → Q')
    (left right : Nat) : Q' :=
  listQSum
    (fun k =>
      errAt (diagonal k) 0 *
        Q'.abs (lower left k * lower right k))
    (List.range n)

theorem ldlFactorResidualEnvelope_eq_coefficient_mul_half
    (n : Nat) (lower : Nat → Nat → Q') (diagonal : Nat → Q')
    (stage left right : Nat) :
    ldlFactorResidualEnvelope n lower diagonal stage left right ≈
      ldlFactorResidualCoefficient n lower diagonal left right *
        HalfPow.half ^ stage := by
  unfold ldlFactorResidualEnvelope ldlFactorResidualCoefficient
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun k =>
        poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 0) (.var 2)) (.var 1))
          (by decide) (fun
            | 0 => errAt (diagonal k) 0
            | 1 => HalfPow.half ^ stage
            | _ => Q'.abs (lower left k * lower right k)))
      (List.range n)) ?_
  exact listQSum_mul_right
    (fun k =>
      errAt (diagonal k) 0 *
        Q'.abs (lower left k * lower right k))
    (HalfPow.half ^ stage) (List.range n)

theorem physicalResidualEnvelope_eq_coefficient_mul_half
    (physicalSize stage : Nat)
    (entryEnvelope entryCoefficient : Nat → Nat → Q')
    (leftRow rightRow : Nat → Q')
    (hentry : ∀ left right,
      entryEnvelope left right ≈
        entryCoefficient left right * HalfPow.half ^ stage) :
    physicalCovarianceBilinearResidualEnvelope physicalSize
        entryEnvelope leftRow rightRow ≈
      physicalCovarianceBilinearResidualEnvelope physicalSize
        entryCoefficient leftRow rightRow * HalfPow.half ^ stage := by
  unfold physicalCovarianceBilinearResidualEnvelope
  simp only [qListSum_map_eq_listQSum_local]
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (f := fun left =>
        listQSum
          (fun right =>
            Q'.abs (leftRow left * rightRow right) *
              entryEnvelope left right)
          (List.range physicalSize))
      (g := fun left =>
        listQSum
          (fun right =>
            Q'.abs (leftRow left * rightRow right) *
              entryCoefficient left right)
          (List.range physicalSize) * HalfPow.half ^ stage)
      (fun left => ?_) (List.range physicalSize)) ?_
  · refine Q'.eqv_trans _ _ _
      (listQSum_congr
        (f := fun right =>
          Q'.abs (leftRow left * rightRow right) *
            entryEnvelope left right)
        (g := fun right =>
          (Q'.abs (leftRow left * rightRow right) *
            entryCoefficient left right) * HalfPow.half ^ stage)
        (fun right => ?_) (List.range physicalSize)) ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.abs (leftRow left * rightRow right)) _ _
          (hentry left right))
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.abs (leftRow left * rightRow right))
            (entryCoefficient left right) (HalfPow.half ^ stage)))
    · exact listQSum_mul_right
        (fun right =>
          Q'.abs (leftRow left * rightRow right) *
            entryCoefficient left right)
        (HalfPow.half ^ stage) (List.range physicalSize)
  · exact listQSum_mul_right
      (fun left =>
        listQSum
          (fun right =>
            Q'.abs (leftRow left * rightRow right) *
              entryCoefficient left right)
          (List.range physicalSize))
      (HalfPow.half ^ stage) (List.range physicalSize)

/-- Stage-independent coefficient controlling the lower-face one-bond Heron
mixed-covariance error. -/
def bulkSourceLowerFaceHeronResidualCoefficient (s : Nat) : Q' :=
  let width := bulkSourceWidth s
  let coordinateCount :=
    historyCoordinateCount 1 (combGaugeEdgeCount width)
  let data := combGaugeFreeHistoryCovariancePositiveLDL 1 width
  let faceIndex :=
    bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)
  physicalCovarianceBilinearResidualEnvelope coordinateCount
    (ldlFactorResidualCoefficient coordinateCount
      data.lower data.diagonal)
    (combGaugeFreeHistoryCurlRow width 0 faceIndex)
    (combGaugeFreeHistoryCurlRow width 1 faceIndex)

/-- Staged rational mixed covariance of the concrete lower bulk face. -/
def bulkSourceLowerFaceHeronMixedCovariance
    (s stage : Nat) : Q' :=
  let width := bulkSourceWidth s
  let coordinateCount :=
    historyCoordinateCount 1 (combGaugeEdgeCount width)
  let faceIndex :=
    bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)
  physicalCovarianceBilinear coordinateCount coordinateCount
    (combGaugeFreeHistoryHeronTransform 1 width stage)
    (combGaugeFreeHistoryCurlRow width 0 faceIndex)
    (combGaugeFreeHistoryCurlRow width 1 faceIndex)

theorem bulkSourceLowerFaceHeronResidualEnvelope_eq
    (s stage : Nat) :
    combGaugeFreeHistoryHeronBilinearResidualEnvelope
        1 (bulkSourceWidth s) stage
        (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 0
          (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)))
        (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 1
          (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s))) ≈
      bulkSourceLowerFaceHeronResidualCoefficient s *
        HalfPow.half ^ stage := by
  unfold combGaugeFreeHistoryHeronBilinearResidualEnvelope
    bulkSourceLowerFaceHeronResidualCoefficient
  exact physicalResidualEnvelope_eq_coefficient_mul_half
    (historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))) stage
    (ldlFactorResidualEnvelope
      (historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth s)))
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth s)).lower
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth s)).diagonal
      stage)
    (ldlFactorResidualCoefficient
      (historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth s)))
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth s)).lower
      (combGaugeFreeHistoryCovariancePositiveLDL
        1 (bulkSourceWidth s)).diagonal)
    _ _
    (fun left right =>
      ldlFactorResidualEnvelope_eq_coefficient_mul_half
        (historyCoordinateCount 1
          (combGaugeEdgeCount (bulkSourceWidth s)))
        (combGaugeFreeHistoryCovariancePositiveLDL
          1 (bulkSourceWidth s)).lower
        (combGaugeFreeHistoryCovariancePositiveLDL
          1 (bulkSourceWidth s)).diagonal
        stage left right)

theorem bulkSourceLowerFaceHeronResidualCoefficient_nonnegative
    (s : Nat) :
    (0 : Q') ≤ bulkSourceLowerFaceHeronResidualCoefficient s := by
  unfold bulkSourceLowerFaceHeronResidualCoefficient
    physicalCovarianceBilinearResidualEnvelope
  simp only [qListSum_map_eq_listQSum_local]
  apply listQSum_nonnegative_on
  intro left hleft
  apply listQSum_nonnegative_on
  intro right hright
  apply Q'.mul_nonneg
  · exact Q'.abs_nonneg _
  · unfold ldlFactorResidualCoefficient
    apply listQSum_nonnegative_on
    intro k hk
    apply Q'.mul_nonneg
    · exact errAt_nonneg
        ((combGaugeFreeHistoryCovariancePositiveLDL
          1 (bulkSourceWidth s)).diagonal k)
        (finiteLDLPositiveDiagonalCheck_pos
          (combGaugeFreeHistoryCovariancePositiveLDL_diagonal_check
            1 (bulkSourceWidth s))
          (List.mem_range.mp hk)) 0
    · exact Q'.abs_nonneg _

/-- Explicit side-dependent stage at which the lower-face mixed covariance
retains half of its exact positive value. -/
def bulkSourcePositiveHeronStage (s : Nat) : Nat :=
  geoOuterModulus
    (HalfPow.half * bulkSourceLowerFaceHeronResidualCoefficient s)
    (HalfPow.half * bulkSourceLowerFaceOneBondCovariance s)

theorem lower_of_abs_remainder_local
    {next model error lower : Q'}
    (habs : Q'.abs (next + -model) ≤ error)
    (hwindow : lower + error ≤ model) :
    lower ≤ next := by
  have hnegError : -error ≤ -(Q'.abs (next + -model)) :=
    Q'.neg_le_neg habs
  have hnegAbs : -(Q'.abs (next + -model)) ≤ next + -model := by
    have hnegated :
        -(Q'.abs (next + -model)) ≤ -(-(next + -model)) :=
      Q'.neg_le_neg (Q'.neg_le_abs (next + -model))
    exact Q'.le_trans' _ _ _ hnegated
      (Q'.le_of_eqv (Q'.neg_neg_eqv (next + -model)))
  have hdiff : -error ≤ next + -model :=
    Q'.le_trans' _ _ _ hnegError hnegAbs
  have hadd :
      (-error) + model ≤ (next + -model) + model :=
    Q'.add_le_add_right (-error) (next + -model) model hdiff
  have hleft : ((-error) + model).eqv (model + (-error)) :=
    Q'.add_comm_eqv (-error) model
  have hright : ((next + -model) + model).eqv next := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv next (-model) model) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left next ((-model) + model) 0
        (Q'.neg_add_self_eqv model)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' next)
  have hwindowCommuted : error + lower ≤ model :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_comm_eqv error lower)) hwindow
  have hshifted :
      (error + lower) + (-error) ≤ model + (-error) :=
    Q'.add_le_add_right (error + lower) model (-error) hwindowCommuted
  have hcancel : ((error + lower) + (-error)).eqv lower := by
    exact poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun
        | 0 => error
        | _ => lower)
  have hmodelSubError : lower ≤ model + (-error) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hshifted
  exact Q'.le_trans' _ _ _ hmodelSubError
    (Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright)))

theorem bulkSourceLowerFaceHeronResidualEnvelope_le_half
    (s : Nat) (hs : 0 < s) :
    combGaugeFreeHistoryHeronBilinearResidualEnvelope
        1 (bulkSourceWidth s) (bulkSourcePositiveHeronStage s)
        (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 0
          (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)))
        (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 1
          (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s))) ≤
      HalfPow.half * bulkSourceLowerFaceOneBondCovariance s := by
  let coefficient := bulkSourceLowerFaceHeronResidualCoefficient s
  let exactMixed := bulkSourceLowerFaceOneBondCovariance s
  let amplitude := HalfPow.half * coefficient
  let tolerance := HalfPow.half * exactMixed
  have hcoefficient : (0 : Q') ≤ coefficient :=
    bulkSourceLowerFaceHeronResidualCoefficient_nonnegative s
  have hamplitude : (0 : Q') ≤ amplitude :=
    Q'.mul_nonneg _ _ HalfPow.half_nonneg hcoefficient
  have htolerance : (0 : Q') < tolerance :=
    ExpNeg.half_mul_pos exactMixed
      (bulkSourceLowerFaceOneBondCovariance_pos s hs)
  have htail := geoTail_le_of_modulus amplitude hamplitude
    tolerance htolerance (bulkSourcePositiveHeronStage s)
    (Nat.le_refl (bulkSourcePositiveHeronStage s))
  have henvelope :
      combGaugeFreeHistoryHeronBilinearResidualEnvelope
          1 (bulkSourceWidth s) (bulkSourcePositiveHeronStage s)
          (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 0
            (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)))
          (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 1
            (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s))) ≈
        geoTail amplitude (bulkSourcePositiveHeronStage s) := by
    refine Q'.eqv_trans _ _ _
      (bulkSourceLowerFaceHeronResidualEnvelope_eq
        s (bulkSourcePositiveHeronStage s)) ?_
    unfold amplitude coefficient geoTail
    have hamplitudeEq :
        (Q'.ofNat 2 *
            (HalfPow.half *
              bulkSourceLowerFaceHeronResidualCoefficient s)) ≈
          bulkSourceLowerFaceHeronResidualCoefficient s := by
      refine Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.mul (.const 2) (.mul (.var 0) (.var 1)))
          (.add (.mul (.var 0) (.var 1))
            (.mul (.var 0) (.var 1)))
          (by decide) (fun
            | 0 => HalfPow.half
            | _ => bulkSourceLowerFaceHeronResidualCoefficient s)) ?_
      exact ExpNeg.two_halves
        (bulkSourceLowerFaceHeronResidualCoefficient s)
    exact Q'.eqv_symm
      (Q'.mul_eqv_congr_right _ _
        (HalfPow.half ^ bulkSourcePositiveHeronStage s) hamplitudeEq)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv henvelope) htail

theorem bulkSourceLowerFaceHeronMixedCovariance_ge_half
    (s : Nat) (hs : 0 < s) :
    HalfPow.half * bulkSourceLowerFaceOneBondCovariance s ≤
      bulkSourceLowerFaceHeronMixedCovariance
        s (bulkSourcePositiveHeronStage s) := by
  let envelope :=
    combGaugeFreeHistoryHeronBilinearResidualEnvelope
      1 (bulkSourceWidth s) (bulkSourcePositiveHeronStage s)
      (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 0
        (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)))
      (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 1
        (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)))
  have herror := combGaugeFreeHistoryHeronBilinear_error
    1 (bulkSourceWidth s) (bulkSourcePositiveHeronStage s)
    (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 0
      (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)))
    (combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 1
      (bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)))
  have henvelope :
      envelope ≤ HalfPow.half *
        bulkSourceLowerFaceOneBondCovariance s :=
    bulkSourceLowerFaceHeronResidualEnvelope_le_half s hs
  have hwindow :
      HalfPow.half * bulkSourceLowerFaceOneBondCovariance s + envelope ≤
        bulkSourceLowerFaceOneBondCovariance s := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left
        (HalfPow.half * bulkSourceLowerFaceOneBondCovariance s) envelope
        (HalfPow.half * bulkSourceLowerFaceOneBondCovariance s)
        henvelope) ?_
    exact Q'.le_of_eqv
      (ExpNeg.two_halves (bulkSourceLowerFaceOneBondCovariance s))
  exact lower_of_abs_remainder_local herror hwindow

theorem bulkSourceLowerFaceHeronMixedCovariance_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourceLowerFaceHeronMixedCovariance
      s (bulkSourcePositiveHeronStage s) := by
  exact Q'.pos_of_lt_of_le
    (ExpNeg.half_mul_pos _
      (bulkSourceLowerFaceOneBondCovariance_pos s hs))
    (bulkSourceLowerFaceHeronMixedCovariance_ge_half s hs)

def bulkSourceHeronCrossGramSummand
    (s : Nat) (hs : 0 < s) (stage sourceRow directionRow : Nat) : Q' :=
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))
  (bulkSourceIndexWeight s hs (sourceRow / 3) *
      bulkSourceIndexWeight s hs (directionRow / 3)) *
    (finiteRowGram
        (coordinateCount + (coordinateCount + coordinateCount))
        (bulkSourceHeronColorCurlRow 1 s stage 0 sourceRow)
        (bulkSourceHeronColorCurlRow 1 s stage 1 directionRow) *
      finiteRowGram
        (coordinateCount + (coordinateCount + coordinateCount))
        (bulkSourceHeronColorCurlRow 1 s stage 0 sourceRow)
        (bulkSourceHeronColorCurlRow 1 s stage 1 directionRow))

theorem bulkSourceHeronCrossGramSummand_nonnegative
    {s stage sourceRow directionRow : Nat} (hs : 0 < s)
    (hsource : sourceRow < 3 * (bulkSourceFaces s).length)
    (hdirection : directionRow < 3 * (bulkSourceFaces s).length) :
    (0 : Q') ≤ bulkSourceHeronCrossGramSummand
      s hs stage sourceRow directionRow := by
  have hsourceIndex : sourceRow / 3 < (bulkSourceFaces s).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    rwa [Nat.mul_comm]
  have hdirectionIndex : directionRow / 3 < (bulkSourceFaces s).length := by
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).2
    rwa [Nat.mul_comm]
  have hsourceWeight := bulkSourceIndexWeight_pos hs hsourceIndex
  have hdirectionWeight := bulkSourceIndexWeight_pos hs hdirectionIndex
  unfold bulkSourceHeronCrossGramSummand
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt hsourceWeight)
      (Q'.le_of_lt hdirectionWeight))
    (SumOfSquares.q_mul_self_nonneg _)

theorem bulkSourceLowerFaceHeronColorGram_eqv_mixed
    (s stage : Nat) :
    let coordinateCount :=
      historyCoordinateCount 1
        (combGaugeEdgeCount (bulkSourceWidth s))
    let rowIndex := bulkSourceLowerFaceIndex s * 3
    finiteRowGram
        (coordinateCount + (coordinateCount + coordinateCount))
        (bulkSourceHeronColorCurlRow 1 s stage 0 rowIndex)
        (bulkSourceHeronColorCurlRow 1 s stage 1 rowIndex) ≈
      bulkSourceLowerFaceHeronMixedCovariance s stage := by
  let coordinateCount :=
    historyCoordinateCount 1
      (combGaugeEdgeCount (bulkSourceWidth s))
  let transform :=
    combGaugeFreeHistoryHeronTransform 1 (bulkSourceWidth s) stage
  let faceIndex :=
    bulkSourceInternalFaceIndex s (bulkSourceLowerFaceIndex s)
  let lowerRow :=
    combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 0 faceIndex
  let upperRow :=
    combGaugeFreeHistoryCurlRow (bulkSourceWidth s) 1 faceIndex
  have hcolor := finiteRowGram_threeColorRows coordinateCount 0 0
    (pulledRow coordinateCount transform lowerRow)
    (pulledRow coordinateCount transform upperRow)
    (by decide) (by decide)
  have hcolor' :
      finiteRowGram
          (coordinateCount + (coordinateCount + coordinateCount))
          (threeColorRows coordinateCount
            (pulledRow coordinateCount transform lowerRow) 0)
          (threeColorRows coordinateCount
            (pulledRow coordinateCount transform upperRow) 0) ≈
        finiteRowGram coordinateCount
          (pulledRow coordinateCount transform lowerRow)
          (pulledRow coordinateCount transform upperRow) := by
    simpa using hcolor
  have hpull := finiteRowGram_pulledRow
    coordinateCount coordinateCount transform lowerRow upperRow
  have hgram := Q'.eqv_trans _ _ _ hcolor' hpull
  have hdiv : bulkSourceLowerFaceIndex s * 3 / 3 =
      bulkSourceLowerFaceIndex s := by omega
  have hmod : bulkSourceLowerFaceIndex s * 3 % 3 = 0 := by omega
  have hlowerColor :
      bulkSourceHeronColorCurlRow 1 s stage 0
          (bulkSourceLowerFaceIndex s * 3) =
        threeColorRows coordinateCount
          (pulledRow coordinateCount transform lowerRow) 0 := by
    funext coordinate
    unfold bulkSourceHeronColorCurlRow
      combGaugeFreeHistoryHeronColorCurlRow
    rw [hdiv, hmod]
  have hupperColor :
      bulkSourceHeronColorCurlRow 1 s stage 1
          (bulkSourceLowerFaceIndex s * 3) =
        threeColorRows coordinateCount
          (pulledRow coordinateCount transform upperRow) 0 := by
    funext coordinate
    unfold bulkSourceHeronColorCurlRow
      combGaugeFreeHistoryHeronColorCurlRow
    rw [hdiv, hmod]
  dsimp only
  rw [hlowerColor, hupperColor]
  simpa [
    bulkSourceLowerFaceHeronMixedCovariance,
    coordinateCount, transform, faceIndex, lowerRow, upperRow,
    hdiv, hmod] using hgram

theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      value witness ≤ listQSum value items
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item hitem =>
              hnonnegative item (List.mem_cons_of_mem head hitem)))
      · have htailLe := listQSum_member_le_nonnegative_local
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail
        have hsumLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ htailLe hsumLe

theorem bulkSourceHeronCrossGramSquareTrace_eq_sum
    (s : Nat) (hs : 0 < s) (stage : Nat) :
    bulkSourceHeronCrossGramSquareTrace 1 s hs stage 0 1 ≈
      listQSum
        (fun sourceRow =>
          listQSum
            (fun directionRow =>
              bulkSourceHeronCrossGramSummand
                s hs stage sourceRow directionRow)
            (List.range (3 * (bulkSourceFaces s).length)))
        (List.range (3 * (bulkSourceFaces s).length)) := by
  unfold bulkSourceHeronCrossGramSquareTrace
    finiteWeightedCrossGramSquareTrace
    bulkSourceHeronCrossGramSummand
  simp only [qListSum_map_eq_listQSum_local]
  exact Q'.eqv_refl _

/-- At the selected explicit stage, the full weighted cross-Gram-square trace
is strictly positive because it contains the positive color-zero lower-face
square. -/
theorem bulkSourcePositiveHeronCrossGramSquareTrace_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourceHeronCrossGramSquareTrace
      1 s hs (bulkSourcePositiveHeronStage s) 0 1 := by
  let rowIndex := bulkSourceLowerFaceIndex s * 3
  have hfaceIndex := bulkSourceLowerFaceIndex_lt s hs
  have hrowIndex : rowIndex < 3 * (bulkSourceFaces s).length := by
    unfold rowIndex
    omega
  have hweight := bulkSourceIndexWeight_pos hs hfaceIndex
  have hgramEq := bulkSourceLowerFaceHeronColorGram_eqv_mixed
    s (bulkSourcePositiveHeronStage s)
  have hgramPos :
      (0 : Q') <
        finiteRowGram
          (historyCoordinateCount 1
              (combGaugeEdgeCount (bulkSourceWidth s)) +
            (historyCoordinateCount 1
                (combGaugeEdgeCount (bulkSourceWidth s)) +
              historyCoordinateCount 1
                (combGaugeEdgeCount (bulkSourceWidth s))))
          (bulkSourceHeronColorCurlRow 1 s
            (bulkSourcePositiveHeronStage s) 0 rowIndex)
          (bulkSourceHeronColorCurlRow 1 s
            (bulkSourcePositiveHeronStage s) 1 rowIndex) :=
    Q'.pos_of_lt_of_le
      (bulkSourceLowerFaceHeronMixedCovariance_pos s hs)
      (Q'.ge_of_eqv hgramEq)
  have hsummand :
      (0 : Q') < bulkSourceHeronCrossGramSummand s hs
        (bulkSourcePositiveHeronStage s) rowIndex rowIndex := by
    have hdiv : bulkSourceLowerFaceIndex s * 3 / 3 =
        bulkSourceLowerFaceIndex s := by omega
    unfold bulkSourceHeronCrossGramSummand rowIndex
    rw [hdiv]
    exact Q'.mul_pos
      (Q'.mul_pos hweight hweight)
      (Q'.mul_pos hgramPos hgramPos)
  have hinner :
      bulkSourceHeronCrossGramSummand s hs
          (bulkSourcePositiveHeronStage s) rowIndex rowIndex ≤
        listQSum
          (fun directionRow =>
            bulkSourceHeronCrossGramSummand s hs
              (bulkSourcePositiveHeronStage s) rowIndex directionRow)
          (List.range (3 * (bulkSourceFaces s).length)) := by
    apply listQSum_member_le_nonnegative_local
    · intro directionRow hdirection
      exact bulkSourceHeronCrossGramSummand_nonnegative hs hrowIndex
        (List.mem_range.mp hdirection)
    · exact List.mem_range.mpr hrowIndex
  have houter :
      listQSum
          (fun directionRow =>
            bulkSourceHeronCrossGramSummand s hs
              (bulkSourcePositiveHeronStage s) rowIndex directionRow)
          (List.range (3 * (bulkSourceFaces s).length)) ≤
        listQSum
          (fun sourceRow =>
            listQSum
              (fun directionRow =>
                bulkSourceHeronCrossGramSummand s hs
                  (bulkSourcePositiveHeronStage s) sourceRow directionRow)
              (List.range (3 * (bulkSourceFaces s).length)))
          (List.range (3 * (bulkSourceFaces s).length)) := by
    apply listQSum_member_le_nonnegative_local
    · intro sourceRow hsource
      apply listQSum_nonnegative_on
      intro directionRow hdirection
      exact bulkSourceHeronCrossGramSummand_nonnegative hs
        (List.mem_range.mp hsource) (List.mem_range.mp hdirection)
    · exact List.mem_range.mpr hrowIndex
  have hsum :
      bulkSourceHeronCrossGramSummand s hs
          (bulkSourcePositiveHeronStage s) rowIndex rowIndex ≤
        listQSum
          (fun sourceRow =>
            listQSum
              (fun directionRow =>
                bulkSourceHeronCrossGramSummand s hs
                  (bulkSourcePositiveHeronStage s) sourceRow directionRow)
              (List.range (3 * (bulkSourceFaces s).length)))
          (List.range (3 * (bulkSourceFaces s).length)) :=
    Q'.le_trans' _ _ _ hinner houter
  have htrace := bulkSourceHeronCrossGramSquareTrace_eq_sum
    s hs (bulkSourcePositiveHeronStage s)
  exact Q'.pos_of_lt_of_le hsummand
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv htrace))

/-- The actual finite product-Gaussian covariance of the two weighted bulk
source radial squares is strictly positive at the same explicit stage. -/
theorem bulkSourcePositiveHeronRadialPairCovariance_pos
    (s : Nat) (hs : 0 < s) :
    (0 : Q') < bulkSourceHeronRadialPairCovariance
      1 s hs (bulkSourcePositiveHeronStage s) 0 1 := by
  have htraceIdentity := bulkSourceHeronRadialPairCovariance_trace
    1 s hs (bulkSourcePositiveHeronStage s) 0 1
  change bulkSourceHeronRadialPairCovariance
      1 s hs (bulkSourcePositiveHeronStage s) 0 1 ≈
    2 * bulkSourceHeronCrossGramSquareTrace
      1 s hs (bulkSourcePositiveHeronStage s) 0 1 at htraceIdentity
  exact Q'.pos_of_lt_of_le
    (Q'.mul_pos (by decide)
      (bulkSourcePositiveHeronCrossGramSquareTrace_pos s hs))
    (Q'.ge_of_eqv htraceIdentity)

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.bulkSourceLowerFaceHeronResidualCoefficient_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.bulkSourceLowerFaceHeronResidualEnvelope_le_half
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.bulkSourceLowerFaceHeronMixedCovariance_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.bulkSourcePositiveHeronCrossGramSquareTrace_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.bulkSourcePositiveHeronRadialPairCovariance_pos
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.qListSum_map_eq_listQSum_local
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.ldlFactorResidualEnvelope_eq_coefficient_mul_half
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.physicalResidualEnvelope_eq_coefficient_mul_half
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.lower_of_abs_remainder_local
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.bulkSourceHeronCrossGramSummand_nonnegative
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.listQSum_member_le_nonnegative_local
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeBulkHeronPositiveStage.bulkSourceHeronCrossGramSquareTrace_eq_sum
