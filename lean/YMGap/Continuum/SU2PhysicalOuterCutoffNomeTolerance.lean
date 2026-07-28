/-
# Arbitrary-nome tolerance schedule for the physical SU(2) outer tail

For every constructive rational nome `0 < w < 1`, this module builds an
executable cutoff for the physical degree-thirteen Casimir tail.  The cutoff
has two stages:

* `physicalNomeRatioStart` uses the general-base power modulus to force the
  degree-thirteen successive-term ratio below `1/2`;
* `physicalNomeHeadOffset` spends a finite, explicitly computed burn-in after
  that ratio start to force the first tail term below `1/2`.

Every further retained label buys another dyadic power.  At a fixed finite
tensor dimension, an `invSucc` rescaling then pays the finite tensor
coefficient and produces a cutoff for an arbitrary positive rational total
tolerance.  All estimates are uniform in the later outer cutoff.

The cutoff is allowed to diverge as `w` approaches one.  No spacing-uniform
claim is made here.

## Axiom gate

Constructive `Nat`/`Q'` recursion only.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, choice, functional extensionality, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

namespace YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The ratio stage -/

/-- Power target which exactly pays the degree-thirteen polynomial ratio:
`2^13 * 2^(-14) = 1/2`. -/
def physicalDegreeRatioPowerTarget : Q' :=
  Q'.mkPos 1
    (2 ^ (physicalFacePolynomialDegree + 1))
    (by decide)

/-- Raw power cutoff supplied by the general-base constructive modulus. -/
def physicalNomeRawPowerCutoff (w : Q') : Nat :=
  powBaseCutoff w physicalDegreeRatioPowerTarget

/-- First label at which the degree-thirteen ratio stage is active.  The
extra successor makes positivity of the eventual base cutoff transparent. -/
def physicalNomeRatioStart (w : Q') : Nat :=
  physicalNomeRawPowerCutoff w + 1

theorem physicalNomeRatioStart_pos (w : Q') :
    1 ≤ physicalNomeRatioStart w := by
  unfold physicalNomeRatioStart
  omega

theorem physicalNomeRawPower_le_target
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    qpow w (physicalNomeRawPowerCutoff w) ≤
      physicalDegreeRatioPowerTarget := by
  have hpow :
      w ^ physicalNomeRawPowerCutoff w ≤
        physicalDegreeRatioPowerTarget := by
    exact pow_base_le_cutoff hw0 hw1 (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (SU2PointwiseHeatSpacingCompletion.qpow_eqv_pow
        w (physicalNomeRawPowerCutoff w)))
    hpow

/-- Every exponent beyond the raw power cutoff satisfies the physical
degree-thirteen ratio condition. -/
theorem physicalDegreeThirteenCutoffCondition_of_raw_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {S : Nat}
    (hraw :
      physicalNomeRawPowerCutoff w ≤ 2 * S + 3) :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
        qpow w (2 * S + 3) ≤
      HalfPow.half := by
  have hmono :
      qpow w (2 * S + 3) ≤
        qpow w (physicalNomeRawPowerCutoff w) :=
    qpow_antitone
      (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      (physicalNomeRawPowerCutoff w)
      (2 * S + 3) hraw
  have hscaled :
      Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          qpow w (2 * S + 3) ≤
        Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
          physicalDegreeRatioPowerTarget :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.le_trans' _ _ _ hmono
        (physicalNomeRawPower_le_target hw0 hw1))
      (by exact zero_le_ofNat _)
  refine Q'.le_trans' _ _ _ hscaled ?_
  unfold physicalDegreeRatioPowerTarget
    physicalFacePolynomialDegree HalfPow.half
  decide

theorem physicalNomeRatioStartCondition
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
        qpow w (2 * physicalNomeRatioStart w + 3) ≤
      HalfPow.half := by
  exact physicalDegreeThirteenCutoffCondition_of_raw_le
    hw0 hw1 (by
      unfold physicalNomeRatioStart
      omega)

/-! ## 2. Executable burn-in for the head -/

/-- The degree-thirteen term at the start of the geometric-ratio regime. -/
def physicalNomeRatioHead (w : Q') : Q' :=
  tailTerm w physicalFacePolynomialDegree
    (physicalNomeRatioStart w)

/-- A structurally positive coefficient dominating the ratio-stage head. -/
def physicalNomeHeadCoefficient (w : Q') : Q' :=
  1 + physicalNomeRatioHead w

theorem physicalNomeHeadCoefficient_pos
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') < physicalNomeHeadCoefficient w := by
  have hhead :
      (0 : Q') ≤ physicalNomeRatioHead w := by
    unfold physicalNomeRatioHead
    exact tailTerm_nonneg
      (Q'.le_of_lt hw0)
      physicalFacePolynomialDegree
      (physicalNomeRatioStart w)
  have hone :
      (1 : Q') ≤ physicalNomeHeadCoefficient w := by
    unfold physicalNomeHeadCoefficient
    exact Q'.add_le_self_of_nonneg 1 _ hhead
  exact lt_of_lt_of_le (by decide) hone

/-- Tolerance used to pay the actual ratio-stage head.  `HKConv.divPos` is a
total rational program; its cancellation theorem is invoked only after the
coefficient positivity proof is available. -/
def physicalNomeHeadScaledTolerance (w : Q') : Q' :=
  YMGap.Continuum.HKConv.divPos
    HalfPow.half (physicalNomeHeadCoefficient w)

/-- Number of post-ratio labels spent to make the head at most `1/2`. -/
def physicalNomeHeadOffset (w : Q') : Nat :=
  (physicalNomeHeadScaledTolerance w).den

/-- The final one-coordinate base cutoff. -/
def physicalNomeBaseCutoff (w : Q') : Nat :=
  physicalNomeRatioStart w + physicalNomeHeadOffset w

theorem physicalNomeBaseCutoff_pos (w : Q') :
    1 ≤ physicalNomeBaseCutoff w := by
  unfold physicalNomeBaseCutoff
  exact Nat.le_trans
    (physicalNomeRatioStart_pos w)
    (Nat.le_add_right _ _)

private theorem physicalDegreeThirteenHeadFromRatioStart
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ∀ precision : Nat,
      tailTerm w physicalFacePolynomialDegree
          (physicalNomeRatioStart w + precision) ≤
        dyad precision * physicalNomeRatioHead w
  | 0 => by
      unfold physicalNomeRatioHead
      simpa only [Nat.add_zero, dyad, Q'.pow_zero] using
        Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.one_mul_eqv
              (tailTerm w physicalFacePolynomialDegree
                (physicalNomeRatioStart w))))
  | precision + 1 => by
      have ih :=
        physicalDegreeThirteenHeadFromRatioStart
          hw0 hw1 precision
      have hratio :=
        tailTerm_ratio
          (w := w)
          (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
          physicalFacePolynomialDegree
          (physicalNomeRatioStart w)
          precision
      have hterm0 :
          (0 : Q') ≤
            tailTerm w physicalFacePolynomialDegree
              (physicalNomeRatioStart w + precision) :=
        tailTerm_nonneg
          (Q'.le_of_lt hw0)
          physicalFacePolynomialDegree
          (physicalNomeRatioStart w + precision)
      have hratioHalf :
          (Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
              qpow w (2 * physicalNomeRatioStart w + 3)) *
                tailTerm w physicalFacePolynomialDegree
                  (physicalNomeRatioStart w + precision) ≤
            HalfPow.half *
                tailTerm w physicalFacePolynomialDegree
                  (physicalNomeRatioStart w + precision) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (physicalNomeRatioStartCondition hw0 hw1)
          hterm0
      have hdyad :
          HalfPow.half *
                tailTerm w physicalFacePolynomialDegree
                  (physicalNomeRatioStart w + precision) ≤
            HalfPow.half *
              (dyad precision * physicalNomeRatioHead w) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih
          HalfPow.half_nonneg
      have hcombined :
          tailTerm w physicalFacePolynomialDegree
              (physicalNomeRatioStart w + (precision + 1)) ≤
            HalfPow.half *
              (dyad precision * physicalNomeRatioHead w) :=
        Q'.le_trans' _ _ _ hratio
          (Q'.le_trans' _ _ _ hratioHalf hdyad)
      exact Q'.le_trans' _ _ _ hcombined
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              HalfPow.half (dyad precision)
              (physicalNomeRatioHead w))))

theorem physicalNomeHeadOffset_pays
    {w : Q'} (hw0 : (0 : Q') < w) :
    dyad (physicalNomeHeadOffset w) *
        physicalNomeRatioHead w ≤
      HalfPow.half := by
  let coefficient := physicalNomeHeadCoefficient w
  let tolerance := physicalNomeHeadScaledTolerance w
  have hcoefficientPos : (0 : Q') < coefficient :=
    physicalNomeHeadCoefficient_pos hw0
  have htolerancePos : (0 : Q') < tolerance := by
    exact YMGap.Continuum.HKConv.divPos_pos (by decide)
  have hdyad :
      dyad (physicalNomeHeadOffset w) ≤ tolerance := by
    change HalfPow.half ^ tolerance.den ≤ tolerance
    exact HalfPow.pow_half_le tolerance htolerancePos
  have hheadNonnegative :
      (0 : Q') ≤ physicalNomeRatioHead w := by
    unfold physicalNomeRatioHead
    exact tailTerm_nonneg
      (Q'.le_of_lt hw0)
      physicalFacePolynomialDegree
      (physicalNomeRatioStart w)
  have hheadLe :
      physicalNomeRatioHead w ≤ coefficient := by
    dsimp only [coefficient]
    unfold physicalNomeHeadCoefficient
    refine Q'.le_trans' _ (physicalNomeRatioHead w + 1) _ ?_ ?_
    · exact Q'.add_le_self_of_nonneg _ _ Q'.zero_le_one
    · exact Q'.le_of_eqv
        (Q'.add_comm_eqv
          (physicalNomeRatioHead w) 1)
  have hscale :
      dyad (physicalNomeHeadOffset w) *
          physicalNomeRatioHead w ≤
        tolerance * coefficient := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        _ _ _ hdyad hheadNonnegative)
      (Q'.mul_le_mul_of_nonneg_left
        _ _ _ hheadLe (Q'.le_of_lt htolerancePos))
  have hcancel : tolerance * coefficient ≈ HalfPow.half := by
    exact YMGap.Continuum.HKConv.divPos_mul_eqv
      (CReal.num_pos_of_pos hcoefficientPos)
  exact Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hcancel)

theorem physicalNomeBaseHead
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    tailTerm w physicalFacePolynomialDegree
        (physicalNomeBaseCutoff w) ≤
      dyad 1 := by
  have hburn :=
    physicalDegreeThirteenHeadFromRatioStart
      hw0 hw1 (physicalNomeHeadOffset w)
  unfold physicalNomeBaseCutoff
  exact Q'.le_trans' _ _ _ hburn
    (physicalNomeHeadOffset_pays hw0)

theorem physicalNomeBaseCondition
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
        qpow w (2 * physicalNomeBaseCutoff w + 3) ≤
      HalfPow.half := by
  exact physicalDegreeThirteenCutoffCondition_of_raw_le
    hw0 hw1 (by
      unfold physicalNomeBaseCutoff physicalNomeRatioStart
      omega)

/-! ## 3. Every further label buys one dyadic power -/

/-- Retained cutoff whose first omitted label is
`physicalNomeBaseCutoff w + precision`. -/
def physicalNomeRetainedCutoff (w : Q') (precision : Nat) : Nat :=
  physicalNomeBaseCutoff w - 1 + precision

theorem physicalNomeRetainedCutoff_succ
    (w : Q') (precision : Nat) :
    physicalNomeRetainedCutoff w precision + 1 =
      physicalNomeBaseCutoff w + precision := by
  unfold physicalNomeRetainedCutoff
  have hbase := physicalNomeBaseCutoff_pos w
  omega

private theorem physicalDegreeThirteenHeadFromBase
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ∀ precision : Nat,
      tailTerm w physicalFacePolynomialDegree
          (physicalNomeBaseCutoff w + precision) ≤
        dyad (precision + 1)
  | 0 => by
      simpa only [Nat.add_zero] using
        physicalNomeBaseHead hw0 hw1
  | precision + 1 => by
      have ih :=
        physicalDegreeThirteenHeadFromBase
          hw0 hw1 precision
      have hratio :=
        tailTerm_ratio
          (w := w)
          (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
          physicalFacePolynomialDegree
          (physicalNomeBaseCutoff w)
          precision
      have hterm0 :
          (0 : Q') ≤
            tailTerm w physicalFacePolynomialDegree
              (physicalNomeBaseCutoff w + precision) :=
        tailTerm_nonneg
          (Q'.le_of_lt hw0)
          physicalFacePolynomialDegree
          (physicalNomeBaseCutoff w + precision)
      have hratioHalf :
          (Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
              qpow w (2 * physicalNomeBaseCutoff w + 3)) *
                tailTerm w physicalFacePolynomialDegree
                  (physicalNomeBaseCutoff w + precision) ≤
            HalfPow.half *
                tailTerm w physicalFacePolynomialDegree
                  (physicalNomeBaseCutoff w + precision) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (physicalNomeBaseCondition hw0 hw1)
          hterm0
      have hdyad :
          HalfPow.half *
                tailTerm w physicalFacePolynomialDegree
                  (physicalNomeBaseCutoff w + precision) ≤
            HalfPow.half * dyad (precision + 1) :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ ih
          HalfPow.half_nonneg
      have hcombined :
          tailTerm w physicalFacePolynomialDegree
              (physicalNomeBaseCutoff w + (precision + 1)) ≤
            HalfPow.half * dyad (precision + 1) :=
        Q'.le_trans' _ _ _ hratio
          (Q'.le_trans' _ _ _ hratioHalf hdyad)
      simpa only [dyad, Q'.pow_succ] using hcombined

theorem physicalNomeRetainedHead
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (precision : Nat) :
    tailTerm w physicalFacePolynomialDegree
        (physicalNomeRetainedCutoff w precision + 1) ≤
      dyad (precision + 1) := by
  rw [physicalNomeRetainedCutoff_succ]
  exact physicalDegreeThirteenHeadFromBase hw0 hw1 precision

theorem physicalNomeRetainedCondition
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (precision : Nat) :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
        qpow w
          (2 * (physicalNomeRetainedCutoff w precision + 1) + 3) ≤
      HalfPow.half := by
  exact physicalDegreeThirteenCutoffCondition_of_raw_le
    hw0 hw1 (by
      rw [physicalNomeRetainedCutoff_succ]
      unfold physicalNomeBaseCutoff physicalNomeRatioStart
      omega)

theorem physicalNomeOuterShellMass_le_dyad
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (precision K : Nat) :
    su2PhysicalOuterShellMass
        w (physicalNomeRetainedCutoff w precision) K ≤
      dyad precision := by
  exact su2PhysicalOuterShellMass_le_dyad
    hw0 hw1 precision
    (physicalNomeRetainedCondition hw0 hw1 precision)
    (physicalNomeRetainedHead hw0 hw1 precision)

/-! ## 4. Fixed-dimensional total tolerance -/

def physicalNomeOneFaceCeiling (w : Q') : Q' :=
  su2PhysicalHeatCeiling w (physicalNomeBaseCutoff w)

theorem physicalNomeOneFaceCeiling_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤ physicalNomeOneFaceCeiling w := by
  unfold physicalNomeOneFaceCeiling
  exact su2PhysicalHeatCeiling_nonnegative
    hw0 (physicalNomeBaseCutoff w)

def physicalNomeTensorTailCoefficient (w : Q') : Nat → Q'
  | 0 => 0
  | dimension + 1 =>
      physicalNomeOneFaceCeiling w ^ dimension +
        physicalNomeOneFaceCeiling w *
          physicalNomeTensorTailCoefficient w dimension

theorem physicalNomeTensorTailCoefficient_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) :
    ∀ dimension,
      (0 : Q') ≤
        physicalNomeTensorTailCoefficient w dimension
  | 0 => Q'.le_refl' 0
  | dimension + 1 =>
      Q'.zero_le_add _ _
        (Q'.pow_nonneg _
          (physicalNomeOneFaceCeiling_nonnegative hw0)
          dimension)
        (Q'.mul_nonneg _ _
          (physicalNomeOneFaceCeiling_nonnegative hw0)
          (physicalNomeTensorTailCoefficient_nonnegative
            hw0 dimension))

theorem physicalNomeTensorTailEnvelope_eqv_coefficient
    (w : Q') (M precision : Nat) :
    ∀ dimension,
      su2PhysicalTensorTailEnvelope
          w (physicalNomeBaseCutoff w)
          M precision dimension ≈
        dyad precision *
          physicalNomeTensorTailCoefficient w dimension
  | 0 =>
      Q'.eqv_symm
        (Q'.mul_zero_eqv (dyad precision))
  | dimension + 1 => by
      have ih :=
        physicalNomeTensorTailEnvelope_eqv_coefficient
          w M precision dimension
      change
        dyad precision *
              physicalNomeOneFaceCeiling w ^ dimension +
            physicalNomeOneFaceCeiling w *
              su2PhysicalTensorTailEnvelope
                w (physicalNomeBaseCutoff w)
                M precision dimension ≈
          dyad precision *
            (physicalNomeOneFaceCeiling w ^ dimension +
              physicalNomeOneFaceCeiling w *
                physicalNomeTensorTailCoefficient w dimension)
      have hsecond :
          physicalNomeOneFaceCeiling w *
              su2PhysicalTensorTailEnvelope
                w (physicalNomeBaseCutoff w)
                M precision dimension ≈
            dyad precision *
              (physicalNomeOneFaceCeiling w *
                physicalNomeTensorTailCoefficient w dimension) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (physicalNomeOneFaceCeiling w) _ _ ih) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv
              (physicalNomeOneFaceCeiling w)
              (dyad precision)
              (physicalNomeTensorTailCoefficient w dimension))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (physicalNomeOneFaceCeiling w * dyad precision)
            (dyad precision * physicalNomeOneFaceCeiling w)
            (physicalNomeTensorTailCoefficient w dimension)
            (Q'.mul_comm_eqv
              (physicalNomeOneFaceCeiling w)
              (dyad precision))) ?_
        exact Q'.mul_assoc_eqv
          (dyad precision)
          (physicalNomeOneFaceCeiling w)
          (physicalNomeTensorTailCoefficient w dimension)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (dyad precision *
            physicalNomeOneFaceCeiling w ^ dimension)
          _ _ hsecond) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv
          (dyad precision)
          (physicalNomeOneFaceCeiling w ^ dimension)
          (physicalNomeOneFaceCeiling w *
            physicalNomeTensorTailCoefficient w dimension))

def physicalNomeTensorScaledTolerance
    (w : Q') (dimension : Nat) (ε : Q') : Q' :=
  ε * Q'.invSucc
    (physicalNomeTensorTailCoefficient w dimension).num.toNat

theorem physicalNomeTensorScaledTolerance_pos
    {w : Q'}
    (dimension : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') <
      physicalNomeTensorScaledTolerance w dimension ε := by
  unfold physicalNomeTensorScaledTolerance
  exact Q'.mul_pos hε (Q'.invSucc_pos _)

def physicalNomeTensorTolerancePrecision
    (w : Q') (dimension : Nat) (ε : Q') : Nat :=
  (physicalNomeTensorScaledTolerance w dimension ε).den

def physicalNomeTensorToleranceRetainedCutoff
    (w : Q') (dimension : Nat) (ε : Q') : Nat :=
  physicalNomeRetainedCutoff w
    (physicalNomeTensorTolerancePrecision w dimension ε)

theorem physicalNomeTensorTailEnvelope_le_tolerance
    {w : Q'} (hw0 : (0 : Q') < w)
    (dimension : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    su2PhysicalTensorTailEnvelope
        w (physicalNomeBaseCutoff w)
        (physicalNomeTensorToleranceRetainedCutoff
          w dimension ε)
        (physicalNomeTensorTolerancePrecision
          w dimension ε)
        dimension ≤
      ε := by
  let coefficient :=
    physicalNomeTensorTailCoefficient w dimension
  let tolerance :=
    physicalNomeTensorScaledTolerance w dimension ε
  let precision :=
    physicalNomeTensorTolerancePrecision w dimension ε
  have hcoefficient : (0 : Q') ≤ coefficient :=
    physicalNomeTensorTailCoefficient_nonnegative hw0 dimension
  have htolerance : (0 : Q') < tolerance :=
    physicalNomeTensorScaledTolerance_pos
      dimension hε
  have hdyad :
      dyad precision ≤ tolerance := by
    change HalfPow.half ^ tolerance.den ≤ tolerance
    exact HalfPow.pow_half_le tolerance htolerance
  have hfactor :=
    physicalNomeTensorTailEnvelope_eqv_coefficient
      w
      (physicalNomeTensorToleranceRetainedCutoff
        w dimension ε)
      precision dimension
  have hscaled :
      dyad precision * coefficient ≤
        tolerance * coefficient :=
    Q'.mul_le_mul_of_nonneg_right
      _ _ _ hdyad hcoefficient
  have hpay :
      tolerance * coefficient ≤ ε := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv tolerance coefficient)) ?_
    dsimp only [coefficient, tolerance]
    exact
      YMGap.Constructive.ExpNeg.mul_le_of_mul_invSucc_toNat
        (physicalNomeTensorTailCoefficient w dimension)
        ε
        (physicalNomeTensorTailCoefficient_nonnegative
          hw0 dimension)
        (Q'.le_of_lt hε)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hfactor)
    (Q'.le_trans' _ _ _ hscaled hpay)

/-! ## 5. Uniformity in the later outer cutoff -/

theorem physicalNomeTensorOutsideUnionMass_le_tolerance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (dimension : Nat) {ε : Q'} (hε : (0 : Q') < ε)
    (K : Nat) :
    su2PhysicalTensorOutsideUnionMass
        w
        (physicalNomeTensorToleranceRetainedCutoff
          w dimension ε)
        K dimension ≤
      ε := by
  let precision :=
    physicalNomeTensorTolerancePrecision w dimension ε
  let retained :=
    physicalNomeTensorToleranceRetainedCutoff w dimension ε
  have henvelope :=
    su2PhysicalTensorOutsideUnionMass_le_envelope
      hw0 hw1
      (physicalNomeBaseCutoff w)
      precision
      (M := retained) (K := K)
      (physicalNomeBaseCondition hw0 hw1)
      (physicalNomeBaseHead hw0 hw1)
      (physicalNomeRetainedCondition hw0 hw1 precision)
      (physicalNomeRetainedHead hw0 hw1 precision)
      dimension
  exact Q'.le_trans' _ _ _ henvelope
    (physicalNomeTensorTailEnvelope_le_tolerance
      hw0 dimension hε)

/-- Literal finite-Fubini outside-event mass at fixed finite face carrier.
The later cutoff only has to contain the executable retained cutoff. -/
theorem boundedSU2PhysicalOutsideFaceMass_le_tolerance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (faces : List Nat) (hfaces : faces.Nodup)
    {ε : Q'} (hε : (0 : Q') < ε)
    {K : Nat}
    (hK :
      physicalNomeTensorToleranceRetainedCutoff
          w faces.length ε ≤ K) :
    boundedSU2PhysicalOutsideFaceMass
        w
        (physicalNomeTensorToleranceRetainedCutoff
          w faces.length ε)
        K faces ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (boundedSU2PhysicalOutsideFaceMass_le_unionMass
      hw0 hK faces hfaces)
    (physicalNomeTensorOutsideUnionMass_le_tolerance
      hw0 hw1 faces.length hε K)

structure PhysicalNomeTensorToleranceSchedule
    (w : Q') (dimension : Nat) (ε : Q') : Type where
  baseCutoff : Nat
  precision : Nat
  retainedCutoff : Nat
  baseCutoff_eq :
    baseCutoff = physicalNomeBaseCutoff w
  retainedCutoff_eq :
    retainedCutoff =
      physicalNomeRetainedCutoff w precision
  envelope_le :
    su2PhysicalTensorTailEnvelope
        w baseCutoff retainedCutoff precision dimension ≤
      ε

def canonicalPhysicalNomeTensorToleranceSchedule
    {w : Q'} (hw0 : (0 : Q') < w)
    (dimension : Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    PhysicalNomeTensorToleranceSchedule w dimension ε where
  baseCutoff := physicalNomeBaseCutoff w
  precision := physicalNomeTensorTolerancePrecision w dimension ε
  retainedCutoff :=
    physicalNomeTensorToleranceRetainedCutoff w dimension ε
  baseCutoff_eq := rfl
  retainedCutoff_eq := rfl
  envelope_le :=
    physicalNomeTensorTailEnvelope_le_tolerance
      hw0 dimension hε

/-! ## Axiom audit -/

#print axioms physicalNomeRawPower_le_target
#print axioms physicalNomeBaseHead
#print axioms physicalNomeRetainedHead
#print axioms physicalNomeTensorTailEnvelope_le_tolerance
#print axioms physicalNomeTensorOutsideUnionMass_le_tolerance
#print axioms boundedSU2PhysicalOutsideFaceMass_le_tolerance
#print axioms canonicalPhysicalNomeTensorToleranceSchedule

end YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
