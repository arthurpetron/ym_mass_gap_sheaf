/-
# Core-B consumer at the origin root diagonal

The endpoint comparison requested by `CrossRatioMonotone` is the zero-offset
potential `offsetDelta wH w s 0`.  Its diagonal telescope starts at the single
origin family

  cumulativeResidual wH w 0 0 s,

not at every root offset.  This file records that consumer-aligned reduction.
The already-proved worst-endpoint base-row sign then reduces the origin family
once more to the single row-one family `cumulativeResidual wH w 1 0 n`.

The final section banks the exact front/tail splice for arbitrary cumulative
lengths and its odd/even specializations at `(s,r)=(1,0)`.  These identities
isolate one full low-diagonal suffix in each parity.  They are algebraic only:
no sign is asserted for either the direct head or the parity suffix.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Continuum.CoreBResidualBaseWorstEndpoint
import YMGap.Continuum.CoreBRootCumulative
import YMGap.Continuum.CoreBUniversalSquareGap

namespace YMGap.Continuum.CoreBConsumerOrigin

set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FiniteSMarginWorstcase
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CoreBResidualPotential
open YMGap.Continuum.CoreBResidualBaseWorstEndpoint
open YMGap.Continuum.CoreBRootCumulative
open YMGap.Continuum.CoreBUniversalSquareGap

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact origin-root consumer -/

/-- Nonnegativity only on the root diagonal beginning at `(s,r)=(0,0)`.
This is the precise cumulative family consumed by `CrossRatioMonotone`. -/
structure OriginCumulativeResidualNonnegative (W h : Q') : Type where
  nonneg : ∀ n, (0 : Q') ≤ cumulativeResidual W h 0 0 n

/-- The remaining row-one origin family after separating the base-row head. -/
structure RowOneOriginCumulativeResidualNonnegative (W h : Q') : Type where
  nonneg : ∀ n, (0 : Q') ≤ cumulativeResidual W h 1 0 n

private theorem cumulativeResidual_zeroStart_nonneg_of_rowOneAt
    {W h : Q'} (r : Nat)
    (Hbase : ∀ k, (0 : Q') ≤ boundaryResidualAt W h 0 k)
    (Hone : ∀ n, (0 : Q') ≤ cumulativeResidual W h 1 r n) :
    ∀ n, (0 : Q') ≤ cumulativeResidual W h 0 r n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      have hsum : (0 : Q') ≤
          boundaryResidualAt W h 0 (r + n) +
            cumulativeResidual W h 1 r n :=
        Q'.zero_le_add _ _ (Hbase (r + n)) (Hone n)
      exact Q'.le_trans' _ _ _ hsum
        (Q'.ge_of_eqv (cumulativeResidual_zero_succ_split W h r n))

/-- At the worst endpoint, the uniform base-row theorem and the exact
root/row-one split reduce the origin cumulative to row one only. -/
def originCumulativeOfRowOneEndpoint {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hwH : w ≤ YMGap.Continuum.FusionCoreStepRoundA.wH)
    (H : RowOneOriginCumulativeResidualNonnegative
      YMGap.Continuum.FusionCoreStepRoundA.wH w) :
    OriginCumulativeResidualNonnegative
      YMGap.Continuum.FusionCoreStepRoundA.wH w where
  nonneg := cumulativeResidual_zeroStart_nonneg_of_rowOneAt 0
    (boundaryResidualAt_zero_nonneg_wH hw0 hwH) H.nonneg

/-- Origin-root cumulative positivity propagates to exactly the zero-offset
determinant needed by the cross-ratio comparison. -/
theorem offsetDelta_zeroOffset_nonneg_of_origin_cumulative {W h : Q'}
    (hh0 : (0 : Q') ≤ h) (hhW : h ≤ W)
    (H : OriginCumulativeResidualNonnegative W h) (s : Nat) :
    (0 : Q') ≤ offsetDelta W h s 0 := by
  have hsum : (0 : Q') ≤
      offsetDelta W h 0 s + cumulativeResidual W h 0 0 s :=
    Q'.zero_le_add _ _ (offsetDelta_zero_nonneg hh0 hhW s) (H.nonneg s)
  have htel := offsetDelta_diagonal_telescope W h 0 0 s
  have htel' : offsetDelta W h s 0 ≈
      offsetDelta W h 0 s + cumulativeResidual W h 0 0 s := by
    simpa only [Nat.zero_add] using htel
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv htel')

/-- **Origin-root CrossRatio adapter.**  The determinant orientation is
`A(wH)M(w)-M(wH)A(w) ≥ 0`; one commutation gives the exact field of
`CrossRatioMonotone.cross`. -/
def crossRatioMonotoneOfOriginCumulative {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hwH : w ≤ YMGap.Continuum.FusionCoreStepRoundA.wH)
    (H : OriginCumulativeResidualNonnegative
      YMGap.Continuum.FusionCoreStepRoundA.wH w) :
    CrossRatioMonotone w where
  cross := fun s => by
    have hdelta := offsetDelta_zeroOffset_nonneg_of_origin_cumulative
      hw0 hwH H s
    change (0 : Q') ≤
      offsetA YMGap.Continuum.FusionCoreStepRoundA.wH s 0 *
          offsetM w s 0 +
        -(offsetM YMGap.Continuum.FusionCoreStepRoundA.wH s 0 *
          offsetA w s 0) at hdelta
    have hle :
        offsetM YMGap.Continuum.FusionCoreStepRoundA.wH s 0 *
            offsetA w s 0 ≤
          offsetA YMGap.Continuum.FusionCoreStepRoundA.wH s 0 *
            offsetM w s 0 :=
      Q'.le_of_sub_nonneg hdelta
    have hoffset :
        offsetA w s 0 *
            offsetM YMGap.Continuum.FusionCoreStepRoundA.wH s 0 ≤
          offsetA YMGap.Continuum.FusionCoreStepRoundA.wH s 0 *
            offsetM w s 0 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hle
    simpa [offsetA, offsetM, modeWindow, Nat.add_zero, Nat.zero_add,
      Nat.add_assoc] using hoffset

/-- The endpoint base-row theorem makes the row-one origin cumulative the
sole residual sign premise of the consumer. -/
def crossRatioMonotoneOfRowOneOrigin {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hwH : w ≤ YMGap.Continuum.FusionCoreStepRoundA.wH)
    (H : RowOneOriginCumulativeResidualNonnegative
      YMGap.Continuum.FusionCoreStepRoundA.wH w) :
    CrossRatioMonotone w :=
  crossRatioMonotoneOfOriginCumulative hw0 hwH
    (originCumulativeOfRowOneEndpoint hw0 hwH H)

/-! ## 2. Quotient-to-consumer adapter -/

/-- Nonnegativity of the explicit universal square-gap quotient on the single
row-one origin family. -/
structure RowOneOriginSquareGapQuotientNonnegative (w : Q') : Type where
  nonneg : ∀ n, (0 : Q') ≤
    diagonalCumulativeSquareGapQuotient
      YMGap.Continuum.FusionCoreStepRoundA.wH w 1 0 n

/-- A coefficient payment for one canonical consumer length.
One producer may first combine equal bivariate monomials and then separate the
resulting polynomial into a reserve, adverse mass, and a favorable tail.
The interface does not require that implementation: an atomwise triangle
estimate may instead assemble the same three `Q'` values directly. -/
structure RowOneOriginCoefficientPayment (w : Q') (n : Nat) : Type where
  reserve : Q'
  favorable : Q'
  adverse : Q'
  quotient_eqv :
    diagonalCumulativeSquareGapQuotient
        YMGap.Continuum.FusionCoreStepRoundA.wH w 1 0 n ≈
      (reserve + -adverse) + favorable
  favorable_nonneg : (0 : Q') ≤ favorable
  adverse_le_reserve : adverse ≤ reserve

/-- Collected reserve payments at every length are exactly sufficient for the
row-one origin quotient certificate. -/
def rowOneOriginSquareGapQuotientNonnegativeOfPayments {w : Q'}
    (H : ∀ n, RowOneOriginCoefficientPayment w n) :
    RowOneOriginSquareGapQuotientNonnegative w where
  nonneg := by
    intro n
    let P := H n
    have hreserve : (0 : Q') ≤ P.reserve + -P.adverse :=
      Q'.sub_nonneg_of_le P.adverse_le_reserve
    have hsum : (0 : Q') ≤
        (P.reserve + -P.adverse) + P.favorable :=
      Q'.zero_le_add _ _ hreserve P.favorable_nonneg
    exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv P.quotient_eqv)

private theorem squareGap_wH_nonneg {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hwH : w ≤ YMGap.Continuum.FusionCoreStepRoundA.wH) :
    (0 : Q') ≤ squareGap YMGap.Continuum.FusionCoreStepRoundA.wH w := by
  unfold squareGap
  exact Q'.sub_nonneg_of_le (qpow_mono hw0 hwH 2)

/-- A nonnegative row-one quotient gives the row-one cumulative sign after
multiplication by the nonnegative endpoint square gap. -/
def rowOneOriginCumulativeOfSquareGapQuotient {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hwH : w ≤ YMGap.Continuum.FusionCoreStepRoundA.wH)
    (H : RowOneOriginSquareGapQuotientNonnegative w) :
    RowOneOriginCumulativeResidualNonnegative
      YMGap.Continuum.FusionCoreStepRoundA.wH w where
  nonneg := by
    intro n
    have hprod : (0 : Q') ≤
        squareGap YMGap.Continuum.FusionCoreStepRoundA.wH w *
          diagonalCumulativeSquareGapQuotient
            YMGap.Continuum.FusionCoreStepRoundA.wH w 1 0 n :=
      Q'.mul_nonneg _ _ (squareGap_wH_nonneg hw0 hwH) (H.nonneg n)
    exact Q'.le_trans' _ _ _ hprod
      (Q'.ge_of_eqv
        (cumulativeResidual_squareGap_factor
          YMGap.Continuum.FusionCoreStepRoundA.wH w 1 0 n))

/-- Direct quotient-level endpoint consumer.  Proving one explicit
row-one-origin quotient family nonnegative is sufficient for the whole
cross-ratio theorem. -/
def crossRatioMonotoneOfRowOneOriginSquareGapQuotient {w : Q'}
    (hw0 : (0 : Q') ≤ w)
    (hwH : w ≤ YMGap.Continuum.FusionCoreStepRoundA.wH)
    (H : RowOneOriginSquareGapQuotientNonnegative w) :
    CrossRatioMonotone w :=
  crossRatioMonotoneOfRowOneOrigin hw0 hwH
    (rowOneOriginCumulativeOfSquareGapQuotient hw0 hwH H)

/-! ## 3. Exact length splice and the two parity suffixes -/

/-- Split a diagonal cumulative after its first `a` cells.  The first block's
offset increases by the tail length, while the tail begins at row `s+a`. -/
theorem cumulativeResidual_add_length (W h : Q') (s r a : Nat) : ∀ b,
    cumulativeResidual W h s r (a + b) ≈
      cumulativeResidual W h s (r + b) a +
        cumulativeResidual W h (s + a) r b
  | 0 => by
      simp only [Nat.add_zero, cumulativeResidual]
      exact Q'.eqv_symm (q_add_zero_eqv _)
  | b + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      simp only [cumulativeResidual]
      have ih := cumulativeResidual_add_length W h s (r + 1) a b
      rw [show r + (b + 1) = (r + 1) + b by omega]
      rw [show s + (a + b) = s + a + b by omega]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      exact Q'.add_assoc_eqv _ _ _

/-- The same front/tail splice directly on the explicit cumulative quotient. -/
theorem diagonalCumulativeSquareGapQuotient_add_length
    (W h : Q') (s r a b : Nat) :
    diagonalCumulativeSquareGapQuotient W h s r (a + b) ≈
      diagonalCumulativeSquareGapQuotient W h s (r + b) a +
        diagonalCumulativeSquareGapQuotient W h (s + a) r b := by
  unfold diagonalCumulativeSquareGapQuotient
  refine Q'.eqv_trans _ _ _
    (YMGap.Continuum.FusionCoreStepRoundH.fsum_split_at
      (fun t => boundaryResidualSquareGapQuotient W h
        (s + t) (r + (a + b) - 1 - t)) a b) ?_
  exact Q'.add_eqv_congr'
    (fsum_eqv_congr_lt _ _ a (fun t ht =>
      Q'.eqv_of_eq (by congr 1 <;> omega)))
    (fsum_eqv_congr_lt _ _ b (fun t ht =>
      Q'.eqv_of_eq (by congr 1 <;> omega)))

/-- Odd length: a direct head plus the full odd low-diagonal suffix
`C(k+2,0,k)`. -/
theorem cumulativeResidual_one_zero_odd_split
    (W h : Q') (k : Nat) :
    cumulativeResidual W h 1 0 (2 * k + 1) ≈
      cumulativeResidual W h 1 k (k + 1) +
        cumulativeResidual W h (k + 2) 0 k := by
  have hs := cumulativeResidual_add_length W h 1 0 (k + 1) k
  rw [show k + 1 + k = 2 * k + 1 by omega,
    show 0 + k = k by omega,
    show 1 + (k + 1) = k + 2 by omega] at hs
  exact hs

/-- Even positive length: a direct head plus the full even low-diagonal
suffix `C(k+3,0,k)`. -/
theorem cumulativeResidual_one_zero_even_split
    (W h : Q') (k : Nat) :
    cumulativeResidual W h 1 0 (2 * (k + 1)) ≈
      cumulativeResidual W h 1 k (k + 2) +
        cumulativeResidual W h (k + 3) 0 k := by
  have hs := cumulativeResidual_add_length W h 1 0 (k + 2) k
  rw [show k + 2 + k = 2 * (k + 1) by omega,
    show 0 + k = k by omega,
    show 1 + (k + 2) = k + 3 by omega] at hs
  exact hs

/-- Quotient-level odd head/full-suffix splice. -/
theorem diagonalCumulativeSquareGapQuotient_one_zero_odd_split
    (W h : Q') (k : Nat) :
    diagonalCumulativeSquareGapQuotient W h 1 0 (2 * k + 1) ≈
      diagonalCumulativeSquareGapQuotient W h 1 k (k + 1) +
        diagonalCumulativeSquareGapQuotient W h (k + 2) 0 k := by
  have hs := diagonalCumulativeSquareGapQuotient_add_length
    W h 1 0 (k + 1) k
  rw [show k + 1 + k = 2 * k + 1 by omega,
    show 0 + k = k by omega,
    show 1 + (k + 1) = k + 2 by omega] at hs
  exact hs

/-- Quotient-level even head/full-suffix splice. -/
theorem diagonalCumulativeSquareGapQuotient_one_zero_even_split
    (W h : Q') (k : Nat) :
    diagonalCumulativeSquareGapQuotient W h 1 0 (2 * (k + 1)) ≈
      diagonalCumulativeSquareGapQuotient W h 1 k (k + 2) +
        diagonalCumulativeSquareGapQuotient W h (k + 3) 0 k := by
  have hs := diagonalCumulativeSquareGapQuotient_add_length
    W h 1 0 (k + 2) k
  rw [show k + 2 + k = 2 * (k + 1) by omega,
    show 0 + k = k by omega,
    show 1 + (k + 2) = k + 3 by omega] at hs
  exact hs

#print axioms originCumulativeOfRowOneEndpoint
#print axioms offsetDelta_zeroOffset_nonneg_of_origin_cumulative
#print axioms crossRatioMonotoneOfOriginCumulative
#print axioms crossRatioMonotoneOfRowOneOrigin
#print axioms rowOneOriginCumulativeOfSquareGapQuotient
#print axioms rowOneOriginSquareGapQuotientNonnegativeOfPayments
#print axioms crossRatioMonotoneOfRowOneOriginSquareGapQuotient
#print axioms cumulativeResidual_add_length
#print axioms diagonalCumulativeSquareGapQuotient_add_length
#print axioms cumulativeResidual_one_zero_odd_split
#print axioms cumulativeResidual_one_zero_even_split
#print axioms diagonalCumulativeSquareGapQuotient_one_zero_odd_split
#print axioms diagonalCumulativeSquareGapQuotient_one_zero_even_split

end YMGap.Continuum.CoreBConsumerOrigin
