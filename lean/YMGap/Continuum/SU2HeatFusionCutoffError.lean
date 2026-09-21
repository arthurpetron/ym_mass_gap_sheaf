/-
# Explicit SU(2) heat-fusion cutoff error

The upper endpoint left by a finite adjacent-label fusion sum is retained as
the literal scalar

  `coeffW w (K+1) * dimQ K`.

It is nonnegative for nonnegative nome.  For every rational `0<w<1`, the
existing all-nome squared-dimension majorant and its computable tail cutoff
make this endpoint at most any supplied positive tolerance.  The error is not
discarded or identified with zero; consumers must carry it until applying the
explicit cutoff theorem below.

This is a scalar truncation estimate, not a heat-order theorem, a spectral
gap, or a continuum statement.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeTailInterval

namespace YMGap.Continuum.SU2HeatFusionCutoffError

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatMajorant)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval

local infix:50 " ≈ " => Q'.eqv

/-- The literal unmatched upper endpoint in a fusion sum cut off at `K`. -/
def cutoffError (w : Q') (K : Nat) : Q' :=
  coeffW w (K + 1) * dimQ K

/-- The endpoint has exactly the dimension-weighted rate
`(K+2)(K+1) w^((K+1)(K+3))`, with `qpow` the repository's heat power. -/
theorem cutoffError_exact (w : Q') (K : Nat) :
    cutoffError w K ≈
      (Q'.ofNat (K + 2) * Q'.ofNat (K + 1)) *
        qpow w ((K + 1) * (K + 3)) := by
  unfold cutoffError coeffW dimQ c4
  exact RingNormaliser.poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 2)) (.var 1))
    (.mul (.mul (.var 0) (.var 1)) (.var 2))
    (by decide)
    (fun | 0 => Q'.ofNat (K + 2)
         | 1 => Q'.ofNat (K + 1)
         | _ => qpow w ((K + 1) * (K + 3)))

theorem cutoffError_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') ≤ cutoffError w K :=
  Q'.mul_nonneg _ _ (coeffW_nonneg hw (K + 1)) (dimQ_nonneg K)

/-- The literal crossed endpoint is no larger than the existing
squared-dimension pointwise heat majorant at the same upper label. -/
theorem cutoffError_le_majorant {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) :
    cutoffError w K ≤ pointwiseHeatMajorant w (K + 1) := by
  have hdim : dimQ K ≤ dimQ (K + 1) := by
    unfold dimQ
    exact CReal.ofNat_le_ofNat (by omega)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hdim (coeffW_nonneg hw (K + 1)))
    (Q'.le_of_eqv (heat_dimension_majorant w (K + 1)))

/-- A public computable threshold for the literal fusion endpoint. -/
def cutoffErrorCutoff (w epsilon : Q') : Nat := tailCutoff w epsilon

/-- Every later cutoff makes the explicit endpoint no larger than the supplied
positive tolerance.  This uses the existing all-nome tail rather than assuming
the endpoint negligible. -/
theorem cutoffError_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (K : Nat)
    (hK : cutoffErrorCutoff w epsilon ≤ K) : cutoffError w K ≤ epsilon := by
  have hcut : tailCutoff w epsilon ≤ K := hK
  have hN : spacingLabelCutoff w ≤ K + 1 := by
    unfold tailCutoff at hcut
    omega
  have hM : spacingTailCauchyCutoff w epsilon ≤
      K + 1 - spacingLabelCutoff w := by
    unfold tailCutoff at hcut
    omega
  have hblock := shiftedMajorant_block hw0 hw1
    (K + 1 - spacingLabelCutoff w) 1
  have hmajorant : pointwiseHeatMajorant w (K + 1) ≤
      spacingClosedTail w (K + 1 - spacingLabelCutoff w) := by
    simpa only [finSum, Nat.add_zero, Q'.zero_add', ← Nat.add_assoc,
      Nat.add_sub_of_le hN] using hblock
  exact Q'.le_trans' _ _ _
    (cutoffError_le_majorant (Q'.le_of_lt hw0) K)
    (Q'.le_trans' _ _ _ hmajorant
      (closedTail_small hw0 hw1 epsilon he _ hM))

end YMGap.Continuum.SU2HeatFusionCutoffError

#print axioms YMGap.Continuum.SU2HeatFusionCutoffError.cutoffError
#print axioms YMGap.Continuum.SU2HeatFusionCutoffError.cutoffError_exact
#print axioms YMGap.Continuum.SU2HeatFusionCutoffError.cutoffError_nonnegative
#print axioms YMGap.Continuum.SU2HeatFusionCutoffError.cutoffError_le_majorant
#print axioms YMGap.Continuum.SU2HeatFusionCutoffError.cutoffErrorCutoff
#print axioms YMGap.Continuum.SU2HeatFusionCutoffError.cutoffError_small
