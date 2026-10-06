/-
# Observed-loss circularity guard for the exact companion energy pin

Substituting the exact cap-deficit split `D = I + 4*O`
(`squareChannelCapDeficit_eq_increment_observedLoss_pin`) into the exact
energy/companion identity (`paddedSquare_energy_companion_capDeficit_pin`)
cancels the whole increment and leaves

  (1+beta)(4E+I) = 4(a(1-beta)-4k)M + 4k(4Z-U) + (k/2)(4*O).

Thus the observed loss `O` enters the endpoint energy identity linearly with
coefficient `2k`: any upper bound on `O` is literally an upper bound on the
endpoint energy `E` and conversely. Observed-loss/Ward payments are therefore
identity-only consumers; they supply NO new cost-versus-variance estimate.
This is a kernel-checked guard, not an estimate.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit

namespace YMGap.Continuum.BF4DyadicWilsonSquareObservedLossCircularity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels (channelSum)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatMomentDefect (heatLossPair)
open YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_add)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
open YMGap.Continuum.BF4DyadicWilsonSquareQuadraticHeat (paddedSquare_square_moment)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse
open YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss
open YMGap.Continuum.SU2HeatExactSquareCreditWindow (exactSquareCredit)
open YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit

local infix:50 " ≈ " => Q'.eqv

/-- Cancelling a common `c*I` against a decomposition `D ≈ I + O4`. -/
theorem cancel_increment_guard (L0 P c I D O4 : Q')
    (hE : L0 + c*I ≈ P + c*D) (hD : D ≈ I + O4) :
    L0 ≈ P + c*O4 := by
  let ρ : Nat → Q' := fun
    | 0 => L0 | 1 => P | 2 => c | 3 => I | 4 => D | _ => O4
  have p1 : L0 ≈ (L0 + c*I) + -(c*I) :=
    poly_identity_of_normal_eq (.var 0)
      (.add (.add (.var 0) (.mul (.var 2) (.var 3))) (.neg (.mul (.var 2) (.var 3))))
      (by decide) ρ
  have p2 : (P + c*(I+O4)) + -(c*I) ≈ P + c*O4 :=
    poly_identity_of_normal_eq
      (.add (.add (.var 1) (.mul (.var 2) (.add (.var 3) (.var 5)))) (.neg (.mul (.var 2) (.var 3))))
      (.add (.var 1) (.mul (.var 2) (.var 5)))
      (by decide) ρ
  have s1 : (L0 + c*I) + -(c*I) ≈ (P + c*D) + -(c*I) :=
    Q'.add_eqv_congr_right _ _ _ hE
  have s2 : (P + c*D) + -(c*I) ≈ (P + c*(I+O4)) + -(c*I) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left P _ _ (Q'.mul_eqv_congr_left c _ _ hD))
  exact Q'.eqv_trans _ _ _ p1 (Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s2 p2))

/-- On the actual objects: the observed-loss form IS the exact energy
identity with the increment cancelled. -/
theorem observedLoss_energy_identity {w : Q'}
    (K width : Nat) (h2 : 2 ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let beta := qpow w (32*side scale)
    let k := exactSquareCredit w (side scale)
    let I := squareChannelIncrement w K scale width hwidth depth
    let U := squareOriginalRawSecondMoment w K width depth scale hwidth
    let M := squareChannelMass w K scale width hwidth (terminalMessage w K width depth)
    let Z := oddMass w K width depth
    let O := squareChannelObservedLoss w K scale width hwidth depth
    (1+beta)*(4*energy w K width (terminalMessage w K width depth) f+I) ≈
      4*(a*(1-beta)-4*k)*M+4*k*(4*Z-U)+(HalfPow.half*k)*(4*O) := by
  intro f a beta k I U M Z O
  have hE := paddedSquare_energy_companion_capDeficit_pin (w := w) K width h2 depth scale hwidth
  have hD := squareChannelCapDeficit_eq_increment_observedLoss_pin w K width depth scale hwidth
  exact cancel_increment_guard _ _ _ _ _ _ hE hD

#print axioms cancel_increment_guard
#print axioms observedLoss_energy_identity

end YMGap.Continuum.BF4DyadicWilsonSquareObservedLossCircularity
