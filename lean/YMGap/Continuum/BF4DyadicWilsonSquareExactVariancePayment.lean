/-
# Exact heat payment for the ACTUAL long Wilson square

Use the exact heat images, not a Taylor truncation. The negative square
coefficient pays SAME endpoint OWN variance; the ENTIRE nonnegative
source increment stays on the left. There is no cubic or omitted-mode
error in this alternative. Actual channel mass still needs useful control
against the surviving chronological norm on a justified scaling family.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceCredit
import YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse
import YMGap.Continuum.SU2HeatExactSquareCreditWindow
import YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss

namespace YMGap.Continuum.BF4DyadicWilsonSquareExactVariancePayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
  (squareChannelMass squareChannelMoment)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse
  (responseQuarter squareChannelIncrement exactChannelHeatCost
    paddedSquare_energy_exactChannel_increment)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceCredit
  (paddedSquare_channelMoment_oddVariance_credit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit
  (channelObservableSquareLinearVarianceCredit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2HeatExactSquareCreditWindow (exactSquareCredit)

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] terminalMessage sourceCharacter oddMass oddVariance
  normalizedEnergy squareChannelMass squareChannelMoment squareChannelIncrement
  exactChannelHeatCost channelObservableSquareLinearVarianceCredit

/-- Exact original heat pays OWN variance AFTER keeping the complete signed
coefficient. No Taylor or cutoff error budget is used. The explicit scalar
guard has a proved numeric window; it is not an assumed analytic estimate.
Only SAME positive original partition and positive local-band scalar are
inverted, never an excitation/source norm. -/
theorem paddedSquare_energy_exact_variance_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (h2 : 2 ≤ K) (n scale : Nat)
    (hwidth : side scale < width)
    (hcoefficient : (0 : Q') ≤ exactSquareCredit w (side scale)) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let g := terminalMessage w K width (n+1)
    let r := Q'.recipPos (oddMass w K width (n+1))
      (oddMass_positive hw0 hw1 K width hK (n+1))
    normalizedEnergy hw0 hw1 K width hK (n+1) f +
        responseQuarter*(squareChannelIncrement w K scale width hwidth (n+1)*r) +
        (HalfPow.half*exactSquareCredit w (side scale)*
          channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale))*
          oddVariance hw0 hw1 K width hK (n+1) f ≤
      HalfPow.half*(((1 : Q')-qpow w (32*side scale))*
        squareChannelMass w K scale width hwidth g*r) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let g := terminalMessage w K width (n+1)
  let Z := oddMass w K width (n+1)
  have hZ : (0 : Q') < Z := oddMass_positive hw0 hw1 K width hK (n+1)
  let r := Q'.recipPos Z hZ
  let V := oddVariance hw0 hw1 K width hK (n+1) f
  let E := normalizedEnergy hw0 hw1 K width hK (n+1) f
  let M := squareChannelMass w K scale width hwidth g
  let Q := squareChannelMoment w K scale width hwidth g
  let I := squareChannelIncrement w K scale width hwidth (n+1)
  let B := exactChannelHeatCost w K scale width hwidth (n+1)
  let rho := channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale)
  let k := exactSquareCredit w (side scale)
  let a := qpow w (12*side scale)
  let b := qpow w (32*side scale)
  let c := HalfPow.half*k
  have hc : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide) hcoefficient
  have hidentity : E ≈ HalfPow.half*(B*r)-responseQuarter*(I*r) :=
    paddedSquare_energy_exactChannel_increment hw0 hw1 K width hK h2 (n+1) scale hwidth
  have henergy : E+responseQuarter*(I*r) ≈ HalfPow.half*(B*r) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hidentity)
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
        (by decide) (fun | 0 => HalfPow.half*(B*r) | _ => responseQuarter*(I*r)))
  have hcredit := Q'.mul_le_mul_of_nonneg_left _ _ c
    (paddedSquare_channelMoment_oddVariance_credit hw0 hw1 K hK scale width hwidth n) hc
  have hnorm := Q'.mul_le_mul_of_nonneg_right _ _ r hcredit
    (Q'.le_of_lt (Q'.recipPos_pos Z hZ))
  have hpay : (c*rho)*V ≤ (c*Q)*r := by
    have hp : (c*(rho*(Z*V)))*r ≈ ((c*rho)*V)*(Z*r) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.var 4))
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.var 2) (.var 4)))
        (by decide) (fun | 0 => c | 1 => rho | 2 => Z | 3 => V | _ => r)
    have hcancel := Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv _))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel) hnorm
  have hcombine : HalfPow.half*(B*r)+(c*Q)*r ≈
      HalfPow.half*((1-b)*M*r) := by
    dsimp only [B, exactChannelHeatCost, c, k, exactSquareCredit, a, b, M, Q, g]
    unfold exactChannelHeatCost
    dsimp only
    exact poly_identity_of_normal_eq
      (.add
        (.mul (.var 0) (.mul
          (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 3))
            (.mul (.add (.add (.const 1) (.var 2))
              (.neg (.mul (.const 2) (.var 1)))) (.var 4))) (.var 5)))
        (.mul (.mul (.mul (.var 0)
          (.add (.add (.mul (.const 2) (.var 1)) (.neg (.const 1)))
            (.neg (.var 2)))) (.var 4)) (.var 5)))
      (.mul (.var 0) (.mul
        (.mul (.add (.const 1) (.neg (.var 2))) (.var 3)) (.var 5)))
      (by decide) (fun
        | 0 => HalfPow.half
        | 1 => qpow w (12*side scale)
        | 2 => qpow w (32*side scale)
        | 3 => M
        | 4 => Q
        | _ => r)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.le_of_eqv henergy) hpay) (Q'.le_of_eqv hcombine)

/-- Rho-free exact heat payment from the ACTUAL source-loss comparison.
The coefficient k/4 does not use absolute source bands; its price is the
computed additive loss k*(M-Z)/(4Z). The ENTIRE source increment remains,
and no useful relative-loss or physical scaling estimate is assumed. -/
theorem paddedSquare_energy_exact_loss_variance_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (h2 : 2 ≤ K) (depth scale : Nat)
    (hwidth : side scale < width)
    (hcoefficient : (0 : Q') ≤ exactSquareCredit w (side scale)) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let g := terminalMessage w K width depth
    let r := Q'.recipPos (oddMass w K width depth)
      (oddMass_positive hw0 hw1 K width hK depth)
    let L := YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss.channelHeatLoss
      w K width depth scale hwidth
    normalizedEnergy hw0 hw1 K width hK depth f +
        responseQuarter*(squareChannelIncrement w K scale width hwidth depth*r) +
        (responseQuarter*exactSquareCredit w (side scale))*
          oddVariance hw0 hw1 K width hK depth f ≤
      HalfPow.half*(((1 : Q')-qpow w (32*side scale))*
        squareChannelMass w K scale width hwidth g*r) +
        (responseQuarter*exactSquareCredit w (side scale))*(L*r) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let g := terminalMessage w K width depth
  let Z := oddMass w K width depth
  have hZ : (0 : Q') < Z := oddMass_positive hw0 hw1 K width hK depth
  let r := Q'.recipPos Z hZ
  let V := oddVariance hw0 hw1 K width hK depth f
  let E := normalizedEnergy hw0 hw1 K width hK depth f
  let M := squareChannelMass w K scale width hwidth g
  let Q := squareChannelMoment w K scale width hwidth g
  let L := YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss.channelHeatLoss
    w K width depth scale hwidth
  let I := squareChannelIncrement w K scale width hwidth depth
  let B := exactChannelHeatCost w K scale width hwidth depth
  let k := exactSquareCredit w (side scale)
  let b := qpow w (32*side scale)
  let c := responseQuarter*k
  have hc : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide) hcoefficient
  have hidentity : E ≈ HalfPow.half*(B*r)-responseQuarter*(I*r) :=
    paddedSquare_energy_exactChannel_increment hw0 hw1 K width hK h2 depth scale hwidth
  have henergy : E+responseQuarter*(I*r) ≈ HalfPow.half*(B*r) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hidentity)
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
        (by decide) (fun | 0 => HalfPow.half*(B*r) | _ => responseQuarter*(I*r)))
  have hcredit := Q'.mul_le_mul_of_nonneg_left _ _ c
    (YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss.paddedSquare_oddVariance_le_twice_channelMoment_add_loss
      hw0 hw1 K width hK depth scale hwidth) hc
  have hnorm := Q'.mul_le_mul_of_nonneg_right _ _ r hcredit
    (Q'.le_of_lt (Q'.recipPos_pos Z hZ))
  have hpay : c*V ≤ ((HalfPow.half*k)*Q)*r+c*(L*r) := by
    have hp : (c*(Z*V))*r ≈ (c*V)*(Z*r) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
        (by decide) (fun | 0 => c | 1 => Z | 2 => V | _ => r)
    have hcancel := Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv _))
    have hdouble : 2*c ≈ HalfPow.half*k :=
      Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.mul (.const 2) (.mul (.var 0) (.var 1)))
          (.mul (.mul (.const 2) (.var 0)) (.var 1))
          (by decide) (fun | 0 => responseQuarter | _ => k))
        (Q'.mul_eqv_congr_right _ _ k (by decide : 2*responseQuarter ≈ HalfPow.half))
    have hshape : (c*(2*Q+L))*r ≈ ((2*c)*Q)*r+c*(L*r) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.add (.mul (.const 2) (.var 1)) (.var 2))) (.var 3))
        (.add (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3))
          (.mul (.var 0) (.mul (.var 2) (.var 3))))
        (by decide) (fun | 0 => c | 1 => Q | 2 => L | _ => r)
    have hright : (c*(2*Q+L))*r ≈ ((HalfPow.half*k)*Q)*r+c*(L*r) :=
      Q'.eqv_trans _ _ _ hshape (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ r (Q'.mul_eqv_congr_right _ _ Q hdouble)))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
      (Q'.le_trans' _ _ _ hnorm (Q'.le_of_eqv hright))
  have hcombine : HalfPow.half*(B*r)+((HalfPow.half*k)*Q)*r ≈
      HalfPow.half*((1-b)*M*r) := by
    dsimp only [B, exactChannelHeatCost, k, exactSquareCredit, b, M, Q, g]
    unfold exactChannelHeatCost
    dsimp only
    exact poly_identity_of_normal_eq
      (.add
        (.mul (.var 0) (.mul
          (.add (.mul (.add (.const 1) (.neg (.var 2))) (.var 3))
            (.mul (.add (.add (.const 1) (.var 2))
              (.neg (.mul (.const 2) (.var 1)))) (.var 4))) (.var 5)))
        (.mul (.mul (.mul (.var 0)
          (.add (.add (.mul (.const 2) (.var 1)) (.neg (.const 1)))
            (.neg (.var 2)))) (.var 4)) (.var 5)))
      (.mul (.var 0) (.mul
        (.mul (.add (.const 1) (.neg (.var 2))) (.var 3)) (.var 5)))
      (by decide) (fun
        | 0 => HalfPow.half
        | 1 => qpow w (12*side scale)
        | 2 => qpow w (32*side scale)
        | 3 => M
        | 4 => Q
        | _ => r)
  have hright : HalfPow.half*(B*r)+(((HalfPow.half*k)*Q)*r+c*(L*r)) ≈
      HalfPow.half*((1-b)*M*r)+c*(L*r) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _).symm
      (Q'.add_eqv_congr_right _ _ _ hcombine)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.le_of_eqv henergy) hpay) (Q'.le_of_eqv hright)

#print axioms paddedSquare_energy_exact_loss_variance_payment
#print axioms paddedSquare_energy_exact_variance_payment

end YMGap.Continuum.BF4DyadicWilsonSquareExactVariancePayment
