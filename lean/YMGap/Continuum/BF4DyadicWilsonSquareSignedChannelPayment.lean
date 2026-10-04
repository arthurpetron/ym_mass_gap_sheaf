/-
# Joint signed-channel payment on the ACTUAL long Wilson square

Combine the first-order angular moment, signed curvature and literal
Casimir square BEFORE estimating the observable moment. The coefficient
of that moment is nonpositive precisely when alpha is nonnegative. In that
numeric window the actual local-band credit pays SAME OWN odd variance.
The complete original active Sobolev/omitted-mode error and channel mass
remain; no useful comparison with the filtered starting norm is claimed.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceCredit
import YMGap.Continuum.BF4DyadicWilsonSquareChannelMomentBalance

namespace YMGap.Continuum.BF4DyadicWilsonSquareSignedChannelPayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare (side side_positive paddedSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareCasimirCurvature (perimeter)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
  (squareChannelMass squareChannelMoment)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelMomentBalance
  (paddedSquare_energy_exact_channel_moment_bound signedChannelMomentBalance)
open YMGap.Continuum.BF4DyadicWilsonSquareActiveChannelSobolev
  (activeChannelSobolevBudget)
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

local infix:50 " ≈ " => Q'.eqv

/-- The coefficient of the negative raw square moment AFTER combining all
first- and second-order channel terms. It may be negative outside the window. -/
def signedSquareCoefficient (w : Q') (scale : Nat) : Q' :=
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let P := perimeter scale
  (h+t)*P-5*(t*(P*P))

/-- The SAME channel-mass coefficient in the joint signed combination. -/
def signedMassCoefficient (w : Q') (scale : Nat) : Q' :=
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let P := perimeter scale
  4*((h+t)*P)-8*(t*(P*P))

private theorem perimeter_positive (scale : Nat) : (0 : Q') < perimeter scale := by
  exact Q'.mul_pos (by decide) (by
    apply CReal.pos_of_num_pos
    change (0 : Int) < (side scale : Int)
    exact Int.ofNat_lt.mpr (side_positive scale))

/-- A concrete heat/perimeter window pays at least t*P. This is scalar
arithmetic, not an assumed analytic dominance or physical scaling law. -/
theorem signedSquareCoefficient_ge_quadratic_window {w : Q'}
    (hw1 : w < (1 : Q')) (scale : Nat)
    (hwindow : ((1 : Q')-w)*perimeter scale ≤ Q'.mkPos 2 5 (by decide)) :
    HalfPow.half*(((1 : Q')-w)*((1 : Q')-w))*perimeter scale ≤
      signedSquareCoefficient w scale := by
  let h := (1 : Q')-w
  let P := perimeter scale
  let t := HalfPow.half*(h*h)
  let x := h*P
  have hx0 : (0 : Q') ≤ x := Q'.le_of_lt
    (Q'.mul_pos (HKPos.one_sub_pos hw1) (perimeter_positive scale))
  have hc : (5*HalfPow.half)*x ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (5*HalfPow.half) hwindow (by decide))
    (by decide)
  have hmul : x*((5*HalfPow.half)*x) ≤ x := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ x hc hx0)
    (Q'.le_of_eqv (Q'.mul_one_eqv x))
  have hpin : 5*(t*(P*P)) ≈ x*((5*HalfPow.half)*x) :=
    poly_identity_of_normal_eq
      (.mul (.const 5) (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.var 2) (.var 2))))
      (.mul (.mul (.var 1) (.var 2))
        (.mul (.mul (.const 5) (.var 0)) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => HalfPow.half | 1 => h | _ => P)
  have hd : (0 : Q') ≤ x-5*(t*(P*P)) :=
    Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) hmul)
  have hshape : t*P+(x-5*(t*(P*P))) ≈ signedSquareCoefficient w scale :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 1) (.var 2))
        (.add (.mul (.var 0) (.var 2))
          (.neg (.mul (.const 5) (.mul (.var 1) (.mul (.var 2) (.var 2)))))))
      (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.neg (.mul (.const 5) (.mul (.var 1) (.mul (.var 2) (.var 2))))))
      (by decide) (fun | 0 => h | 1 => t | _ => P)
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hd) (Q'.le_of_eqv hshape)

theorem signedSquareCoefficient_positive_window {w : Q'}
    (hw1 : w < (1 : Q')) (scale : Nat)
    (hwindow : ((1 : Q')-w)*perimeter scale ≤ Q'.mkPos 2 5 (by decide)) :
    (0 : Q') < signedSquareCoefficient w scale :=
  Q'.pos_of_lt_of_le
    (Q'.mul_pos (Q'.mul_pos (by decide)
      (Q'.mul_pos (HKPos.one_sub_pos hw1) (HKPos.one_sub_pos hw1)))
      (perimeter_positive scale))
    (signedSquareCoefficient_ge_quadratic_window hw1 scale hwindow)

private theorem combined_moments (a b M Q err : Q') :
    a*(4*M-Q)+b*(5*Q-8*M)+err ≈
      (4*a-8*b)*M-(a-5*b)*Q+err :=
  poly_identity_of_normal_eq
    (.add
      (.add (.mul (.var 0) (.add (.mul (.const 4) (.var 2)) (.neg (.var 3))))
        (.mul (.var 1) (.add (.mul (.const 5) (.var 3))
          (.neg (.mul (.const 8) (.var 2)))))) (.var 4))
    (.add
      (.add (.mul (.add (.mul (.const 4) (.var 0))
          (.neg (.mul (.const 8) (.var 1)))) (.var 2))
        (.neg (.mul (.add (.var 0) (.neg (.mul (.const 5) (.var 1)))) (.var 3))))
      (.var 4))
    (by decide) (fun | 0 => a | 1 => b | 2 => M | 3 => Q | _ => err)

attribute [local irreducible] terminalMessage sourceCharacter oddMass oddVariance
  normalizedEnergy squareChannelMass squareChannelMoment activeChannelSobolevBudget
  channelObservableSquareLinearVarianceCredit

/-- Pay SAME OWN variance only AFTER the complete signed channel combination
has been formed. The guard is the sign of an explicit scalar, not a new
analytic field. Original channel mass and ENTIRE active error remain unpaid. -/
theorem paddedSquare_energy_full_signed_variance_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (n scale : Nat) (hwidth : side scale < width)
    (hcoefficient : (0 : Q') ≤ signedSquareCoefficient w scale) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let g := terminalMessage w K width (n+1)
    normalizedEnergy hw0 hw1 K width hK (n+1) f +
      (signedSquareCoefficient w scale *
        channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale)) *
        oddVariance hw0 hw1 K width hK (n+1) f ≤
      (signedMassCoefficient w scale * squareChannelMass w K scale width hwidth g +
        activeChannelSobolevBudget hw0 hw1 K width hK (n+1) scale hwidth) *
        Q'.recipPos (oddMass w K width (n+1))
          (oddMass_positive hw0 hw1 K width hK (n+1)) := by
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
  let err := activeChannelSobolevBudget hw0 hw1 K width hK (n+1) scale hwidth
  let rho := channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale)
  let alpha := signedSquareCoefficient w scale
  let beta := signedMassCoefficient w scale
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let P := perimeter scale
  let a := (h+t)*P
  let b := t*(P*P)
  have hbase := paddedSquare_energy_exact_channel_moment_bound
    hw0 hw1 K width hK (n+1) scale hwidth
  change E ≤ (a*(4*M-Q)+t*((P*P)*(5*Q-8*M))+err)*r at hbase
  have hshape : a*(4*M-Q)+t*((P*P)*(5*Q-8*M))+err ≈ beta*M-alpha*Q+err :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ err (Q'.add_eqv_congr_left _ _ _
        (Q'.mul_assoc_eqv t (P*P) (5*Q-8*M)).symm))
      (combined_moments a b M Q err)
  have he : E ≤ (beta*M-alpha*Q+err)*r :=
    Q'.le_trans' _ _ _ hbase
      (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ r hshape))
  have hcredit := Q'.mul_le_mul_of_nonneg_left _ _ alpha
    (paddedSquare_channelMoment_oddVariance_credit hw0 hw1 K hK scale width hwidth n)
    hcoefficient
  have hnorm := Q'.mul_le_mul_of_nonneg_right _ _ r hcredit
    (Q'.le_of_lt (Q'.recipPos_pos Z hZ))
  have hpay : (alpha* rho)*V ≤ (alpha*Q)*r := by
    have hp : (alpha*(rho*(Z*V)))*r ≈ ((alpha*rho)*V)*(Z*r) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3)))) (.var 4))
        (.mul (.mul (.mul (.var 0) (.var 1)) (.var 3)) (.mul (.var 2) (.var 4)))
        (by decide) (fun | 0 => alpha | 1 => rho | 2 => Z | 3 => V | _ => r)
    have hc := Q'.eqv_trans _ _ _ hp
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv _))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc) hnorm
  have hcancel : (beta*M-alpha*Q+err)*r+(alpha*Q)*r ≈ (beta*M+err)*r :=
    poly_identity_of_normal_eq
      (.add (.mul (.add (.add (.var 0) (.neg (.var 1))) (.var 2)) (.var 3))
        (.mul (.var 1) (.var 3)))
      (.mul (.add (.var 0) (.var 2)) (.var 3))
      (by decide) (fun | 0 => beta*M | 1 => alpha*Q | 2 => err | _ => r)
  exact Q'.le_trans' _ _ _ (Q'.add_le_add he hpay) (Q'.le_of_eqv hcancel)

#print axioms signedSquareCoefficient
#print axioms signedMassCoefficient
#print axioms signedSquareCoefficient_ge_quadratic_window
#print axioms signedSquareCoefficient_positive_window
#print axioms paddedSquare_energy_full_signed_variance_payment

end YMGap.Continuum.BF4DyadicWilsonSquareSignedChannelPayment
