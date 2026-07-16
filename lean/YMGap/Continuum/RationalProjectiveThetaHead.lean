/-
Rational projective clearing of the variable theta head.

For an arbitrary rational coupling `0 <= w < 1`, put

  `den = 1/(1-w)`, `x = w/(1-w)`, `t = x.num.toNat`.

The rational projective corridor proves the Pascal deficit at the computable
anchor `m = 2t+4`.  Clearing the strictly positive projective denominator and
using the exact coefficient-evaluation identity produces the physical theta
head residual at `b = m-2 = 2t+2`.  No density, limit, or measured constant
enters the construction.
-/

import YMGap.Continuum.HarmonicThetaPascalEvaluation
import YMGap.Continuum.HarmonicVariableAnchorThetaBridge
import YMGap.Continuum.RationalProjectiveThetaCorridor

namespace YMGap.Continuum.RationalProjectiveThetaHead

set_option maxHeartbeats 4000000
set_option maxRecDepth 50000

open YMGap.Constructive
open YMGap.Constructive.RatNat
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaPascalBridge
open YMGap.Continuum.HarmonicThetaPascalEvaluation
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicVariableAnchorThetaBridge
open YMGap.Continuum.RationalProjectiveThetaCorridor

local infix:50 " ≈ " => Q'.eqv

/-- Positive common projective denominator `1/(1-w)`. -/
def rationalProjectiveDen (w : Q') (hu : (0 : Q') < (1 : Q') - w) : Q' :=
  Q'.divPos 1 ((1 : Q') - w) hu

/-- Projective coordinate `x=w/(1-w)`. -/
def rationalProjectiveCoord (w : Q')
    (hu : (0 : Q') < (1 : Q') - w) : Q' :=
  w * rationalProjectiveDen w hu

/-- Computable integer ceiling carrier for the projective coordinate. -/
def rationalProjectiveIndex (w : Q')
    (hu : (0 : Q') < (1 : Q') - w) : Nat :=
  (rationalProjectiveCoord w hu).num.toNat

/-- Minimal-degree Pascal endpoint selected by the rational coordinate. -/
def rationalThetaEndpoint (w : Q')
    (hu : (0 : Q') < (1 : Q') - w) : Nat :=
  2 * rationalProjectiveIndex w hu + 4

/-- Retained diagonal head; the adjacent head has one additional edge. -/
def rationalThetaHead (w : Q')
    (hu : (0 : Q') < (1 : Q') - w) : Nat :=
  2 * rationalProjectiveIndex w hu + 2

theorem rationalProjectiveDen_pos (w : Q')
    (hu : (0 : Q') < (1 : Q') - w) :
    (0 : Q') < rationalProjectiveDen w hu := by
  unfold rationalProjectiveDen
  exact Q'.divPos_pos 1 ((1 : Q') - w) hu (by decide)

theorem rationalProjectiveCoord_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hu : (0 : Q') < (1 : Q') - w) :
    (0 : Q') ≤ rationalProjectiveCoord w hu := by
  unfold rationalProjectiveCoord
  exact Q'.mul_nonneg _ _ hw0
    (Q'.le_of_lt (rationalProjectiveDen_pos w hu))

theorem rationalProjectiveCoord_le_index {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hu : (0 : Q') < (1 : Q') - w) :
    rationalProjectiveCoord w hu ≤
      Q'.ofNat (rationalProjectiveIndex w hu) := by
  exact le_ofNat_toNat _ (rationalProjectiveCoord_nonneg hw0 hu)

theorem rationalProjective_clear_weight (w : Q')
    (hu : (0 : Q') < (1 : Q') - w) :
    w * rationalProjectiveDen w hu ≈ rationalProjectiveCoord w hu :=
  Q'.eqv_refl _

theorem rationalProjective_clear_complement (w : Q')
    (hu : (0 : Q') < (1 : Q') - w) :
    ((1 : Q') - w) * rationalProjectiveDen w hu ≈ (1 : Q') := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
  unfold rationalProjectiveDen
  exact Q'.divPos_mul_eqv 1 ((1 : Q') - w) hu

private theorem pow_pos (q : Q') (hq : (0 : Q') < q) : ∀ n : Nat,
    (0 : Q') < q ^ n
  | 0 => by
      change (0 : Q') < 1
      decide
  | n + 1 => by
      rw [Q'.pow_succ]
      exact Q'.mul_pos hq (pow_pos q hq n)

theorem rationalThetaEndpoint_sub_two (w : Q')
    (hu : (0 : Q') < (1 : Q') - w) :
    rationalThetaEndpoint w hu - 2 = rationalThetaHead w hu := by
  unfold rationalThetaEndpoint rationalThetaHead
  omega

/-- The exact growing-head residual is nonnegative at the computable
rational projective anchor. -/
theorem rational_theta_head_residual_nonnegative {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    (0 : Q') ≤ growingHeadScaledThetaResidual w
      (rationalThetaHead w hu) := by
  let x := rationalProjectiveCoord w hu
  let t := rationalProjectiveIndex w hu
  let m := rationalThetaEndpoint w hu
  let D := 2 * m * m + 1
  let den := rationalProjectiveDen w hu
  have hm : 2 ≤ m := by
    dsimp [m, rationalThetaEndpoint]
    omega
  have hx0 : (0 : Q') ≤ x := rationalProjectiveCoord_nonneg hw0 hu
  have hxt : x ≤ Q'.ofNat t := rationalProjectiveCoord_le_index hw0 hu
  have hprojective : (0 : Q') ≤ projectiveDeficitEval D
      (growingHeadThetaBernCoeff D m) x := by
    dsimp [D, m, t]
    exact growing_head_projective_deficit_nonnegative_below_nat
      (rationalProjectiveIndex w hu) hx0 hxt
  have hclear := signedBernsteinEval_mul_den_pow_eqv_projectiveDeficitEval
    D (growingHeadThetaBernCoeff D m) w den x
      (by
        dsimp [den, x]
        exact rationalProjective_clear_weight w hu)
      (by
        dsimp [den]
        exact rationalProjective_clear_complement w hu)
  have hscaled : (0 : Q') ≤
      signedBernsteinEval D (growingHeadThetaBernCoeff D m) w * den ^ D :=
    Q'.le_trans' _ _ _ hprojective (Q'.ge_of_eqv hclear)
  have hcomm : den ^ D *
        signedBernsteinEval D (growingHeadThetaBernCoeff D m) w ≈
      signedBernsteinEval D (growingHeadThetaBernCoeff D m) w * den ^ D :=
    Q'.mul_comm_eqv _ _
  have hleft : (0 : Q') ≤ den ^ D *
      signedBernsteinEval D (growingHeadThetaBernCoeff D m) w :=
    Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hcomm)
  have hmul : den ^ D * (0 : Q') ≤ den ^ D *
      signedBernsteinEval D (growingHeadThetaBernCoeff D m) w :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (den ^ D))) hleft
  have hden : (0 : Q') < den ^ D :=
    pow_pos den (rationalProjectiveDen_pos w hu) D
  have hsigned : (0 : Q') ≤
      signedBernsteinEval D (growingHeadThetaBernCoeff D m) w :=
    Q'.le_of_mul_le_mul_left hmul hden
  have hscaledEval : (0 : Q') ≤ w ^ 2 *
      signedBernsteinEval D (growingHeadThetaBernCoeff D m) w :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg w hw0 2) hsigned
  have heval := growingHeadThetaBernCoeff_scaled_eval_eqv_residual m w hm
  have hres : (0 : Q') ≤ growingHeadScaledThetaResidual w (m - 2) :=
    Q'.le_trans' _ _ _ hscaledEval (Q'.le_of_eqv heval)
  have hidx : m - 2 = rationalThetaHead w hu := by
    dsimp [m]
    exact rationalThetaEndpoint_sub_two w hu
  rw [hidx] at hres
  exact hres

/-- Exact integer/half-integer theta comparison at the rational anchor. -/
theorem rational_theta_head_premise {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    w * halfThetaSum w (rationalThetaHead w hu + 1) ≤
      retuneCube w * integerThetaSum w (rationalThetaHead w hu) :=
  growing_head_theta_premise_of_residual_nonnegative
    (rationalThetaHead w hu) (rational_theta_head_residual_nonnegative hw0 hu)

/-- Physical adjacent/diagonal head inequality supplied by the rational
theta certificate. -/
theorem rational_retained_head {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwp : (0 : Q') < w)
    (hu : (0 : Q') < (1 : Q') - w) :
    adjCorr w (rationalThetaHead w hu + 1) ≤
      retuneCube w * coordNormSq w (rationalThetaHead w hu) :=
  theta_head_comparison_implies_retained_head hwp
    (rationalThetaHead w hu) (rational_theta_head_premise hw0 hu)

end YMGap.Continuum.RationalProjectiveThetaHead

#print axioms YMGap.Continuum.RationalProjectiveThetaHead.rationalProjectiveDen_pos
#print axioms YMGap.Continuum.RationalProjectiveThetaHead.rationalProjectiveCoord_le_index
#print axioms YMGap.Continuum.RationalProjectiveThetaHead.rational_theta_head_residual_nonnegative
#print axioms YMGap.Continuum.RationalProjectiveThetaHead.rational_theta_head_premise
#print axioms YMGap.Continuum.RationalProjectiveThetaHead.rational_retained_head
