/-
Finite-theta cross for the growing-anchor moving determinant.

This module starts from the exact last residual exported by
`HarmonicMovingDeterminantGrowingTail`.  No hypothesis is introduced: every
certificate below is an exact rational statement about the finite theta
heads.
-/

import YMGap.Continuum.HarmonicMovingDeterminantGrowingTail
import YMGap.Continuum.HarmonicThetaPascalClosure

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaCross

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMovingDeterminantAllTail
open YMGap.Continuum.HarmonicMovingDeterminantDirect
open YMGap.Continuum.HarmonicMovingDeterminantGrowingTail
open YMGap.Continuum.HarmonicMovingDeterminantRecurrence
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem thetaCross_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "theta_cross_ring" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.mkPos_num, Q'.mkPos_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Q'.neg_den, thetaCross_neg_num_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             try ac_rfl))

private def thetaDeficitDecompL : RingNormaliser.PolyExpr :=
  .mul (.const 8) (.add (.var 0) (.neg (.var 1)))

private def thetaDeficitDecompR : RingNormaliser.PolyExpr :=
  .add
    (.mul (.add (.const 8) (.neg (.var 2))) (.var 0))
    (.add (.mul (.var 2) (.var 0))
      (.neg (.mul (.const 8) (.var 1))))

private theorem thetaDeficitDecomp_normal :
    RingNormaliser.normalize thetaDeficitDecompL =
      RingNormaliser.normalize thetaDeficitDecompR := by
  decide

private theorem theta_deficit_decomp (I B F : Q') :
    Q'.ofNat 8 * (I + -B) ≈
      (Q'.ofNat 8 + -F) * I + (F * I + -(Q'.ofNat 8 * B)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    thetaDeficitDecompL thetaDeficitDecompR thetaDeficitDecomp_normal
    (fun
      | 0 => I
      | 1 => B
      | _ => F)
  simpa [thetaDeficitDecompL, thetaDeficitDecompR,
    RingNormaliser.eval] using h

/-! ## 1. Exact threshold audit -/

/-- The proposed finite-theta cross has a strict reserve already at the first
all-tail scale.  This is a kernel reduction of the derived rational sums, not
a floating-point or measured input. -/
theorem growing_theta_cross_k38 :
    (qpow (harmW 38) 2 * qpow (harmW 39) 2) *
        dyad (2 * (38 + 2) + 5) ≤ growingHeadThetaCore 38 := by
  unfold growingHeadThetaCore growingHeadThetaDeficit integerThetaSum
    halfThetaSum integerThetaTerm halfThetaTerm normalizedDemandCoeff
    normalizedSpacingGain movingCutoffScale harmonicSpacing shellDropFraction
    growingAnchor harmW harmU ReciprocalBernoulliUpper.oneSub unit Ncut
    finSum qpow
  decide

/-- A coarse rational reserve at the threshold, useful for any subsequent
cross-scale induction: the finite theta core is already at least two. -/
theorem two_le_growingHeadThetaCore_k38 :
    Q'.ofNat 2 ≤ growingHeadThetaCore 38 := by
  unfold growingHeadThetaCore growingHeadThetaDeficit integerThetaSum
    halfThetaSum integerThetaTerm halfThetaTerm normalizedDemandCoeff
    normalizedSpacingGain movingCutoffScale harmonicSpacing shellDropFraction
    growingAnchor harmW harmU ReciprocalBernoulliUpper.oneSub unit Ncut
    finSum qpow
  decide

/-- The adverse old-scale Pascal remainder fits inside eight inverse-square
integer-head units at the threshold.  This exact check determines the useful
uniform target for the residual-upper stage; the proposed sixteen-unit budget
is therefore not threshold-obstructed. -/
theorem old_pascal_residual_eight_budget_k38 :
    normalizedDemandCoeff 38 *
        growingHeadScaledThetaResidual (harmW 38) (growingAnchor 38) ≤
      Q'.ofNat 8 * (harmU 38 * harmU 38) *
        integerThetaSum (harmW 38) (growingAnchor 38) := by
  unfold growingHeadScaledThetaResidual integerThetaSum halfThetaSum
    integerThetaTerm halfThetaTerm normalizedDemandCoeff
    normalizedSpacingGain movingCutoffScale harmonicSpacing shellDropFraction
    growingAnchor harmW harmU ReciprocalBernoulliUpper.oneSub unit Ncut
    finSum qpow
  decide

/-- Sharp lower fence on any separated old-residual upper: one inverse-square
unit is already insufficient at the threshold. -/
theorem old_pascal_residual_one_budget_fails_k38 :
    ¬ (normalizedDemandCoeff 38 *
        growingHeadScaledThetaResidual (harmW 38) (growingAnchor 38) ≤
      (harmU 38 * harmU 38) *
        integerThetaSum (harmW 38) (growingAnchor 38)) := by
  unfold growingHeadScaledThetaResidual integerThetaSum halfThetaSum
    integerThetaTerm halfThetaTerm normalizedDemandCoeff
    normalizedSpacingGain movingCutoffScale harmonicSpacing shellDropFraction
    growingAnchor harmW harmU ReciprocalBernoulliUpper.oneSub unit Ncut
    finSum qpow
  decide

/-! Two exact fences around tempting but invalid residual-upper routes. -/

/-- The signed contribution of a single diagonal/half-edge theta cell to the
cleared Pascal residual.  The useful upper bound is necessarily cumulative:
individual cells do not obey the eight-unit budget. -/
def growingThetaResidualCell (w : Q') (n : Nat) : Q' :=
  qpow ((1 : Q') + w) 3 * integerThetaTerm w n +
    -(Q'.ofNat 8 * (w * halfThetaTerm w n))

/-- Raw cellwise domination already fails at cell five of the first all-tail
scale.  This is an exact rational counterexample, not a numerical sample. -/
theorem old_pascal_cellwise_eight_budget_fails_k38_n5 :
    ¬ (normalizedDemandCoeff 38 *
          growingThetaResidualCell (harmW 38) 5 ≤
        Q'.ofNat 8 * (harmU 38 * harmU 38) *
          integerThetaTerm (harmW 38) 5) := by
  unfold growingThetaResidualCell integerThetaTerm halfThetaTerm
    normalizedDemandCoeff normalizedSpacingGain movingCutoffScale
    harmonicSpacing shellDropFraction harmW harmU
    ReciprocalBernoulliUpper.oneSub unit Ncut qpow
  decide

/-! The cellwise upper fails, but the signed cells have a rigid one-crossing
structure.  The following denominator-free slope is the cell factor

`n (1+w)^3 - 8 (n+1) w^(2n+1)`.

After division by the positive integer `n`, it is exactly the residual-cell
coefficient relative to `integerThetaTerm w n`. -/

def thetaResidualCellSlope (w : Q') (n : Nat) : Q' :=
  Q'.ofNat n * qpow ((1 : Q') + w) 3 +
    -(Q'.ofNat 8 *
      (Q'.ofNat (n + 1) * qpow w (2 * n + 1)))

/-- The adjacent edge ratio is antitone, in division-free form.  This is the
exact local inequality behind the unique sign crossing of the theta-residual
cells; unlike the refuted cellwise budget, it preserves the cancellation. -/
theorem theta_edge_ratio_cross_antitone {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (n : Nat) :
    (Q'.ofNat n * Q'.ofNat (n + 2)) * qpow w (2 * (n + 1) + 1) ≤
      (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * qpow w (2 * n + 1) := by
  have hexp : 2 * n + 1 ≤ 2 * (n + 1) + 1 := by omega
  have hp : qpow w (2 * (n + 1) + 1) ≤ qpow w (2 * n + 1) :=
    HeatKernelRGStep.qpow_antitone hw0 hw1
      (2 * n + 1) (2 * (n + 1) + 1) hexp
  have hc : Q'.ofNat n * Q'.ofNat (n + 2) ≤
      Q'.ofNat (n + 1) * Q'.ofNat (n + 1) := by
    show _ * (_ : Int) ≤ _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one]
    push_cast
    simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul]
    omega
  have hleft := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat n * Q'.ofNat (n + 2)) hp
      (Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
        (HeatKernelRGStep.zero_le_ofNat _))
  have hright := Q'.mul_le_mul_of_nonneg_right _ _
    (qpow w (2 * n + 1)) hc (qpow_nonneg w hw0 _)
  exact Q'.le_trans' _ _ _ hleft hright

/-- Consequently the cleared cell slope divided by its index is monotone:
`slope n / n ≤ slope (n+1)/(n+1)`.  The statement is cross-multiplied,
so it remains constructive and contains no reciprocal or choice. -/
theorem thetaResidualCellSlope_cross_mono {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (n : Nat) :
    Q'.ofNat (n + 1) * thetaResidualCellSlope w n ≤
      Q'.ofNat n * thetaResidualCellSlope w (n + 1) := by
  let A := qpow ((1 : Q') + w) 3
  let p := qpow w (2 * n + 1)
  let p' := qpow w (2 * (n + 1) + 1)
  let L := (Q'.ofNat (n + 1) * Q'.ofNat (n + 1)) * p
  let R := (Q'.ofNat n * Q'.ofNat (n + 2)) * p'
  have hRL : R ≤ L := by
    dsimp only [R, L, p, p']
    exact theta_edge_ratio_cross_antitone hw0 hw1 n
  have h8 : Q'.ofNat 8 * R ≤ Q'.ofNat 8 * L :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hRL
      (HeatKernelRGStep.zero_le_ofNat 8)
  have hneg : -(Q'.ofNat 8 * L) ≤ -(Q'.ofNat 8 * R) :=
    Q'.neg_le_neg h8
  have hadd := Q'.add_le_add_left
    ((Q'.ofNat (n + 1) * Q'.ofNat n) * A)
    (-(Q'.ofNat 8 * L)) (-(Q'.ofNat 8 * R)) hneg
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by
      dsimp only [thetaResidualCellSlope, A, L, p]
      theta_cross_ring))
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (by
        dsimp only [thetaResidualCellSlope, A, R, p']
        theta_cross_ring)))

/-- Once the normalized cell slope is nonnegative, every following cell is
nonnegative.  This is the forward half of the exact one-crossing statement. -/
theorem thetaResidualCellSlope_nonnegative_succ {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) {n : Nat}
    (hn : 0 < n) (hcell : (0 : Q') ≤ thetaResidualCellSlope w n) :
    (0 : Q') ≤ thetaResidualCellSlope w (n + 1) := by
  cases n with
  | zero => omega
  | succ n =>
      have hleft : (0 : Q') ≤
          Q'.ofNat (n + 1 + 1) * thetaResidualCellSlope w (n + 1) :=
        Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _) hcell
      have hcross := thetaResidualCellSlope_cross_mono hw0 hw1 (n + 1)
      have hscaled : (0 : Q') ≤
          Q'.ofNat (n + 1) * thetaResidualCellSlope w (n + 1 + 1) :=
        Q'.le_trans' _ _ _ hleft hcross
      have hcancel : Q'.ofNat (n + 1) * (0 : Q') ≤
          Q'.ofNat (n + 1) * thetaResidualCellSlope w (n + 1 + 1) :=
        Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.mul_zero_eqv (Q'.ofNat (n + 1)))) hscaled
      exact Q'.le_of_mul_le_mul_left hcancel (Q'.ofNat_succ_pos n)

/-- Dually, a nonpositive cell forces every preceding normalized slope to be
nonpositive.  Together with `thetaResidualCellSlope_nonnegative_succ`, this
rules out more than one sign crossing. -/
theorem thetaResidualCellSlope_nonpositive_pred {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) {n : Nat}
    (hcell : thetaResidualCellSlope w (n + 1) ≤ (0 : Q')) :
    thetaResidualCellSlope w n ≤ (0 : Q') := by
  have hcross := thetaResidualCellSlope_cross_mono hw0 hw1 n
  have hright : Q'.ofNat n * thetaResidualCellSlope w (n + 1) ≤
      Q'.ofNat n * (0 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcell
      (HeatKernelRGStep.zero_le_ofNat n)
  have hscaled : Q'.ofNat (n + 1) * thetaResidualCellSlope w n ≤
      Q'.ofNat (n + 1) * (0 : Q') :=
    Q'.le_trans' _ _ _ hcross
      (Q'.le_trans' _ _ _ hright
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (Q'.mul_zero_eqv (Q'.ofNat n))
          (Q'.eqv_symm (Q'.mul_zero_eqv (Q'.ofNat (n + 1)))))))
  exact Q'.le_of_mul_le_mul_left hscaled (Q'.ofNat_succ_pos n)

/-- Degree-`D` Pascal row for the integer head after the common `w²` factor
has been removed.  A length `c` contains the monomials belonging to
`n=1,...,c`. -/
def integerHeadAfterW2BernCoeff (D j : Nat) : Nat → Int
  | 0 => 0
  | c + 1 =>
      integerHeadAfterW2BernCoeff D j c +
        Int.ofNat ((c + 1) * (c + 1)) *
          HarmonicThetaPascalBridge.thetaMonoBernCoeff D
            (2 * (c + 1) * (c + 1) - 2) j

/-- Numerator of
`9/25-(2s+1)/(s+1)²`, with the positive denominator suppressed. -/
def normalizedDemandNumerator (s : Nat) : Int :=
  Int.ofNat (9 * ((s + 1) * (s + 1))) - Int.ofNat (25 * (2 * s + 1))

/-- Coefficient row of the schedule-cleared proposed residual upper

`s² C_s E ≤ 200(s+1)² P`,

where `E` is the growing Pascal row and `P=I/w²`.  Nonnegativity of this
whole row would prove the desired bound by Bernstein positivity, but it is
strictly stronger than the projectively weighted comparison. -/
def oldPascalCoefficientwiseEightGap (s j : Nat) : Int :=
  let m := 2 * s + 2
  let D := 2 * m * m + 1
  Int.ofNat (200 * ((s + 1) * (s + 1))) *
      integerHeadAfterW2BernCoeff D j (2 * s + 1) -
    Int.ofNat (s * s) * normalizedDemandNumerator s *
      HarmonicThetaPascalBridge.growingHeadThetaBernCoeff D m j

/-- The natural coefficientwise Bernstein comparison fails at its very
first coefficient at `k=38` (`s=k+2=40`).  The exact negative value forces
the subsequent argument to retain projective weighting/cancellation. -/
theorem old_pascal_coefficientwise_eight_gap_negative_k38_j0 :
    oldPascalCoefficientwiseEightGap 40 0 = (-20630200 : Int) := by
  decide

/-! ## 2. Exact Pascal-residual separation -/

/-- The already-positive one-scale Pascal remainder at the growing anchor. -/
def growingPascalResidual (k : Nat) : Q' :=
  growingHeadScaledThetaResidual (harmW k) (growingAnchor k)

/-- Eight times the cubic-retune mass floor, before division by the integer
theta head. -/
def retuneMarginEight (k : Nat) : Q' :=
  Q'.ofNat 8 + -(qpow ((1 : Q') + harmW k) 3)

/-- The scalar part of the two-weight cross after both one-scale Pascal
remainders are exposed exactly. -/
def growingThetaMainScalar (k : Nat) : Q' :=
  shellDropFraction * retuneMarginEight (k + 1) +
    -(normalizedDemandCoeff k * retuneMarginEight k)

/-- Large-scale exact audit of the proposed sixteen-unit main reserve.  The
coefficient here is `shellDropFraction = 9/25`; this check fences off the
incorrect `24/25` asymptotic normalization. -/
theorem sixteen_harmU_sq_le_main_k1000 :
    Q'.ofNat 16 * (harmU 1000 * harmU 1000) ≤
      growingThetaMainScalar 1000 := by
  unfold growingThetaMainScalar retuneMarginEight normalizedDemandCoeff
    normalizedSpacingGain movingCutoffScale harmonicSpacing shellDropFraction
    harmW harmU ReciprocalBernoulliUpper.oneSub unit Ncut qpow
  decide

private def thetaCrossHalf : Q' := Q'.mkPos 1 2 (by decide)

private def thetaCrossRetuneCube (w : Q') : Q' :=
  qpow (thetaCrossHalf * ((1 : Q') + w)) 3

private theorem retuneCube_eq_thetaCrossRetuneCube (w : Q') :
    retuneCube w = thetaCrossRetuneCube w := rfl

private theorem eight_mul_retuneCube_eqv (w : Q') :
    Q'.ofNat 8 * retuneCube w ≈ qpow ((1 : Q') + w) 3 := by
  rw [retuneCube_eq_thetaCrossRetuneCube]
  unfold thetaCrossRetuneCube thetaCrossHalf
  simp only [qpow]
  theta_cross_ring

/-- Exact cubic profile of the retune margin:
`8-(1+w_k)^3 = u_k(12-6u_k+u_k²)`. -/
theorem retuneMarginEight_profile_eqv (k : Nat) :
    retuneMarginEight k ≈
      harmU k *
        ((Q'.ofNat 12 + -(Q'.ofNat 6 * harmU k)) +
          harmU k * harmU k) := by
  have hc := eight_mul_retuneCube_eqv (harmW k)
  have hfactor :
      Q'.ofNat 8 + -(Q'.ofNat 8 * retuneCube (harmW k)) ≈
        Q'.ofNat 8 * ((1 : Q') + -retuneCube (harmW k)) := by
    theta_cross_ring
  have hp :=
    YMGap.Continuum.HarmonicRetuneFloor.harmonic_retune_floor_cleared k
  change Q'.ofNat 8 * ((1 : Q') + -retuneCube (harmW k)) ≈
      harmU k *
        ((Q'.ofNat 12 + -(Q'.ofNat 6 * harmU k)) +
          harmU k * harmU k) at hp
  unfold retuneMarginEight
  exact Q'.eqv_trans _
    (Q'.ofNat 8 + -(Q'.ofNat 8 * retuneCube (harmW k))) _
    (Q'.add_eqv_congr_left (Q'.ofNat 8) _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hc)))
    (Q'.eqv_trans _ _ _ hfactor hp)

/-- The leading and quadratic parts of the exact cubic profile are a lower
bound; only the nonnegative cubic term was discarded. -/
theorem retuneMarginEight_quadratic_lower (k : Nat) :
    harmU k * (Q'.ofNat 12 + -(Q'.ofNat 6 * harmU k)) ≤
      retuneMarginEight k := by
  let u := harmU k
  let A := Q'.ofNat 12 + -(Q'.ofNat 6 * u)
  have hu0 : (0 : Q') ≤ u := harmU_nonneg k
  have hu2 : (0 : Q') ≤ u * u := Q'.mul_nonneg _ _ hu0 hu0
  have hi : A ≤ A + u * u := Q'.add_le_self_of_nonneg _ _ hu2
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ u hi hu0
  exact Q'.le_trans' _ _ _ (by simpa [u, A] using hm)
    (Q'.le_of_eqv (Q'.eqv_symm (retuneMarginEight_profile_eqv k)))

/-- A companion upper profile valid for every harmonic unit. -/
theorem retuneMarginEight_profile_upper (k : Nat) :
    retuneMarginEight k ≤
      harmU k *
        ((Q'.ofNat 12 + -(Q'.ofNat 6 * harmU k)) + harmU k) := by
  let u := harmU k
  let A := Q'.ofNat 12 + -(Q'.ofNat 6 * u)
  have hu0 : (0 : Q') ≤ u := harmU_nonneg k
  have hu1 : u ≤ (1 : Q') := harmU_le_one k
  have hu2 : u * u ≤ u := by
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ u hu1 hu0
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv u))
  have hi : A + u * u ≤ A + u := Q'.add_le_add_left A _ _ hu2
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ u hi hu0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (retuneMarginEight_profile_eqv k))
    (by simpa [u, A] using hm)

private def marginDropPolyL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let v := RingNormaliser.PolyExpr.var 1
  .add
    (.mul u (.add (.add (.const 12) (.neg (.mul (.const 6) u))) u))
    (.neg (.mul v (.add (.const 12) (.neg (.mul (.const 6) v)))))

private def marginDropPolyR : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  let v := RingNormaliser.PolyExpr.var 1
  .add
    (.mul (.const 12) (.add u (.neg v)))
    (.add (.mul (.const 6) (.mul v v))
      (.neg (.mul (.const 5) (.mul u u))))

private theorem marginDropPoly_normal :
    RingNormaliser.normalize marginDropPolyL =
      RingNormaliser.normalize marginDropPolyR := by
  decide

private theorem margin_drop_poly_identity (u v : Q') :
    u * ((Q'.ofNat 12 + -(Q'.ofNat 6 * u)) + u) +
        -(v * (Q'.ofNat 12 + -(Q'.ofNat 6 * v))) ≈
      Q'.ofNat 12 * (u + -v) +
        (Q'.ofNat 6 * (v * v) + -(Q'.ofNat 5 * (u * u))) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    marginDropPolyL marginDropPolyR marginDropPoly_normal
    (fun
      | 0 => u
      | _ => v)
  simpa [marginDropPolyL, marginDropPolyR, RingNormaliser.eval] using h

private def sixMinusFivePolyL : RingNormaliser.PolyExpr :=
  let u := RingNormaliser.PolyExpr.var 0
  .add (.mul (.const 6) (.mul u u))
    (.neg (.mul (.const 5) (.mul u u)))

private def sixMinusFivePolyR : RingNormaliser.PolyExpr :=
  .mul (.var 0) (.var 0)

private theorem sixMinusFivePoly_normal :
    RingNormaliser.normalize sixMinusFivePolyL =
      RingNormaliser.normalize sixMinusFivePolyR := by
  decide

private theorem six_minus_five_sq_identity (u : Q') :
    Q'.ofNat 6 * (u * u) + -(Q'.ofNat 5 * (u * u)) ≈ u * u := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    sixMinusFivePolyL sixMinusFivePolyR sixMinusFivePoly_normal
    (fun _ => u)
  simpa [sixMinusFivePolyL, sixMinusFivePolyR,
    RingNormaliser.eval] using h

/-- The one-step loss of the explicit retune margin has a uniform second-order
upper envelope.  This is the cancellation estimate needed by the moving
two-weight determinant. -/
theorem retuneMarginEight_drop_upper (k : Nat) :
    retuneMarginEight k + -retuneMarginEight (k + 1) ≤
      Q'.ofNat 12 * (harmU k + -harmU (k + 1)) +
        harmU k * harmU k := by
  let u := harmU k
  let v := harmU (k + 1)
  let U := u * ((Q'.ofNat 12 + -(Q'.ofNat 6 * u)) + u)
  let L := v * (Q'.ofNat 12 + -(Q'.ofNat 6 * v))
  have hM0 : retuneMarginEight k ≤ U := by
    simpa [u, U] using retuneMarginEight_profile_upper k
  have hM1 : L ≤ retuneMarginEight (k + 1) := by
    simpa [v, L] using retuneMarginEight_quadratic_lower (k + 1)
  have hsum : retuneMarginEight k + -retuneMarginEight (k + 1) ≤
      U + -L := by
    have h0 := Q'.add_le_add_right _ _ (-retuneMarginEight (k + 1)) hM0
    have h1 := Q'.add_le_add_left U _ _ (Q'.neg_le_neg hM1)
    exact Q'.le_trans' _ _ _ h0 h1
  have hvu : v ≤ u := by
    dsimp only [u, v]
    unfold harmU
    exact unit_antitone (by omega) (by omega) (by omega)
  have hu0 : (0 : Q') ≤ u := by dsimp [u]; exact harmU_nonneg k
  have hv0 : (0 : Q') ≤ v := by dsimp [v]; exact harmU_nonneg (k + 1)
  have hv2u2 : v * v ≤ u * u := by
    have h0 := Q'.mul_le_mul_of_nonneg_right v u v hvu hv0
    have h1 := Q'.mul_le_mul_of_nonneg_left v u u hvu hu0
    exact Q'.le_trans' _ _ _ h0 h1
  have h6 := Q'.mul_le_mul_of_nonneg_left (v * v) (u * u)
    (Q'.ofNat 6) hv2u2 (by decide)
  have hrem : Q'.ofNat 6 * (v * v) + -(Q'.ofNat 5 * (u * u)) ≤
      u * u := by
    have hadd := Q'.add_le_add_right _ _
      (-(Q'.ofNat 5 * (u * u))) h6
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (six_minus_five_sq_identity u))
  have hfinal := Q'.add_le_add_left (Q'.ofNat 12 * (u + -v)) _ _ hrem
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (margin_drop_poly_identity u v))
      (by simpa [u, v] using hfinal))

private def scalarRearrangePolyL : RingNormaliser.PolyExpr :=
  let r := RingNormaliser.PolyExpr.var 0
  let g := RingNormaliser.PolyExpr.var 1
  let M0 := RingNormaliser.PolyExpr.var 2
  let M1 := RingNormaliser.PolyExpr.var 3
  .add (.mul r M1) (.neg (.mul (.add r (.neg g)) M0))

private def scalarRearrangePolyR : RingNormaliser.PolyExpr :=
  let r := RingNormaliser.PolyExpr.var 0
  let g := RingNormaliser.PolyExpr.var 1
  let M0 := RingNormaliser.PolyExpr.var 2
  let M1 := RingNormaliser.PolyExpr.var 3
  .add (.mul g M0) (.neg (.mul r (.add M0 (.neg M1))))

private theorem scalarRearrangePoly_normal :
    RingNormaliser.normalize scalarRearrangePolyL =
      RingNormaliser.normalize scalarRearrangePolyR := by
  decide

private theorem scalar_rearrange_identity (r g M0 M1 : Q') :
    r * M1 + -((r + -g) * M0) ≈
      g * M0 + -(r * (M0 + -M1)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    scalarRearrangePolyL scalarRearrangePolyR scalarRearrangePoly_normal
    (fun
      | 0 => r
      | 1 => g
      | 2 => M0
      | _ => M1)
  simpa [scalarRearrangePolyL, scalarRearrangePolyR,
    RingNormaliser.eval] using h

/-- Explicit second-order lower carrier for the scalar reserve. -/
def growingThetaScalarLower (k : Nat) : Q' :=
  normalizedSpacingGain k *
      (harmU k * (Q'.ofNat 12 + -(Q'.ofNat 6 * harmU k))) +
    -(shellDropFraction *
      (Q'.ofNat 12 * (harmU k + -harmU (k + 1)) +
        harmU k * harmU k))

/-- The exact main scalar dominates its closed second-order carrier. -/
theorem growingThetaScalarLower_le_main (k : Nat) :
    growingThetaScalarLower k ≤ growingThetaMainScalar k := by
  let g := normalizedSpacingGain k
  let r := shellDropFraction
  let M0 := retuneMarginEight k
  let M1 := retuneMarginEight (k + 1)
  let L0 := harmU k * (Q'.ofNat 12 + -(Q'.ofNat 6 * harmU k))
  let D := Q'.ofNat 12 * (harmU k + -harmU (k + 1)) +
    harmU k * harmU k
  have hg0 : (0 : Q') ≤ g := by
    dsimp [g]
    exact normalizedSpacingGain_nonneg k
  have hr0 : (0 : Q') ≤ r := by dsimp [r, shellDropFraction]; decide
  have hM0 : L0 ≤ M0 := by
    simpa [L0, M0] using retuneMarginEight_quadratic_lower k
  have hdrop : M0 + -M1 ≤ D := by
    simpa [M0, M1, D] using retuneMarginEight_drop_upper k
  have hpos := Q'.mul_le_mul_of_nonneg_left L0 M0 g hM0 hg0
  have hneg0 := Q'.mul_le_mul_of_nonneg_left (M0 + -M1) D r hdrop hr0
  have hneg : -(r * D) ≤ -(r * (M0 + -M1)) := Q'.neg_le_neg hneg0
  have hsum0 := Q'.add_le_add_right _ _ (-(r * D)) hpos
  have hsum1 := Q'.add_le_add_left (g * M0) _ _ hneg
  have hsum : g * L0 + -(r * D) ≤
      g * M0 + -(r * (M0 + -M1)) := Q'.le_trans' _ _ _ hsum0 hsum1
  have hrearrange : growingThetaMainScalar k ≈
      g * M0 + -(r * (M0 + -M1)) := by
    unfold growingThetaMainScalar normalizedDemandCoeff
    change r * M1 + -((r + -g) * M0) ≈
      g * M0 + -(r * (M0 + -M1))
    exact scalar_rearrange_identity r g M0 M1
  exact Q'.le_trans' _ _ _ (by simpa [g, r, L0, D] using hsum)
    (Q'.le_of_eqv (Q'.eqv_symm hrearrange))

/-- The normalized spacing gain retains at least `19/10` harmonic units on
the all-tail range. -/
theorem nineteen_tenths_harmU_le_normalizedSpacingGain
    {k : Nat} (hk : 38 ≤ k) :
    Q'.mkPos 19 10 (by decide) * harmU k ≤ normalizedSpacingGain k := by
  have hclosed : Q'.mkPos 19 10 (by decide) * harmU k ≤
      normalizedSpacingGainClosed k := by
    unfold normalizedSpacingGainClosed harmU unit
    show _ * (_ : Int) ≤ _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast,
      Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
      Int.one_mul, Int.mul_one]
    push_cast
    let m := k + 2
    have hm : 40 ≤ m := by dsimp [m]; omega
    have hsq : 28 * m + 19 ≤ m * m := by
      have hmul := Nat.mul_le_mul_right m hm
      have h19 : 19 ≤ 12 * m := by omega
      omega
    have hnat :
        19 * ((m + 1) * (m + 1)) ≤
          10 * m * (2 * m + 1) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      rw [show 10 * m * (2 * m) = 20 * (m * m) by ac_rfl]
      omega
    have hint :
        (19 : Int) * (((k : Int) + 1 + 1 + 1) * ((k : Int) + 1 + 1 + 1)) ≤
          (2 * ((k : Int) + 1 + 1) + 1) *
            (10 * ((k : Int) + 1 + 1)) := by
      have hnat' : 19 * ((k + 3) * (k + 3)) ≤
          (2 * (k + 2) + 1) * (10 * (k + 2)) := by
        simpa [m, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hnat
      exact_mod_cast hnat'
    exact hint
  exact Q'.le_trans' _ _ _ hclosed
    (Q'.le_of_eqv (Q'.eqv_symm (normalizedSpacingGain_eq_closed k)))

private theorem harmU_le_fortieth {k : Nat} (hk : 38 ≤ k) :
    harmU k ≤ Q'.mkPos 1 40 (by decide) := by
  unfold harmU
  exact unit_antitone (by decide) (by omega) (by omega)

private theorem harmonic_unit_drop_le_sq (k : Nat) :
    harmU k + -harmU (k + 1) ≤ harmU k * harmU k := by
  unfold harmU
  change Q'.mkPos 1 (k + 2) (by omega) +
      -(Q'.mkPos 1 (k + 3) (by omega)) ≤
    Q'.mkPos 1 (k + 2) (by omega) * Q'.mkPos 1 (k + 2) (by omega)
  show _ * (_ : Int) ≤ _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
    Q'.mul_den_cast, Q'.neg_den, thetaCross_neg_num_cast,
    Q'.mkPos_num, Q'.mkPos_den, Int.add_mul,
    Int.neg_mul, Int.one_mul, Int.mul_one]
  push_cast
  let m : Int := (k : Int) + 2
  change (m + 1) * (m * m) + -(m * (m * m)) ≤ m * (m + 1)
  have hleft : (m + 1) * (m * m) + -(m * (m * m)) = m * m := by
    rw [Int.add_mul, Int.one_mul]
    omega
  rw [hleft]
  exact Int.mul_le_mul_of_nonneg_left (by omega) (by dsimp [m]; omega)

private theorem le_sub_of_add_le {a b c : Q'} (h : a + b ≤ c) :
    a ≤ c + -b := by
  have hs := Q'.add_le_add_right (a + b) c (-b) h
  have hleft : (a + b) + -b ≈ a := by
    refine Q'.eqv_trans _ (a + (b + -b)) _
      (Q'.add_assoc_eqv a b (-b)) ?_
    exact Q'.eqv_trans _ (a + (0 : Q')) _
      (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv b))
      (QPoly.q_add_zero_eqv a)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft)) hs

/-- Uniform sixteen-unit main reserve on the complete all-tail range. -/
theorem sixteen_harmU_sq_le_growingThetaMainScalar
    {k : Nat} (hk : 38 ≤ k) :
    Q'.ofNat 16 * (harmU k * harmU k) ≤ growingThetaMainScalar k := by
  let u := harmU k
  let v := harmU (k + 1)
  let g := normalizedSpacingGain k
  let r := shellDropFraction
  let L0 := u * (Q'.ofNat 12 + -(Q'.ofNat 6 * u))
  let D := Q'.ofNat 12 * (u + -v) + u * u
  let P := Q'.mkPos 4503 200 (by decide) * (u * u)
  let N := Q'.mkPos 117 25 (by decide) * (u * u)
  have hu0 : (0 : Q') ≤ u := by dsimp [u]; exact harmU_nonneg k
  have hg : Q'.mkPos 19 10 (by decide) * u ≤ g := by
    simpa [u, g] using nineteen_tenths_harmU_le_normalizedSpacingGain hk
  have hu40 : u ≤ Q'.mkPos 1 40 (by decide) := by
    simpa [u] using harmU_le_fortieth hk
  have h6 := Q'.mul_le_mul_of_nonneg_left u (Q'.mkPos 1 40 (by decide))
    (Q'.ofNat 6) hu40 (by decide)
  have hinner : Q'.mkPos 237 20 (by decide) ≤
      Q'.ofNat 12 + -(Q'.ofNat 6 * u) := by
    have hn := Q'.neg_le_neg h6
    have ha := Q'.add_le_add_left (Q'.ofNat 12) _ _ hn
    exact Q'.le_trans' _ _ _ (by decide) ha
  have hL : Q'.mkPos 237 20 (by decide) * u ≤ L0 := by
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ u hinner hu0
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
  have hL0 : (0 : Q') ≤ L0 := by
    dsimp [L0]
    exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ (by decide) hu0)
      (Q'.le_trans' _ _ _ hL (Q'.le_refl' _))
  have hga := Q'.mul_le_mul_of_nonneg_right _ _ L0 hg hL0
  have ha0 : (0 : Q') ≤ Q'.mkPos 19 10 (by decide) * u :=
    Q'.mul_nonneg _ _ (by decide) hu0
  have hgb := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 19 10 (by decide) * u) hL ha0
  have hpos : P ≤ g * L0 := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ hgb hga)
    dsimp [P]
    exact Q'.le_of_eqv (by theta_cross_ring)
  have hdrop : u + -v ≤ u * u := by
    simpa [u, v] using harmonic_unit_drop_le_sq k
  have h12 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 12) hdrop (by decide)
  have hD : D ≤ Q'.ofNat 13 * (u * u) := by
    have ha := Q'.add_le_add_right _ _ (u * u) h12
    have hcollapse : Q'.ofNat 12 * (u * u) + u * u ≈
        Q'.ofNat 13 * (u * u) := by
      refine Q'.eqv_trans _
        (Q'.ofNat 12 * (u * u) + (1 : Q') * (u * u)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.one_mul_eqv (u * u)))
      refine Q'.eqv_trans _
        ((Q'.ofNat 12 + (1 : Q')) * (u * u)) _
        (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
      exact Q'.mul_eqv_congr_right _ _ (u * u) (by decide)
    exact Q'.le_trans' _ _ _ (by simpa [D] using ha)
      (Q'.le_of_eqv hcollapse)
  have hr0 : (0 : Q') ≤ r := by dsimp [r, shellDropFraction]; decide
  have hneg0 := Q'.mul_le_mul_of_nonneg_left D
    (Q'.ofNat 13 * (u * u)) r hD hr0
  have hneg : r * D ≤ N := by
    exact Q'.le_trans' _ _ _ hneg0
      (Q'.le_of_eqv (by dsimp [r, N, shellDropFraction]; theta_cross_ring))
  have hbudget : Q'.ofNat 16 * (u * u) + N ≤ P := by
    dsimp [N, P]
    have hc : Q'.ofNat 16 + Q'.mkPos 117 25 (by decide) ≤
        Q'.mkPos 4503 200 (by decide) := by decide
    have hm := Q'.mul_le_mul_of_nonneg_right _ _ (u * u) hc
      (Q'.mul_nonneg _ _ hu0 hu0)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by theta_cross_ring)) hm
  have hsum := Q'.add_le_add_left (Q'.ofNat 16 * (u * u)) _ _ hneg
  have hpaid : Q'.ofNat 16 * (u * u) + r * D ≤ g * L0 :=
    Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ hbudget hpos)
  have hlower : Q'.ofNat 16 * (u * u) ≤ g * L0 + -(r * D) :=
    le_sub_of_add_le hpaid
  exact Q'.le_trans' _ _ _
    (by simpa [u, v, g, r, L0, D, growingThetaScalarLower] using hlower)
    (growingThetaScalarLower_le_main k)

private theorem thetaCross_finSum_nonnegative
    (f : Nat → Q') (hf : ∀ j, (0 : Q') ≤ f j) : ∀ N,
    (0 : Q') ≤ finSum f N
  | 0 => Q'.le_refl' 0
  | N + 1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _ (thetaCross_finSum_nonnegative f hf N) (hf N)

private theorem integerThetaTerm_nonnegative_harmonic (k n : Nat) :
    (0 : Q') ≤ integerThetaTerm (harmW k) n := by
  unfold integerThetaTerm
  exact Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
    (qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _)

/-- The first integer-theta monomial is retained in every harmonic head. -/
theorem harmonic_first_integerThetaTerm_le_sum (k N : Nat) :
    integerThetaTerm (harmW k) 1 ≤ integerThetaSum (harmW k) N := by
  let f : QSeq := fun j => integerThetaTerm (harmW k) (j + 1)
  have htail : (0 : Q') ≤ finSum (fun j => f (j + 1)) N := by
    apply thetaCross_finSum_nonnegative
    intro j
    dsimp only [f]
    exact integerThetaTerm_nonnegative_harmonic k (j + 1 + 1)
  have hadd : f 0 ≤ f 0 + finSum (fun j => f (j + 1)) N :=
    Q'.add_le_self_of_nonneg _ _ htail
  have hpeel := RationalTail.finSum_peel_left f N
  unfold integerThetaSum
  exact Q'.le_trans' _ _ _ (by simpa [f] using hadd)
    (Q'.le_of_eqv (Q'.eqv_symm hpeel))

private theorem integerThetaTerm_one_eqv_qpow_two (w : Q') :
    integerThetaTerm w 1 ≈ qpow w 2 := by
  unfold integerThetaTerm
  simp only [Nat.one_mul, qpow]
  theta_cross_ring

private theorem unit_sq_eqv_unit_sq_den (s : Nat) (hs : 0 < s) :
    unit s hs * unit s hs ≈ unit (s * s) (Nat.mul_pos hs hs) := by
  unfold unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Int.one_mul, Int.mul_one]
  push_cast
  rfl

/-- The scale-linear dyadic tail is smaller than one harmonic inverse-square
unit.  This is symbolic in `k`; no finite range is enumerated. -/
theorem linear_dyad_le_harmU_sq (k : Nat) :
    dyad (2 * (k + 2) + 5) ≤ harmU k * harmU k := by
  let s := k + 2
  let r := 2 * s + 5
  have hs : 0 < s := by dsimp [s]; omega
  have hsPow : s ≤ 2 ^ s := CasimirMoment.nat_le_two_pow s
  have hsq : s * s ≤ (2 ^ s) * (2 ^ s) := Nat.mul_le_mul hsPow hsPow
  have hdouble : (2 ^ s) * (2 ^ s) = 2 ^ (s + s) := by
    rw [← Nat.pow_add]
  have hbase : s * s ≤ 2 ^ (s + s) := by simpa [hdouble] using hsq
  have hext : 2 ^ (s + s) ≤ 2 ^ r := by
    apply Nat.pow_le_pow_right (by decide)
    dsimp [r]
    omega
  have hden : s * s ≤ 2 ^ r := Nat.le_trans hbase hext
  have hunit : unit (2 ^ r) (twoPow_pos r) ≤
      unit (s * s) (Nat.mul_pos hs hs) :=
    unit_antitone (Nat.mul_pos hs hs) (twoPow_pos r) hden
  have hdyad : dyad r ≈ unit (2 ^ r) (twoPow_pos r) :=
    half_pow_eqv_unit r
  have hu : harmU k * harmU k ≈
      unit (s * s) (Nat.mul_pos hs hs) := by
    unfold harmU
    dsimp only [s]
    exact unit_sq_eqv_unit_sq_den (k + 2) (by omega)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdyad)
    (Q'.le_trans' _ _ _ hunit (Q'.le_of_eqv (Q'.eqv_symm hu)))

/-- Same scalar with the spacing gain replaced by its exact closed rational
form.  Unlike `normalizedDemandCoeff`, this presentation is subtraction-free
at the representation level and can therefore be denominator-cleared
uniformly. -/
def growingThetaMainClosed (k : Nat) : Q' :=
  shellDropFraction * retuneMarginEight (k + 1) +
    -((shellDropFraction + -normalizedSpacingGainClosed k) *
      retuneMarginEight k)

theorem growingThetaMainScalar_eqv_closed (k : Nat) :
    growingThetaMainScalar k ≈ growingThetaMainClosed k := by
  have hg : normalizedSpacingGain k ≈ normalizedSpacingGainClosed k :=
    normalizedSpacingGain_eq_closed k
  have hc : normalizedDemandCoeff k ≈
      shellDropFraction + -normalizedSpacingGainClosed k := by
    unfold normalizedDemandCoeff
    change shellDropFraction + -normalizedSpacingGain k ≈
      shellDropFraction + -normalizedSpacingGainClosed k
    exact Q'.add_eqv_congr_left shellDropFraction _ _
      (Q'.neg_eqv_congr _ _ hg)
  unfold growingThetaMainScalar growingThetaMainClosed
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ (retuneMarginEight k) hc))

/-- Exact one-scale decomposition: eight times the retained theta deficit is
the cubic-retune floor times the integer head plus the Pascal remainder. -/
theorem eight_mul_growingHeadThetaDeficit_eqv (k : Nat) :
    Q'.ofNat 8 * growingHeadThetaDeficit k ≈
      retuneMarginEight k *
          integerThetaSum (harmW k) (growingAnchor k) +
        growingPascalResidual k := by
  unfold growingHeadThetaDeficit retuneMarginEight growingPascalResidual
    growingHeadScaledThetaResidual
  change Q'.ofNat 8 *
      (integerThetaSum (harmW k) (growingAnchor k) +
        -(harmW k * halfThetaSum (harmW k) (growingAnchor k + 1))) ≈
    (Q'.ofNat 8 + -(qpow ((1 : Q') + harmW k) 3)) *
        integerThetaSum (harmW k) (growingAnchor k) +
      (qpow ((1 : Q') + harmW k) 3 *
          integerThetaSum (harmW k) (growingAnchor k) +
        -(Q'.ofNat 8 *
          (harmW k * halfThetaSum (harmW k) (growingAnchor k + 1))))
  exact theta_deficit_decomp _ _ _

/-- Exact two-weight normal form.  The first product is the explicit scalar
reserve; the next-scale Pascal remainder is favorable; only the old-scale
Pascal remainder has the adverse sign.  This identity preserves every finite
theta term and introduces no comparison premise. -/
theorem eight_mul_growingHeadThetaCore_eqv (k : Nat) :
    Q'.ofNat 8 * growingHeadThetaCore k ≈
      (growingThetaMainScalar k *
          integerThetaSum (harmW k) (growingAnchor k)) *
            integerThetaSum (harmW (k + 1)) (growingAnchor (k + 1)) +
        (shellDropFraction * growingPascalResidual (k + 1)) *
          integerThetaSum (harmW k) (growingAnchor k) -
        (normalizedDemandCoeff k * growingPascalResidual k) *
          integerThetaSum (harmW (k + 1)) (growingAnchor (k + 1)) := by
  let r := shellDropFraction
  let c := normalizedDemandCoeff k
  let T0 := growingHeadThetaDeficit k
  let T1 := growingHeadThetaDeficit (k + 1)
  let M0 := retuneMarginEight k
  let M1 := retuneMarginEight (k + 1)
  let R0 := growingPascalResidual k
  let R1 := growingPascalResidual (k + 1)
  let I0 := integerThetaSum (harmW k) (growingAnchor k)
  let I1 := integerThetaSum (harmW (k + 1)) (growingAnchor (k + 1))
  have h0 : Q'.ofNat 8 * T0 ≈ M0 * I0 + R0 := by
    dsimp only [T0, M0, R0, I0]
    exact eight_mul_growingHeadThetaDeficit_eqv k
  have h1 : Q'.ofNat 8 * T1 ≈ M1 * I1 + R1 := by
    dsimp only [T1, M1, R1, I1]
    exact eight_mul_growingHeadThetaDeficit_eqv (k + 1)
  have hscale :
      Q'.ofNat 8 * ((r * T1) * I0 + -((c * T0) * I1)) ≈
        (r * (Q'.ofNat 8 * T1)) * I0 +
          -((c * (Q'.ofNat 8 * T0)) * I1) := by
    theta_cross_ring
  refine Q'.eqv_trans _
    ((r * (Q'.ofNat 8 * T1)) * I0 +
      -((c * (Q'.ofNat 8 * T0)) * I1)) _ ?_ ?_
  · unfold growingHeadThetaCore
    dsimp only [r, c, T0, T1, I0, I1] at hscale ⊢
    exact hscale
  refine Q'.eqv_trans _
    ((r * (M1 * I1 + R1)) * I0 +
      -((c * (M0 * I0 + R0)) * I1)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ I0
        (Q'.mul_eqv_congr_left r _ _ h1))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ I1
          (Q'.mul_eqv_congr_left c _ _ h0)))
  · unfold growingThetaMainScalar
    change
      (r * (M1 * I1 + R1)) * I0 + -((c * (M0 * I0 + R0)) * I1) ≈
        (((r * M1 + -(c * M0)) * I0) * I1 +
          (r * R1) * I0) + -((c * R0) * I1)
    theta_cross_ring

/-- The exact remaining analytic estimate is sufficient for the complete
finite-theta cross.  Everything after `hold` is discharged here: the
sixteen-unit scalar reserve pays eight units of the old residual, the
next-scale Pascal remainder is favorable, and the remaining inverse-square
unit absorbs the scale-linear dyadic tail. -/
theorem growing_theta_cross_of_old_pascal_eight_budget
    {k : Nat} (hk : 38 ≤ k)
    (hold : normalizedDemandCoeff k * growingPascalResidual k ≤
      Q'.ofNat 8 * (harmU k * harmU k) *
        integerThetaSum (harmW k) (growingAnchor k)) :
    (qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) *
        dyad (2 * (k + 2) + 5) ≤ growingHeadThetaCore k := by
  let u2 := harmU k * harmU k
  let I0 := integerThetaSum (harmW k) (growingAnchor k)
  let I1 := integerThetaSum (harmW (k + 1)) (growingAnchor (k + 1))
  let M := growingThetaMainScalar k
  let R0 := growingPascalResidual k
  let R1 := growingPascalResidual (k + 1)
  let c := normalizedDemandCoeff k
  let r := shellDropFraction
  have hI0 : (0 : Q') ≤ I0 := by
    dsimp only [I0]
    exact HarmonicThetaLinearCarrier.harmonic_integerThetaSum_nonnegative
      k (growingAnchor k)
  have hI1 : (0 : Q') ≤ I1 := by
    dsimp only [I1]
    exact HarmonicThetaLinearCarrier.harmonic_integerThetaSum_nonnegative
      (k + 1) (growingAnchor (k + 1))
  have hR1 : (0 : Q') ≤ R1 := by
    dsimp only [R1, growingPascalResidual]
    exact harmonic_growing_head_scaled_theta_residual_nonnegative (k + 1)
  have hr : (0 : Q') ≤ r := by dsimp [r, shellDropFraction]; decide
  have hfav : (0 : Q') ≤ (r * R1) * I0 :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hr hR1) hI0
  have hmain : Q'.ofNat 16 * u2 ≤ M := by
    simpa [u2, M] using sixteen_harmU_sq_le_growingThetaMainScalar hk
  have hmainI0 := Q'.mul_le_mul_of_nonneg_right _ _ I0 hmain hI0
  have hmainProd := Q'.mul_le_mul_of_nonneg_right _ _ I1 hmainI0 hI1
  have holdI1 := Q'.mul_le_mul_of_nonneg_right _ _ I1
    (by simpa [c, R0, I0] using hold) hI1
  let A := (Q'.ofNat 8 * u2 * I0) * I1
  let B := Q'.ofNat 8 * u2
  have hBB : B + B ≈ Q'.ofNat 16 * u2 := by
    refine Q'.eqv_trans _ ((Q'.ofNat 8 + Q'.ofNat 8) * u2) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
    · exact Q'.mul_eqv_congr_right _ _ u2 (by decide)
  have hAA : A + A ≈ (Q'.ofNat 16 * u2 * I0) * I1 := by
    change (B * I0) * I1 + (B * I0) * I1 ≈
      (Q'.ofNat 16 * u2 * I0) * I1
    refine Q'.eqv_trans _ ((B * I0 + B * I0) * I1) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    refine Q'.mul_eqv_congr_right _ _ I1 ?_
    refine Q'.eqv_trans _ ((B + B) * I0) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ I0 hBB
  have hpay : A + (c * R0) * I1 ≤ (M * I0) * I1 := by
    have hadd := Q'.add_le_add_left A _ _ holdI1
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hAA) hmainProd)
  have hafter : A ≤ (M * I0) * I1 + -((c * R0) * I1) :=
    le_sub_of_add_le hpay
  have hwithfav : A ≤
      ((M * I0) * I1 + (r * R1) * I0) + -((c * R0) * I1) := by
    have hAadd : A ≤ A + (r * R1) * I0 :=
      Q'.add_le_self_of_nonneg A _ hfav
    have hadd := Q'.add_le_add_right _ _ ((r * R1) * I0) hafter
    have htarget :
        ((M * I0) * I1 + -((c * R0) * I1)) + (r * R1) * I0 ≈
          ((M * I0) * I1 + (r * R1) * I0) + -((c * R0) * I1) := by
      theta_cross_ring
    exact Q'.le_trans' _ _ _ hAadd
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv htarget))
  have h8core : A ≤ Q'.ofNat 8 * growingHeadThetaCore k := by
    exact Q'.le_trans' _ _ _ hwithfav
      (Q'.le_of_eqv (Q'.eqv_symm (by
        simpa [M, I0, I1, R0, R1, c, r] using
          eight_mul_growingHeadThetaCore_eqv k)))
  have huI : u2 * (I0 * I1) ≤ growingHeadThetaCore k := by
    have hscaled : Q'.ofNat 8 * (u2 * (I0 * I1)) ≤
        Q'.ofNat 8 * growingHeadThetaCore k := by
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
        dsimp only [A]
        theta_cross_ring)) h8core
    exact Q'.le_of_mul_le_mul_left hscaled (by decide)
  have hdyad := linear_dyad_le_harmU_sq k
  have hterm0 := harmonic_first_integerThetaTerm_le_sum k (growingAnchor k)
  have hterm1 := harmonic_first_integerThetaTerm_le_sum
    (k + 1) (growingAnchor (k + 1))
  have hw0 : qpow (harmW k) 2 ≤ I0 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (integerThetaTerm_one_eqv_qpow_two _)))
      (by simpa [I0] using hterm0)
  have hw1 : qpow (harmW (k + 1)) 2 ≤ I1 :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (integerThetaTerm_one_eqv_qpow_two _)))
      (by simpa [I1] using hterm1)
  have hwp0 : (0 : Q') ≤ qpow (harmW k) 2 :=
    qpow_nonneg _ (harmW_nonneg k) _
  have hwp1 : (0 : Q') ≤ qpow (harmW (k + 1)) 2 :=
    qpow_nonneg _ (harmW_nonneg (k + 1)) _
  have hIprod : qpow (harmW k) 2 * qpow (harmW (k + 1)) 2 ≤ I0 * I1 :=
    Q'.mul_le_mul_of_nonneg hw0 hw1 hI0 hwp1
  have hu20 : (0 : Q') ≤ u2 := by
    dsimp [u2]
    exact Q'.mul_nonneg _ _ (harmU_nonneg k) (harmU_nonneg k)
  have hscaledDyad := Q'.mul_le_mul_of_nonneg_left _ _
    (qpow (harmW k) 2 * qpow (harmW (k + 1)) 2) hdyad
      (Q'.mul_nonneg _ _ hwp0 hwp1)
  have hscaledHeads := Q'.mul_le_mul_of_nonneg_left _ _ u2 hIprod hu20
  exact Q'.le_trans' _ _ _ hscaledDyad
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ hscaledHeads huI))

/-- Downstream normalized-slack consumer for the same sole residual. -/
theorem normalizedGlobalSlack_nonneg_of_old_pascal_eight_budget
    {k : Nat} (hk : 38 ≤ k)
    (hold : normalizedDemandCoeff k * growingPascalResidual k ≤
      Q'.ofNat 8 * (harmU k * harmU k) *
        integerThetaSum (harmW k) (growingAnchor k)) :
    (0 : Q') ≤ normalizedGlobalSlack k :=
  normalizedGlobalSlack_nonneg_of_theta_head_linear_dyad hk
    (growing_theta_cross_of_old_pascal_eight_budget hk hold)

/-- Full moving determinant after the eight-unit Pascal residual is paid. -/
theorem fullDeterminant_of_old_pascal_eight_budget
    {k : Nat} (hk : 38 ≤ k)
    (hold : normalizedDemandCoeff k * growingPascalResidual k ≤
      Q'.ofNat 8 * (harmU k * harmU k) *
        integerThetaSum (harmW k) (growingAnchor k)) :
    (shellDropFraction * harmonicMassCross k) * harmonicSpacing k ≤
      movingSpacingPayment k :=
  fullDeterminant_of_normalizedGlobalSlack_nonneg k
    (normalizedGlobalSlack_nonneg_of_old_pascal_eight_budget hk hold)

/-- Final shell/spacing law after the eight-unit Pascal residual is paid. -/
theorem harmonicMass_shell_spacing_of_old_pascal_eight_budget
    {k : Nat} (hk : 38 ≤ k)
    (hold : normalizedDemandCoeff k * growingPascalResidual k ≤
      Q'.ofNat 8 * (harmU k * harmU k) *
        integerThetaSum (harmW k) (growingAnchor k)) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k :=
  harmonicMass_shell_spacing_of_fullDeterminant k
    (fullDeterminant_of_old_pascal_eight_budget hk hold)

/-! ## 3. Fence around the separated one-scale route -/

/-- Scalar obtained by combining only the Pascal lower deficit at scale
`k+1` with the zeroth-half-edge upper deficit at scale `k`.  If this were
nonnegative, the two signed products in the theta cross could be separated.
The definition is recorded so that the failure below cannot be hidden by a
normalization change. -/
def separatedOneScaleFloor (k : Nat) : Q' :=
  shellDropFraction *
      ((1 : Q') - retuneCube (harmW (k + 1))) -
    normalizedDemandCoeff k *
      ((1 : Q') - qpow (harmW k) 3)

/-- The separated one-scale argument fails already at the first all-tail
scale: its scalar floor is strictly negative.  Thus the valid threshold
certificate above genuinely uses the finite two-weight cross cancellation;
the two Pascal/half-edge estimates cannot prove it term-by-term. -/
theorem separated_one_scale_floor_negative_k38 :
    separatedOneScaleFloor 38 < (0 : Q') := by
  unfold separatedOneScaleFloor normalizedDemandCoeff normalizedSpacingGain
    movingCutoffScale harmonicSpacing shellDropFraction retuneCube retuneBase
    harmW harmU ReciprocalBernoulliUpper.oneSub unit Ncut qpow
  decide

#print axioms growing_theta_cross_k38
#print axioms two_le_growingHeadThetaCore_k38
#print axioms old_pascal_residual_eight_budget_k38
#print axioms old_pascal_residual_one_budget_fails_k38
#print axioms growingThetaResidualCell
#print axioms old_pascal_cellwise_eight_budget_fails_k38_n5
#print axioms thetaResidualCellSlope
#print axioms theta_edge_ratio_cross_antitone
#print axioms thetaResidualCellSlope_cross_mono
#print axioms thetaResidualCellSlope_nonnegative_succ
#print axioms thetaResidualCellSlope_nonpositive_pred
#print axioms integerHeadAfterW2BernCoeff
#print axioms normalizedDemandNumerator
#print axioms oldPascalCoefficientwiseEightGap
#print axioms old_pascal_coefficientwise_eight_gap_negative_k38_j0
#print axioms growingPascalResidual
#print axioms retuneMarginEight
#print axioms growingThetaMainScalar
#print axioms sixteen_harmU_sq_le_main_k1000
#print axioms retuneMarginEight_profile_eqv
#print axioms retuneMarginEight_quadratic_lower
#print axioms retuneMarginEight_profile_upper
#print axioms retuneMarginEight_drop_upper
#print axioms growingThetaScalarLower
#print axioms growingThetaScalarLower_le_main
#print axioms nineteen_tenths_harmU_le_normalizedSpacingGain
#print axioms sixteen_harmU_sq_le_growingThetaMainScalar
#print axioms harmonic_first_integerThetaTerm_le_sum
#print axioms linear_dyad_le_harmU_sq
#print axioms growingThetaMainClosed
#print axioms growingThetaMainScalar_eqv_closed
#print axioms eight_mul_growingHeadThetaDeficit_eqv
#print axioms eight_mul_growingHeadThetaCore_eqv
#print axioms growing_theta_cross_of_old_pascal_eight_budget
#print axioms normalizedGlobalSlack_nonneg_of_old_pascal_eight_budget
#print axioms fullDeterminant_of_old_pascal_eight_budget
#print axioms harmonicMass_shell_spacing_of_old_pascal_eight_budget
#print axioms separatedOneScaleFloor
#print axioms separated_one_scale_floor_negative_k38

end YMGap.Continuum.HarmonicMovingDeterminantThetaCross
