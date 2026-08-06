/-
Track 11.7-fusion / R3k -- scale-invariant coordinates for the normalized
block-compatible theta tail.

# Result

Write `L_k = N_k + 1` for the physical cutoff length.  The recursive schedule
has three exact, index-free invariants:

    L_(k+1) = 2 L_k,
    u_k L_k^2 = 25/12,
    delta_k L_k^3 = 25/72.

The last two identities explain the scale of the remaining normalized-deficit
tail: the heat drift is quadratic in `1/L_k`, while the available shared debt
is cubic in `1/L_k`.  They are proved by structural induction from the exact
quarter/eighth schedule laws, not by evaluating any growing theta sum.

# Constructivity

Natural-number recurrence, exact `Q'` setoid algebra, and closed rational
facts only.  No `Classical`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaNormalizedDeficit
import YMGap.Continuum.P2BlockCompatibleHeatPower
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor

namespace YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleHeatPower
open YMGap.Continuum.P2BlockCompatibleThetaNormalizedDeficit
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "scale_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast,
               Q'.neg_den, neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- Physical cutoff length `L_k=N_k+1`, embedded into exact rationals. -/
def blockLength (k : Nat) : Q' := Q'.ofNat (blockNcut k + 1)

/-- The cutoff length doubles exactly at each square block step. -/
theorem blockLength_succ_eqv (k : Nat) :
    blockLength (k + 1) ≈ Q'.ofNat 2 * blockLength k := by
  unfold blockLength
  have hnat : blockNcut (k + 1) + 1 = 2 * (blockNcut k + 1) := by
    rw [blockNcut_succ]
    omega
  rw [hnat]
  exact YMGap.Constructive.SU3CharFactor.ofNat_mul_eqv 2 (blockNcut k + 1)

/-- Every physical cutoff length is strictly positive. -/
theorem blockLength_pos (k : Nat) : (0 : Q') < blockLength k := by
  unfold blockLength
  simpa only [Nat.succ_eq_add_one] using Q'.ofNat_succ_pos (blockNcut k)

private theorem quarter_times_four_eqv_one :
    blockQuarter * (Q'.ofNat 2 * Q'.ofNat 2) ≈ (1 : Q') := by
  unfold blockQuarter
  decide

private theorem eighth_times_eight_eqv_one :
    Q'.mkPos 1 8 (by decide) *
        ((Q'.ofNat 2 * Q'.ofNat 2) * Q'.ofNat 2) ≈ (1 : Q') := by
  decide

private theorem six_quarter_square_eqv_three_eighths :
    Q'.ofNat 6 * (blockQuarter * blockQuarter) ≈
      Q'.mkPos 3 8 (by decide) := by
  unfold blockQuarter
  decide

/-- Universal quadratic allowance for the fourth-power fine heat drift. -/
def blockQuadraticDrift (k : Nat) : Q' :=
  Q'.mkPos 3 8 (by decide) * (blockMargin k * blockMargin k)

private theorem blockQuadraticDrift_succ_eqv (k : Nat) :
    blockQuadraticDrift (k + 1) ≈
      blockQuadraticDrift k * Q'.mkPos 1 16 (by decide) := by
  have hm := blockMargin_succ_eqv k
  unfold blockQuadraticDrift
  refine Q'.eqv_trans _
    (Q'.mkPos 3 8 (by decide) *
      ((blockMargin k * blockQuarter) *
        (blockMargin k * blockQuarter))) _
    (Q'.mul_eqv_congr_left _ _ _ (mul_eqv_both hm hm)) ?_
  refine Q'.eqv_trans _
    ((Q'.mkPos 3 8 (by decide) *
        (blockMargin k * blockMargin k)) *
      (blockQuarter * blockQuarter)) _
    (by scale_ring) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (by
    unfold blockQuarter
    decide)

/-- Exact scale-free heat invariant `u_k L_k^2 = 25/12`. -/
theorem blockMargin_mul_length_sq_eqv (k : Nat) :
    blockMargin k * (blockLength k * blockLength k) ≈
      Q'.mkPos 25 12 (by decide) := by
  induction k with
  | zero =>
      unfold blockMargin blockLength blockNcut
      decide
  | succ k ih =>
      have hm := blockMargin_succ_eqv k
      have hL := blockLength_succ_eqv k
      have hL2 := mul_eqv_both hL hL
      refine Q'.eqv_trans _
        ((blockMargin k * blockQuarter) *
          ((Q'.ofNat 2 * blockLength k) *
            (Q'.ofNat 2 * blockLength k))) _
        (mul_eqv_both hm hL2) ?_
      refine Q'.eqv_trans _
        ((blockMargin k * (blockLength k * blockLength k)) *
          (blockQuarter * (Q'.ofNat 2 * Q'.ofNat 2))) _
        (by scale_ring) ?_
      refine Q'.eqv_trans _
        ((blockMargin k * (blockLength k * blockLength k)) * 1) _
        (Q'.mul_eqv_congr_left _ _ _ quarter_times_four_eqv_one) ?_
      exact Q'.eqv_trans _ _ _
        (Q'.mul_one_eqv (blockMargin k * (blockLength k * blockLength k))) ih

/-- Exact scale-free debt invariant `delta_k L_k^3 = 25/72`. -/
theorem blockParityDebt_mul_length_cube_eqv (k : Nat) :
    blockParityDebt k *
        ((blockLength k * blockLength k) * blockLength k) ≈
      Q'.mkPos 25 72 (by decide) := by
  induction k with
  | zero =>
      unfold blockParityDebt blockMargin blockLength blockNcut
      decide
  | succ k ih =>
      have hd := blockParityDebt_succ_eqv k
      have hL := blockLength_succ_eqv k
      have hL2 := mul_eqv_both hL hL
      have hL3 := mul_eqv_both hL2 hL
      refine Q'.eqv_trans _
        ((blockParityDebt k * Q'.mkPos 1 8 (by decide)) *
          (((Q'.ofNat 2 * blockLength k) *
              (Q'.ofNat 2 * blockLength k)) *
            (Q'.ofNat 2 * blockLength k))) _
        (mul_eqv_both hd hL3) ?_
      refine Q'.eqv_trans _
        ((blockParityDebt k *
            ((blockLength k * blockLength k) * blockLength k)) *
          (Q'.mkPos 1 8 (by decide) *
            ((Q'.ofNat 2 * Q'.ofNat 2) * Q'.ofNat 2))) _
        (by scale_ring) ?_
      refine Q'.eqv_trans _
        ((blockParityDebt k *
            ((blockLength k * blockLength k) * blockLength k)) * 1) _
        (Q'.mul_eqv_congr_left _ _ _ eighth_times_eight_eqv_one) ?_
      exact Q'.eqv_trans _ _ _
        (Q'.mul_one_eqv
          (blockParityDebt k *
            ((blockLength k * blockLength k) * blockLength k))) ih

/-- Division-free form of `delta_k = u_k/(6 L_k)`. -/
theorem six_mul_debt_mul_length_eqv_margin (k : Nat) :
    Q'.ofNat 6 * (blockParityDebt k * blockLength k) ≈
      blockMargin k := by
  induction k with
  | zero =>
      unfold blockParityDebt blockMargin blockLength blockNcut
      decide
  | succ k ih =>
      have hd := blockParityDebt_succ_eqv k
      have hL := blockLength_succ_eqv k
      have hm := blockMargin_succ_eqv k
      refine Q'.eqv_trans _
        (Q'.ofNat 6 *
          ((blockParityDebt k * Q'.mkPos 1 8 (by decide)) *
            (Q'.ofNat 2 * blockLength k))) _
        (Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _
          (mul_eqv_both hd hL)) ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat 6 * (blockParityDebt k * blockLength k)) *
          (Q'.mkPos 1 8 (by decide) * Q'.ofNat 2)) _
        (by scale_ring) ?_
      refine Q'.eqv_trans _
        (blockMargin k *
          (Q'.mkPos 1 8 (by decide) * Q'.ofNat 2)) _
        (Q'.mul_eqv_congr_right _ _ _ ih) ?_
      refine Q'.eqv_trans _
        (blockMargin k * blockQuarter) _
        (Q'.mul_eqv_congr_left _ _ _ (by
          unfold blockQuarter
          decide)) ?_
      exact Q'.eqv_symm hm

/-- The heat-drift allowance and parity debt have the same cubic scale after
multiplication by the physical cutoff length.  The fixed ratio `75/16` is the
dimensionless constant left for the normalized path-energy estimate. -/
theorem quadraticDrift_mul_length_eqv_debt (k : Nat) :
    blockQuadraticDrift k * blockLength k ≈
      Q'.mkPos 75 16 (by decide) * blockParityDebt k := by
  induction k with
  | zero =>
      unfold blockQuadraticDrift blockParityDebt blockMargin blockLength
        blockNcut
      decide
  | succ k ih =>
      have hq := blockQuadraticDrift_succ_eqv k
      have hL := blockLength_succ_eqv k
      have hd := blockParityDebt_succ_eqv k
      refine Q'.eqv_trans _
        ((blockQuadraticDrift k * Q'.mkPos 1 16 (by decide)) *
          (Q'.ofNat 2 * blockLength k)) _
        (mul_eqv_both hq hL) ?_
      refine Q'.eqv_trans _
        ((blockQuadraticDrift k * blockLength k) *
          (Q'.mkPos 1 16 (by decide) * Q'.ofNat 2)) _
        (by scale_ring) ?_
      refine Q'.eqv_trans _
        ((Q'.mkPos 75 16 (by decide) * blockParityDebt k) *
          (Q'.mkPos 1 16 (by decide) * Q'.ofNat 2)) _
        (Q'.mul_eqv_congr_right _ _ _ ih) ?_
      refine Q'.eqv_trans _
        (Q'.mkPos 75 16 (by decide) *
          (blockParityDebt k * Q'.mkPos 1 8 (by decide))) _
        (by scale_ring) ?_
      exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hd)

/-- Dimensionless slope constant left by the exact schedule arithmetic. -/
def blockNormalizedSlopeCoeff : Q' := Q'.mkPos 16 75 (by decide)

/-- Exact cancellation of the cutoff-scaled heat drift against the complete
parity debt.  Thus the common-cutoff analytic theorem only has to prove the
uniform dimensionless slope bound `16/75`; no scale-dependent arithmetic is
left in that frontier. -/
theorem normalizedSlopeBudget_eqv_debt (k : Nat) :
    blockNormalizedSlopeCoeff *
        (blockQuadraticDrift k * blockLength k) ≈
      blockParityDebt k := by
  refine Q'.eqv_trans _
    (blockNormalizedSlopeCoeff *
      (Q'.mkPos 75 16 (by decide) * blockParityDebt k)) _
    (Q'.mul_eqv_congr_left blockNormalizedSlopeCoeff _ _
      (quadraticDrift_mul_length_eqv_debt k)) ?_
  refine Q'.eqv_trans _
    ((blockNormalizedSlopeCoeff * Q'.mkPos 75 16 (by decide)) *
      blockParityDebt k) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    ((1 : Q') * blockParityDebt k) _
    (Q'.mul_eqv_congr_right _ _ _ (by
      unfold blockNormalizedSlopeCoeff
      decide)) ?_
  exact Q'.one_mul_eqv _

/-- Scale-free form of the honest normalized tail.  The difficult coarse
comparison is now a fixed `16/75` path-slope estimate; the fine field is the
separate dyadic even/odd reserve.  This structure is deliberately not an
instance: both analytic fields still have to be proved. -/
structure BlockCompatibleP2DimensionlessNormalizedTailFromSeven : Type where
  coarseSlope : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    coefficientDeficitRatio w4 (blockNcut k)
        (qpow_nonneg _ (blockWeight_nonneg (k + 1)) 4) <=
      coefficientDeficitRatio (blockWeight k) (blockNcut k)
          (blockWeight_nonneg k) +
        blockNormalizedSlopeCoeff *
          (blockQuadraticDrift k * blockLength k)
  fineReserve : forall k, 7 <= k ->
    let w4 := qpow (blockWeight (k + 1)) 4
    Q'.ofNat 2 *
          coefficientDeficitRatio (blockWeight (k + 1)) (blockNcut (k + 1))
            (blockWeight_nonneg (k + 1)) + blockParityDebt k <=
      coefficientDeficitRatio w4 (blockNcut k)
        (qpow_nonneg _ (blockWeight_nonneg (k + 1)) 4)

/-- The exact schedule identity compiles the dimensionless pair of analytic
atoms to the normalized tail consumed by the checked finite prefix. -/
def BlockCompatibleP2DimensionlessNormalizedTailFromSeven.toNormalizedTail
    (T : BlockCompatibleP2DimensionlessNormalizedTailFromSeven) :
    BlockCompatibleP2NormalizedDeficitTailFromSeven where
  coarse := fun k hk => by
    let R0 := coefficientDeficitRatio (blockWeight k) (blockNcut k)
      (blockWeight_nonneg k)
    have h := T.coarseSlope k hk
    have hbudget := normalizedSlopeBudget_eqv_debt k
    exact Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv
        (Q'.add_eqv_congr_left R0 _ _ hbudget))
  fine := fun k hk => T.fineReserve k hk

/-- Constant-size quadratic enclosure for the fourth-power heat drift.

This is the symbolic replacement for evaluating the fourth power separately
at every cutoff: alternating Taylor gives the coefficient `6`, while the
quarter schedule converts `6 u_(k+1)^2` exactly to `(3/8) u_k^2`. -/
theorem fineFourth_le_coarse_add_quadratic (k : Nat) :
    qpow (blockWeight (k + 1)) 4 <=
      blockWeight k + blockQuadraticDrift k := by
  let u := blockMargin k
  let v := blockMargin (k + 1)
  have htaylor := qpow_oneSub_le_taylor2
    (blockMargin_nonneg (k + 1)) (blockMargin_le_one (k + 1)) 4
  have htaylor' : qpow (blockWeight (k + 1)) 4 <=
      oneSubTaylor2 v 4 := by
    simpa only [blockWeight, v] using htaylor
  have hlinear :
      (1 : Q') + -(Q'.ofNat 4 * v) ≈ blockWeight k := by
    simpa only [v] using
      one_sub_four_mul_blockMargin_succ_eqv k
  have hv := blockMargin_succ_eqv k
  have hv2 : v * v ≈
      (u * blockQuarter) * (u * blockQuarter) := by
    exact mul_eqv_both (by simpa only [u, v] using hv)
      (by simpa only [u, v] using hv)
  have hquadratic : Q'.ofNat 6 * (v * v) ≈
      Q'.mkPos 3 8 (by decide) * (u * u) := by
    refine Q'.eqv_trans _
      (Q'.ofNat 6 *
        ((u * blockQuarter) * (u * blockQuarter))) _
      (Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _ hv2) ?_
    refine Q'.eqv_trans _
      ((Q'.ofNat 6 * (blockQuarter * blockQuarter)) * (u * u)) _
      (by scale_ring) ?_
    exact Q'.mul_eqv_congr_right _ _ (u * u)
      six_quarter_square_eqv_three_eighths
  have henclosure : oneSubTaylor2 v 4 ≈
      blockWeight k + blockQuadraticDrift k := by
    change (((1 : Q') + -(Q'.ofNat 4 * v)) +
      Q'.ofNat 6 * (v * v)) ≈
        blockWeight k +
          Q'.mkPos 3 8 (by decide) * (blockMargin k * blockMargin k)
    exact Q'.add_eqv_congr' hlinear
      (by simpa only [u] using hquadratic)
  exact Q'.le_trans' _ _ _ htaylor' (Q'.le_of_eqv henclosure)

#print axioms blockLength_succ_eqv
#print axioms blockLength_pos
#print axioms blockMargin_mul_length_sq_eqv
#print axioms blockParityDebt_mul_length_cube_eqv
#print axioms six_mul_debt_mul_length_eqv_margin
#print axioms quadraticDrift_mul_length_eqv_debt
#print axioms normalizedSlopeBudget_eqv_debt
#print axioms BlockCompatibleP2DimensionlessNormalizedTailFromSeven.toNormalizedTail
#print axioms fineFourth_le_coarse_add_quadratic

end YMGap.Continuum.P2BlockCompatibleThetaScaleInvariant
