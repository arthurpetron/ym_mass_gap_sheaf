/-
# Survival calibration on the same fixed-width joint completion

A supplied positive sampled response and norm ceiling constrain the certified
two-step rate of the actual all-nome fixed-width joint completion.  The sample
floor remains an explicit input; no changing-width identification or survival
producer is asserted.

Here `A.spacing` calibrates one application of the certified TWO-step rate,
because the sampled response is evaluated at physical time `2*floor(t/a)`.
The logarithmic scalar below is only the exact rate logarithm per supplied
two-step spacing; it is not identified with a Hamiltonian or spectral edge.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation
import YMGap.Continuum.PhysicalSamplingSurvivalMargin
import YMGap.Continuum.PhysicalSeparationSamplingEscape
import YMGap.Continuum.DirectLogMarginUpper

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero (floorLatticeSteps)
open YMGap.Continuum.PhysicalSeparationSamplingEscape
open YMGap.Continuum.PhysicalSamplingSurvivalMargin
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation (time_norm_decay)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse
  (completedInner_even_diagonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative twoStepRate_lt_one)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width
local infix:50 " ≈ " => Q'.eqv

/-- The rational response comparison on this same fixed-width carrier. -/
theorem response_power_floor (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (n : Nat) (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*n) x))) : floor ≤ q^n * C := by
  have hdiag : B x (T (2*n) x) = B (T n x) (T n x) := by
    exact (completedInner_even_diagonal hw0 hw1 width n x).symm
  have h := RCle_trans (time_norm_decay hw0 hw1 width x hx n)
    (RCscale_mono (Q'.pow_nonneg q (twoStepRate_nonnegative hw0 hw1 width) n) hcap)
  rw [hdiag] at hresponse
  exact GNSQuotient.GNSData.RCofQ'_le_reflect (RCle_trans hresponse h)

theorem margin_le_of_sampled_response (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (j t : Nat) (ht : 0 < t)
    (ha : A.spacing j ≤ HalfPow.half * Q'.ofNat t)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*floorLatticeSteps A j t) x))) :
    1 + -q ≤ A.spacing j * responseMarginCeiling C floor hf t ht :=
  margin_le_spacing_mul_ceiling (twoStepRate_nonnegative hw0 hw1 width)
    (Q'.le_of_lt (twoStepRate_lt_one hw0 hw1 width)) hC hf A j t ht ha
    (response_power_floor hw0 hw1 width x hx C floor hcap _ hresponse)

theorem marginRate_le_of_sampled_response (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (j t : Nat) (ht : 0 < t)
    (ha : A.spacing j ≤ HalfPow.half * Q'.ofNat t)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*floorLatticeSteps A j t) x))) :
    Q'.divPos (1 + -q) (A.spacing j) (A.spacing_pos j) ≤
      responseMarginCeiling C floor hf t ht :=
  marginRate_le_ceiling (twoStepRate_nonnegative hw0 hw1 width)
    (Q'.le_of_lt (twoStepRate_lt_one hw0 hw1 width)) hC hf A j t ht ha
    (response_power_floor hw0 hw1 width x hx C floor hcap _ hresponse)

private theorem rate_num_lt_den : (q).num < ((q).den : Int) := by
  have h := twoStepRate_lt_one hw0 hw1 width
  change (q).num * (1 : Int) < (1 : Int) * ((q).den : Int) at h
  simpa only [Int.mul_one, Int.one_mul] using h

def rateBinary (hq : (0 : Q') < q) : BinExpData q :=
  binExpOf q (Q'.num_pos_of_pos hq) (rate_num_lt_den hw0 hw1 width)

def transferLogRate (hq : (0 : Q') < q) : CReal :=
  hamiltonianGapRealAll (mant q (rateBinary hw0 hw1 width hq).k)
    (rateBinary hw0 hw1 width hq).k
    (mant_pos q _ (Q'.num_pos_of_pos hq))
    (mant_window q (rateBinary hw0 hw1 width hq) (Q'.num_pos_of_pos hq))

def transferLogReduction (hq : (0 : Q') < q) : CRealLogRangeReduction (ofQ' q) :=
  reductionOf q (rateBinary hw0 hw1 width hq) (Q'.num_pos_of_pos hq)

theorem transferLogRate_log_pin (hq : (0 : Q') < q) :
    Equiv (transferLogRate hw0 hw1 width hq)
      (CReal.neg (CReal.log (ofQ' q) (transferLogReduction hw0 hw1 width hq))) := by
  unfold transferLogRate transferLogReduction CReal.log reductionOf
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  exact add_neg_eqv_neg_neg_add
    ((kLog2 (rateBinary hw0 hw1 width hq).k).approx n)
    ((logRat (mant q (rateBinary hw0 hw1 width hq).k) _ _).approx n)

def sampledLogRate (hq : (0 : Q') < q) (A : PhysicalSpacing) (j : Nat) : CReal :=
  CReal.mul (ofQ' (Q'.recipPos (A.spacing j) (A.spacing_pos j)))
    (transferLogRate hw0 hw1 width hq)

def survivalRateThreshold {A : PhysicalSpacing} (Z : SpacingToZero A)
    (C floor : Q') (t : Nat) : Nat :=
  max (Z.modulus (HalfPow.half * Q'.ofNat t))
    (stepEscapeModulus A Z t
      (geometricCutoff HalfPow.half C (HalfPow.half * floor)))

theorem halfRate_of_sampled_response (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (j t : Nat) (ht : 0 < t)
    (hj : survivalRateThreshold Z C floor t ≤ j)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*floorLatticeSteps A j t) x))) : HalfPow.half ≤ q := by
  apply Int.le_of_not_gt
  intro hqhalf
  let n := floorLatticeSteps A j t
  have hn : geometricCutoff HalfPow.half C (HalfPow.half*floor) ≤ n :=
    floorLatticeSteps_ge_stepEscapeModulus A Z ht
      (Nat.le_trans (Nat.le_max_right _ _) hj)
  have hgeom : HalfPow.half^n*C ≤ HalfPow.half*floor :=
    geometric_bound (by decide) (by decide) hC
      (ExpNeg.half_mul_pos floor hf) n hn
  have hp : q^n ≤ HalfPow.half^n :=
    pow_le_pow_base q HalfPow.half (twoStepRate_nonnegative hw0 hw1 width)
      (Q'.le_of_lt hqhalf) n
  have hfloor := response_power_floor hw0 hw1 width x hx C floor hcap n hresponse
  have hbad : floor ≤ HalfPow.half*floor :=
    Q'.le_trans' _ _ _ hfloor
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ C hp hC) hgeom)
  have hstrict : HalfPow.half*floor < floor :=
    ClusteringImpliesGap.lt_of_lt_of_le
      (ClusteringImpliesGap.mul_lt_mul_of_pos_right hf
        (by decide : HalfPow.half < (1 : Q')))
      (Q'.le_of_eqv (Q'.one_mul_eqv floor))
  exact Int.not_lt.mpr hbad hstrict

def responseLogCeiling (C floor : Q') (hf : (0 : Q') < floor)
    (t : Nat) (ht : 0 < t) : Q' :=
  EffMassConvergence.c94 * responseMarginCeiling C floor hf t ht

theorem logRate_le_of_sampled_response (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (j t : Nat) (ht : 0 < t)
    (hj : survivalRateThreshold Z C floor t ≤ j)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*floorLatticeSteps A j t) x))) :
    let hq : (0 : Q') < q := ClusteringImpliesGap.lt_of_lt_of_le (by decide)
      (halfRate_of_sampled_response hw0 hw1 width x hx C floor hC hf hcap A Z j t ht hj hresponse)
    leEv (sampledLogRate hw0 hw1 width hq A j)
      (ofQ' (responseLogCeiling C floor hf t ht)) := by
  let hhalf := halfRate_of_sampled_response hw0 hw1 width x hx C floor hC hf
    hcap A Z j t ht hj hresponse
  let hq : (0 : Q') < q := ClusteringImpliesGap.lt_of_lt_of_le (by decide) hhalf
  have ha := Z.spacing_le (HalfPow.half * Q'.ofNat t)
    (ExpNeg.half_mul_pos _ (positive_physical_time ht)) j
    (Nat.le_trans (Nat.le_max_left _ _) hj)
  have hmargin := marginRate_le_of_sampled_response hw0 hw1 width x hx C floor
    hC hf hcap A j t ht ha hresponse
  have hlog : leEv (transferLogRate hw0 hw1 width hq)
      (ofQ' (EffMassConvergence.c94 * (1 + -q))) :=
    DirectLogMarginUpper.binaryMass_le_c94_margin q
      (Q'.num_pos_of_pos hq) (rate_num_lt_den hw0 hw1 width) hhalf
  have hscaled := leEv_smul_nonneg
    (Q'.le_of_lt (Q'.recipPos_pos (A.spacing j) (A.spacing_pos j))) hlog
  apply leEv_trans hscaled
  apply leEv_le_ofQ'_of_approx_le
  intro n
  change Q'.recipPos (A.spacing j) (A.spacing_pos j) *
    (EffMassConvergence.c94 * (1 + -q)) ≤ responseLogCeiling C floor hf t ht
  let r := Q'.recipPos (A.spacing j) (A.spacing_pos j)
  let d := (1 : Q') + -q
  have he : (r * (EffMassConvergence.c94 * d)).eqv
      (EffMassConvergence.c94 * (d * r)) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 2) (.var 0)))
      (by decide) (fun | 0 => r | 1 => EffMassConvergence.c94 | _ => d)
  change Q'.recipPos (A.spacing j) (A.spacing_pos j) *
      (EffMassConvergence.c94 * (1 + -q)) ≈
    EffMassConvergence.c94 *
      ((1 + -q) * Q'.recipPos (A.spacing j) (A.spacing_pos j)) at he
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hmargin (by decide))

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration.response_power_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration.margin_le_of_sampled_response
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration.marginRate_le_of_sampled_response
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration.transferLogRate_log_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration.halfRate_of_sampled_response
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointSurvivalCalibration.logRate_le_of_sampled_response
