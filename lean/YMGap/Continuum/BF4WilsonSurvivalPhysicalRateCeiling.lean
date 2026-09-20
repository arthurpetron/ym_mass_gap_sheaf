/-
# Original Wilson survival supplies a finite logarithmic rate ceiling

For the actual centered Wilson vector, a positive response at a fixed sampled
physical time and a rational squared-norm cap imply a linear spacing bound on
the ACTUAL certified two-step margin. Multiplicative Bernoulli supplies the
quantitative constant; no margin or physical-rate ceiling is assumed.

The exact binary logarithm of that same certified rate, divided by the supplied
two-step physical spacing, is then bounded by (9/4)*2*C/(f*t) on an explicitly
computed tail. The rate is not identified with the exact spectral radius.
The required positive-time survival and changing-coupling family remain open;
no uniform positive mass floor, continuum theory or Clay closure is asserted.
-/

import YMGap.Continuum.BF4WilsonUniformLatticeRateScalingObstruction
import YMGap.Continuum.PhysicalSamplingSurvivalMargin
import YMGap.Continuum.DirectLogMarginUpper

namespace YMGap.Continuum.BF4WilsonSurvivalPhysicalRateCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero (floorLatticeSteps)
open YMGap.Continuum.PhysicalSamplingSurvivalMargin
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation (even_autocorrelation_decay)
open YMGap.Continuum.BF4WilsonUniformLatticeRateScalingObstruction
  (physicalDecayModulus rate_gt_of_response_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "q" => twoStepRate w hd

/-- The rational comparison follows from the SAME original completed pairing. -/
theorem response_power_floor (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (n : Nat) (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor)) (B x (T (2*n) x))) :
    floor ≤ q^n * C := by
  have h := RCle_trans (even_autocorrelation_decay hw0 hw1 hsmall hd hs x hx n)
    (RCscale_mono (Q'.pow_nonneg q (Q'.le_of_lt (twoStepRate_positive hw0 hd)) n) hcap)
  exact GNSQuotient.GNSData.RCofQ'_le_reflect (RCle_trans hresponse h)

/-- Positive-time survival forces an O(spacing) defect in the certified original rate. -/
theorem margin_le_of_sampled_response (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (j t : Nat) (ht : 0 < t)
    (ha : A.spacing j ≤ HalfPow.half * Q'.ofNat t)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*floorLatticeSteps A j t) x))) :
    1 + -q ≤ A.spacing j * responseMarginCeiling C floor hf t ht :=
  margin_le_spacing_mul_ceiling (Q'.le_of_lt (twoStepRate_positive hw0 hd))
    (Q'.le_of_lt (twoStepRate_lt_one hw0 hd hs)) hC hf A j t ht ha
    (response_power_floor hw0 hw1 hsmall hd hs x hx C floor hcap _ hresponse)

theorem marginRate_le_of_sampled_response (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (j t : Nat) (ht : 0 < t)
    (ha : A.spacing j ≤ HalfPow.half * Q'.ofNat t)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*floorLatticeSteps A j t) x))) :
    Q'.divPos (1 + -q) (A.spacing j) (A.spacing_pos j) ≤
      responseMarginCeiling C floor hf t ht :=
  marginRate_le_ceiling (Q'.le_of_lt (twoStepRate_positive hw0 hd))
    (Q'.le_of_lt (twoStepRate_lt_one hw0 hd hs)) hC hf A j t ht ha
    (response_power_floor hw0 hw1 hsmall hd hs x hx C floor hcap _ hresponse)

include hw0 hs in
private theorem rate_num_lt_den : (q).num < ((q).den : Int) := by
  have h := twoStepRate_lt_one hw0 hd hs
  change (q).num * (1 : Int) < (1 : Int) * ((q).den : Int) at h
  simpa only [Int.mul_one, Int.one_mul] using h

/-- Binary reduction of the certified original two-step rate, for every admissible nome. -/
def rateBinary : BinExpData q :=
  binExpOf q (Q'.num_pos_of_pos (twoStepRate_positive hw0 hd)) (rate_num_lt_den hw0 hd hs)

/-- Exact -log(q) of the certified original rate; not an equality with a spectral edge. -/
def transferLogMass : CReal :=
  hamiltonianGapRealAll (mant q (rateBinary hw0 hd hs).k) (rateBinary hw0 hd hs).k
    (mant_pos q _ (Q'.num_pos_of_pos (twoStepRate_positive hw0 hd)))
    (mant_window q (rateBinary hw0 hd hs) (Q'.num_pos_of_pos (twoStepRate_positive hw0 hd)))

def transferLogReduction : CRealLogRangeReduction (ofQ' q) :=
  reductionOf q (rateBinary hw0 hd hs) (Q'.num_pos_of_pos (twoStepRate_positive hw0 hd))

theorem transferLogMass_log_pin :
    Equiv (transferLogMass hw0 hd hs)
      (CReal.neg (CReal.log (ofQ' q) (transferLogReduction hw0 hd hs))) := by
  unfold transferLogMass transferLogReduction CReal.log reductionOf
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  exact add_neg_eqv_neg_neg_add
    ((kLog2 (rateBinary hw0 hd hs).k).approx n)
    ((logRat (mant q (rateBinary hw0 hd hs).k) _ _).approx n)

/-- The exact certified logarithmic exponent per supplied TWO-step physical spacing. -/
def sampledLogRate (A : PhysicalSpacing) (j : Nat) : CReal :=
  CReal.mul (ofQ' (Q'.recipPos (A.spacing j) (A.spacing_pos j))) (transferLogMass hw0 hd hs)

/-- Explicit scale threshold for both the half-time sampler and the half-window rate. -/
def survivalRateThreshold {A : PhysicalSpacing} (Z : SpacingToZero A)
    (C floor : Q') (t : Nat) : Nat :=
  max (Z.modulus (HalfPow.half * Q'.ofNat t))
    (physicalDecayModulus Z HalfPow.half C t (HalfPow.half * floor))

/-- The computed tail threshold and response force q into the direct logarithm window. -/
theorem halfRate_of_sampled_response (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (j t : Nat) (ht : 0 < t)
    (hj : survivalRateThreshold Z C floor t ≤ j)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*floorLatticeSteps A j t) x))) :
    HalfPow.half ≤ q :=
  Q'.le_of_lt (rate_gt_of_response_floor
    (fun _ => hw0) (fun _ => hw1) (fun _ => hsmall) (fun _ => hd) (fun _ => hs)
    (fun _ => x) A Z t ht HalfPow.half C floor (by decide) (by decide) hC hf j
    (Nat.le_trans (Nat.le_max_right _ _) hj) hx hcap hresponse)

/-- Computed finite ceiling, depending only on norm cap, response floor and physical time. -/
def responseLogCeiling (C floor : Q') (hf : (0 : Q') < floor) (t : Nat) (ht : 0 < t) : Q' :=
  EffMassConvergence.c94 * responseMarginCeiling C floor hf t ht

/-- Observable survival DERIVES the finite ceiling for the same rate's exact logarithm.
Only the norm/response bounds are required at j; using common C,f across a family makes
the displayed ceiling uniform. No across-family survival bound is asserted. -/
theorem logRate_le_of_sampled_response (x : V) (hx : B x U = RCzero)
    (C floor : Q') (hC : (0 : Q') ≤ C) (hf : (0 : Q') < floor)
    (hcap : RCle (B x x) (Quotient.mk crealSetoid (ofQ' C)))
    (A : PhysicalSpacing) (Z : SpacingToZero A) (j t : Nat) (ht : 0 < t)
    (hj : survivalRateThreshold Z C floor t ≤ j)
    (hresponse : RCle (Quotient.mk crealSetoid (ofQ' floor))
      (B x (T (2*floorLatticeSteps A j t) x))) :
    leEv (sampledLogRate hw0 hd hs A j) (ofQ' (responseLogCeiling C floor hf t ht)) := by
  have hhalf := halfRate_of_sampled_response hw0 hw1 hsmall hd hs x hx C floor hC hf
    hcap A Z j t ht hj hresponse
  have ha := Z.spacing_le (HalfPow.half * Q'.ofNat t)
    (ExpNeg.half_mul_pos _ (positive_physical_time ht)) j
    (Nat.le_trans (Nat.le_max_left _ _) hj)
  have hmargin := marginRate_le_of_sampled_response hw0 hw1 hsmall hd hs x hx C floor
    hC hf hcap A j t ht ha hresponse
  have hlog : leEv (transferLogMass hw0 hd hs)
      (ofQ' (EffMassConvergence.c94 * (1 + -q))) :=
    DirectLogMarginUpper.binaryMass_le_c94_margin q
      (Q'.num_pos_of_pos (twoStepRate_positive hw0 hd)) (rate_num_lt_den hw0 hd hs) hhalf
  have hscaled := leEv_smul_nonneg
    (Q'.le_of_lt (Q'.recipPos_pos (A.spacing j) (A.spacing_pos j))) hlog
  apply leEv_trans hscaled
  apply leEv_le_ofQ'_of_approx_le
  intro n
  change Q'.recipPos (A.spacing j) (A.spacing_pos j) *
    (EffMassConvergence.c94 * (1 + -q)) ≤ responseLogCeiling C floor hf t ht
  have he : (Q'.recipPos (A.spacing j) (A.spacing_pos j) *
      (EffMassConvergence.c94 * (1 + -q))).eqv
      (EffMassConvergence.c94 * Q'.divPos (1 + -q) (A.spacing j) (A.spacing_pos j)) := by
    unfold Q'.divPos
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hmargin (by decide : (0 : Q') ≤ EffMassConvergence.c94))

#print axioms response_power_floor
#print axioms margin_le_of_sampled_response
#print axioms marginRate_le_of_sampled_response
#print axioms rateBinary
#print axioms transferLogMass
#print axioms transferLogReduction
#print axioms transferLogMass_log_pin
#print axioms sampledLogRate
#print axioms survivalRateThreshold
#print axioms halfRate_of_sampled_response
#print axioms responseLogCeiling
#print axioms logRate_le_of_sampled_response

end YMGap.Continuum.BF4WilsonSurvivalPhysicalRateCeiling
