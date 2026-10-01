/-
# Zero-shift resolvent limit on the original witnessed vacuum complement

The positive-shift resolvent identity supplies a uniform parameter modulus
on the same fixed-nome, fixed-width completion.  We evaluate it on the
explicit halving schedule and use the input's supplied original Cauchy
representative for a rational norm ceiling.  The resulting sector limit
retains its original time-range witness and an explicit convergence rate.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorResolventContinuity
import YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
import YMGap.Continuum.BF4WilsonAllNomeTimeSector
import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
import YMGap.Constructive.ExpNeg

namespace YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Constructive.ExpNeg (pow_half_antitone)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State CauchySequence)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolvent (state state_pin)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap
  (state_orthogonal uniform_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolventContinuity (parameter_bound)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin coreMargin_positive)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "P" => pairingData hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "dist" => completedDist hw0 hw1
local notation "Sector" => State hw0 hw1 (width := width)
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- A positive parameter which converges to zero with an explicit modulus. -/
def parameter (depth : Nat) : Q' := half^(depth+1)

theorem parameter_positive (depth : Nat) : (0 : Q') < parameter depth :=
  BF4WilsonAllNomeDyadicResolvent.dyadicStep_positive (depth+1)

private theorem parameter_le_power {start depth : Nat} (h : start ≤ depth) :
    parameter depth ≤ half^start := by
  unfold parameter
  have hs : start + (depth+1-start) = depth+1 := Nat.add_sub_of_le (by omega)
  rw [← hs]
  exact pow_half_antitone start (depth+1-start)

private theorem square_le_of_abs_le {a A : Q'} (hA : (0 : Q') ≤ A)
    (ha : Q'.abs a ≤ A) : a*a ≤ A*A :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_mul_self_eqv a))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg a))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ ha hA))

private theorem parameter_difference_square {start m n : Nat}
    (hm : start ≤ m) (hn : start ≤ n) :
    (parameter n-parameter m)*(parameter n-parameter m) ≤
      (half^start)*(half^start) := by
  let h := half^start
  have hh : (0 : Q') ≤ h := Q'.pow_nonneg half half_nonneg start
  have hm0 : (0 : Q') ≤ parameter m := Q'.le_of_lt (parameter_positive m)
  have hn0 : (0 : Q') ≤ parameter n := Q'.le_of_lt (parameter_positive n)
  have hmh : parameter m ≤ h := parameter_le_power hm
  have hnh : parameter n ≤ h := parameter_le_power hn
  have hnm : parameter n ≤ parameter m + h :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm
      (QPoly.q_zero_add_eqv _))) (ExpNeg.add_le_add2 hm0 hnh)
  have hmn : parameter m ≤ parameter n + h :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm
      (QPoly.q_zero_add_eqv _))) (ExpNeg.add_le_add2 hn0 hmh)
  have ha : Q'.abs (parameter n + -(parameter m)) ≤ h :=
    CReal.abs_sub_le_of_bounds hnm hmn
  exact square_le_of_abs_le hh ha

/-- The supplied original representative gives a rational bound on the
parameter-Lipschitz coefficient times its actual squared norm. -/
def normCap (x : Sector) : Q' :=
  let r := Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1)
  (r*r)*(r*r)*normCeiling P (representative hw0 hw1 x.range)

theorem normCap_nonnegative (x : Sector) : (0 : Q') ≤ normCap hw0 hw1 x := by
  unfold normCap
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (SumOfSquares.q_mul_self_nonneg _) (SumOfSquares.q_mul_self_nonneg _))
    (normCeiling_nonnegative P (representative hw0 hw1 x.range))

def modulus (x : Sector) (epsilon : Q') : Nat :=
  (linearTolerance (normCap hw0 hw1 x) (normCap_nonnegative hw0 hw1 x) epsilon).den

/-- Every sufficiently deep original positive-shift pair is close in the
same completed squared distance. -/
theorem parameter_cauchy (x : Sector) (hx : B U x.val = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (m n : Nat)
    (hm : modulus hw0 hw1 x epsilon ≤ m)
    (hn : modulus hw0 hw1 x epsilon ≤ n) :
    RCle (dist (state hw0 hw1 (parameter m) (parameter_positive m) x).val
      (state hw0 hw1 (parameter n) (parameter_positive n) x).val)
      (rat epsilon) := by
  let cap := normCap hw0 hw1 x
  let delta := linearTolerance cap (normCap_nonnegative hw0 hw1 x) epsilon
  let k := modulus hw0 hw1 x epsilon
  let h := half^k
  let r := Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1)
  let X := representative hw0 hw1 x.range
  have hh0 : (0 : Q') ≤ h := Q'.pow_nonneg half half_nonneg k
  have hh1 : h ≤ 1 := HKPos.pow_le_one half_nonneg (by decide) k
  have hh2 : h*h ≤ h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hh1 hh0)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hdelta : (0 : Q') < delta :=
    linearTolerance_pos cap (normCap_nonnegative hw0 hw1 x) he
  have hpow : h ≤ delta := Q'.le_trans' _ _ _ (pow_half_le_invSucc k)
    (invSucc_den_le delta hdelta)
  have hsmall : h*cap ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ cap hpow (normCap_nonnegative hw0 hw1 x))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (linearTolerance_budget cap (normCap_nonnegative hw0 hw1 x) he))
  have hdiff := parameter_difference_square hm hn
  have hr0 : (0 : Q') ≤ r*r := SumOfSquares.q_mul_self_nonneg r
  have hcoeff :
      (((parameter n-parameter m)*(parameter n-parameter m)*(r*r))*(r*r)) ≤
        ((h*h)*(r*r))*(r*r) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hdiff hr0) hr0
  have hcoeff0 : (0 : Q') ≤
      (((parameter n-parameter m)*(parameter n-parameter m)*(r*r))*(r*r)) :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _) hr0) hr0
  have hraw := parameter_bound hw0 hw1
    (parameter m) (parameter n) (parameter_positive m) (parameter_positive n) x hx
  have hnorm : RCle (B x.val x.val)
      (rat (normCeiling P X)) := by
    rw [← representative_pin hw0 hw1 x.range]
    exact completedInner_diagonal_le_normCeiling P X
  have hcap := RCle_trans hraw (RCscale_mono hcoeff0 hnorm)
  have hcap' : RCle (dist (state hw0 hw1 (parameter m) (parameter_positive m) x).val
      (state hw0 hw1 (parameter n) (parameter_positive n) x).val)
      (rat (((parameter n-parameter m)*(parameter n-parameter m)*(r*r))*(r*r) *
        normCeiling P X)) := by
    have hs : RCscale
        (((parameter n-parameter m)*(parameter n-parameter m)*(r*r))*(r*r))
        (rat (normCeiling P X)) =
        rat ((((parameter n-parameter m)*(parameter n-parameter m)*(r*r))*(r*r)) *
          normCeiling P X) :=
      Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
    rw [hs] at hcap
    exact hcap
  have hbudget :
      (((parameter n-parameter m)*(parameter n-parameter m)*(r*r))*(r*r) *
        normCeiling P X) ≤ epsilon := by
    have ha := Q'.mul_le_mul_of_nonneg_right _ _ _ hcoeff
      (normCeiling_nonnegative P X)
    have hb : (((h*h)*(r*r))*(r*r))*normCeiling P X ≤ h*cap := by
      have hc : ((h*h)*(r*r))*(r*r)*normCeiling P X ≤
          (h*(r*r))*(r*r)*normCeiling P X :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ _
            (Q'.mul_le_mul_of_nonneg_right _ _ _ hh2 hr0) hr0)
          (normCeiling_nonnegative P X)
      exact Q'.le_trans' _ _ _ hc (Q'.le_of_eqv
        (poly_identity_of_normal_eq
          (.mul (.mul (.mul (.var 0) (.var 1)) (.var 1)) (.var 2))
          (.mul (.var 0) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
          (by decide) (fun | 0 => h | 1 => r*r | _ => normCeiling P X)))
    exact Q'.le_trans' _ _ _ ha (Q'.le_trans' _ _ _ hb hsmall)
  exact RCle_trans hcap' (leEv_le_ofQ'_of_approx_le (fun _ => hbudget))

/-- Constructive sector-valued sequence, with all rows and their range
witnesses computed from the original positive-shift resolvent. -/
def rows (x : Sector) (hx : B U x.val = RCzero) :
    CauchySequence hw0 hw1 (width := width) where
  seq := fun depth => state hw0 hw1 (parameter depth) (parameter_positive depth) x
  modulus := modulus hw0 hw1 x
  bound := parameter_cauchy hw0 hw1 x hx

/-- Actual represented zero-shift limit in the unchanged original sector. -/
def zeroShift (x : Sector) (hx : B U x.val = RCzero) : Sector :=
  BF4WilsonAllNomeTimeSector.limit hw0 hw1 (rows hw0 hw1 x hx)

def zeroShiftRate (x : Sector) (hx : B U x.val = RCzero) : Q' → Nat :=
  BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (rows hw0 hw1 x hx)

theorem zeroShift_bound (x : Sector) (hx : B U x.val = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (depth : Nat)
    (hd : zeroShiftRate hw0 hw1 x hx epsilon ≤ depth) :
    RCle (dist (state hw0 hw1 (parameter depth) (parameter_positive depth) x).val
      (zeroShift hw0 hw1 x hx).val) (rat epsilon) :=
  BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1 (rows hw0 hw1 x hx)
    epsilon he depth hd

/-- The represented zero-shift limit stays in the same vacuum complement. -/
theorem zeroShift_orthogonal (x : Sector) (hx : B U x.val = RCzero) :
    B U (zeroShift hw0 hw1 x hx).val = RCzero := by
  apply BF4WilsonAllNomeCauchyRows.limit_orthogonal hw0 hw1
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1 (rows hw0 hw1 x hx))
  intro n
  rw [BF4WilsonAllNomeTimeSector.representedRows_point]
  exact state_orthogonal hw0 hw1 (parameter n) (parameter_positive n) x hx

/-- The shift-independent fixed-sector squared norm cap survives the
original represented limit. -/
theorem zeroShift_norm_bound (x : Sector) (hx : B U x.val = RCzero) :
    let r := Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1)
    RCle (B (zeroShift hw0 hw1 x hx).val (zeroShift hw0 hw1 x hx).val)
      (RCscale (r*r) (B x.val x.val)) := by
  apply BF4WilsonAllNomeRowPairingLimit.rowLimit_norm_bound hw0 hw1
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1 (rows hw0 hw1 x hx))
  intro n
  rw [BF4WilsonAllNomeTimeSector.representedRows_point]
  exact uniform_norm_bound hw0 hw1 (parameter n) (parameter_positive n) x hx

end YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit

#print axioms YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit.parameter_cauchy
#print axioms YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit.rows
#print axioms YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit.zeroShift
#print axioms YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit.zeroShift_bound
#print axioms YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit.zeroShift_orthogonal
#print axioms YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit.zeroShift_norm_bound
