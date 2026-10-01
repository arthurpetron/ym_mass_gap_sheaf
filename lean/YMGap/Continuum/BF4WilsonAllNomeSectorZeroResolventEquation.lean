/-
The zero-shift limit solves the original derivative equation.  The argument
uses the full-carrier Lipschitz estimate for the original derivative, the
positive-shift equation, and the fixed-sector uniform norm estimate.  The
output is the *supplied* original sector vector, not a selected preimage.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit
import YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation

namespace YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventEquation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow
open YMGap.Constructive.ExpNeg (pow_half_antitone)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows (completedDist_time)
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDerivativeCore (derivativeAction_dist_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation (sub_error)
open YMGap.Continuum.BF4WilsonAllNomeResolventEquation (resolvent_equation)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolvent (state state_pin)
open YMGap.Continuum.BF4WilsonAllNomeSectorResolventGap (uniform_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit
  (parameter parameter_positive zeroShift zeroShiftRate zeroShift_bound)
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap (coreMargin coreMargin_positive)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "P" => pairingData hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Sector" => State hw0 hw1 (width := width)
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private def shiftCap (x : Sector) : Q' :=
  let r := Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1)
  (r*r)*normCeiling P (representative hw0 hw1 x.range)

private theorem shiftCap_nonnegative (x : Sector) :
    (0 : Q') ≤ shiftCap hw0 hw1 x :=
  Q'.mul_nonneg _ _ (SumOfSquares.q_mul_self_nonneg _)
    (normCeiling_nonnegative P (representative hw0 hw1 x.range))

private def shiftRate (x : Sector) (epsilon : Q') : Nat :=
  (linearTolerance (shiftCap hw0 hw1 x) (shiftCap_nonnegative hw0 hw1 x) epsilon).den

private theorem parameter_small (x : Sector) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : shiftRate hw0 hw1 x epsilon ≤ n) :
    parameter n ≤ linearTolerance (shiftCap hw0 hw1 x)
      (shiftCap_nonnegative hw0 hw1 x) epsilon := by
  let cap := shiftCap hw0 hw1 x
  let delta := linearTolerance cap (shiftCap_nonnegative hw0 hw1 x) epsilon
  have hsmall : half^(n+1) ≤ half^(shiftRate hw0 hw1 x epsilon) := by
    have hnat : shiftRate hw0 hw1 x epsilon +
        (n+1-shiftRate hw0 hw1 x epsilon) = n+1 := Nat.add_sub_of_le (by omega)
    rw [← hnat]
    exact pow_half_antitone _ _
  exact Q'.le_trans' _ _ _ hsmall (Q'.le_trans' _ _ _
    (pow_half_le_invSucc _) (invSucc_den_le delta
      (linearTolerance_pos cap (shiftCap_nonnegative hw0 hw1 x) he)))

private theorem shift_bound (x : Sector) (hx : B U x.val = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : shiftRate hw0 hw1 x epsilon ≤ n) :
    RCle (dist (A (state hw0 hw1 (parameter n) (parameter_positive n) x).val)
      (T 1 x.val)) (rat epsilon) := by
  let lambda := parameter n
  let u := state hw0 hw1 lambda (parameter_positive n) x
  let r := Q'.recipPos (coreMargin hw0 hw1 width) (coreMargin_positive hw0 hw1)
  let X := representative hw0 hw1 x.range
  let cap := shiftCap hw0 hw1 x
  let delta := linearTolerance cap (shiftCap_nonnegative hw0 hw1 x) epsilon
  have hl0 : (0 : Q') ≤ lambda := Q'.le_of_lt (parameter_positive n)
  have hl1 : lambda ≤ 1 := by
    change half^(n+1) ≤ 1
    exact HKPos.pow_le_one half_nonneg (by decide) (n+1)
  have hsq : lambda*lambda ≤ lambda := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ lambda hl1 hl0)
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hpow : lambda ≤ delta := parameter_small hw0 hw1 x epsilon he n hn
  have hbudget : lambda*cap ≤ epsilon := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ cap hpow (shiftCap_nonnegative hw0 hw1 x))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (linearTolerance_budget cap (shiftCap_nonnegative hw0 hw1 x) he))
  have hnorm : RCle (B x.val x.val) (rat (normCeiling P X)) := by
    rw [← representative_pin hw0 hw1 x.range]
    exact completedInner_diagonal_le_normCeiling P X
  have huniform := uniform_norm_bound hw0 hw1 lambda (parameter_positive n) x hx
  have hscale := RCscale_mono (SumOfSquares.q_mul_self_nonneg lambda)
    (RCle_trans huniform
      (RCscale_mono (SumOfSquares.q_mul_self_nonneg r) hnorm))
  rw [RCscale_RCscale] at hscale
  have hscale' : RCle (B (S lambda u.val) (S lambda u.val))
      (rat ((lambda*lambda)*(r*r)*normCeiling P X)) := by
    rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
    have hs : RCscale ((lambda*lambda)*(r*r)) (rat (normCeiling P X)) =
        rat (((lambda*lambda)*(r*r))*normCeiling P X) :=
      Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
    rw [hs] at hscale
    exact hscale
  have hcoeff : ((lambda*lambda)*(r*r))*normCeiling P X ≤ epsilon := by
    have h1 : ((lambda*lambda)*(r*r))*normCeiling P X ≤
        (lambda*(r*r))*normCeiling P X :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hsq
          (SumOfSquares.q_mul_self_nonneg r))
        (normCeiling_nonnegative P X)
    have h2 : (lambda*(r*r))*normCeiling P X ≤ lambda*cap :=
      Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => lambda | 1 => r*r | _ => normCeiling P X))
    exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 hbudget)
  have heq : A u.val = T 1 (Sub x.val (S lambda u.val)) :=
    resolvent_equation hw0 hw1 lambda (parameter_positive n) x.val
  have ht := completedDist_time hw0 hw1 1
    (Sub x.val (S lambda u.val)) x.val
  rw [← heq] at ht
  rw [sub_error] at ht
  exact RCle_trans ht (RCle_trans hscale'
    (leEv_le_ofQ'_of_approx_le (fun _ => hcoeff)))

private def quarter (e : Q') : Q' := half*(half*e)

private theorem quarter_positive {e : Q'} (he : (0 : Q') < e) :
    (0 : Q') < quarter e :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)

private theorem four_quarters (e : Q') :
    RCadd (RCadd (rat (quarter e)) (rat (quarter e)))
      (RCadd (rat (quarter e)) (rat (quarter e))) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (half*e))
        (ExpNeg.two_halves (half*e))) (ExpNeg.two_halves e)))

private theorem eq_of_dist_small (x y : Completion hw0 hw1 width)
    (h : ∀ e : Q', (0 : Q') < e → RCle (dist x y) (rat e)) : x = y := by
  apply (completedDist_zero_iff hw0 hw1 x y).mp
  apply RCle_antisymm ?_ (completedDist_nonnegative hw0 hw1 x y)
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro e he
  have hz : RCadd RCzero (rat e) = rat e := by
    refine Quotient.inductionOn (rat e) ?_
    intro Y
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.eqv_of_eq (Q'.zero_add' (Y.approx n))))
  rw [hz]
  exact h e he

/-- The original zero-shift sector limit has derivative output exactly the
supplied original sector vector, in the original time-one normalization. -/
theorem zeroShift_equation (x : Sector) (hx : B U x.val = RCzero) :
    A (zeroShift hw0 hw1 x hx).val = T 1 x.val := by
  apply eq_of_dist_small hw0 hw1
  intro epsilon he
  let d := quarter epsilon
  let n := max (zeroShiftRate hw0 hw1 x hx d) (shiftRate hw0 hw1 x d)
  have hlimit := zeroShift_bound hw0 hw1 x hx d (quarter_positive he) n
    (Nat.le_max_left _ _)
  have hshift := shift_bound hw0 hw1 x hx d (quarter_positive he) n
    (Nat.le_max_right _ _)
  have hleft := RCle_trans
    (derivativeAction_dist_bound hw0 hw1 (zeroShift hw0 hw1 x hx).val
      (state hw0 hw1 (parameter n) (parameter_positive n) x).val)
    (by rw [completedDist_symm]; exact hlimit)
  have htriangle := RCle_trans
    (completedDist_triangle hw0 hw1 (A (zeroShift hw0 hw1 x hx).val)
      (A (state hw0 hw1 (parameter n) (parameter_positive n) x).val) (T 1 x.val))
    (RCadd_le_add (RCadd_le_add hleft hleft) (RCadd_le_add hshift hshift))
  rwa [four_quarters] at htriangle

/-- A domain point of the unchanged original witnessed sector graph. Its
output is exactly `x`, not a quotient-level or projected replacement. -/
def domainPoint (x : Sector) (hx : B U x.val = RCzero) :
    DomainPoint hw0 hw1 (width := width) where
  input := zeroShift hw0 hw1 x hx
  output := x
  equation := zeroShift_equation hw0 hw1 x hx

#print axioms zeroShift_equation
#print axioms domainPoint

end YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventEquation
