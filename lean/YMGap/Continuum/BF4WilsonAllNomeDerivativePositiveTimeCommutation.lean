/-
# Original dyadic derivative commutes with original positive time

The original positive-real-time action commutes with each actual dyadic root,
and hence with every finite derivative quotient. The two original represented
quotient limits are compared using their own computed all-tail rates. This is
an equality of bounded actions on the SAME Wilson completion; it is not a
logarithm identification, a maximal-generator theorem, or physical-time
calibration.
-/

import YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
import YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
import YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativePositiveTimeCommutation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue dyadicTime)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeDistance
  (completedDist completedDist_symm completedDist_triangle completedDist_zero_iff
    completedDist_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (defect)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
  (differenceQuotient derivativeAction derivativeRate derivative_bound derivativeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction
  (positiveAction outputRepresentative outputRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins
  (positiveAction_dyadic positiveAction_original realTimeAction_pin)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
  (positiveAction_smul positiveAction_sub positiveAction_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomePositiveRealSemigroup
  (realTimeAction_commutes)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (action_root)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "S" => positiveAction hw0 hw1
local notation "R" => root hw0 hw1
local notation "Q" => differenceQuotient hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Positive real time commutes with every ACTUAL original dyadic root. -/
theorem positiveAction_root_commutes (s : PositiveTime) (k : Nat) (x : V) :
    S s (R k x) = R k (S s x) := by
  let p : YMGap.Constructive.NonnegativeDyadicTime.MeshPoint := ⟨k,1⟩
  have hp : 0 < p.steps := Nat.succ_pos 0
  have h := realTimeAction_commutes hw0 hw1 (timeValue s)
    (timeValue (dyadicTime p hp)) x
  change S s (S (dyadicTime p hp) x) = S (dyadicTime p hp) (S s x) at h
  rw [positiveAction_dyadic hw0 hw1 p hp x,
    positiveAction_dyadic hw0 hw1 p hp (S s x),
    action_root hw0 hw1 k x,action_root hw0 hw1 k (S s x)] at h
  exact h

private theorem positiveAction_time_one_commutes (s : PositiveTime) (x : V) :
    S s (T 1 x) = T 1 (S s x) := by
  let p : YMGap.Constructive.NonnegativeDyadicTime.MeshPoint := ⟨0,1⟩
  have hp : 0 < p.steps := Nat.succ_pos 0
  have h := realTimeAction_commutes hw0 hw1 (timeValue s)
    (timeValue (dyadicTime p hp)) x
  change S s (S (dyadicTime p hp) x) = S (dyadicTime p hp) (S s x) at h
  rw [positiveAction_original hw0 hw1 1 hp x,
    positiveAction_original hw0 hw1 1 hp (S s x)] at h
  exact h

/-- Each finite difference quotient commutes with the same positive-time
action before taking either original represented limit. -/
theorem positiveAction_differenceQuotient (s : PositiveTime) (k : Nat) (x : V) :
    S s (Q k x) = Q k (S s x) := by
  unfold differenceQuotient defect
  rw [positiveAction_smul,positiveAction_sub,
    positiveAction_time_one_commutes hw0 hw1 s x,
    positiveAction_root_commutes hw0 hw1 s k (T 1 x),
    positiveAction_time_one_commutes hw0 hw1 s x]

private def quarter (e : Q') : Q' := HalfPow.half*(HalfPow.half*e)

private theorem quarter_positive {e : Q'} (he : (0 : Q') < e) :
    (0 : Q') < quarter e :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)

private theorem four_quarters (e : Q') :
    RCadd (RCadd (rat (quarter e)) (rat (quarter e)))
      (RCadd (rat (quarter e)) (rat (quarter e))) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*e))
        (ExpNeg.two_halves (HalfPow.half*e))) (ExpNeg.two_halves e)))

private theorem zero_add_rat (e : Q') : RCadd RCzero (rat e) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => by change Q'.eqv (0+e) e; rw [Q'.zero_add']; exact Q'.eqv_refl _))

private theorem eq_of_dist_small (x y : V)
    (h : ∀ e : Q', (0 : Q') < e → RCle (dist x y) (rat e)) : x = y := by
  apply (completedDist_zero_iff hw0 hw1 x y).mp
  apply RCle_antisymm ?_ (completedDist_nonnegative hw0 hw1 x y)
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro e he
  rw [zero_add_rat]
  exact h e he

/-- The original bounded dyadic derivative commutes with the original
strictly-positive real-time action on the entire SAME completion. Both
represented all-tail derivative rates are retained in the proof. -/
theorem derivativeAction_positiveAction_commutes (s : PositiveTime) (x : V) :
    A (S s x) = S s (A x) := by
  refine Quotient.inductionOn x ?_
  intro X
  let Y : (PD).Cauchy := outputRepresentative hw0 hw1 s X
  have hY : Class Y = S s (Class X) := outputRepresentative_pin hw0 hw1 s X
  apply eq_of_dist_small hw0 hw1
  intro e he
  let q := quarter e
  have hq : (0 : Q') < q := quarter_positive he
  let n := max (derivativeRate hw0 hw1 X q) (derivativeRate hw0 hw1 Y q)
  have hX := derivative_bound hw0 hw1 X q hq n (Nat.le_max_left _ _)
  have hYbound := derivative_bound hw0 hw1 Y q hq n (Nat.le_max_right _ _)
  rw [← derivativeAction_pin] at hX hYbound
  rw [hY] at hYbound
  have htransport := RCle_trans
    (positiveAction_distance_bound hw0 hw1 s (Q n (Class X)) (A (Class X))) hX
  rw [positiveAction_differenceQuotient hw0 hw1 s n (Class X)] at htransport
  have hleft : RCle (dist (A (S s (Class X))) (Q n (S s (Class X))))
      (rat q) := by
    rw [completedDist_symm]
    exact hYbound
  have htriangle := RCle_trans
    (completedDist_triangle hw0 hw1
      (A (S s (Class X))) (Q n (S s (Class X))) (S s (A (Class X))))
    (RCadd_le_add (RCadd_le_add hleft hleft)
      (RCadd_le_add htransport htransport))
  rwa [four_quarters] at htriangle

#print axioms positiveAction_root_commutes
#print axioms positiveAction_differenceQuotient
#print axioms derivativeAction_positiveAction_commutes

end YMGap.Continuum.BF4WilsonAllNomeDerivativePositiveTimeCommutation
