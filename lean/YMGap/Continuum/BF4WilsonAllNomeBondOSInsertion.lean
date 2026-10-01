/-
# Original buffered Wilson insertions on the physical bond completion

The actual operator sqrt(T) M sqrt(T) descends to EVERY physical bond
Cauchy class. On original finite sources it is exactly multiplication
after one geometric time advance. Thus it is a genuine source operation,
not an assumed restriction of the time-zero multiplier to the sector.

The original spin-only bound and symmetry hold on this SAME completion.
The buffer is load-bearing: products insert an original time step between
successive multipliers, not an equal-time observable-algebra homomorphism.
All assertions are at fixed nome/width and dimensionless lattice time.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
import YMGap.Continuum.BF4WilsonAllNomeSectorInsertion

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSInsertion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (dyadicTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier (multiply)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion completedInner embed)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime completedTime_embed)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
  (completedMultiply completedMultiply_embed completedDist_multiply_bound)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (positiveAction_dyadic)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws (positiveAction_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (action_root)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root root_zero_depth)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility (root_square)
open YMGap.Continuum.BF4WilsonAllNomeSectorInsertion
  (sandwich insertion sandwich_add sandwich_realSmul sandwich_symmetric sandwich_norm_bound)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (image)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion toSectorRep close_iff_limit_eq ofSource bondCompletedInner bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_ofSource bondValue_inner bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (ofState ofState_congr bondValue_ofState add bondValue_add realSmul bondValue_realSmul)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier (multiplierCap_nonnegative)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "R" => root hw0 hw1 1
local notation "B" => bondCompletedInner hw0 hw1

/-- One half of the ORIGINAL one-step lattice time, not a physical spacing. -/
def halfTime : PositiveTime := dyadicTime ⟨1,1⟩ (Nat.succ_pos 0)

theorem halfTime_action (x : V) : positiveAction hw0 hw1 halfTime x = R x := by
  rw [halfTime, positiveAction_dyadic]
  exact action_root hw0 hw1 1 x

/-- A literal finite source operation, including its necessary time buffer. -/
def bufferedSource (L : SourceLoop width) (spin : Nat)
    (x : IntrinsicExpression width) : IntrinsicExpression width :=
  multiply L spin (advance 1 x)

/-- The source operation has exactly the original square-root sandwich image. -/
theorem image_bufferedSource (L : SourceLoop width) (spin : Nat)
    (x : IntrinsicExpression width) :
    (image hw0 hw1 (bufferedSource L spin x)).val =
      sandwich hw0 hw1 halfTime L spin (image hw0 hw1 x).val := by
  unfold sandwich
  simp only [halfTime_action]
  change R (embed hw0 hw1 (multiply L spin (advance 1 x))) =
    R (completedMultiply hw0 hw1 L spin (R (R (embed hw0 hw1 x))))
  rw [← completedMultiply_embed, ← completedTime_embed,
    root_square hw0 hw1 0, root_zero_depth]

/-- Construct the sector range witness before quotienting; choose no row. -/
def act (L : SourceLoop width) (spin : Nat) : H → H :=
  Quotient.lift
    (fun X => ofState hw0 hw1
      (insertion hw0 hw1 halfTime L spin (toSectorRep hw0 hw1 X)))
    (fun _ _ h => by
      apply ofState_congr hw0 hw1
      exact congrArg (sandwich hw0 hw1 halfTime L spin)
        ((close_iff_limit_eq hw0 hw1 _ _).mp h))

theorem act_value (L : SourceLoop width) (spin : Nat) (x : H) :
    bondValue hw0 hw1 (act hw0 hw1 L spin x) =
      sandwich hw0 hw1 halfTime L spin (bondValue hw0 hw1 x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact bondValue_ofState hw0 hw1 _

theorem act_root_pin (L : SourceLoop width) (spin : Nat) (x : H) :
    bondValue hw0 hw1 (act hw0 hw1 L spin x) =
      R (completedMultiply hw0 hw1 L spin (R (bondValue hw0 hw1 x))) := by
  rw [act_value]
  simp only [sandwich, halfTime_action]

/-- Exact geometric-source pin; this also proves physical bond-null descent. -/
theorem act_ofSource (L : SourceLoop width) (spin : Nat)
    (x : IntrinsicExpression width) :
    act hw0 hw1 L spin (ofSource hw0 hw1 x) =
      ofSource hw0 hw1 (bufferedSource L spin x) := by
  apply bondValue_injective hw0 hw1
  rw [act_value, bondValue_ofSource, bondValue_ofSource, image_bufferedSource]

theorem act_add (L : SourceLoop width) (spin : Nat) (x y : H) :
    act hw0 hw1 L spin (add hw0 hw1 x y) =
      add hw0 hw1 (act hw0 hw1 L spin x) (act hw0 hw1 L spin y) := by
  apply bondValue_injective hw0 hw1
  simp only [act_value, bondValue_add]
  exact sandwich_add hw0 hw1 halfTime L spin _ _

theorem act_realSmul (L : SourceLoop width) (spin : Nat)
    (s : CReal) (cs : QCauchy s.approx) (x : H) :
    act hw0 hw1 L spin (realSmul hw0 hw1 s cs x) =
      realSmul hw0 hw1 s cs (act hw0 hw1 L spin x) := by
  apply bondValue_injective hw0 hw1
  simp only [act_value, bondValue_realSmul]
  exact sandwich_realSmul hw0 hw1 halfTime L spin s cs _

theorem act_symmetric (L : SourceLoop width) (spin : Nat) (x y : H) :
    B (act hw0 hw1 L spin x) y = B x (act hw0 hw1 L spin y) := by
  simp only [bondValue_inner, act_value]
  exact sandwich_symmetric hw0 hw1 halfTime L spin _ _

theorem act_norm_bound (L : SourceLoop width) (spin : Nat) (x : H) :
    RCle (B (act hw0 hw1 L spin x) (act hw0 hw1 L spin x))
      (RCscale (characterBound spin) (B x x)) := by
  simp only [bondValue_inner, act_value]
  exact sandwich_norm_bound hw0 hw1 halfTime L spin _

/-- Continuity uses the SAME physical bond distance on every input class. -/
theorem act_distance_bound (L : SourceLoop width) (spin : Nat) (x y : H) :
    RCle (bondCompletedDistance hw0 hw1 (act hw0 hw1 L spin x) (act hw0 hw1 L spin y))
      (RCscale (characterBound spin) (bondCompletedDistance hw0 hw1 x y)) := by
  simp only [bondValue_distance, act_value, sandwich]
  exact RCle_trans (positiveAction_distance_bound hw0 hw1 halfTime _ _)
    (RCle_trans (completedDist_multiply_bound hw0 hw1 L spin _ _)
      (RCscale_mono (multiplierCap_nonnegative spin)
        (positiveAction_distance_bound hw0 hw1 halfTime _ _)))

#print axioms halfTime_action
#print axioms image_bufferedSource
#print axioms act
#print axioms act_value
#print axioms act_root_pin
#print axioms act_ofSource
#print axioms act_add
#print axioms act_realSmul
#print axioms act_symmetric
#print axioms act_norm_bound
#print axioms act_distance_bound

end YMGap.Continuum.BF4WilsonAllNomeBondOSInsertion
