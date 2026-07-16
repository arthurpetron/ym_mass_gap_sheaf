/-
# Exact two-block tensor obstruction for the finite physical law

The complete-law coupling is global.  A first genuinely blockwise attempt is
to multiply two centered one-block factors while retaining the exact target
physical mass.  This file computes, without an independence assumption, the
two residuals of that tensor product:

* its row sum is shifted by the target cross-centered moment;
* its physical pushforward is shifted by the source cross-centered moment.

Thus one-block normalization does not tensorize over the interacting physical
law.  The missing datum is an exact correlation identity, not another local
normalization check.
-/

import YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
import YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder

namespace YMGap.Continuum.Z4BlockLocalityTensorObstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4AdjacentTimeUnitCubeCylinder
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4RetunedParityPhysicalMixtureKernel
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-- Exact cross-centered moment of two finite Boolean coordinates. -/
def finiteCenteredCrossMoment {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool) : Q' :=
  listQSum
    (fun state => mass state *
      (centeredEventCoordinate firstParameter firstEvent state *
        centeredEventCoordinate secondParameter secondEvent state))
    states

def finiteJointEventMass {A : Type}
    (mass : A → Q') (states : List A)
    (firstEvent secondEvent : A → Bool) : Q' :=
  finiteEventMass mass states
    (fun state => firstEvent state && secondEvent state)

def signedCenteredEventMass {A : Type}
    (mass : A → Q') (states : List A) (firstParameter : Q')
    (firstEvent secondEvent : A → Bool) : Q' :=
  finiteEventMass
    (fun state => mass state *
      centeredEventCoordinate firstParameter firstEvent state)
    states secondEvent

private theorem masked_centered_pointwise {A : Type}
    (mass : A → Q') (firstParameter : Q')
    (firstEvent secondEvent : A → Bool) (state : A) :
    (if secondEvent state then
        mass state * centeredEventCoordinate firstParameter firstEvent state
      else 0) ≈
      (if firstEvent state && secondEvent state then mass state else 0) +
        (-firstParameter) *
          (if secondEvent state then mass state else 0) := by
  cases hsecond : secondEvent state
  · simp only [hsecond, Bool.and_false, Bool.false_eq_true, if_false]
    exact Q'.eqv_symm
      (Q'.eqv_trans _ ((0 : Q') + 0) _
        (Q'.add_eqv_congr' (Q'.eqv_refl 0)
          (Q'.mul_zero_eqv (-firstParameter)))
        (Q'.eqv_of_eq (Q'.zero_add' 0)))
  · simp only [hsecond, Bool.and_true, if_true]
    exact Q'.eqv_trans _ _ _
      (centeredWeight_pointwise mass firstParameter firstEvent state)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_symm
          (Q'.neg_mul_eqv firstParameter (mass state))))

private theorem signedCenteredEventMass_eqv_joint_sub_product {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (hsecondEvent :
      finiteEventMass mass states secondEvent ≈ secondParameter) :
    signedCenteredEventMass mass states firstParameter
        firstEvent secondEvent ≈
      finiteJointEventMass mass states firstEvent secondEvent +
        -(firstParameter * secondParameter) := by
  let jointTerm := fun state =>
    if firstEvent state && secondEvent state then mass state else 0
  let secondTerm := fun state =>
    if secondEvent state then mass state else 0
  unfold signedCenteredEventMass finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun state => jointTerm state +
        (-firstParameter) * secondTerm state) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    exact masked_centered_pointwise mass firstParameter
      firstEvent secondEvent state
  refine Q'.eqv_trans _
    (listQSum jointTerm states +
      listQSum (fun state => (-firstParameter) * secondTerm state) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum jointTerm states +
      (-firstParameter) * listQSum secondTerm states) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_mul_left (-firstParameter) secondTerm states)) ?_
  change
    finiteJointEventMass mass states firstEvent secondEvent +
        (-firstParameter) * finiteEventMass mass states secondEvent ≈
      finiteJointEventMass mass states firstEvent secondEvent +
        -(firstParameter * secondParameter)
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.eqv_trans _ ((-firstParameter) * secondParameter) _
      (Q'.mul_eqv_congr_left (-firstParameter) _ _ hsecondEvent)
      (Q'.neg_mul_eqv firstParameter secondParameter))

private theorem centered_cross_via_mask_pointwise {A : Type}
    (mass : A → Q') (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool) (state : A) :
    mass state *
        (centeredEventCoordinate firstParameter firstEvent state *
          centeredEventCoordinate secondParameter secondEvent state) ≈
      (if secondEvent state then
          mass state * centeredEventCoordinate
            firstParameter firstEvent state
        else 0) +
        (-secondParameter) *
          (mass state * centeredEventCoordinate
            firstParameter firstEvent state) := by
  refine Q'.eqv_trans _
    ((mass state * centeredEventCoordinate
        firstParameter firstEvent state) *
      centeredEventCoordinate secondParameter secondEvent state) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (mass state)
        (centeredEventCoordinate firstParameter firstEvent state)
        (centeredEventCoordinate secondParameter secondEvent state))
  refine Q'.eqv_trans _ _ _
    (centeredWeight_pointwise
      (fun candidate => mass candidate *
        centeredEventCoordinate firstParameter firstEvent candidate)
      secondParameter secondEvent state) ?_
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.eqv_symm
      (Q'.neg_mul_eqv secondParameter
        (mass state * centeredEventCoordinate
          firstParameter firstEvent state)))

/-- The cross-centered moment is exactly the joint atom minus the product of
the two marginals; no independence statement is used. -/
theorem finiteCenteredCrossMoment_eqv_joint_sub_product {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (hfirstEvent :
      finiteEventMass mass states firstEvent ≈ firstParameter)
    (hsecondEvent :
      finiteEventMass mass states secondEvent ≈ secondParameter)
    (htotal : listQSum mass states ≈ 1) :
    finiteCenteredCrossMoment mass states
        firstParameter secondParameter firstEvent secondEvent ≈
      finiteJointEventMass mass states firstEvent secondEvent +
        -(firstParameter * secondParameter) := by
  let firstWeighted := fun state => mass state *
    centeredEventCoordinate firstParameter firstEvent state
  have hfirstMean : listQSum firstWeighted states ≈ 0 :=
    centeredEventCoordinate_mean_zero mass states firstEvent
      firstParameter hfirstEvent htotal
  unfold finiteCenteredCrossMoment
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        (if secondEvent state then firstWeighted state else 0) +
          (-secondParameter) * firstWeighted state) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    exact centered_cross_via_mask_pointwise mass
      firstParameter secondParameter
      firstEvent secondEvent state
  refine Q'.eqv_trans _
    (listQSum
        (fun state => if secondEvent state then firstWeighted state else 0)
        states +
      listQSum (fun state => (-secondParameter) * firstWeighted state)
        states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum
        (fun state => if secondEvent state then firstWeighted state else 0)
        states +
      (-secondParameter) * listQSum firstWeighted states) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_mul_left (-secondParameter) firstWeighted states)) ?_
  refine Q'.eqv_trans _
    (listQSum
        (fun state => if secondEvent state then firstWeighted state else 0)
        states +
      (-secondParameter) * 0) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left (-secondParameter) _ _ hfirstMean)) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun state => if secondEvent state then firstWeighted state else 0)
      states + 0) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_zero_eqv (-secondParameter))) ?_
  rw [Q'.add_zero']
  change
    signedCenteredEventMass mass states firstParameter
        firstEvent secondEvent ≈
      finiteJointEventMass mass states firstEvent secondEvent +
        -(firstParameter * secondParameter)
  exact signedCenteredEventMass_eqv_joint_sub_product
    mass states firstParameter secondParameter firstEvent secondEvent
    hsecondEvent

theorem finiteJointEventMass_self_eqv {A : Type}
    (mass : A → Q') (states : List A) (event : A → Bool) :
    finiteJointEventMass mass states event event ≈
      finiteEventMass mass states event := by
  unfold finiteJointEventMass finiteEventMass
  apply listQSum_congr_on
  intro state _
  cases hevent : event state <;>
    simp only [hevent, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, if_false, if_true] <;>
    exact Q'.eqv_refl _

/-- The diagonal cross moment is the exact Bernoulli variance.  Exchange or
reflection symmetry alone therefore produces a variance, not independence. -/
theorem finiteCenteredVariance_eqv {A : Type}
    (mass : A → Q') (states : List A) (parameter : Q')
    (event : A → Bool)
    (hevent : finiteEventMass mass states event ≈ parameter)
    (htotal : listQSum mass states ≈ 1) :
    finiteCenteredCrossMoment mass states parameter parameter event event ≈
      parameter * ((1 : Q') + -parameter) := by
  refine Q'.eqv_trans _
    (finiteJointEventMass mass states event event +
      -(parameter * parameter)) _ ?_ ?_
  · exact finiteCenteredCrossMoment_eqv_joint_sub_product
      mass states parameter parameter event event hevent hevent htotal
  refine Q'.eqv_trans _
    (parameter + -(parameter * parameter)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (finiteJointEventMass_self_eqv mass states event) hevent)
      (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (parameter * 1 + parameter * -parameter) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.mul_one_eqv parameter))
      (Q'.eqv_symm (Q'.mul_neg_eqv parameter parameter))
  exact Q'.eqv_symm (Q'.mul_add_eqv parameter 1 (-parameter))

def minimalSymmetricPairStateSpace : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

def minimalSymmetricPairHalf : Q' := Q'.mkPos 1 2 (by decide)

def minimalSymmetricPairQuarter : Q' := Q'.mkPos 1 4 (by decide)

/-- The smallest symmetric correlated two-bit law: equal mass on the two
diagonal atoms and zero mass on the off-diagonal atoms. -/
def minimalSymmetricCorrelatedPairMass : Bool × Bool → Q'
  | (false, false) => minimalSymmetricPairHalf
  | (true, true) => minimalSymmetricPairHalf
  | _ => 0

theorem minimalSymmetricCorrelatedPairMass_nonnegative
    (state : Bool × Bool) :
    (0 : Q') ≤ minimalSymmetricCorrelatedPairMass state := by
  rcases state with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem minimalSymmetricCorrelatedPairMass_normalized :
    listQSum minimalSymmetricCorrelatedPairMass
      minimalSymmetricPairStateSpace ≈ 1 := by
  decide

theorem minimalSymmetricCorrelatedPairMass_swap
    (state : Bool × Bool) :
    minimalSymmetricCorrelatedPairMass (state.2, state.1) =
      minimalSymmetricCorrelatedPairMass state := by
  rcases state with ⟨first, second⟩
  cases first <;> cases second <;> rfl

theorem minimalSymmetricCorrelatedPair_firstEventMass :
    finiteEventMass minimalSymmetricCorrelatedPairMass
        minimalSymmetricPairStateSpace Prod.fst ≈
      minimalSymmetricPairHalf := by
  decide

theorem minimalSymmetricCorrelatedPair_secondEventMass :
    finiteEventMass minimalSymmetricCorrelatedPairMass
        minimalSymmetricPairStateSpace Prod.snd ≈
      minimalSymmetricPairHalf := by
  decide

/-- Kernel-checked fence: swap symmetry and exact equal marginals do not
force the cross-centered moment to vanish. -/
theorem minimalSymmetricCorrelatedPair_crossMoment_eqv_quarter :
    finiteCenteredCrossMoment minimalSymmetricCorrelatedPairMass
        minimalSymmetricPairStateSpace
        minimalSymmetricPairHalf minimalSymmetricPairHalf
        Prod.fst Prod.snd ≈
      minimalSymmetricPairQuarter := by
  decide

theorem minimalSymmetricCorrelatedPair_crossMoment_ne_zero :
    ¬ finiteCenteredCrossMoment minimalSymmetricCorrelatedPairMass
        minimalSymmetricPairStateSpace
        minimalSymmetricPairHalf minimalSymmetricPairHalf
        Prod.fst Prod.snd ≈ 0 := by
  decide

/-- A two-coordinate multiplicative tilt of one complete finite law. -/
def twoCoordinateTensorTilt {A : Type}
    (mass : A → Q')
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (firstCoefficient secondCoefficient : Q')
    (state : A) : Q' :=
  mass state *
    ((1 : Q') + firstCoefficient *
      centeredEventCoordinate firstParameter firstEvent state) *
    ((1 : Q') + secondCoefficient *
      centeredEventCoordinate secondParameter secondEvent state)

private theorem tensor_product_expand
    (mass firstCoefficient secondCoefficient
      firstCoordinate secondCoordinate : Q') :
    mass *
        (((1 : Q') + firstCoefficient * firstCoordinate) *
          ((1 : Q') + secondCoefficient * secondCoordinate)) ≈
      mass +
        (firstCoefficient * (mass * firstCoordinate) +
          (secondCoefficient * (mass * secondCoordinate) +
            (firstCoefficient * secondCoefficient) *
              (mass * (firstCoordinate * secondCoordinate)))) := by
  have hfactor :
      ((1 : Q') + firstCoefficient * firstCoordinate) *
          ((1 : Q') + secondCoefficient * secondCoordinate) ≈
        ((1 : Q') + firstCoefficient * firstCoordinate) +
          (secondCoefficient * secondCoordinate +
            (firstCoefficient * firstCoordinate) *
              (secondCoefficient * secondCoordinate)) := by
    refine Q'.eqv_trans _
      ((((1 : Q') + firstCoefficient * firstCoordinate) * 1) +
        (((1 : Q') + firstCoefficient * firstCoordinate) *
          (secondCoefficient * secondCoordinate))) _ ?_ ?_
    · exact Q'.mul_add_eqv
        ((1 : Q') + firstCoefficient * firstCoordinate) 1
        (secondCoefficient * secondCoordinate)
    refine Q'.eqv_trans _
      (((1 : Q') + firstCoefficient * firstCoordinate) +
        (((1 : Q') + firstCoefficient * firstCoordinate) *
          (secondCoefficient * secondCoordinate))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_one_eqv ((1 : Q') + firstCoefficient * firstCoordinate))
        (Q'.eqv_refl _)
    refine Q'.eqv_trans _
      (((1 : Q') + firstCoefficient * firstCoordinate) +
        ((1 : Q') * (secondCoefficient * secondCoordinate) +
          (firstCoefficient * firstCoordinate) *
            (secondCoefficient * secondCoordinate))) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_mul_eqv 1 (firstCoefficient * firstCoordinate)
          (secondCoefficient * secondCoordinate))
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr'
        (Q'.one_mul_eqv (secondCoefficient * secondCoordinate))
        (Q'.eqv_refl _))
  refine Q'.eqv_trans _
    (mass *
      (((1 : Q') + firstCoefficient * firstCoordinate) +
        (secondCoefficient * secondCoordinate +
          (firstCoefficient * firstCoordinate) *
            (secondCoefficient * secondCoordinate)))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left mass _ _ hfactor
  refine Q'.eqv_trans _
    (mass * ((1 : Q') + firstCoefficient * firstCoordinate) +
      mass *
        (secondCoefficient * secondCoordinate +
          (firstCoefficient * firstCoordinate) *
            (secondCoefficient * secondCoordinate))) _
    (Q'.mul_add_eqv mass _ _) ?_
  refine Q'.eqv_trans _
    ((mass * 1 + mass * (firstCoefficient * firstCoordinate)) +
      (mass * (secondCoefficient * secondCoordinate) +
        mass * ((firstCoefficient * firstCoordinate) *
          (secondCoefficient * secondCoordinate)))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_add_eqv mass 1 (firstCoefficient * firstCoordinate))
      (Q'.mul_add_eqv mass
        (secondCoefficient * secondCoordinate)
        ((firstCoefficient * firstCoordinate) *
          (secondCoefficient * secondCoordinate)))
  refine Q'.eqv_trans _
    ((mass + mass * (firstCoefficient * firstCoordinate)) +
      (mass * (secondCoefficient * secondCoordinate) +
        mass * ((firstCoefficient * firstCoordinate) *
          (secondCoefficient * secondCoordinate)))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.mul_one_eqv mass) (Q'.eqv_refl _))
      (Q'.eqv_refl _)
  refine Q'.eqv_trans _
    (mass +
      (mass * (firstCoefficient * firstCoordinate) +
        (mass * (secondCoefficient * secondCoordinate) +
          mass * ((firstCoefficient * firstCoordinate) *
            (secondCoefficient * secondCoordinate))))) _ ?_ ?_
  · exact Q'.add_assoc_eqv mass
      (mass * (firstCoefficient * firstCoordinate))
      (mass * (secondCoefficient * secondCoordinate) +
        mass * ((firstCoefficient * firstCoordinate) *
          (secondCoefficient * secondCoordinate)))
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_refl _
  apply Q'.add_eqv_congr'
  · ac_qeqv
  apply Q'.add_eqv_congr'
  · ac_qeqv
  · ac_qeqv

private theorem twoCoordinateTensorTilt_pointwise {A : Type}
    (mass : A → Q')
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (firstCoefficient secondCoefficient : Q') (state : A) :
    twoCoordinateTensorTilt mass firstParameter secondParameter
        firstEvent secondEvent firstCoefficient secondCoefficient state ≈
      mass state +
        (firstCoefficient *
            (mass state * centeredEventCoordinate
              firstParameter firstEvent state) +
          (secondCoefficient *
              (mass state * centeredEventCoordinate
                secondParameter secondEvent state) +
            (firstCoefficient * secondCoefficient) *
              (mass state *
                (centeredEventCoordinate firstParameter firstEvent state *
                  centeredEventCoordinate secondParameter secondEvent
                    state)))) := by
  unfold twoCoordinateTensorTilt
  refine Q'.eqv_trans _
    (mass state *
      (((1 : Q') + firstCoefficient *
          centeredEventCoordinate firstParameter firstEvent state) *
        ((1 : Q') + secondCoefficient *
          centeredEventCoordinate secondParameter secondEvent state))) _ ?_ ?_
  · exact Q'.mul_assoc_eqv (mass state)
      ((1 : Q') + firstCoefficient *
        centeredEventCoordinate firstParameter firstEvent state)
      ((1 : Q') + secondCoefficient *
        centeredEventCoordinate secondParameter secondEvent state)
  · exact tensor_product_expand _ _ _ _ _

/-- Exact row-sum algebra for a two-block tensor tilt.  The two first moments
are zero, but their cross moment remains. -/
theorem twoCoordinateTensorTilt_total {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (firstCoefficient secondCoefficient : Q')
    (hfirstEvent :
      finiteEventMass mass states firstEvent ≈ firstParameter)
    (hsecondEvent :
      finiteEventMass mass states secondEvent ≈ secondParameter)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent firstCoefficient secondCoefficient)
        states ≈
      (1 : Q') +
        (firstCoefficient * secondCoefficient) *
          finiteCenteredCrossMoment mass states
            firstParameter secondParameter firstEvent secondEvent := by
  let firstWeighted := fun state =>
    mass state * centeredEventCoordinate firstParameter firstEvent state
  let secondWeighted := fun state =>
    mass state * centeredEventCoordinate secondParameter secondEvent state
  let crossWeighted := fun state => mass state *
    (centeredEventCoordinate firstParameter firstEvent state *
      centeredEventCoordinate secondParameter secondEvent state)
  have hfirstMean : listQSum firstWeighted states ≈ 0 :=
    centeredEventCoordinate_mean_zero mass states firstEvent
      firstParameter hfirstEvent htotal
  have hsecondMean : listQSum secondWeighted states ≈ 0 :=
    centeredEventCoordinate_mean_zero mass states secondEvent
      secondParameter hsecondEvent htotal
  refine Q'.eqv_trans _
    (listQSum
      (fun state => mass state +
        (firstCoefficient * firstWeighted state +
          (secondCoefficient * secondWeighted state +
            (firstCoefficient * secondCoefficient) *
              crossWeighted state))) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    exact twoCoordinateTensorTilt_pointwise mass
      firstParameter secondParameter firstEvent secondEvent
      firstCoefficient secondCoefficient state
  refine Q'.eqv_trans _
    (listQSum mass states +
      listQSum
        (fun state =>
          firstCoefficient * firstWeighted state +
            (secondCoefficient * secondWeighted state +
              (firstCoefficient * secondCoefficient) *
                crossWeighted state)) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum mass states +
      (listQSum (fun state => firstCoefficient * firstWeighted state) states +
        listQSum
          (fun state =>
            secondCoefficient * secondWeighted state +
              (firstCoefficient * secondCoefficient) *
                crossWeighted state) states)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_add _ _ states)
  refine Q'.eqv_trans _
    (listQSum mass states +
      (listQSum (fun state => firstCoefficient * firstWeighted state) states +
        (listQSum
            (fun state => secondCoefficient * secondWeighted state) states +
          listQSum
            (fun state => (firstCoefficient * secondCoefficient) *
              crossWeighted state) states))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (listQSum_add _ _ states))
  refine Q'.eqv_trans _
    (listQSum mass states +
      (firstCoefficient * listQSum firstWeighted states +
        (secondCoefficient * listQSum secondWeighted states +
          (firstCoefficient * secondCoefficient) *
            listQSum crossWeighted states))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr'
        (listQSum_mul_left firstCoefficient firstWeighted states)
        (Q'.add_eqv_congr'
          (listQSum_mul_left secondCoefficient secondWeighted states)
          (listQSum_mul_left
            (firstCoefficient * secondCoefficient) crossWeighted states)))
  change
    listQSum mass states +
        (firstCoefficient * listQSum firstWeighted states +
          (secondCoefficient * listQSum secondWeighted states +
            (firstCoefficient * secondCoefficient) *
              listQSum crossWeighted states)) ≈
      (1 : Q') +
        (firstCoefficient * secondCoefficient) *
          listQSum crossWeighted states
  refine Q'.eqv_trans _
    ((1 : Q') +
      (firstCoefficient * 0 +
        (secondCoefficient * 0 +
          (firstCoefficient * secondCoefficient) *
            listQSum crossWeighted states))) _ ?_ ?_
  · exact Q'.add_eqv_congr' htotal
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left firstCoefficient _ _ hfirstMean)
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left secondCoefficient _ _ hsecondMean)
          (Q'.eqv_refl _)))
  refine Q'.eqv_trans _
    ((1 : Q') +
      (0 +
        (0 +
          (firstCoefficient * secondCoefficient) *
            listQSum crossWeighted states))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr'
        (Q'.mul_zero_eqv firstCoefficient)
        (Q'.add_eqv_congr'
          (Q'.mul_zero_eqv secondCoefficient)
          (Q'.eqv_refl _)))
  rw [Q'.zero_add', Q'.zero_add']
  exact Q'.eqv_refl _

/-! ## The blockwise product kernel and its two exact residuals -/

/-- Product of two one-block centered factors over the complete target law. -/
def twoBlockTensorizedConfigurationKernel {Source Target : Type}
    (targetMass : Target → Q')
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (source : Source) (target : Target) : Q' :=
  twoCoordinateTensorTilt targetMass
    targetFirstParameter targetSecondParameter
    targetFirstEvent targetSecondEvent
    (centeredEventCoordinate sourceFirstParameter sourceFirstEvent source)
    (centeredEventCoordinate sourceSecondParameter sourceSecondEvent source)
    target

theorem twoBlockTensorizedConfigurationKernel_nonnegative
    {Source Target : Type}
    (targetMass : Target → Q')
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (hsourceFirst0 : (0 : Q') ≤ sourceFirstParameter)
    (hsourceFirst1 : sourceFirstParameter ≤ (1 : Q'))
    (hsourceSecond0 : (0 : Q') ≤ sourceSecondParameter)
    (hsourceSecond1 : sourceSecondParameter ≤ (1 : Q'))
    (htargetFirst0 : (0 : Q') ≤ targetFirstParameter)
    (htargetFirst1 : targetFirstParameter ≤ (1 : Q'))
    (htargetSecond0 : (0 : Q') ≤ targetSecondParameter)
    (htargetSecond1 : targetSecondParameter ≤ (1 : Q'))
    (htargetMass : ∀ target, (0 : Q') ≤ targetMass target)
    (source : Source) (target : Target) :
    (0 : Q') ≤ twoBlockTensorizedConfigurationKernel targetMass
      sourceFirstParameter sourceSecondParameter
      targetFirstParameter targetSecondParameter
      sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent
      source target := by
  unfold twoBlockTensorizedConfigurationKernel twoCoordinateTensorTilt
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (htargetMass target)
      (centeredEventFactor_nonnegative
        hsourceFirst0 hsourceFirst1 htargetFirst0 htargetFirst1
        sourceFirstEvent targetFirstEvent source target))
    (centeredEventFactor_nonnegative
        hsourceSecond0 hsourceSecond1 htargetSecond0 htargetSecond1
        sourceSecondEvent targetSecondEvent source target)

/-- The target cross moment is the exact obstruction to tensorized row
normalization. -/
theorem twoBlockTensorizedConfigurationKernel_row_sum
    {Source Target : Type}
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (htargetFirstEvent :
      finiteEventMass targetMass targetStates targetFirstEvent ≈
        targetFirstParameter)
    (htargetSecondEvent :
      finiteEventMass targetMass targetStates targetSecondEvent ≈
        targetSecondParameter)
    (htargetTotal : listQSum targetMass targetStates ≈ 1)
    (source : Source) :
    listQSum
        (twoBlockTensorizedConfigurationKernel targetMass
          sourceFirstParameter sourceSecondParameter
          targetFirstParameter targetSecondParameter
          sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent
          source)
        targetStates ≈
      (1 : Q') +
        (centeredEventCoordinate sourceFirstParameter sourceFirstEvent source *
          centeredEventCoordinate sourceSecondParameter sourceSecondEvent
            source) *
          finiteCenteredCrossMoment targetMass targetStates
            targetFirstParameter targetSecondParameter
            targetFirstEvent targetSecondEvent := by
  exact twoCoordinateTensorTilt_total targetMass targetStates
    targetFirstParameter targetSecondParameter
    targetFirstEvent targetSecondEvent
    (centeredEventCoordinate sourceFirstParameter sourceFirstEvent source)
    (centeredEventCoordinate sourceSecondParameter sourceSecondEvent source)
    htargetFirstEvent htargetSecondEvent htargetTotal

/-- Dually, the source cross moment is the exact obstruction to the complete
target law being the pushforward of the tensorized kernel. -/
theorem twoBlockTensorizedConfigurationKernel_pushforward
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q')
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (hsourceFirstEvent :
      finiteEventMass sourceMass sourceStates sourceFirstEvent ≈
        sourceFirstParameter)
    (hsourceSecondEvent :
      finiteEventMass sourceMass sourceStates sourceSecondEvent ≈
        sourceSecondParameter)
    (hsourceTotal : listQSum sourceMass sourceStates ≈ 1)
    (target : Target) :
    configurationPushforward sourceMass sourceStates
        (twoBlockTensorizedConfigurationKernel targetMass
          sourceFirstParameter sourceSecondParameter
          targetFirstParameter targetSecondParameter
          sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent)
        target ≈
      targetMass target *
        ((1 : Q') +
          (centeredEventCoordinate targetFirstParameter targetFirstEvent
              target *
            centeredEventCoordinate targetSecondParameter targetSecondEvent
              target) *
            finiteCenteredCrossMoment sourceMass sourceStates
              sourceFirstParameter sourceSecondParameter
              sourceFirstEvent sourceSecondEvent) := by
  let firstTargetCoordinate :=
    centeredEventCoordinate targetFirstParameter targetFirstEvent target
  let secondTargetCoordinate :=
    centeredEventCoordinate targetSecondParameter targetSecondEvent target
  have htilt := twoCoordinateTensorTilt_total sourceMass sourceStates
    sourceFirstParameter sourceSecondParameter
    sourceFirstEvent sourceSecondEvent
    firstTargetCoordinate secondTargetCoordinate
    hsourceFirstEvent hsourceSecondEvent hsourceTotal
  unfold configurationPushforward
  refine Q'.eqv_trans _
    (listQSum
      (fun source => targetMass target *
        twoCoordinateTensorTilt sourceMass
          sourceFirstParameter sourceSecondParameter
          sourceFirstEvent sourceSecondEvent
          firstTargetCoordinate secondTargetCoordinate source)
      sourceStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    unfold twoBlockTensorizedConfigurationKernel
      twoCoordinateTensorTilt firstTargetCoordinate secondTargetCoordinate
    ac_qeqv
  refine Q'.eqv_trans _
    (targetMass target *
      listQSum
        (twoCoordinateTensorTilt sourceMass
          sourceFirstParameter sourceSecondParameter
          sourceFirstEvent sourceSecondEvent
          firstTargetCoordinate secondTargetCoordinate)
        sourceStates) _
    (listQSum_mul_left (targetMass target) _ sourceStates) ?_
  exact Q'.mul_eqv_congr_left (targetMass target) _ _ htilt

theorem twoBlockTensorizedConfigurationKernel_row_normalized_of_cross_zero
    {Source Target : Type}
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (htargetFirstEvent :
      finiteEventMass targetMass targetStates targetFirstEvent ≈
        targetFirstParameter)
    (htargetSecondEvent :
      finiteEventMass targetMass targetStates targetSecondEvent ≈
        targetSecondParameter)
    (htargetTotal : listQSum targetMass targetStates ≈ 1)
    (hcross : finiteCenteredCrossMoment targetMass targetStates
      targetFirstParameter targetSecondParameter
      targetFirstEvent targetSecondEvent ≈ 0)
    (source : Source) :
    listQSum
        (twoBlockTensorizedConfigurationKernel targetMass
          sourceFirstParameter sourceSecondParameter
          targetFirstParameter targetSecondParameter
          sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent
          source)
        targetStates ≈ 1 := by
  refine Q'.eqv_trans _
    ((1 : Q') +
      (centeredEventCoordinate sourceFirstParameter sourceFirstEvent source *
        centeredEventCoordinate sourceSecondParameter sourceSecondEvent
          source) *
        finiteCenteredCrossMoment targetMass targetStates
          targetFirstParameter targetSecondParameter
          targetFirstEvent targetSecondEvent) _ ?_ ?_
  · exact twoBlockTensorizedConfigurationKernel_row_sum
      targetMass targetStates sourceFirstParameter sourceSecondParameter
      targetFirstParameter targetSecondParameter
      sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent
      htargetFirstEvent htargetSecondEvent htargetTotal source
  refine Q'.eqv_trans _ ((1 : Q') + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_trans _
        ((centeredEventCoordinate sourceFirstParameter sourceFirstEvent source *
          centeredEventCoordinate sourceSecondParameter sourceSecondEvent
            source) * 0) _
        (Q'.mul_eqv_congr_left _ _ _ hcross)
        (Q'.mul_zero_eqv _))
  exact Q'.eqv_of_eq (Q'.add_zero' 1)

theorem twoBlockTensorizedConfigurationKernel_pushforward_of_cross_zero
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q')
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (hsourceFirstEvent :
      finiteEventMass sourceMass sourceStates sourceFirstEvent ≈
        sourceFirstParameter)
    (hsourceSecondEvent :
      finiteEventMass sourceMass sourceStates sourceSecondEvent ≈
        sourceSecondParameter)
    (hsourceTotal : listQSum sourceMass sourceStates ≈ 1)
    (hcross : finiteCenteredCrossMoment sourceMass sourceStates
      sourceFirstParameter sourceSecondParameter
      sourceFirstEvent sourceSecondEvent ≈ 0)
    (target : Target) :
    configurationPushforward sourceMass sourceStates
        (twoBlockTensorizedConfigurationKernel targetMass
          sourceFirstParameter sourceSecondParameter
          targetFirstParameter targetSecondParameter
          sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent)
        target ≈ targetMass target := by
  refine Q'.eqv_trans _
    (targetMass target *
      ((1 : Q') +
        (centeredEventCoordinate targetFirstParameter targetFirstEvent target *
          centeredEventCoordinate targetSecondParameter targetSecondEvent
            target) *
          finiteCenteredCrossMoment sourceMass sourceStates
            sourceFirstParameter sourceSecondParameter
            sourceFirstEvent sourceSecondEvent)) _ ?_ ?_
  · exact twoBlockTensorizedConfigurationKernel_pushforward
      sourceMass sourceStates targetMass
      sourceFirstParameter sourceSecondParameter
      targetFirstParameter targetSecondParameter
      sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent
      hsourceFirstEvent hsourceSecondEvent hsourceTotal target
  refine Q'.eqv_trans _ (targetMass target * ((1 : Q') + 0)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (targetMass target) _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _
          ((centeredEventCoordinate targetFirstParameter targetFirstEvent
              target *
            centeredEventCoordinate targetSecondParameter targetSecondEvent
              target) * 0) _
          (Q'.mul_eqv_congr_left _ _ _ hcross)
          (Q'.mul_zero_eqv _)))
  rw [Q'.add_zero']
  exact Q'.mul_one_eqv _

/-! ## A covariance counterterm that preserves both finite marginals -/

/-- The two-block product density with the exact second-order covariance
counterterm.  `sourceCross` and `targetCross` are data of the two complete
joint laws; in particular this construction does not infer them from the
one-block marginals. -/
def covarianceCorrectedTensorDensity
    (epsilon sourceFirst sourceSecond targetFirst targetSecond
      sourceCross targetCross : Q') : Q' :=
  (((1 : Q') + epsilon * sourceFirst * targetFirst) *
      ((1 : Q') + epsilon * sourceSecond * targetSecond) +
    -((epsilon * epsilon) * (sourceFirst * sourceSecond) * targetCross)) +
    -((epsilon * epsilon) * sourceCross *
      (targetFirst * targetSecond + -targetCross))

/-- Centering the product coordinate by its exact cross moment has zero
finite expectation. -/
theorem finiteCenteredCrossDeviation_total {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter cross : Q')
    (firstEvent secondEvent : A → Bool)
    (hcross : finiteCenteredCrossMoment mass states
      firstParameter secondParameter firstEvent secondEvent ≈ cross)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (fun state => mass state *
          (centeredEventCoordinate firstParameter firstEvent state *
              centeredEventCoordinate secondParameter secondEvent state +
            -cross)) states ≈ 0 := by
  let crossWeighted := fun state => mass state *
    (centeredEventCoordinate firstParameter firstEvent state *
      centeredEventCoordinate secondParameter secondEvent state)
  refine Q'.eqv_trans _
    (listQSum
      (fun state => crossWeighted state + (-cross) * mass state) states) _
    ?_ ?_
  · apply listQSum_congr_on
    intro state _
    unfold crossWeighted
    ac_qeqv
  refine Q'.eqv_trans _
    (listQSum crossWeighted states +
      listQSum (fun state => (-cross) * mass state) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum crossWeighted states + (-cross) * listQSum mass states) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_mul_left (-cross) mass states)) ?_
  change
    finiteCenteredCrossMoment mass states firstParameter secondParameter
        firstEvent secondEvent + (-cross) * listQSum mass states ≈ 0
  refine Q'.eqv_trans _ (cross + (-cross) * 1) _ ?_ ?_
  · exact Q'.add_eqv_congr' hcross
      (Q'.mul_eqv_congr_left (-cross) _ _ htotal)
  refine Q'.eqv_trans _ (cross + -cross) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_one_eqv (-cross))
  exact Q'.add_neg_self_eqv cross

private theorem covarianceCorrectedTensorDensity_target_pointwise
    {A : Type} (mass : A → Q')
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (epsilon sourceFirst sourceSecond sourceCross targetCross : Q')
    (state : A) :
    mass state * covarianceCorrectedTensorDensity epsilon
        sourceFirst sourceSecond
        (centeredEventCoordinate firstParameter firstEvent state)
        (centeredEventCoordinate secondParameter secondEvent state)
        sourceCross targetCross ≈
      twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent
          (epsilon * sourceFirst) (epsilon * sourceSecond) state +
        ((-((epsilon * epsilon) *
            (sourceFirst * sourceSecond) * targetCross)) * mass state +
          (-((epsilon * epsilon) * sourceCross)) *
            (mass state *
              (centeredEventCoordinate firstParameter firstEvent state *
                  centeredEventCoordinate secondParameter secondEvent state +
                -targetCross))) := by
  unfold covarianceCorrectedTensorDensity twoCoordinateTensorTilt
  ac_qeqv

/-- First exact counterterm identity: expectation over the target joint law
is one for every fixed pair of source coordinates. -/
theorem covarianceCorrectedTensorDensity_target_expectation
    {A : Type} (mass : A → Q') (states : List A)
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (epsilon sourceFirst sourceSecond sourceCross targetCross : Q')
    (hfirstEvent :
      finiteEventMass mass states firstEvent ≈ firstParameter)
    (hsecondEvent :
      finiteEventMass mass states secondEvent ≈ secondParameter)
    (htotal : listQSum mass states ≈ 1)
    (hcross : finiteCenteredCrossMoment mass states
      firstParameter secondParameter firstEvent secondEvent ≈ targetCross) :
    listQSum
        (fun state => mass state * covarianceCorrectedTensorDensity epsilon
          sourceFirst sourceSecond
          (centeredEventCoordinate firstParameter firstEvent state)
          (centeredEventCoordinate secondParameter secondEvent state)
          sourceCross targetCross) states ≈ 1 := by
  let firstCorrection :=
    -((epsilon * epsilon) *
      (sourceFirst * sourceSecond) * targetCross)
  let secondCorrection := -((epsilon * epsilon) * sourceCross)
  let crossDeviation := fun state => mass state *
    (centeredEventCoordinate firstParameter firstEvent state *
        centeredEventCoordinate secondParameter secondEvent state +
      -targetCross)
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        twoCoordinateTensorTilt mass firstParameter secondParameter
            firstEvent secondEvent
            (epsilon * sourceFirst) (epsilon * sourceSecond) state +
          (firstCorrection * mass state +
            secondCorrection * crossDeviation state)) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    unfold firstCorrection secondCorrection crossDeviation
    exact covarianceCorrectedTensorDensity_target_pointwise
      mass firstParameter secondParameter firstEvent secondEvent
      epsilon sourceFirst sourceSecond sourceCross targetCross state
  refine Q'.eqv_trans _
    (listQSum
        (twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent
          (epsilon * sourceFirst) (epsilon * sourceSecond)) states +
      listQSum
        (fun state => firstCorrection * mass state +
          secondCorrection * crossDeviation state) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum
        (twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent
          (epsilon * sourceFirst) (epsilon * sourceSecond)) states +
      (listQSum (fun state => firstCorrection * mass state) states +
        listQSum
          (fun state => secondCorrection * crossDeviation state) states)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_add _ _ states)) ?_
  refine Q'.eqv_trans _
    (listQSum
        (twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent
          (epsilon * sourceFirst) (epsilon * sourceSecond)) states +
      (firstCorrection * listQSum mass states +
        secondCorrection * listQSum crossDeviation states)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr'
        (listQSum_mul_left firstCorrection mass states)
        (listQSum_mul_left secondCorrection crossDeviation states))
  have hraw := twoCoordinateTensorTilt_total mass states
    firstParameter secondParameter firstEvent secondEvent
    (epsilon * sourceFirst) (epsilon * sourceSecond)
    hfirstEvent hsecondEvent htotal
  have hdeviation : listQSum crossDeviation states ≈ 0 := by
    unfold crossDeviation
    exact finiteCenteredCrossDeviation_total mass states
      firstParameter secondParameter targetCross firstEvent secondEvent
      hcross htotal
  refine Q'.eqv_trans _
    (((1 : Q') +
        ((epsilon * sourceFirst) * (epsilon * sourceSecond)) *
          finiteCenteredCrossMoment mass states
            firstParameter secondParameter firstEvent secondEvent) +
      (firstCorrection * 1 + secondCorrection * 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr' hraw
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left firstCorrection _ _ htotal)
        (Q'.mul_eqv_congr_left secondCorrection _ _ hdeviation))
  unfold firstCorrection secondCorrection
  have hreplace :
      ((epsilon * sourceFirst) * (epsilon * sourceSecond)) *
          finiteCenteredCrossMoment mass states
            firstParameter secondParameter firstEvent secondEvent ≈
        ((epsilon * sourceFirst) * (epsilon * sourceSecond)) *
          targetCross :=
    Q'.mul_eqv_congr_left _ _ _ hcross
  refine Q'.eqv_trans _
    (((1 : Q') +
        ((epsilon * sourceFirst) * (epsilon * sourceSecond)) * targetCross) +
      ((-((epsilon * epsilon) *
          (sourceFirst * sourceSecond) * targetCross)) * 1 +
        (-((epsilon * epsilon) * sourceCross)) * 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hreplace)
      (Q'.eqv_refl _)
  let rawCross :=
    ((epsilon * sourceFirst) * (epsilon * sourceSecond)) * targetCross
  let correctionCross :=
    ((epsilon * epsilon) * (sourceFirst * sourceSecond)) * targetCross
  have hrawCorrection : rawCross ≈ correctionCross := by
    unfold rawCross correctionCross
    ac_qeqv
  change
    ((1 + rawCross) +
      ((-correctionCross) * 1 +
        (-((epsilon * epsilon) * sourceCross)) * 0)) ≈ 1
  refine Q'.eqv_trans _
    ((1 + rawCross) + (-correctionCross + 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr'
        (Q'.mul_one_eqv (-correctionCross))
        (Q'.mul_zero_eqv (-((epsilon * epsilon) * sourceCross))))
  refine Q'.eqv_trans _ ((1 + rawCross) + -correctionCross) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_of_eq (Q'.add_zero' (-correctionCross)))
  refine Q'.eqv_trans _ ((1 + rawCross) + -rawCross) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr correctionCross rawCross
        (Q'.eqv_symm hrawCorrection))
  refine Q'.eqv_trans _ (1 + (rawCross + -rawCross)) _ ?_ ?_
  · exact Q'.add_assoc_eqv 1 rawCross (-rawCross)
  refine Q'.eqv_trans _ (1 + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_neg_self_eqv rawCross)
  exact Q'.eqv_of_eq (Q'.add_zero' 1)

private theorem covarianceCorrectedTensorDensity_source_pointwise
    {A : Type} (mass : A → Q')
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (epsilon targetFirst targetSecond sourceCross targetCross : Q')
    (state : A) :
    mass state * covarianceCorrectedTensorDensity epsilon
        (centeredEventCoordinate firstParameter firstEvent state)
        (centeredEventCoordinate secondParameter secondEvent state)
        targetFirst targetSecond sourceCross targetCross ≈
      twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent
          (epsilon * targetFirst) (epsilon * targetSecond) state +
        ((-((epsilon * epsilon) * targetCross)) *
            (mass state *
              (centeredEventCoordinate firstParameter firstEvent state *
                centeredEventCoordinate secondParameter secondEvent state)) +
          (-((epsilon * epsilon) * sourceCross *
            (targetFirst * targetSecond + -targetCross))) * mass state) := by
  unfold covarianceCorrectedTensorDensity twoCoordinateTensorTilt
  ac_qeqv

/-- Second exact counterterm identity: expectation over the source joint law
is one for every fixed pair of target coordinates. -/
theorem covarianceCorrectedTensorDensity_source_expectation
    {A : Type} (mass : A → Q') (states : List A)
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (epsilon targetFirst targetSecond sourceCross targetCross : Q')
    (hfirstEvent :
      finiteEventMass mass states firstEvent ≈ firstParameter)
    (hsecondEvent :
      finiteEventMass mass states secondEvent ≈ secondParameter)
    (htotal : listQSum mass states ≈ 1)
    (hcross : finiteCenteredCrossMoment mass states
      firstParameter secondParameter firstEvent secondEvent ≈ sourceCross) :
    listQSum
        (fun state => mass state * covarianceCorrectedTensorDensity epsilon
          (centeredEventCoordinate firstParameter firstEvent state)
          (centeredEventCoordinate secondParameter secondEvent state)
          targetFirst targetSecond sourceCross targetCross) states ≈ 1 := by
  let crossWeighted := fun state => mass state *
    (centeredEventCoordinate firstParameter firstEvent state *
      centeredEventCoordinate secondParameter secondEvent state)
  let crossCorrection := -((epsilon * epsilon) * targetCross)
  let constantCorrection := -((epsilon * epsilon) * sourceCross *
    (targetFirst * targetSecond + -targetCross))
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        twoCoordinateTensorTilt mass firstParameter secondParameter
            firstEvent secondEvent
            (epsilon * targetFirst) (epsilon * targetSecond) state +
          (crossCorrection * crossWeighted state +
            constantCorrection * mass state)) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    unfold crossWeighted crossCorrection constantCorrection
    exact covarianceCorrectedTensorDensity_source_pointwise
      mass firstParameter secondParameter firstEvent secondEvent
      epsilon targetFirst targetSecond sourceCross targetCross state
  refine Q'.eqv_trans _
    (listQSum
        (twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent
          (epsilon * targetFirst) (epsilon * targetSecond)) states +
      listQSum
        (fun state => crossCorrection * crossWeighted state +
          constantCorrection * mass state) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum
        (twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent
          (epsilon * targetFirst) (epsilon * targetSecond)) states +
      (listQSum (fun state => crossCorrection * crossWeighted state) states +
        listQSum (fun state => constantCorrection * mass state) states)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_add _ _ states)) ?_
  refine Q'.eqv_trans _
    (listQSum
        (twoCoordinateTensorTilt mass firstParameter secondParameter
          firstEvent secondEvent
          (epsilon * targetFirst) (epsilon * targetSecond)) states +
      (crossCorrection * listQSum crossWeighted states +
        constantCorrection * listQSum mass states)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr'
        (listQSum_mul_left crossCorrection crossWeighted states)
        (listQSum_mul_left constantCorrection mass states))
  have hraw := twoCoordinateTensorTilt_total mass states
    firstParameter secondParameter firstEvent secondEvent
    (epsilon * targetFirst) (epsilon * targetSecond)
    hfirstEvent hsecondEvent htotal
  have hcrossWeighted : listQSum crossWeighted states ≈ sourceCross := by
    change finiteCenteredCrossMoment mass states
      firstParameter secondParameter firstEvent secondEvent ≈ sourceCross
    exact hcross
  refine Q'.eqv_trans _
    (((1 : Q') +
        ((epsilon * targetFirst) * (epsilon * targetSecond)) *
          finiteCenteredCrossMoment mass states
            firstParameter secondParameter firstEvent secondEvent) +
      (crossCorrection * sourceCross + constantCorrection * 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr' hraw
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left crossCorrection _ _ hcrossWeighted)
        (Q'.mul_eqv_congr_left constantCorrection _ _ htotal))
  unfold crossCorrection constantCorrection
  have hreplace :
      ((epsilon * targetFirst) * (epsilon * targetSecond)) *
          finiteCenteredCrossMoment mass states
            firstParameter secondParameter firstEvent secondEvent ≈
        ((epsilon * targetFirst) * (epsilon * targetSecond)) * sourceCross :=
    Q'.mul_eqv_congr_left _ _ _ hcross
  refine Q'.eqv_trans _
    (((1 : Q') +
        ((epsilon * targetFirst) * (epsilon * targetSecond)) * sourceCross) +
      ((-((epsilon * epsilon) * targetCross)) * sourceCross +
        (-((epsilon * epsilon) * sourceCross *
          (targetFirst * targetSecond + -targetCross))) * 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hreplace)
      (Q'.eqv_refl _)
  let rawCross :=
    ((epsilon * targetFirst) * (epsilon * targetSecond)) * sourceCross
  let crossCounterterm :=
    ((epsilon * epsilon) * targetCross) * sourceCross
  let deviationCounterterm :=
    ((epsilon * epsilon) * sourceCross) *
      (targetFirst * targetSecond + -targetCross)
  let common := (epsilon * epsilon) * sourceCross
  let targetProduct := targetFirst * targetSecond
  have hinside :
      targetCross + (targetProduct + -targetCross) ≈ targetProduct := by
    refine Q'.eqv_trans _ ((targetCross + targetProduct) + -targetCross) _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv targetCross targetProduct (-targetCross))) ?_
    refine Q'.eqv_trans _ ((targetProduct + targetCross) + -targetCross) _
      (Q'.add_eqv_congr'
        (Q'.add_comm_eqv targetCross targetProduct) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ (targetProduct + (targetCross + -targetCross)) _
      (Q'.add_assoc_eqv targetProduct targetCross (-targetCross)) ?_
    refine Q'.eqv_trans _ (targetProduct + 0) _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_neg_self_eqv targetCross)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' targetProduct)
  have hrawCommon : rawCross ≈ common * targetProduct := by
    unfold rawCross common targetProduct
    ac_qeqv
  have hcounterterms :
      crossCounterterm + deviationCounterterm ≈
        common * targetProduct := by
    refine Q'.eqv_trans _
      (common * targetCross +
        common * (targetProduct + -targetCross)) _ ?_ ?_
    · unfold crossCounterterm deviationCounterterm common targetProduct
      exact Q'.add_eqv_congr' (by ac_qeqv) (Q'.eqv_refl _)
    refine Q'.eqv_trans _
      (common * (targetCross + (targetProduct + -targetCross))) _
      (Q'.eqv_symm
        (Q'.mul_add_eqv common targetCross
          (targetProduct + -targetCross))) ?_
    exact Q'.mul_eqv_congr_left common _ _ hinside
  have hbalance :
      rawCross ≈ crossCounterterm + deviationCounterterm := by
    exact Q'.eqv_trans _ (common * targetProduct) _
      hrawCommon (Q'.eqv_symm hcounterterms)
  change
    ((1 + rawCross) +
      ((-((epsilon * epsilon) * targetCross)) * sourceCross +
        (-deviationCounterterm) * 1)) ≈ 1
  refine Q'.eqv_trans _
    ((1 + rawCross) +
      (-crossCounterterm + -deviationCounterterm)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _
          (-(((epsilon * epsilon) * targetCross) * sourceCross)) _
          (Q'.neg_mul_eqv ((epsilon * epsilon) * targetCross) sourceCross)
          (Q'.eqv_refl (-crossCounterterm)))
        (Q'.mul_one_eqv (-deviationCounterterm)))
  refine Q'.eqv_trans _
    ((1 + rawCross) + -(crossCounterterm + deviationCounterterm)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm
        (Q'.neg_add_eqv crossCounterterm deviationCounterterm))
  refine Q'.eqv_trans _ ((1 + rawCross) + -rawCross) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr
        (crossCounterterm + deviationCounterterm) rawCross
        (Q'.eqv_symm hbalance))
  refine Q'.eqv_trans _ (1 + (rawCross + -rawCross)) _ ?_ ?_
  · exact Q'.add_assoc_eqv 1 rawCross (-rawCross)
  refine Q'.eqv_trans _ (1 + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.add_neg_self_eqv rawCross)
  exact Q'.eqv_of_eq (Q'.add_zero' 1)

/-! ### Constructive positivity at a closed rational tilt -/

/-- Every centered Boolean coordinate with parameter in `[0,1]` lies in
`[-1,1]`. -/
theorem centeredEventCoordinate_unit_bounds {A : Type}
    (parameter : Q') (event : A → Bool) (state : A)
    (hparameter0 : (0 : Q') ≤ parameter)
    (hparameter1 : parameter ≤ (1 : Q')) :
    -(1 : Q') ≤ centeredEventCoordinate parameter event state ∧
      centeredEventCoordinate parameter event state ≤ (1 : Q') := by
  cases hevent : event state
  · simp only [centeredEventCoordinate, hevent, Bool.false_eq_true,
      if_false]
    constructor
    · exact Q'.neg_le_neg hparameter1
    · have hneg := Q'.neg_le_neg hparameter0
      exact Q'.le_trans' _ (-(0 : Q')) _ hneg (by decide)
  · simp only [centeredEventCoordinate, hevent, if_true]
    constructor
    · exact Q'.le_trans' _ (0 : Q') _ (by decide)
        (Q'.sub_nonneg_of_le hparameter1)
    · have hneg : -parameter ≤ (0 : Q') :=
        Q'.le_trans' _ (-(0 : Q')) _
          (Q'.neg_le_neg hparameter0) (by decide)
      exact Q'.le_trans' _ ((1 : Q') + 0) _
        (Q'.add_le_add_left 1 (-parameter) 0 hneg)
        (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))

/-- The product of two quantities in `[-1,1]` remains in `[-1,1]`. -/
theorem qUnitProduct_bounds (u v : Q')
    (huLower : -(1 : Q') ≤ u) (huUpper : u ≤ (1 : Q'))
    (hvLower : -(1 : Q') ≤ v) (hvUpper : v ≤ (1 : Q')) :
    -(1 : Q') ≤ u * v ∧ u * v ≤ (1 : Q') := by
  have hupperRaw : u * v ≤ (1 : Q') * 1 :=
    Q'.mul_le_of_bounds (by decide) (by decide)
      huLower huUpper hvLower hvUpper
  have hupper : u * v ≤ (1 : Q') :=
    Q'.le_trans' _ ((1 : Q') * 1) _ hupperRaw
      (Q'.le_of_eqv (Q'.mul_one_eqv 1))
  have hnegULower : -(1 : Q') ≤ -u := Q'.neg_le_neg huUpper
  have hnegUUpper : -u ≤ (1 : Q') := by
    refine Q'.le_trans' _ (-(-(1 : Q'))) _
      (Q'.neg_le_neg huLower) ?_
    exact Q'.le_of_eqv (Q'.neg_neg_eqv 1)
  have hnegUpperRaw : (-u) * v ≤ (1 : Q') * 1 :=
    Q'.mul_le_of_bounds (by decide) (by decide)
      hnegULower hnegUUpper hvLower hvUpper
  have hnegUpper : -(u * v) ≤ (1 : Q') := by
    refine Q'.le_trans' _ ((-u) * v) _ ?_ ?_
    · exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.neg_mul_eqv u v))
    · exact Q'.le_trans' _ ((1 : Q') * 1) _ hnegUpperRaw
        (Q'.le_of_eqv (Q'.mul_one_eqv 1))
  have hlowerNeg : -(1 : Q') ≤ -(-(u * v)) :=
    Q'.neg_le_neg hnegUpper
  have hlower : -(1 : Q') ≤ u * v :=
    Q'.le_trans' _ (-(-(u * v))) _ hlowerNeg
      (Q'.le_of_eqv (Q'.neg_neg_eqv (u * v)))
  exact ⟨hlower, hupper⟩

/-- A difference of two quantities in `[-1,1]` lies in `[-2,2]`. -/
theorem qUnitDifference_bounds (u v : Q')
    (huLower : -(1 : Q') ≤ u) (huUpper : u ≤ (1 : Q'))
    (hvLower : -(1 : Q') ≤ v) (hvUpper : v ≤ (1 : Q')) :
    -(2 : Q') ≤ u + -v ∧ u + -v ≤ (2 : Q') := by
  have hnegVLower : -(1 : Q') ≤ -v := Q'.neg_le_neg hvUpper
  have hnegVUpper : -v ≤ (1 : Q') := by
    refine Q'.le_trans' _ (-(-(1 : Q'))) _
      (Q'.neg_le_neg hvLower) ?_
    exact Q'.le_of_eqv (Q'.neg_neg_eqv 1)
  constructor
  · exact Q'.le_trans' _ (-(1 : Q') + -(1 : Q')) _
      (by decide) (Q'.add_le_add huLower hnegVLower)
  · exact Q'.le_trans' _ ((1 : Q') + 1) _
      (Q'.add_le_add huUpper hnegVUpper) (by decide)

/-- A cross-centered moment of two Boolean coordinates under a nonnegative
normalized finite law lies in `[-1,1]`. -/
theorem finiteCenteredCrossMoment_unit_bounds {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter : Q')
    (firstEvent secondEvent : A → Bool)
    (hmass : ∀ state, state ∈ states → (0 : Q') ≤ mass state)
    (hfirst0 : (0 : Q') ≤ firstParameter)
    (hfirst1 : firstParameter ≤ (1 : Q'))
    (hsecond0 : (0 : Q') ≤ secondParameter)
    (hsecond1 : secondParameter ≤ (1 : Q'))
    (hfirstEvent :
      finiteEventMass mass states firstEvent ≈ firstParameter)
    (hsecondEvent :
      finiteEventMass mass states secondEvent ≈ secondParameter)
    (htotal : listQSum mass states ≈ 1) :
    -(1 : Q') ≤ finiteCenteredCrossMoment mass states
        firstParameter secondParameter firstEvent secondEvent ∧
      finiteCenteredCrossMoment mass states
        firstParameter secondParameter firstEvent secondEvent ≤ (1 : Q') := by
  let joint := finiteJointEventMass mass states firstEvent secondEvent
  let product := firstParameter * secondParameter
  have hjoint0 : (0 : Q') ≤ joint := by
    unfold joint finiteJointEventMass
    exact finiteEventMass_nonnegative mass states _ hmass
  have hjoint1 : joint ≤ (1 : Q') := by
    unfold joint finiteJointEventMass
    exact finiteEventMass_le_one mass states _ hmass htotal
  have hproduct0 : (0 : Q') ≤ product := by
    unfold product
    exact Q'.mul_nonneg _ _ hfirst0 hsecond0
  have hproduct1 : product ≤ (1 : Q') := by
    unfold product
    refine Q'.le_trans' _ ((1 : Q') * 1) _ ?_
      (Q'.le_of_eqv (Q'.mul_one_eqv 1))
    exact Q'.mul_le_mul_of_nonneg hfirst1 hsecond1
      (by decide) hsecond0
  have hlowerRhs : -(1 : Q') ≤ joint + -product := by
    have hnegLower : -(1 : Q') ≤ -product := Q'.neg_le_neg hproduct1
    have hadd : -product ≤ -product + joint :=
      Q'.add_le_self_of_nonneg (-product) joint hjoint0
    exact Q'.le_trans' _ (-product) _ hnegLower
      (Q'.le_trans' _ (-product + joint) _ hadd
        (Q'.le_of_eqv (Q'.add_comm_eqv (-product) joint)))
  have hupperRhs : joint + -product ≤ (1 : Q') := by
    have hnegUpper : -product ≤ (0 : Q') := by
      exact Q'.le_trans' _ (-(0 : Q')) _
        (Q'.neg_le_neg hproduct0) (by decide)
    refine Q'.le_trans' _ (joint + 0) _
      (Q'.add_le_add_left joint (-product) 0 hnegUpper) ?_
    exact Q'.le_trans' _ joint _
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' joint))) hjoint1
  have hformula := finiteCenteredCrossMoment_eqv_joint_sub_product
    mass states firstParameter secondParameter firstEvent secondEvent
    hfirstEvent hsecondEvent htotal
  change
    finiteCenteredCrossMoment mass states firstParameter secondParameter
        firstEvent secondEvent ≈ joint + -product at hformula
  constructor
  · exact Q'.le_trans' _ (joint + -product) _ hlowerRhs
      (Q'.le_of_eqv (Q'.eqv_symm hformula))
  · exact Q'.le_trans' _ (joint + -product) _
      (Q'.le_of_eqv hformula) hupperRhs

/-- Uniform lower bound for the corrected density.  It uses only the unit
bounds of the four centered coordinates and the two exact cross moments. -/
theorem covarianceCorrectedTensorDensity_lower_bound
    (epsilon sourceFirst sourceSecond targetFirst targetSecond
      sourceCross targetCross : Q')
    (hepsilon0 : (0 : Q') ≤ epsilon)
    (hepsilon1 : epsilon ≤ (1 : Q'))
    (hsourceFirst : -(1 : Q') ≤ sourceFirst ∧ sourceFirst ≤ (1 : Q'))
    (hsourceSecond : -(1 : Q') ≤ sourceSecond ∧ sourceSecond ≤ (1 : Q'))
    (htargetFirst : -(1 : Q') ≤ targetFirst ∧ targetFirst ≤ (1 : Q'))
    (htargetSecond : -(1 : Q') ≤ targetSecond ∧ targetSecond ≤ (1 : Q'))
    (hsourceCross : -(1 : Q') ≤ sourceCross ∧ sourceCross ≤ (1 : Q'))
    (htargetCross : -(1 : Q') ≤ targetCross ∧ targetCross ≤ (1 : Q')) :
    (((1 : Q') + -epsilon) * ((1 : Q') + -epsilon) +
        -((epsilon * epsilon) * 1)) +
      -((epsilon * epsilon) * 2) ≤
        covarianceCorrectedTensorDensity epsilon
          sourceFirst sourceSecond targetFirst targetSecond
          sourceCross targetCross := by
  let lowerFactor := (1 : Q') + -epsilon
  let firstFactor := (1 : Q') + epsilon * sourceFirst * targetFirst
  let secondFactor := (1 : Q') + epsilon * sourceSecond * targetSecond
  have hepsilonProduct0 : (0 : Q') ≤ epsilon * epsilon :=
    Q'.mul_nonneg _ _ hepsilon0 hepsilon0
  have hlowerFactor0 : (0 : Q') ≤ lowerFactor := by
    unfold lowerFactor
    exact Q'.sub_nonneg_of_le hepsilon1
  have hfirstCoordinate := qUnitProduct_bounds sourceFirst targetFirst
    hsourceFirst.1 hsourceFirst.2 htargetFirst.1 htargetFirst.2
  have hsecondCoordinate := qUnitProduct_bounds sourceSecond targetSecond
    hsourceSecond.1 hsourceSecond.2 htargetSecond.1 htargetSecond.2
  have hscaledFirst : -epsilon ≤ epsilon * sourceFirst * targetFirst := by
    have hscale := Q'.mul_le_mul_of_nonneg_left
      (-(1 : Q')) (sourceFirst * targetFirst) epsilon
      hfirstCoordinate.1 hepsilon0
    have hminus : epsilon * -(1 : Q') ≈ -epsilon := by
      exact Q'.eqv_trans _ (-(epsilon * 1)) _
        (Q'.mul_neg_eqv epsilon 1)
        (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv epsilon))
    refine Q'.le_trans' _ (epsilon * -(1 : Q')) _
      (Q'.le_of_eqv (Q'.eqv_symm hminus)) ?_
    exact Q'.le_trans' _ (epsilon * (sourceFirst * targetFirst)) _
      hscale (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv epsilon sourceFirst targetFirst)))
  have hscaledSecond : -epsilon ≤ epsilon * sourceSecond * targetSecond := by
    have hscale := Q'.mul_le_mul_of_nonneg_left
      (-(1 : Q')) (sourceSecond * targetSecond) epsilon
      hsecondCoordinate.1 hepsilon0
    have hminus : epsilon * -(1 : Q') ≈ -epsilon := by
      exact Q'.eqv_trans _ (-(epsilon * 1)) _
        (Q'.mul_neg_eqv epsilon 1)
        (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv epsilon))
    refine Q'.le_trans' _ (epsilon * -(1 : Q')) _
      (Q'.le_of_eqv (Q'.eqv_symm hminus)) ?_
    exact Q'.le_trans' _ (epsilon * (sourceSecond * targetSecond)) _
      hscale (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv epsilon sourceSecond targetSecond)))
  have hlowerFirst : lowerFactor ≤ firstFactor := by
    unfold lowerFactor firstFactor
    exact Q'.add_le_add_left 1 (-epsilon)
      (epsilon * sourceFirst * targetFirst) hscaledFirst
  have hlowerSecond : lowerFactor ≤ secondFactor := by
    unfold lowerFactor secondFactor
    exact Q'.add_le_add_left 1 (-epsilon)
      (epsilon * sourceSecond * targetSecond) hscaledSecond
  have hfirst0 : (0 : Q') ≤ firstFactor :=
    Q'.le_trans' _ lowerFactor _ hlowerFactor0 hlowerFirst
  have hsecond0 : (0 : Q') ≤ secondFactor :=
    Q'.le_trans' _ lowerFactor _ hlowerFactor0 hlowerSecond
  have hfactorProduct :
      lowerFactor * lowerFactor ≤ firstFactor * secondFactor := by
    refine Q'.le_trans' _ (lowerFactor * secondFactor) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_left
        lowerFactor secondFactor lowerFactor hlowerSecond hlowerFactor0
    · exact Q'.mul_le_mul_of_nonneg_right
        lowerFactor firstFactor secondFactor hlowerFirst hsecond0
  have hsourceProduct := qUnitProduct_bounds sourceFirst sourceSecond
    hsourceFirst.1 hsourceFirst.2 hsourceSecond.1 hsourceSecond.2
  have hfirstCorrectionCoordinate := qUnitProduct_bounds
    (sourceFirst * sourceSecond) targetCross
    hsourceProduct.1 hsourceProduct.2 htargetCross.1 htargetCross.2
  have hfirstCorrection :
      (epsilon * epsilon) * (sourceFirst * sourceSecond) * targetCross ≤
        (epsilon * epsilon) * 1 := by
    refine Q'.le_trans' _
      (epsilon * epsilon * ((sourceFirst * sourceSecond) * targetCross)) _
      (Q'.le_of_eqv
        (Q'.mul_assoc_eqv (epsilon * epsilon)
          (sourceFirst * sourceSecond) targetCross)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      hfirstCorrectionCoordinate.2 hepsilonProduct0
  have htargetProduct := qUnitProduct_bounds targetFirst targetSecond
    htargetFirst.1 htargetFirst.2 htargetSecond.1 htargetSecond.2
  have htargetDeviation := qUnitDifference_bounds
    (targetFirst * targetSecond) targetCross
    htargetProduct.1 htargetProduct.2 htargetCross.1 htargetCross.2
  have hsecondCorrectionCoordinate :
      sourceCross * (targetFirst * targetSecond + -targetCross) ≤
        (1 : Q') * 2 :=
    Q'.mul_le_of_bounds (by decide) (by decide)
      hsourceCross.1 hsourceCross.2
      htargetDeviation.1 htargetDeviation.2
  have hsecondCorrection :
      (epsilon * epsilon) * sourceCross *
          (targetFirst * targetSecond + -targetCross) ≤
        (epsilon * epsilon) * 2 := by
    refine Q'.le_trans' _
      ((epsilon * epsilon) *
        (sourceCross * (targetFirst * targetSecond + -targetCross))) _
      (Q'.le_of_eqv
        (Q'.mul_assoc_eqv (epsilon * epsilon) sourceCross
          (targetFirst * targetSecond + -targetCross))) ?_
    refine Q'.le_trans' _ ((epsilon * epsilon) * ((1 : Q') * 2)) _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        hsecondCorrectionCoordinate hepsilonProduct0) ?_
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (epsilon * epsilon) _ _
        (Q'.one_mul_eqv 2))
  unfold covarianceCorrectedTensorDensity
  change
    (lowerFactor * lowerFactor + -((epsilon * epsilon) * 1)) +
        -((epsilon * epsilon) * 2) ≤
      (firstFactor * secondFactor +
        -((epsilon * epsilon) * (sourceFirst * sourceSecond) * targetCross)) +
        -((epsilon * epsilon) * sourceCross *
          (targetFirst * targetSecond + -targetCross))
  exact Q'.add_le_add
    (Q'.add_le_add hfactorProduct (Q'.neg_le_neg hfirstCorrection))
    (Q'.neg_le_neg hsecondCorrection)

def covarianceCorrectionEpsilon : Q' := Q'.mkPos 1 4 (by decide)

/-- The closed choice `epsilon = 1/4` makes the covariance-corrected density
nonnegative uniformly over every admissible pair of finite Boolean laws. -/
theorem covarianceCorrectedTensorDensity_quarter_nonnegative
    (sourceFirst sourceSecond targetFirst targetSecond
      sourceCross targetCross : Q')
    (hsourceFirst : -(1 : Q') ≤ sourceFirst ∧ sourceFirst ≤ (1 : Q'))
    (hsourceSecond : -(1 : Q') ≤ sourceSecond ∧ sourceSecond ≤ (1 : Q'))
    (htargetFirst : -(1 : Q') ≤ targetFirst ∧ targetFirst ≤ (1 : Q'))
    (htargetSecond : -(1 : Q') ≤ targetSecond ∧ targetSecond ≤ (1 : Q'))
    (hsourceCross : -(1 : Q') ≤ sourceCross ∧ sourceCross ≤ (1 : Q'))
    (htargetCross : -(1 : Q') ≤ targetCross ∧ targetCross ≤ (1 : Q')) :
    (0 : Q') ≤ covarianceCorrectedTensorDensity covarianceCorrectionEpsilon
      sourceFirst sourceSecond targetFirst targetSecond
      sourceCross targetCross := by
  have hlower := covarianceCorrectedTensorDensity_lower_bound
    covarianceCorrectionEpsilon sourceFirst sourceSecond
    targetFirst targetSecond sourceCross targetCross
    (by decide) (by decide)
    hsourceFirst hsourceSecond htargetFirst htargetSecond
    hsourceCross htargetCross
  exact Q'.le_trans' _
    ((((1 : Q') + -covarianceCorrectionEpsilon) *
        ((1 : Q') + -covarianceCorrectionEpsilon) +
      -((covarianceCorrectionEpsilon * covarianceCorrectionEpsilon) * 1)) +
      -((covarianceCorrectionEpsilon * covarianceCorrectionEpsilon) * 2)) _
    (by decide) hlower

/-! ### The corrected two-block finite configuration kernel -/

def covarianceCorrectedTwoBlockConfigurationKernel {Source Target : Type}
    (targetMass : Target → Q')
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (epsilon sourceCross targetCross : Q')
    (source : Source) (target : Target) : Q' :=
  targetMass target * covarianceCorrectedTensorDensity epsilon
    (centeredEventCoordinate sourceFirstParameter sourceFirstEvent source)
    (centeredEventCoordinate sourceSecondParameter sourceSecondEvent source)
    (centeredEventCoordinate targetFirstParameter targetFirstEvent target)
    (centeredEventCoordinate targetSecondParameter targetSecondEvent target)
    sourceCross targetCross

theorem covarianceCorrectedTwoBlockConfigurationKernel_quarter_nonnegative
    {Source Target : Type}
    (targetMass : Target → Q')
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (sourceCross targetCross : Q')
    (hsourceFirst0 : (0 : Q') ≤ sourceFirstParameter)
    (hsourceFirst1 : sourceFirstParameter ≤ (1 : Q'))
    (hsourceSecond0 : (0 : Q') ≤ sourceSecondParameter)
    (hsourceSecond1 : sourceSecondParameter ≤ (1 : Q'))
    (htargetFirst0 : (0 : Q') ≤ targetFirstParameter)
    (htargetFirst1 : targetFirstParameter ≤ (1 : Q'))
    (htargetSecond0 : (0 : Q') ≤ targetSecondParameter)
    (htargetSecond1 : targetSecondParameter ≤ (1 : Q'))
    (hsourceCross : -(1 : Q') ≤ sourceCross ∧ sourceCross ≤ (1 : Q'))
    (htargetCross : -(1 : Q') ≤ targetCross ∧ targetCross ≤ (1 : Q'))
    (htargetMass : ∀ target, (0 : Q') ≤ targetMass target)
    (source : Source) (target : Target) :
    (0 : Q') ≤ covarianceCorrectedTwoBlockConfigurationKernel targetMass
      sourceFirstParameter sourceSecondParameter
      targetFirstParameter targetSecondParameter
      sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent
      covarianceCorrectionEpsilon sourceCross targetCross source target := by
  unfold covarianceCorrectedTwoBlockConfigurationKernel
  exact Q'.mul_nonneg _ _ (htargetMass target)
    (covarianceCorrectedTensorDensity_quarter_nonnegative _ _ _ _ _ _
      (centeredEventCoordinate_unit_bounds sourceFirstParameter
        sourceFirstEvent source hsourceFirst0 hsourceFirst1)
      (centeredEventCoordinate_unit_bounds sourceSecondParameter
        sourceSecondEvent source hsourceSecond0 hsourceSecond1)
      (centeredEventCoordinate_unit_bounds targetFirstParameter
        targetFirstEvent target htargetFirst0 htargetFirst1)
      (centeredEventCoordinate_unit_bounds targetSecondParameter
        targetSecondEvent target htargetSecond0 htargetSecond1)
      hsourceCross htargetCross)

theorem covarianceCorrectedTwoBlockConfigurationKernel_row_normalized
    {Source Target : Type}
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (epsilon sourceCross targetCross : Q')
    (htargetFirstEvent :
      finiteEventMass targetMass targetStates targetFirstEvent ≈
        targetFirstParameter)
    (htargetSecondEvent :
      finiteEventMass targetMass targetStates targetSecondEvent ≈
        targetSecondParameter)
    (htargetTotal : listQSum targetMass targetStates ≈ 1)
    (htargetCross : finiteCenteredCrossMoment targetMass targetStates
      targetFirstParameter targetSecondParameter
      targetFirstEvent targetSecondEvent ≈ targetCross)
    (source : Source) :
    listQSum
        (covarianceCorrectedTwoBlockConfigurationKernel targetMass
          sourceFirstParameter sourceSecondParameter
          targetFirstParameter targetSecondParameter
          sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent
          epsilon sourceCross targetCross source) targetStates ≈ 1 := by
  unfold covarianceCorrectedTwoBlockConfigurationKernel
  exact covarianceCorrectedTensorDensity_target_expectation
    targetMass targetStates targetFirstParameter targetSecondParameter
    targetFirstEvent targetSecondEvent epsilon
    (centeredEventCoordinate sourceFirstParameter sourceFirstEvent source)
    (centeredEventCoordinate sourceSecondParameter sourceSecondEvent source)
    sourceCross targetCross htargetFirstEvent htargetSecondEvent
    htargetTotal htargetCross

theorem covarianceCorrectedTwoBlockConfigurationKernel_pushforward
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q')
    (sourceFirstParameter sourceSecondParameter : Q')
    (targetFirstParameter targetSecondParameter : Q')
    (sourceFirstEvent sourceSecondEvent : Source → Bool)
    (targetFirstEvent targetSecondEvent : Target → Bool)
    (epsilon sourceCross targetCross : Q')
    (hsourceFirstEvent :
      finiteEventMass sourceMass sourceStates sourceFirstEvent ≈
        sourceFirstParameter)
    (hsourceSecondEvent :
      finiteEventMass sourceMass sourceStates sourceSecondEvent ≈
        sourceSecondParameter)
    (hsourceTotal : listQSum sourceMass sourceStates ≈ 1)
    (hsourceCross : finiteCenteredCrossMoment sourceMass sourceStates
      sourceFirstParameter sourceSecondParameter
      sourceFirstEvent sourceSecondEvent ≈ sourceCross)
    (target : Target) :
    configurationPushforward sourceMass sourceStates
        (covarianceCorrectedTwoBlockConfigurationKernel targetMass
          sourceFirstParameter sourceSecondParameter
          targetFirstParameter targetSecondParameter
          sourceFirstEvent sourceSecondEvent targetFirstEvent targetSecondEvent
          epsilon sourceCross targetCross) target ≈ targetMass target := by
  unfold configurationPushforward
  refine Q'.eqv_trans _
    (listQSum
      (fun source => targetMass target *
        (sourceMass source * covarianceCorrectedTensorDensity epsilon
          (centeredEventCoordinate sourceFirstParameter sourceFirstEvent source)
          (centeredEventCoordinate sourceSecondParameter sourceSecondEvent source)
          (centeredEventCoordinate targetFirstParameter targetFirstEvent target)
          (centeredEventCoordinate targetSecondParameter targetSecondEvent target)
          sourceCross targetCross)) sourceStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    unfold covarianceCorrectedTwoBlockConfigurationKernel
    ac_qeqv
  refine Q'.eqv_trans _
    (targetMass target *
      listQSum
        (fun source => sourceMass source *
          covarianceCorrectedTensorDensity epsilon
            (centeredEventCoordinate sourceFirstParameter sourceFirstEvent source)
            (centeredEventCoordinate sourceSecondParameter sourceSecondEvent source)
            (centeredEventCoordinate targetFirstParameter targetFirstEvent target)
            (centeredEventCoordinate targetSecondParameter targetSecondEvent target)
            sourceCross targetCross) sourceStates) _
    (listQSum_mul_left (targetMass target) _ sourceStates) ?_
  refine Q'.eqv_trans _ (targetMass target * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (targetMass target) _ _
      (covarianceCorrectedTensorDensity_source_expectation
        sourceMass sourceStates sourceFirstParameter sourceSecondParameter
        sourceFirstEvent sourceSecondEvent epsilon
        (centeredEventCoordinate targetFirstParameter targetFirstEvent target)
        (centeredEventCoordinate targetSecondParameter targetSecondEvent target)
        sourceCross targetCross hsourceFirstEvent hsourceSecondEvent
        hsourceTotal hsourceCross)
  exact Q'.mul_one_eqv (targetMass target)

/-! ## Instantiation on the genuine adjacent-time physical cylinders -/

def timeZeroUnitCubeConfigurationEvent (volume : Nat) :
    EdgeLabelling → Bool :=
  cutoffOneLiftedFamilyEvent volume
    (unitCubeOutcomeEvent (timeZeroUnitCubeRootAt volume) true)

def timeOneUnitCubeConfigurationEvent (volume : Nat) :
    EdgeLabelling → Bool :=
  cutoffOneLiftedFamilyEvent volume
    (unitCubeOutcomeEvent (timeOneUnitCubeRootAt volume) true)

def adjacentTimeTrueTrueConfigurationEvent (volume : Nat) :
    EdgeLabelling → Bool :=
  cutoffOneLiftedFamilyEvent volume
    (adjacentTimeOutcomeEvent volume true true)

theorem adjacentTimeTrueTrueConfigurationEvent_eq_and
    (volume : Nat) :
    adjacentTimeTrueTrueConfigurationEvent volume =
      (fun state =>
        timeZeroUnitCubeConfigurationEvent volume state &&
          timeOneUnitCubeConfigurationEvent volume state) := by
  funext state
  rfl

theorem timeZeroUnitCubeConfigurationEventMass_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    finiteEventMass
        (normalizedPhysicalMass coupling hcoupling cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (timeZeroUnitCubeConfigurationEvent volume) ≈
      timeZeroMarginalProbability coupling hcoupling cutoff volume true := by
  unfold activityMatchedConfigurationStateSpace
    timeZeroUnitCubeConfigurationEvent timeZeroMarginalProbability
    couplingKFamilyEventProbability
  exact normalizedPhysicalEventMass_eqv_probability _ _ _ _ _

theorem timeOneUnitCubeConfigurationEventMass_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    finiteEventMass
        (normalizedPhysicalMass coupling hcoupling cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (timeOneUnitCubeConfigurationEvent volume) ≈
      timeOneMarginalProbability coupling hcoupling cutoff volume true := by
  unfold activityMatchedConfigurationStateSpace
    timeOneUnitCubeConfigurationEvent timeOneMarginalProbability
    couplingKFamilyEventProbability
  exact normalizedPhysicalEventMass_eqv_probability _ _ _ _ _

theorem adjacentTimeTrueTrueConfigurationEventMass_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    finiteEventMass
        (normalizedPhysicalMass coupling hcoupling cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (adjacentTimeTrueTrueConfigurationEvent volume) ≈
      adjacentTimeJointProbability
        coupling hcoupling cutoff volume true true := by
  unfold activityMatchedConfigurationStateSpace
    adjacentTimeTrueTrueConfigurationEvent adjacentTimeJointProbability
    couplingKFamilyEventProbability
  exact normalizedPhysicalEventMass_eqv_probability _ _ _ _ _

theorem finiteJointEventMass_physicalAdjacentTime_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    finiteJointEventMass
        (normalizedPhysicalMass coupling hcoupling cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (timeZeroUnitCubeConfigurationEvent volume)
        (timeOneUnitCubeConfigurationEvent volume) ≈
      adjacentTimeJointProbability
        coupling hcoupling cutoff volume true true := by
  unfold finiteJointEventMass
  rw [← adjacentTimeTrueTrueConfigurationEvent_eq_and volume]
  exact adjacentTimeTrueTrueConfigurationEventMass_eqv
    coupling hcoupling cutoff volume

/-- This is the actual adjacent-time cross-centered moment of the complete
finite physical spin-foam law.  It is not set to zero. -/
def physicalAdjacentTimeCrossMoment
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) : Q' :=
  finiteCenteredCrossMoment
    (normalizedPhysicalMass coupling hcoupling cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (timeZeroMarginalProbability coupling hcoupling cutoff volume true)
    (timeOneMarginalProbability coupling hcoupling cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)

/-- The tensor obstruction is exactly the connected adjacent-time cylinder
correlation `P(11) - P(1·)P(·1)`. -/
theorem physicalAdjacentTimeCrossMoment_eqv_connected_probability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    physicalAdjacentTimeCrossMoment coupling hcoupling cutoff volume ≈
      adjacentTimeJointProbability
          coupling hcoupling cutoff volume true true +
        -(timeZeroMarginalProbability
            coupling hcoupling cutoff volume true *
          timeOneMarginalProbability
            coupling hcoupling cutoff volume true) := by
  unfold physicalAdjacentTimeCrossMoment
  refine Q'.eqv_trans _
    (finiteJointEventMass
        (normalizedPhysicalMass coupling hcoupling cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (timeZeroUnitCubeConfigurationEvent volume)
        (timeOneUnitCubeConfigurationEvent volume) +
      -(timeZeroMarginalProbability
          coupling hcoupling cutoff volume true *
        timeOneMarginalProbability
          coupling hcoupling cutoff volume true)) _ ?_ ?_
  · exact finiteCenteredCrossMoment_eqv_joint_sub_product
      (normalizedPhysicalMass coupling hcoupling cutoff volume)
      (activityMatchedConfigurationStateSpace cutoff volume)
      (timeZeroMarginalProbability
        coupling hcoupling cutoff volume true)
      (timeOneMarginalProbability
        coupling hcoupling cutoff volume true)
      (timeZeroUnitCubeConfigurationEvent volume)
      (timeOneUnitCubeConfigurationEvent volume)
      (timeZeroUnitCubeConfigurationEventMass_eqv
        coupling hcoupling cutoff volume)
      (timeOneUnitCubeConfigurationEventMass_eqv
        coupling hcoupling cutoff volume)
      (normalizedPhysicalMass_total
        coupling hcoupling cutoff volume)
  · exact Q'.add_eqv_congr'
      (finiteJointEventMass_physicalAdjacentTime_eqv
        coupling hcoupling cutoff volume)
      (Q'.eqv_refl _)

def physicalTimeZeroCenteredCoordinate
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (state : EdgeLabelling) : Q' :=
  centeredEventCoordinate
    (timeZeroMarginalProbability coupling hcoupling cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume) state

def physicalTimeOneCenteredCoordinate
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (state : EdgeLabelling) : Q' :=
  centeredEventCoordinate
    (timeOneMarginalProbability coupling hcoupling cutoff volume true)
    (timeOneUnitCubeConfigurationEvent volume) state

private theorem timeZeroTrueProbability_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    (0 : Q') ≤ timeZeroMarginalProbability
      coupling hcoupling cutoff volume true := by
  unfold timeZeroMarginalProbability
  exact couplingKFamilyEventProbability_nonnegative _ _ _ _ _

private theorem timeZeroTrueProbability_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    timeZeroMarginalProbability coupling hcoupling cutoff volume true ≤
      (1 : Q') := by
  unfold timeZeroMarginalProbability
  exact couplingKFamilyEventProbability_le_one _ _ _ _ _

private theorem timeOneTrueProbability_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    (0 : Q') ≤ timeOneMarginalProbability
      coupling hcoupling cutoff volume true := by
  unfold timeOneMarginalProbability
  exact couplingKFamilyEventProbability_nonnegative _ _ _ _ _

private theorem timeOneTrueProbability_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    timeOneMarginalProbability coupling hcoupling cutoff volume true ≤
      (1 : Q') := by
  unfold timeOneMarginalProbability
  exact couplingKFamilyEventProbability_le_one _ _ _ _ _

theorem physicalAdjacentTimeCrossMoment_unit_bounds
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) :
    -(1 : Q') ≤ physicalAdjacentTimeCrossMoment
        coupling hcoupling cutoff volume ∧
      physicalAdjacentTimeCrossMoment coupling hcoupling cutoff volume ≤
        (1 : Q') := by
  unfold physicalAdjacentTimeCrossMoment
  exact finiteCenteredCrossMoment_unit_bounds
    (normalizedPhysicalMass coupling hcoupling cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (timeZeroMarginalProbability coupling hcoupling cutoff volume true)
    (timeOneMarginalProbability coupling hcoupling cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (fun state _ => normalizedPhysicalMass_nonnegative
      coupling hcoupling cutoff volume state)
    (timeZeroTrueProbability_nonnegative coupling hcoupling cutoff volume)
    (timeZeroTrueProbability_le_one coupling hcoupling cutoff volume)
    (timeOneTrueProbability_nonnegative coupling hcoupling cutoff volume)
    (timeOneTrueProbability_le_one coupling hcoupling cutoff volume)
    (timeZeroUnitCubeConfigurationEventMass_eqv
      coupling hcoupling cutoff volume)
    (timeOneUnitCubeConfigurationEventMass_eqv
      coupling hcoupling cutoff volume)
    (normalizedPhysicalMass_total coupling hcoupling cutoff volume)

/-- A genuinely two-feature adjacent-time blocking kernel with exact
covariance counterterms.  The source and target cross moments are computed
from their complete finite physical laws, and the tilt is the derived closed
rational `1/4`. -/
def activityMatchedAdjacentTimeCovarianceCorrectedKernel
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) : Q' :=
  covarianceCorrectedTwoBlockConfigurationKernel
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (timeZeroMarginalProbability
      fineCoupling hfine cutoff volume true)
    (timeOneMarginalProbability
      fineCoupling hfine cutoff volume true)
    (timeZeroMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeOneMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    covarianceCorrectionEpsilon
    (physicalAdjacentTimeCrossMoment
      fineCoupling hfine cutoff volume)
    (physicalAdjacentTimeCrossMoment
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    source target

theorem activityMatchedAdjacentTimeCovarianceCorrectedKernel_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) :
    (0 : Q') ≤ activityMatchedAdjacentTimeCovarianceCorrectedKernel
      fineCoupling hfine cutoff volume source target := by
  unfold activityMatchedAdjacentTimeCovarianceCorrectedKernel
  exact covarianceCorrectedTwoBlockConfigurationKernel_quarter_nonnegative
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (timeZeroMarginalProbability fineCoupling hfine cutoff volume true)
    (timeOneMarginalProbability fineCoupling hfine cutoff volume true)
    (timeZeroMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeOneMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (physicalAdjacentTimeCrossMoment fineCoupling hfine cutoff volume)
    (physicalAdjacentTimeCrossMoment
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (timeZeroTrueProbability_nonnegative fineCoupling hfine cutoff volume)
    (timeZeroTrueProbability_le_one fineCoupling hfine cutoff volume)
    (timeOneTrueProbability_nonnegative fineCoupling hfine cutoff volume)
    (timeOneTrueProbability_le_one fineCoupling hfine cutoff volume)
    (timeZeroTrueProbability_nonnegative
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (timeZeroTrueProbability_le_one
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (timeOneTrueProbability_nonnegative
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (timeOneTrueProbability_le_one
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (physicalAdjacentTimeCrossMoment_unit_bounds
      fineCoupling hfine cutoff volume)
    (physicalAdjacentTimeCrossMoment_unit_bounds
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (fun physical => normalizedPhysicalMass_nonnegative
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume physical)
    source target

theorem activityMatchedAdjacentTimeCovarianceCorrectedKernel_row_normalized
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source : EdgeLabelling) :
    listQSum
        (activityMatchedAdjacentTimeCovarianceCorrectedKernel
          fineCoupling hfine cutoff volume source)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈ 1 := by
  unfold activityMatchedAdjacentTimeCovarianceCorrectedKernel
  apply covarianceCorrectedTwoBlockConfigurationKernel_row_normalized
  · exact timeZeroUnitCubeConfigurationEventMass_eqv
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume
  · exact timeOneUnitCubeConfigurationEventMass_eqv
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume
  · exact normalizedPhysicalMass_total
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume
  · exact Q'.eqv_refl _

theorem activityMatchedAdjacentTimeCovarianceCorrectedKernel_pushforward
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (target : EdgeLabelling) :
    configurationPushforward
        (activityMatchedRefinedConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedAdjacentTimeCovarianceCorrectedKernel
          fineCoupling hfine cutoff volume) target ≈
      activityMatchedCoarseConfigurationMass
        fineCoupling hfine cutoff volume target := by
  unfold activityMatchedAdjacentTimeCovarianceCorrectedKernel
  apply covarianceCorrectedTwoBlockConfigurationKernel_pushforward
  · exact timeZeroUnitCubeConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume
  · exact timeOneUnitCubeConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume
  · exact normalizedPhysicalMass_total
      fineCoupling hfine cutoff volume
  · exact Q'.eqv_refl _

/-- The first honest two-block tensor attempt: multiply the two adjacent-time
one-block factors, keeping the complete activity-matched coarse physical law
as the target base mass. -/
def activityMatchedAdjacentTimeTensorKernel
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) : Q' :=
  twoBlockTensorizedConfigurationKernel
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (timeZeroMarginalProbability
      fineCoupling hfine cutoff volume true)
    (timeOneMarginalProbability
      fineCoupling hfine cutoff volume true)
    (timeZeroMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeOneMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    source target

theorem activityMatchedAdjacentTimeTensorKernel_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) :
    (0 : Q') ≤ activityMatchedAdjacentTimeTensorKernel
      fineCoupling hfine cutoff volume source target := by
  unfold activityMatchedAdjacentTimeTensorKernel
  apply twoBlockTensorizedConfigurationKernel_nonnegative
  · exact timeZeroTrueProbability_nonnegative _ _ _ _
  · exact timeZeroTrueProbability_le_one _ _ _ _
  · exact timeOneTrueProbability_nonnegative _ _ _ _
  · exact timeOneTrueProbability_le_one _ _ _ _
  · exact timeZeroTrueProbability_nonnegative _ _ _ _
  · exact timeZeroTrueProbability_le_one _ _ _ _
  · exact timeOneTrueProbability_nonnegative _ _ _ _
  · exact timeOneTrueProbability_le_one _ _ _ _
  · intro physical
    exact normalizedPhysicalMass_nonnegative
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume physical

/-- Exact source-stage audit of the tensor attempt.  The row defect is the
target physical adjacent-time cross moment multiplied by the two source
coordinates. -/
theorem activityMatchedAdjacentTimeTensorKernel_row_sum
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source : EdgeLabelling) :
    listQSum
        (activityMatchedAdjacentTimeTensorKernel
          fineCoupling hfine cutoff volume source)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈
      (1 : Q') +
        (physicalTimeZeroCenteredCoordinate
            fineCoupling hfine cutoff volume source *
          physicalTimeOneCenteredCoordinate
            fineCoupling hfine cutoff volume source) *
          physicalAdjacentTimeCrossMoment
            (unitCubeBlockCoupling fineCoupling)
            (unitCubeBlockCoupling_nonnegative hfine) cutoff volume := by
  unfold activityMatchedAdjacentTimeTensorKernel
    physicalTimeZeroCenteredCoordinate
    physicalTimeOneCenteredCoordinate
    physicalAdjacentTimeCrossMoment
  exact twoBlockTensorizedConfigurationKernel_row_sum
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (timeZeroMarginalProbability fineCoupling hfine cutoff volume true)
    (timeOneMarginalProbability fineCoupling hfine cutoff volume true)
    (timeZeroMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeOneMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEventMass_eqv
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (timeOneUnitCubeConfigurationEventMass_eqv
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (normalizedPhysicalMass_total
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    source

/-- Exact target-law audit of the tensor attempt.  Its pushforward equals
the desired complete coarse law only after the displayed source physical
cross-moment correction is removed. -/
theorem activityMatchedAdjacentTimeTensorKernel_pushforward
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (target : EdgeLabelling) :
    configurationPushforward
        (activityMatchedRefinedConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedAdjacentTimeTensorKernel
          fineCoupling hfine cutoff volume) target ≈
      activityMatchedCoarseConfigurationMass
          fineCoupling hfine cutoff volume target *
        ((1 : Q') +
          (physicalTimeZeroCenteredCoordinate
              (unitCubeBlockCoupling fineCoupling)
              (unitCubeBlockCoupling_nonnegative hfine)
              cutoff volume target *
            physicalTimeOneCenteredCoordinate
              (unitCubeBlockCoupling fineCoupling)
              (unitCubeBlockCoupling_nonnegative hfine)
              cutoff volume target) *
            physicalAdjacentTimeCrossMoment
              fineCoupling hfine cutoff volume) := by
  unfold activityMatchedAdjacentTimeTensorKernel
    physicalTimeZeroCenteredCoordinate
    physicalTimeOneCenteredCoordinate
    physicalAdjacentTimeCrossMoment
  exact twoBlockTensorizedConfigurationKernel_pushforward
    (activityMatchedRefinedConfigurationMass
      fineCoupling hfine cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (timeZeroMarginalProbability fineCoupling hfine cutoff volume true)
    (timeOneMarginalProbability fineCoupling hfine cutoff volume true)
    (timeZeroMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeOneMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume)
    (timeOneUnitCubeConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume)
    (normalizedPhysicalMass_total
      fineCoupling hfine cutoff volume)
    target

theorem activityMatchedAdjacentTimeTensorKernel_row_normalized_of_target_cross_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat)
    (hcross : physicalAdjacentTimeCrossMoment
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume ≈ 0)
    (source : EdgeLabelling) :
    listQSum
        (activityMatchedAdjacentTimeTensorKernel
          fineCoupling hfine cutoff volume source)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈ 1 := by
  unfold activityMatchedAdjacentTimeTensorKernel
    physicalAdjacentTimeCrossMoment at *
  exact twoBlockTensorizedConfigurationKernel_row_normalized_of_cross_zero
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (timeZeroMarginalProbability fineCoupling hfine cutoff volume true)
    (timeOneMarginalProbability fineCoupling hfine cutoff volume true)
    (timeZeroMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeOneMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEventMass_eqv
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (timeOneUnitCubeConfigurationEventMass_eqv
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    (normalizedPhysicalMass_total
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume)
    hcross source

theorem activityMatchedAdjacentTimeTensorKernel_pushforward_of_source_cross_zero
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat)
    (hcross : physicalAdjacentTimeCrossMoment
      fineCoupling hfine cutoff volume ≈ 0)
    (target : EdgeLabelling) :
    configurationPushforward
        (activityMatchedRefinedConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedAdjacentTimeTensorKernel
          fineCoupling hfine cutoff volume) target ≈
      activityMatchedCoarseConfigurationMass
        fineCoupling hfine cutoff volume target := by
  unfold activityMatchedAdjacentTimeTensorKernel
    physicalAdjacentTimeCrossMoment at *
  exact twoBlockTensorizedConfigurationKernel_pushforward_of_cross_zero
    (activityMatchedRefinedConfigurationMass
      fineCoupling hfine cutoff volume)
    (activityMatchedConfigurationStateSpace cutoff volume)
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (timeZeroMarginalProbability fineCoupling hfine cutoff volume true)
    (timeOneMarginalProbability fineCoupling hfine cutoff volume true)
    (timeZeroMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeOneMarginalProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume true)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEvent volume)
    (timeOneUnitCubeConfigurationEvent volume)
    (timeZeroUnitCubeConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume)
    (timeOneUnitCubeConfigurationEventMass_eqv
      fineCoupling hfine cutoff volume)
    (normalizedPhysicalMass_total
      fineCoupling hfine cutoff volume)
    hcross target

/-! ## A covariance-aware corrected two-block cylinder kernel -/

inductive AdjacentTimeFeature where
  | timeZero
  | timeOne
  | trueTrue

def adjacentTimeFeatureEvent (volume : Nat) :
    AdjacentTimeFeature → EdgeLabelling → Bool
  | .timeZero => timeZeroUnitCubeConfigurationEvent volume
  | .timeOne => timeOneUnitCubeConfigurationEvent volume
  | .trueTrue => adjacentTimeTrueTrueConfigurationEvent volume

def adjacentTimeFeatureProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) : AdjacentTimeFeature → Q'
  | .timeZero =>
      timeZeroMarginalProbability coupling hcoupling cutoff volume true
  | .timeOne =>
      timeOneMarginalProbability coupling hcoupling cutoff volume true
  | .trueTrue =>
      adjacentTimeJointProbability coupling hcoupling cutoff volume true true

theorem adjacentTimeFeatureEventMass_eqv
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (feature : AdjacentTimeFeature) :
    finiteEventMass
        (normalizedPhysicalMass coupling hcoupling cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (adjacentTimeFeatureEvent volume feature) ≈
      adjacentTimeFeatureProbability
        coupling hcoupling cutoff volume feature := by
  cases feature with
  | timeZero =>
      exact timeZeroUnitCubeConfigurationEventMass_eqv
        coupling hcoupling cutoff volume
  | timeOne =>
      exact timeOneUnitCubeConfigurationEventMass_eqv
        coupling hcoupling cutoff volume
  | trueTrue =>
      exact adjacentTimeTrueTrueConfigurationEventMass_eqv
        coupling hcoupling cutoff volume

theorem adjacentTimeFeatureProbability_nonnegative
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (feature : AdjacentTimeFeature) :
    (0 : Q') ≤ adjacentTimeFeatureProbability
      coupling hcoupling cutoff volume feature := by
  cases feature with
  | timeZero => exact timeZeroTrueProbability_nonnegative _ _ _ _
  | timeOne => exact timeOneTrueProbability_nonnegative _ _ _ _
  | trueTrue => exact adjacentTimeJointProbability_nonnegative _ _ _ _ _ _

theorem adjacentTimeFeatureProbability_le_one
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff volume : Nat) (feature : AdjacentTimeFeature) :
    adjacentTimeFeatureProbability coupling hcoupling cutoff volume feature ≤
      (1 : Q') := by
  cases feature with
  | timeZero => exact timeZeroTrueProbability_le_one _ _ _ _
  | timeOne => exact timeOneTrueProbability_le_one _ _ _ _
  | trueTrue => exact adjacentTimeJointProbability_le_one _ _ _ _ _ _

/-- One correlation-aware cylinder feature, coupled through the complete
coarse target law. -/
def activityMatchedAdjacentTimeFeatureKernel
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (feature : AdjacentTimeFeature)
    (source target : EdgeLabelling) : Q' :=
  centeredConfigurationKernel
    (activityMatchedCoarseConfigurationMass
      fineCoupling hfine cutoff volume)
    (adjacentTimeFeatureProbability
      fineCoupling hfine cutoff volume feature)
    (adjacentTimeFeatureProbability
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume feature)
    (adjacentTimeFeatureEvent volume feature)
    (adjacentTimeFeatureEvent volume feature)
    source target

theorem activityMatchedAdjacentTimeFeatureKernel_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (feature : AdjacentTimeFeature)
    (source target : EdgeLabelling) :
    (0 : Q') ≤ activityMatchedAdjacentTimeFeatureKernel
      fineCoupling hfine cutoff volume feature source target := by
  unfold activityMatchedAdjacentTimeFeatureKernel
  apply centeredConfigurationKernel_nonnegative
  · exact adjacentTimeFeatureProbability_nonnegative _ _ _ _ _
  · exact adjacentTimeFeatureProbability_le_one _ _ _ _ _
  · exact adjacentTimeFeatureProbability_nonnegative _ _ _ _ _
  · exact adjacentTimeFeatureProbability_le_one _ _ _ _ _
  · intro physical
    exact normalizedPhysicalMass_nonnegative
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume physical

theorem activityMatchedAdjacentTimeFeatureKernel_row_normalized
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (feature : AdjacentTimeFeature)
    (source : EdgeLabelling) :
    listQSum
        (activityMatchedAdjacentTimeFeatureKernel
          fineCoupling hfine cutoff volume feature source)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈ 1 := by
  unfold activityMatchedAdjacentTimeFeatureKernel
  apply centeredConfigurationKernel_row_normalized
  · exact adjacentTimeFeatureEventMass_eqv
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine)
      cutoff volume feature
  · exact normalizedPhysicalMass_total
      (unitCubeBlockCoupling fineCoupling)
      (unitCubeBlockCoupling_nonnegative hfine) cutoff volume

theorem activityMatchedAdjacentTimeFeatureKernel_pushforward
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (feature : AdjacentTimeFeature)
    (target : EdgeLabelling) :
    configurationPushforward
        (activityMatchedRefinedConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedAdjacentTimeFeatureKernel
          fineCoupling hfine cutoff volume feature) target ≈
      activityMatchedCoarseConfigurationMass
        fineCoupling hfine cutoff volume target := by
  unfold activityMatchedAdjacentTimeFeatureKernel
  apply centeredConfigurationKernel_pushforward
  · exact adjacentTimeFeatureEventMass_eqv
      fineCoupling hfine cutoff volume feature
  · exact normalizedPhysicalMass_total
      fineCoupling hfine cutoff volume

def adjacentTimeFeatureThird : Q' := Q'.mkPos 1 3 (by decide)

private theorem listQSum_weighted_three {A : Type}
    (weight : Q') (first second third : A → Q') (states : List A) :
    listQSum
        (fun state => weight * first state +
          (weight * second state + weight * third state)) states ≈
      weight * listQSum first states +
        (weight * listQSum second states +
          weight * listQSum third states) := by
  refine Q'.eqv_trans _
    (listQSum (fun state => weight * first state) states +
      listQSum
        (fun state => weight * second state + weight * third state)
        states) _ (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum (fun state => weight * first state) states +
      (listQSum (fun state => weight * second state) states +
        listQSum (fun state => weight * third state) states)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_add _ _ states)
  exact Q'.add_eqv_congr'
    (listQSum_mul_left weight first states)
    (Q'.add_eqv_congr'
      (listQSum_mul_left weight second states)
      (listQSum_mul_left weight third states))

/-- Corrected local-cylinder construction: instead of multiplying marginal
factors (which creates the covariance defect), take an exact convex mixture
of the time-zero, time-one, and genuine joint-atom couplings.  This preserves
correlation information and requires no independence.  Its target refresh is
still global, so it is not claimed to be a spatial phase-cell RG map. -/
def activityMatchedAdjacentTimeCorrelationAwareKernel
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) : Q' :=
  adjacentTimeFeatureThird *
      activityMatchedAdjacentTimeFeatureKernel
        fineCoupling hfine cutoff volume .timeZero source target +
    (adjacentTimeFeatureThird *
        activityMatchedAdjacentTimeFeatureKernel
          fineCoupling hfine cutoff volume .timeOne source target +
      adjacentTimeFeatureThird *
        activityMatchedAdjacentTimeFeatureKernel
          fineCoupling hfine cutoff volume .trueTrue source target)

theorem activityMatchedAdjacentTimeCorrelationAwareKernel_nonnegative
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source target : EdgeLabelling) :
    (0 : Q') ≤ activityMatchedAdjacentTimeCorrelationAwareKernel
      fineCoupling hfine cutoff volume source target := by
  unfold activityMatchedAdjacentTimeCorrelationAwareKernel
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (by decide)
      (activityMatchedAdjacentTimeFeatureKernel_nonnegative
        fineCoupling hfine cutoff volume .timeZero source target))
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide)
        (activityMatchedAdjacentTimeFeatureKernel_nonnegative
          fineCoupling hfine cutoff volume .timeOne source target))
      (Q'.mul_nonneg _ _ (by decide)
        (activityMatchedAdjacentTimeFeatureKernel_nonnegative
          fineCoupling hfine cutoff volume .trueTrue source target)))

theorem activityMatchedAdjacentTimeCorrelationAwareKernel_row_normalized
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (source : EdgeLabelling) :
    listQSum
        (activityMatchedAdjacentTimeCorrelationAwareKernel
          fineCoupling hfine cutoff volume source)
        (activityMatchedConfigurationStateSpace cutoff volume) ≈ 1 := by
  unfold activityMatchedAdjacentTimeCorrelationAwareKernel
  refine Q'.eqv_trans _
    (adjacentTimeFeatureThird *
        listQSum
          (activityMatchedAdjacentTimeFeatureKernel
            fineCoupling hfine cutoff volume .timeZero source)
          (activityMatchedConfigurationStateSpace cutoff volume) +
      (adjacentTimeFeatureThird *
          listQSum
            (activityMatchedAdjacentTimeFeatureKernel
              fineCoupling hfine cutoff volume .timeOne source)
            (activityMatchedConfigurationStateSpace cutoff volume) +
        adjacentTimeFeatureThird *
          listQSum
            (activityMatchedAdjacentTimeFeatureKernel
              fineCoupling hfine cutoff volume .trueTrue source)
            (activityMatchedConfigurationStateSpace cutoff volume))) _ ?_ ?_
  · exact listQSum_weighted_three adjacentTimeFeatureThird _ _ _ _
  refine Q'.eqv_trans _
    (adjacentTimeFeatureThird * 1 +
      (adjacentTimeFeatureThird * 1 +
        adjacentTimeFeatureThird * 1)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left adjacentTimeFeatureThird _ _
        (activityMatchedAdjacentTimeFeatureKernel_row_normalized
          fineCoupling hfine cutoff volume .timeZero source))
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left adjacentTimeFeatureThird _ _
          (activityMatchedAdjacentTimeFeatureKernel_row_normalized
            fineCoupling hfine cutoff volume .timeOne source))
        (Q'.mul_eqv_congr_left adjacentTimeFeatureThird _ _
          (activityMatchedAdjacentTimeFeatureKernel_row_normalized
            fineCoupling hfine cutoff volume .trueTrue source)))
  decide

private theorem source_mul_weighted_three
    (sourceMass weight first second third : Q') :
    sourceMass * (weight * first + (weight * second + weight * third)) ≈
      weight * (sourceMass * first) +
        (weight * (sourceMass * second) +
          weight * (sourceMass * third)) := by
  refine Q'.eqv_trans _
    (sourceMass * (weight * first) +
      sourceMass * (weight * second + weight * third)) _
    (Q'.mul_add_eqv sourceMass _ _) ?_
  refine Q'.eqv_trans _
    (sourceMass * (weight * first) +
      (sourceMass * (weight * second) +
        sourceMass * (weight * third))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_add_eqv sourceMass _ _)
  apply Q'.add_eqv_congr'
  · ac_qeqv
  apply Q'.add_eqv_congr' <;> ac_qeqv

theorem activityMatchedAdjacentTimeCorrelationAwareKernel_pushforward
    (fineCoupling : Q') (hfine : (0 : Q') ≤ fineCoupling)
    (cutoff volume : Nat) (target : EdgeLabelling) :
    configurationPushforward
        (activityMatchedRefinedConfigurationMass
          fineCoupling hfine cutoff volume)
        (activityMatchedConfigurationStateSpace cutoff volume)
        (activityMatchedAdjacentTimeCorrelationAwareKernel
          fineCoupling hfine cutoff volume) target ≈
      activityMatchedCoarseConfigurationMass
        fineCoupling hfine cutoff volume target := by
  let sourceMass := activityMatchedRefinedConfigurationMass
    fineCoupling hfine cutoff volume
  let targetMass := activityMatchedCoarseConfigurationMass
    fineCoupling hfine cutoff volume target
  let sourceStates := activityMatchedConfigurationStateSpace cutoff volume
  let featureKernel := activityMatchedAdjacentTimeFeatureKernel
    fineCoupling hfine cutoff volume
  unfold configurationPushforward
  refine Q'.eqv_trans _
    (listQSum
      (fun source => adjacentTimeFeatureThird *
          (sourceMass source * featureKernel .timeZero source target) +
        (adjacentTimeFeatureThird *
            (sourceMass source * featureKernel .timeOne source target) +
          adjacentTimeFeatureThird *
            (sourceMass source * featureKernel .trueTrue source target)))
      sourceStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    unfold activityMatchedAdjacentTimeCorrelationAwareKernel
      sourceMass featureKernel
    exact source_mul_weighted_three _ _ _ _ _
  refine Q'.eqv_trans _
    (adjacentTimeFeatureThird *
        listQSum
          (fun source => sourceMass source *
            featureKernel .timeZero source target) sourceStates +
      (adjacentTimeFeatureThird *
          listQSum
            (fun source => sourceMass source *
              featureKernel .timeOne source target) sourceStates +
        adjacentTimeFeatureThird *
          listQSum
            (fun source => sourceMass source *
              featureKernel .trueTrue source target) sourceStates)) _ ?_ ?_
  · exact listQSum_weighted_three adjacentTimeFeatureThird _ _ _ _
  refine Q'.eqv_trans _
    (adjacentTimeFeatureThird * targetMass +
      (adjacentTimeFeatureThird * targetMass +
        adjacentTimeFeatureThird * targetMass)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left adjacentTimeFeatureThird _ _
        (activityMatchedAdjacentTimeFeatureKernel_pushforward
          fineCoupling hfine cutoff volume .timeZero target))
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left adjacentTimeFeatureThird _ _
          (activityMatchedAdjacentTimeFeatureKernel_pushforward
            fineCoupling hfine cutoff volume .timeOne target))
        (Q'.mul_eqv_congr_left adjacentTimeFeatureThird _ _
          (activityMatchedAdjacentTimeFeatureKernel_pushforward
            fineCoupling hfine cutoff volume .trueTrue target)))
  have hweights :
      adjacentTimeFeatureThird +
        (adjacentTimeFeatureThird + adjacentTimeFeatureThird) ≈ 1 := by
    decide
  refine Q'.eqv_trans _
    ((adjacentTimeFeatureThird +
      (adjacentTimeFeatureThird + adjacentTimeFeatureThird)) * targetMass) _
    ?_ ?_
  · refine Q'.eqv_trans _
      (adjacentTimeFeatureThird * targetMass +
        (adjacentTimeFeatureThird + adjacentTimeFeatureThird) * targetMass) _
      ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_symm
          (Q'.add_mul_eqv adjacentTimeFeatureThird
            adjacentTimeFeatureThird targetMass))
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv adjacentTimeFeatureThird
          (adjacentTimeFeatureThird + adjacentTimeFeatureThird) targetMass)
  exact Q'.eqv_trans _ (1 * targetMass) _
    (Q'.mul_eqv_congr_right _ _ targetMass hweights)
    (Q'.one_mul_eqv targetMass)

#print axioms finiteCenteredCrossMoment
#print axioms finiteCenteredCrossMoment_eqv_joint_sub_product
#print axioms finiteCenteredVariance_eqv
#print axioms minimalSymmetricCorrelatedPair_crossMoment_ne_zero
#print axioms twoCoordinateTensorTilt_total
#print axioms twoBlockTensorizedConfigurationKernel_nonnegative
#print axioms twoBlockTensorizedConfigurationKernel_row_sum
#print axioms twoBlockTensorizedConfigurationKernel_pushforward
#print axioms twoBlockTensorizedConfigurationKernel_row_normalized_of_cross_zero
#print axioms twoBlockTensorizedConfigurationKernel_pushforward_of_cross_zero
#print axioms timeZeroUnitCubeConfigurationEventMass_eqv
#print axioms timeOneUnitCubeConfigurationEventMass_eqv
#print axioms activityMatchedAdjacentTimeTensorKernel_nonnegative
#print axioms activityMatchedAdjacentTimeTensorKernel_row_sum
#print axioms activityMatchedAdjacentTimeTensorKernel_pushforward
#print axioms activityMatchedAdjacentTimeTensorKernel_row_normalized_of_target_cross_zero
#print axioms activityMatchedAdjacentTimeTensorKernel_pushforward_of_source_cross_zero
#print axioms finiteCenteredCrossDeviation_total
#print axioms covarianceCorrectedTensorDensity_target_expectation
#print axioms covarianceCorrectedTensorDensity_source_expectation
#print axioms finiteCenteredCrossMoment_unit_bounds
#print axioms covarianceCorrectedTensorDensity_lower_bound
#print axioms covarianceCorrectedTensorDensity_quarter_nonnegative
#print axioms covarianceCorrectedTwoBlockConfigurationKernel_quarter_nonnegative
#print axioms covarianceCorrectedTwoBlockConfigurationKernel_row_normalized
#print axioms covarianceCorrectedTwoBlockConfigurationKernel_pushforward
#print axioms physicalAdjacentTimeCrossMoment_eqv_connected_probability
#print axioms physicalAdjacentTimeCrossMoment_unit_bounds
#print axioms activityMatchedAdjacentTimeCovarianceCorrectedKernel_nonnegative
#print axioms activityMatchedAdjacentTimeCovarianceCorrectedKernel_row_normalized
#print axioms activityMatchedAdjacentTimeCovarianceCorrectedKernel_pushforward
#print axioms activityMatchedAdjacentTimeCorrelationAwareKernel_nonnegative
#print axioms activityMatchedAdjacentTimeCorrelationAwareKernel_row_normalized
#print axioms activityMatchedAdjacentTimeCorrelationAwareKernel_pushforward

end YMGap.Continuum.Z4BlockLocalityTensorObstruction
