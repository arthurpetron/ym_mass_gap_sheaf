/-
# Two-code pushforward for the oriented mixed OS form

Symmetry of the reflected support kernel reduces real polarization to one
oriented cross form.  That cross form is then pushed through two different
finite Boolean codes: the source code on the lower support and the translated
target code on the reflected upper support.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipushforward

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCoefficientZeroExtension
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-- An unsymmetrized finite cross form. -/
def finiteJointCrossBilinear {State : Type}
    (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q') : Q' :=
  listQSum (fun left => listQSum (fun right =>
    (leftCoefficient left * rightCoefficient right) * joint left right)
    states) states

/-- A symmetric joint kernel makes the two orientations of the cross form
equal. -/
theorem finiteJointCrossBilinear_symm_of_joint
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q')
    (hjoint : ∀ left, left ∈ states → ∀ right, right ∈ states →
      joint left right ≈ joint right left) :
    finiteJointCrossBilinear states leftCoefficient rightCoefficient joint ≈
      finiteJointCrossBilinear states rightCoefficient leftCoefficient joint := by
  let backward : State → State → Q' := fun left right =>
    (rightCoefficient left * leftCoefficient right) * joint left right
  have hswap :
      listQSum (fun left => listQSum (backward left) states) states ≈
        listQSum (fun right =>
          listQSum (fun left => backward left right) states) states :=
    Q'.eqv_symm (listQSum_swap backward states states)
  have hrecode :
      listQSum (fun right =>
          listQSum (fun left => backward left right) states) states ≈
        finiteJointCrossBilinear
          states leftCoefficient rightCoefficient joint := by
    unfold finiteJointCrossBilinear
    apply listQSum_congr_on
    intro outer houter
    apply listQSum_congr_on
    intro inner hinner
    unfold backward
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv
          (rightCoefficient inner) (leftCoefficient outer)))
      (Q'.mul_eqv_congr_left _ _ _
        (hjoint inner hinner outer houter))
  unfold finiteJointCrossBilinear
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hswap hrecode)

/-- For a symmetric joint kernel, the exact polarization used by the OS
bilinear reduces to the single oriented cross form. -/
theorem finiteJointPolarizedBilinear_eqv_cross_of_joint_symm
    {State : Type} (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q')
    (hjoint : ∀ left, left ∈ states → ∀ right, right ∈ states →
      joint left right ≈ joint right left) :
    finiteJointPolarizedBilinear states
        leftCoefficient rightCoefficient joint ≈
      finiteJointCrossBilinear states
        leftCoefficient rightCoefficient joint := by
  let forward : State → State → Q' := fun left right =>
    (leftCoefficient left * rightCoefficient right) * joint left right
  let backward : State → State → Q' := fun left right =>
    (rightCoefficient left * leftCoefficient right) * joint left right
  have hscale :
      strictJointPolarizationQuarter + strictJointPolarizationQuarter ≈
        HalfPow.half := by
    decide
  have hpoint : ∀ left right,
      ((strictJointPolarizationQuarter +
          strictJointPolarizationQuarter) *
        ((leftCoefficient left * rightCoefficient right) +
          (rightCoefficient left * leftCoefficient right))) *
          joint left right ≈
        HalfPow.half * forward left right +
          HalfPow.half * backward left right := by
    intro left right
    unfold forward backward
    refine Q'.eqv_trans _
      (HalfPow.half *
        ((leftCoefficient left * rightCoefficient right) +
          (rightCoefficient left * leftCoefficient right)) *
        joint left right) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hscale)
    · ring_qeqv
  have hsplit :
      finiteJointPolarizedBilinear states
          leftCoefficient rightCoefficient joint ≈
        HalfPow.half *
            finiteJointCrossBilinear states
              leftCoefficient rightCoefficient joint +
          HalfPow.half *
            finiteJointCrossBilinear states
              rightCoefficient leftCoefficient joint := by
    unfold finiteJointPolarizedBilinear finiteJointCrossBilinear
    refine Q'.eqv_trans _
      (listQSum (fun left => listQSum (fun right =>
        (HalfPow.half * forward left right) +
          (HalfPow.half * backward left right)) states) states) _ ?_ ?_
    · apply listQSum_congr
      intro left
      apply listQSum_congr
      intro right
      exact hpoint left right
    · refine Q'.eqv_trans _
        (listQSum (fun left =>
          listQSum (fun right => HalfPow.half * forward left right) states +
            listQSum (fun right => HalfPow.half * backward left right) states)
          states) _ ?_ ?_
      · apply listQSum_congr
        intro left
        exact listQSum_add _ _ states
      · refine Q'.eqv_trans _
          (listQSum (fun left =>
            HalfPow.half * listQSum (forward left) states +
              HalfPow.half * listQSum (backward left) states) states) _ ?_ ?_
        · apply listQSum_congr
          intro left
          exact Q'.add_eqv_congr'
            (listQSum_mul_left HalfPow.half (forward left) states)
            (listQSum_mul_left HalfPow.half (backward left) states)
        · refine Q'.eqv_trans _
            (listQSum (fun left =>
                HalfPow.half * listQSum (forward left) states) states +
              listQSum (fun left =>
                HalfPow.half * listQSum (backward left) states) states) _
            (listQSum_add _ _ states) ?_
          exact Q'.add_eqv_congr'
            (listQSum_mul_left HalfPow.half
              (fun left => listQSum (forward left) states) states)
            (listQSum_mul_left HalfPow.half
              (fun left => listQSum (backward left) states) states)
  have horientation :
      finiteJointCrossBilinear states rightCoefficient leftCoefficient joint ≈
        finiteJointCrossBilinear states leftCoefficient rightCoefficient joint :=
    finiteJointCrossBilinear_symm_of_joint
      states rightCoefficient leftCoefficient joint
        (fun left hleft right hright =>
          Q'.eqv_symm (hjoint right hright left hleft))
  refine Q'.eqv_trans _ _ _ hsplit ?_
  · refine Q'.eqv_trans _
      (HalfPow.half *
          finiteJointCrossBilinear states leftCoefficient rightCoefficient joint +
        HalfPow.half *
          finiteJointCrossBilinear states leftCoefficient rightCoefficient joint) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left HalfPow.half _ _ horientation)
    · exact ExpNeg.two_halves
        (finiteJointCrossBilinear
          states leftCoefficient rightCoefficient joint)

/-- Complete source-pair mass with a left code on the first source and a
possibly different right code on the second source. -/
def finiteJointKernelBipushforward
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (joint : Source → Source → Q')
    (leftCode rightCode : Source → Target)
    (left right : Target) : Q' :=
  fiberWeight (cartesian source source)
    (fun pair => joint pair.1 pair.2)
    (fun pair => (leftCode pair.1, rightCode pair.2))
    (left, right)

/-- Exact two-code pushforward of the oriented cross form. -/
theorem finiteJointQuadratic_bipushforward_eqv_cross
    {Source Target : Type} [DecidableEq Target]
    (source : List Source) (joint : Source → Source → Q')
    (leftCode rightCode : Source → Target)
    (targets : List Target) (hnodup : targets.Nodup)
    (hleft : ∀ item, item ∈ source → leftCode item ∈ targets)
    (hright : ∀ item, item ∈ source → rightCode item ∈ targets)
    (coefficient : Target → Q') :
    finiteJointQuadratic targets coefficient
        (finiteJointKernelBipushforward
          source joint leftCode rightCode) ≈
      finiteJointCrossBilinear source
        (fun item => coefficient (leftCode item))
        (fun item => coefficient (rightCode item)) joint := by
  let sourcePairs := cartesian source source
  let targetPairs := cartesian targets targets
  let pairCode : Source × Source → Target × Target := fun pair =>
    (leftCode pair.1, rightCode pair.2)
  let sourceWeight : Source × Source → Q' := fun pair =>
    joint pair.1 pair.2
  let targetCoefficient : Target × Target → Q' := fun pair =>
    coefficient pair.1 * coefficient pair.2
  have htargetNodup : targetPairs.Nodup := by
    unfold targetPairs
    exact cartesian_nodup targets targets hnodup hnodup
  have hpairsCovered : ∀ pair, pair ∈ sourcePairs →
      pairCode pair ∈ targetPairs := by
    intro pair hpair
    have hparts := (mem_cartesian_iff source source pair).1 hpair
    apply (mem_cartesian_iff targets targets (pairCode pair)).2
    exact ⟨hleft pair.1 hparts.1, hright pair.2 hparts.2⟩
  unfold finiteJointQuadratic finiteJointCrossBilinear
    finiteJointKernelBipushforward
  refine Q'.eqv_trans _
    (listQSum (fun pair =>
      targetCoefficient pair *
        fiberWeight sourcePairs sourceWeight pairCode pair)
      targetPairs) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_cartesian_eq_nested
        (fun pair => targetCoefficient pair *
          fiberWeight sourcePairs sourceWeight pairCode pair)
        targets targets)
  · refine Q'.eqv_trans _
      (listQSum (fun pair =>
        finiteCoefficientZeroExtension
            sourcePairs sourceWeight pairCode pair *
          targetCoefficient pair) targetPairs) _ ?_ ?_
    · apply listQSum_congr
      intro pair
      exact Q'.mul_comm_eqv _ _
    · refine Q'.eqv_trans _
        (listQSum (fun pair =>
          sourceWeight pair * targetCoefficient (pairCode pair))
          sourcePairs) _
        (finiteCoefficientZeroExtension_reindex_mul
          sourcePairs sourceWeight pairCode targetPairs
          htargetNodup hpairsCovered targetCoefficient) ?_
      refine Q'.eqv_trans _
        (listQSum (fun pair =>
          targetCoefficient (pairCode pair) * sourceWeight pair)
          sourcePairs) _ ?_ ?_
      · apply listQSum_congr
        intro pair
        exact Q'.mul_comm_eqv _ _
      · exact listQSum_cartesian_eq_nested
          (fun pair =>
            targetCoefficient (pairCode pair) * sourceWeight pair)
          source source

#print axioms finiteJointCrossBilinear_symm_of_joint
#print axioms finiteJointPolarizedBilinear_eqv_cross_of_joint_symm
#print axioms finiteJointQuadratic_bipushforward_eqv_cross

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipushforward
