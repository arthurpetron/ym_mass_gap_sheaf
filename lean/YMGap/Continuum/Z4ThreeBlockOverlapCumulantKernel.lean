/-
# Exact three-block overlap correction

Two adjacent two-block windows `(1,2)` and `(2,3)` share block `2`.  Expanding
the three one-block factors shows that the pairwise covariance counterterms
remove every quadratic defect but leave a cubic residual.  This module:

* identifies that residual as the exact centered third moment of the complete
  finite law;
* gives a finite parity-law witness with zero one- and two-point centered
  moments but nonzero third moment;
* adds the forced third-order counterterm;
* proves exact row normalization, exact pushforward, and a uniform derived
  nonnegativity choice `epsilon = 1/8`.

The construction is generic over three overlapping Boolean block events.  It
therefore exposes all complete-law moments instead of assuming independence
at the shared block.
-/

import YMGap.Continuum.Z4BlockLocalityTensorObstruction

namespace YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4BlockLocalityTensorObstruction

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

/-! ## 1. The exact third centered moment -/

def finiteCenteredThirdMoment {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter thirdParameter : Q')
    (firstEvent secondEvent thirdEvent : A → Bool) : Q' :=
  listQSum
    (fun state => mass state *
      (centeredEventCoordinate firstParameter firstEvent state *
        (centeredEventCoordinate secondParameter secondEvent state *
          centeredEventCoordinate thirdParameter thirdEvent state))) states

/-- Centering the cubic block monomial by the complete-law third moment gives
zero expectation. -/
theorem finiteCenteredThirdDeviation_total {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter thirdParameter thirdMoment : Q')
    (firstEvent secondEvent thirdEvent : A → Bool)
    (hmoment : finiteCenteredThirdMoment mass states
      firstParameter secondParameter thirdParameter
      firstEvent secondEvent thirdEvent ≈ thirdMoment)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (fun state => mass state *
          (centeredEventCoordinate firstParameter firstEvent state *
              (centeredEventCoordinate secondParameter secondEvent state *
                centeredEventCoordinate thirdParameter thirdEvent state) +
            -thirdMoment)) states ≈ 0 := by
  let cubicWeighted := fun state => mass state *
    (centeredEventCoordinate firstParameter firstEvent state *
      (centeredEventCoordinate secondParameter secondEvent state *
        centeredEventCoordinate thirdParameter thirdEvent state))
  refine Q'.eqv_trans _
    (listQSum
      (fun state => cubicWeighted state + (-thirdMoment) * mass state)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    unfold cubicWeighted
    ac_qeqv
  refine Q'.eqv_trans _
    (listQSum cubicWeighted states +
      listQSum (fun state => (-thirdMoment) * mass state) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (listQSum cubicWeighted states +
      (-thirdMoment) * listQSum mass states) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (listQSum_mul_left (-thirdMoment) mass states)) ?_
  change
    finiteCenteredThirdMoment mass states
        firstParameter secondParameter thirdParameter
        firstEvent secondEvent thirdEvent +
      (-thirdMoment) * listQSum mass states ≈ 0
  refine Q'.eqv_trans _ (thirdMoment + (-thirdMoment) * 1) _ ?_ ?_
  · exact Q'.add_eqv_congr' hmoment
      (Q'.mul_eqv_congr_left (-thirdMoment) _ _ htotal)
  refine Q'.eqv_trans _ (thirdMoment + -thirdMoment) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_one_eqv (-thirdMoment))
  exact Q'.add_neg_self_eqv thirdMoment

/-! ## 2. Pairwise correction and the forced cubic correction -/

/-- A finite affine feature density, folded so that adding a head feature is
definitionally an outer addition. -/
def scalarFeatureDensity : List Q' → Q'
  | [] => 1
  | feature :: rest => scalarFeatureDensity rest + feature

/-- Common constant, singleton, and pairwise-centered part of the overlap
density. -/
def threeBlockPairwiseCorrectedBaseDensity
    (epsilon : Q')
    (a1 a2 a3 b1 b2 b3 : Q')
    (source12 source13 source23 : Q')
    (target12 target13 target23 : Q') : Q' :=
  scalarFeatureDensity
    [epsilon * a1 * b1,
      epsilon * a2 * b2,
      epsilon * a3 * b3,
      (epsilon * epsilon) *
        ((a1 * a2 + -source12) * (b1 * b2 + -target12)),
      (epsilon * epsilon) *
        ((a1 * a3 + -source13) * (b1 * b3 + -target13)),
      (epsilon * epsilon) *
        ((a2 * a3 + -source23) * (b2 * b3 + -target23))]

/-- Three one-block factors after all three pairwise covariance corrections,
but before the cubic correction.  The raw cubic monomial remains. -/
def threeBlockPairwiseCorrectedDensity
    (epsilon : Q')
    (a1 a2 a3 b1 b2 b3 : Q')
    (source12 source13 source23 : Q')
    (target12 target13 target23 : Q') : Q' :=
  threeBlockPairwiseCorrectedBaseDensity epsilon
      a1 a2 a3 b1 b2 b3
      source12 source13 source23 target12 target13 target23 +
    ((epsilon * epsilon) * epsilon) *
      ((a1 * (a2 * a3)) * (b1 * (b2 * b3)))

/-- The exact overlap correction adds the centered cubic monomial. -/
def threeBlockOverlapCorrectedDensity
    (epsilon : Q')
    (a1 a2 a3 b1 b2 b3 : Q')
    (source12 source13 source23 : Q')
    (target12 target13 target23 : Q')
    (source123 target123 : Q') : Q' :=
  threeBlockPairwiseCorrectedBaseDensity epsilon
      a1 a2 a3 b1 b2 b3
      source12 source13 source23 target12 target13 target23 +
    ((epsilon * epsilon) * epsilon) *
      ((a1 * (a2 * a3) + -source123) *
        (b1 * (b2 * b3) + -target123))

private theorem scaled_centered_product_expand
    (scale sourceValue sourceMean targetValue targetMean : Q') :
    scale * ((sourceValue + -sourceMean) *
        (targetValue + -targetMean)) ≈
      (scale * (sourceValue * targetValue) +
        -(scale * (sourceValue * targetMean))) +
        -(scale * (sourceMean * (targetValue + -targetMean))) := by
  have hinner :
      (sourceValue + -sourceMean) * (targetValue + -targetMean) ≈
        (sourceValue * targetValue + -(sourceValue * targetMean)) +
          -(sourceMean * (targetValue + -targetMean)) := by
    refine Q'.eqv_trans _
      (sourceValue * (targetValue + -targetMean) +
        (-sourceMean) * (targetValue + -targetMean)) _
      (Q'.add_mul_eqv sourceValue (-sourceMean)
        (targetValue + -targetMean)) ?_
    refine Q'.eqv_trans _
      ((sourceValue * targetValue + sourceValue * -targetMean) +
        (-sourceMean) * (targetValue + -targetMean)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_add_eqv sourceValue targetValue (-targetMean))
        (Q'.eqv_refl _)
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.mul_neg_eqv sourceValue targetMean))
      (Q'.neg_mul_eqv sourceMean (targetValue + -targetMean))
  refine Q'.eqv_trans _
    (scale *
      ((sourceValue * targetValue + -(sourceValue * targetMean)) +
        -(sourceMean * (targetValue + -targetMean)))) _
    (Q'.mul_eqv_congr_left scale _ _ hinner) ?_
  refine Q'.eqv_trans _
    (scale * (sourceValue * targetValue + -(sourceValue * targetMean)) +
      scale * -(sourceMean * (targetValue + -targetMean))) _
    (Q'.mul_add_eqv scale _ _) ?_
  refine Q'.eqv_trans _
    ((scale * (sourceValue * targetValue) +
        scale * -(sourceValue * targetMean)) +
      scale * -(sourceMean * (targetValue + -targetMean))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_add_eqv scale
        (sourceValue * targetValue) (-(sourceValue * targetMean)))
      (Q'.eqv_refl _)
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_neg_eqv scale (sourceValue * targetMean)))
    (Q'.mul_neg_eqv scale
      (sourceMean * (targetValue + -targetMean)))

/-- Algebraic form of the forced third counterterm. -/
theorem threeBlockOverlapCorrectedDensity_eqv_pairwise_minus_cubic_defects
    (epsilon : Q')
    (a1 a2 a3 b1 b2 b3 : Q')
    (source12 source13 source23 : Q')
    (target12 target13 target23 : Q')
    (source123 target123 : Q') :
    threeBlockOverlapCorrectedDensity epsilon
        a1 a2 a3 b1 b2 b3
        source12 source13 source23 target12 target13 target23
        source123 target123 ≈
      (threeBlockPairwiseCorrectedDensity epsilon
          a1 a2 a3 b1 b2 b3
          source12 source13 source23 target12 target13 target23 +
        -(((epsilon * epsilon) * epsilon) *
          ((a1 * (a2 * a3)) * target123))) +
        -(((epsilon * epsilon) * epsilon) *
          (source123 * (b1 * (b2 * b3) + -target123))) := by
  unfold threeBlockOverlapCorrectedDensity
    threeBlockPairwiseCorrectedDensity
  let base := threeBlockPairwiseCorrectedBaseDensity epsilon
    a1 a2 a3 b1 b2 b3
    source12 source13 source23 target12 target13 target23
  let scale := (epsilon * epsilon) * epsilon
  let sourceValue := a1 * (a2 * a3)
  let targetValue := b1 * (b2 * b3)
  refine Q'.eqv_trans _
    (base +
      ((scale * (sourceValue * targetValue) +
        -(scale * (sourceValue * target123))) +
        -(scale *
          (source123 * (targetValue + -target123))))) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (scaled_centered_product_expand scale
        sourceValue source123 targetValue target123)
  refine Q'.eqv_trans _
    ((base +
      (scale * (sourceValue * targetValue) +
        -(scale * (sourceValue * target123)))) +
      -(scale * (source123 * (targetValue + -target123)))) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv base
        (scale * (sourceValue * targetValue) +
          -(scale * (sourceValue * target123)))
        (-(scale * (source123 * (targetValue + -target123)))))) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv base
        (scale * (sourceValue * targetValue))
        (-(scale * (sourceValue * target123)))))

theorem threeBlockOverlapCorrectedDensity_swap
    (epsilon : Q')
    (a1 a2 a3 b1 b2 b3 : Q')
    (source12 source13 source23 : Q')
    (target12 target13 target23 : Q')
    (source123 target123 : Q') :
    threeBlockOverlapCorrectedDensity epsilon
        a1 a2 a3 b1 b2 b3
        source12 source13 source23 target12 target13 target23
        source123 target123 ≈
      threeBlockOverlapCorrectedDensity epsilon
        b1 b2 b3 a1 a2 a3
        target12 target13 target23 source12 source13 source23
        target123 source123 := by
  unfold threeBlockOverlapCorrectedDensity
    threeBlockPairwiseCorrectedBaseDensity scalarFeatureDensity
  apply Q'.add_eqv_congr'
  · apply Q'.add_eqv_congr'
    · apply Q'.add_eqv_congr'
      · apply Q'.add_eqv_congr'
        · apply Q'.add_eqv_congr'
          · apply Q'.add_eqv_congr'
            · apply Q'.add_eqv_congr'
              · exact Q'.eqv_refl 1
              · ac_qeqv
            · ac_qeqv
          · ac_qeqv
        · ac_qeqv
      · ac_qeqv
    · ac_qeqv
  · ac_qeqv

/-! ## 3. Exact expectations of finite centered feature densities -/

/-- Any finite affine density assembled from features of exact mean zero has
total mass one. -/
theorem scalarFeatureDensity_total {A : Type}
    (mass : A → Q') (states : List A) (features : List (A → Q'))
    (htotal : listQSum mass states ≈ 1)
    (hzero : ∀ feature, feature ∈ features →
      listQSum (fun state => mass state * feature state) states ≈ 0) :
    listQSum
        (fun state => mass state *
          scalarFeatureDensity
            (features.map (fun feature => feature state))) states ≈ 1 := by
  induction features with
  | nil =>
      change listQSum (fun state => mass state * 1) states ≈ 1
      refine Q'.eqv_trans _ (listQSum mass states) _ ?_ htotal
      apply listQSum_congr_on
      intro state _
      exact Q'.mul_one_eqv (mass state)
  | cons head tail ih =>
      have htail :
          listQSum
              (fun state => mass state *
                scalarFeatureDensity
                  (tail.map (fun feature => feature state))) states ≈ 1 :=
        ih (fun feature hfeature =>
          hzero feature (List.mem_cons_of_mem head hfeature))
      have hhead :
          listQSum (fun state => mass state * head state) states ≈ 0 :=
        hzero head List.mem_cons_self
      change
        listQSum
          (fun state => mass state *
            (scalarFeatureDensity
                (tail.map (fun feature => feature state)) + head state))
          states ≈ 1
      refine Q'.eqv_trans _
        (listQSum
          (fun state =>
            mass state * scalarFeatureDensity
                (tail.map (fun feature => feature state)) +
              mass state * head state) states) _ ?_ ?_
      · apply listQSum_congr_on
        intro state _
        exact Q'.mul_add_eqv _ _ _
      refine Q'.eqv_trans _
        (listQSum
            (fun state => mass state * scalarFeatureDensity
              (tail.map (fun feature => feature state))) states +
          listQSum (fun state => mass state * head state) states) _
        (listQSum_add _ _ states) ?_
      refine Q'.eqv_trans _ ((1 : Q') + 0) _
        (Q'.add_eqv_congr' htail hhead) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' 1)

theorem scaledCenteredCoordinate_total {A : Type}
    (mass : A → Q') (states : List A)
    (parameter coefficient : Q') (event : A → Bool)
    (hevent : finiteEventMass mass states event ≈ parameter)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (fun state => mass state *
          (coefficient * centeredEventCoordinate parameter event state))
        states ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state => coefficient *
        (mass state * centeredEventCoordinate parameter event state))
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    ac_qeqv
  refine Q'.eqv_trans _
    (coefficient *
      listQSum
        (fun state => mass state *
          centeredEventCoordinate parameter event state) states) _
    (listQSum_mul_left coefficient _ states) ?_
  refine Q'.eqv_trans _ (coefficient * 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left coefficient _ _
      (centeredEventCoordinate_mean_zero mass states event
        parameter hevent htotal)
  exact Q'.mul_zero_eqv coefficient

theorem scaledCenteredCrossDeviation_total {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter cross coefficient : Q')
    (firstEvent secondEvent : A → Bool)
    (hcross : finiteCenteredCrossMoment mass states
      firstParameter secondParameter firstEvent secondEvent ≈ cross)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (fun state => mass state *
          (coefficient *
            (centeredEventCoordinate firstParameter firstEvent state *
                centeredEventCoordinate secondParameter secondEvent state +
              -cross))) states ≈ 0 := by
  let deviation := fun state => mass state *
    (centeredEventCoordinate firstParameter firstEvent state *
        centeredEventCoordinate secondParameter secondEvent state +
      -cross)
  refine Q'.eqv_trans _
    (listQSum (fun state => coefficient * deviation state) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    unfold deviation
    ac_qeqv
  refine Q'.eqv_trans _
    (coefficient * listQSum deviation states) _
    (listQSum_mul_left coefficient deviation states) ?_
  refine Q'.eqv_trans _ (coefficient * 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left coefficient _ _
      (finiteCenteredCrossDeviation_total mass states
        firstParameter secondParameter cross firstEvent secondEvent
        hcross htotal)
  exact Q'.mul_zero_eqv coefficient

theorem scaledCenteredThirdDeviation_total {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter thirdParameter
      thirdMoment coefficient : Q')
    (firstEvent secondEvent thirdEvent : A → Bool)
    (hmoment : finiteCenteredThirdMoment mass states
      firstParameter secondParameter thirdParameter
      firstEvent secondEvent thirdEvent ≈ thirdMoment)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (fun state => mass state *
          (coefficient *
            (centeredEventCoordinate firstParameter firstEvent state *
                (centeredEventCoordinate secondParameter secondEvent state *
                  centeredEventCoordinate thirdParameter thirdEvent state) +
              -thirdMoment))) states ≈ 0 := by
  let deviation := fun state => mass state *
    (centeredEventCoordinate firstParameter firstEvent state *
        (centeredEventCoordinate secondParameter secondEvent state *
          centeredEventCoordinate thirdParameter thirdEvent state) +
      -thirdMoment)
  refine Q'.eqv_trans _
    (listQSum (fun state => coefficient * deviation state) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    unfold deviation
    ac_qeqv
  refine Q'.eqv_trans _
    (coefficient * listQSum deviation states) _
    (listQSum_mul_left coefficient deviation states) ?_
  refine Q'.eqv_trans _ (coefficient * 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left coefficient _ _
      (finiteCenteredThirdDeviation_total mass states
        firstParameter secondParameter thirdParameter thirdMoment
        firstEvent secondEvent thirdEvent hmoment htotal)
  exact Q'.mul_zero_eqv coefficient

theorem nestedScaledCenteredCrossDeviation_total {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter cross scale outer : Q')
    (firstEvent secondEvent : A → Bool)
    (hcross : finiteCenteredCrossMoment mass states
      firstParameter secondParameter firstEvent secondEvent ≈ cross)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (fun state => mass state *
          (scale *
            (outer *
              (centeredEventCoordinate firstParameter firstEvent state *
                  centeredEventCoordinate secondParameter secondEvent state +
                -cross)))) states ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state => mass state *
        ((scale * outer) *
          (centeredEventCoordinate firstParameter firstEvent state *
              centeredEventCoordinate secondParameter secondEvent state +
            -cross))) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    ac_qeqv
  exact scaledCenteredCrossDeviation_total mass states
    firstParameter secondParameter cross (scale * outer)
    firstEvent secondEvent hcross htotal

theorem nestedScaledCenteredThirdDeviation_total {A : Type}
    (mass : A → Q') (states : List A)
    (firstParameter secondParameter thirdParameter thirdMoment
      scale outer : Q')
    (firstEvent secondEvent thirdEvent : A → Bool)
    (hmoment : finiteCenteredThirdMoment mass states
      firstParameter secondParameter thirdParameter
      firstEvent secondEvent thirdEvent ≈ thirdMoment)
    (htotal : listQSum mass states ≈ 1) :
    listQSum
        (fun state => mass state *
          (scale *
            (outer *
              (centeredEventCoordinate firstParameter firstEvent state *
                  (centeredEventCoordinate secondParameter secondEvent state *
                    centeredEventCoordinate thirdParameter thirdEvent state) +
                -thirdMoment)))) states ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state => mass state *
        ((scale * outer) *
          (centeredEventCoordinate firstParameter firstEvent state *
              (centeredEventCoordinate secondParameter secondEvent state *
                centeredEventCoordinate thirdParameter thirdEvent state) +
            -thirdMoment))) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    ac_qeqv
  exact scaledCenteredThirdDeviation_total mass states
    firstParameter secondParameter thirdParameter thirdMoment
    (scale * outer) firstEvent secondEvent thirdEvent hmoment htotal

private theorem scalarFeatureDensity_total_seven {A : Type}
    (mass : A → Q') (states : List A)
    (f0 f1 f2 f3 f4 f5 f6 : A → Q')
    (htotal : listQSum mass states ≈ 1)
    (h0 : listQSum (fun state => mass state * f0 state) states ≈ 0)
    (h1 : listQSum (fun state => mass state * f1 state) states ≈ 0)
    (h2 : listQSum (fun state => mass state * f2 state) states ≈ 0)
    (h3 : listQSum (fun state => mass state * f3 state) states ≈ 0)
    (h4 : listQSum (fun state => mass state * f4 state) states ≈ 0)
    (h5 : listQSum (fun state => mass state * f5 state) states ≈ 0)
    (h6 : listQSum (fun state => mass state * f6 state) states ≈ 0) :
    listQSum
        (fun state => mass state *
          scalarFeatureDensity
            ([f0, f1, f2, f3, f4, f5, f6].map
              (fun feature => feature state))) states ≈ 1 := by
  apply scalarFeatureDensity_total mass states _ htotal
  intro feature hfeature
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfeature
  rcases hfeature with h | h | h | h | h | h | h
  · subst feature; exact h0
  · subst feature; exact h1
  · subst feature; exact h2
  · subst feature; exact h3
  · subst feature; exact h4
  · subst feature; exact h5
  · subst feature; exact h6

/-! ## 4. The smallest overlapping cover `(left, shared, right)` -/

structure ThreeBlockOverlapFiniteLaw (State : Type) where
  mass : State → Q'
  states : List State
  leftParameter : Q'
  sharedParameter : Q'
  rightParameter : Q'
  leftEvent : State → Bool
  sharedEvent : State → Bool
  rightEvent : State → Bool
  mass_nonnegative : ∀ state, (0 : Q') ≤ mass state
  left_nonnegative : (0 : Q') ≤ leftParameter
  left_le_one : leftParameter ≤ (1 : Q')
  shared_nonnegative : (0 : Q') ≤ sharedParameter
  shared_le_one : sharedParameter ≤ (1 : Q')
  right_nonnegative : (0 : Q') ≤ rightParameter
  right_le_one : rightParameter ≤ (1 : Q')
  left_mass : finiteEventMass mass states leftEvent ≈ leftParameter
  shared_mass : finiteEventMass mass states sharedEvent ≈ sharedParameter
  right_mass : finiteEventMass mass states rightEvent ≈ rightParameter
  normalized : listQSum mass states ≈ 1

def overlapLeftCoordinate {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) (state : State) : Q' :=
  centeredEventCoordinate law.leftParameter law.leftEvent state

def overlapSharedCoordinate {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) (state : State) : Q' :=
  centeredEventCoordinate law.sharedParameter law.sharedEvent state

def overlapRightCoordinate {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) (state : State) : Q' :=
  centeredEventCoordinate law.rightParameter law.rightEvent state

def overlapLeftSharedMoment {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) : Q' :=
  finiteCenteredCrossMoment law.mass law.states
    law.leftParameter law.sharedParameter law.leftEvent law.sharedEvent

def overlapLeftRightMoment {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) : Q' :=
  finiteCenteredCrossMoment law.mass law.states
    law.leftParameter law.rightParameter law.leftEvent law.rightEvent

def overlapSharedRightMoment {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) : Q' :=
  finiteCenteredCrossMoment law.mass law.states
    law.sharedParameter law.rightParameter law.sharedEvent law.rightEvent

def overlapThirdMoment {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) : Q' :=
  finiteCenteredThirdMoment law.mass law.states
    law.leftParameter law.sharedParameter law.rightParameter
    law.leftEvent law.sharedEvent law.rightEvent

def threeBlockOverlapConfigurationKernel {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (epsilon : Q') (source : Source) (target : Target) : Q' :=
  targetLaw.mass target *
    threeBlockOverlapCorrectedDensity epsilon
      (overlapLeftCoordinate sourceLaw source)
      (overlapSharedCoordinate sourceLaw source)
      (overlapRightCoordinate sourceLaw source)
      (overlapLeftCoordinate targetLaw target)
      (overlapSharedCoordinate targetLaw target)
      (overlapRightCoordinate targetLaw target)
      (overlapLeftSharedMoment sourceLaw)
      (overlapLeftRightMoment sourceLaw)
      (overlapSharedRightMoment sourceLaw)
      (overlapLeftSharedMoment targetLaw)
      (overlapLeftRightMoment targetLaw)
      (overlapSharedRightMoment targetLaw)
      (overlapThirdMoment sourceLaw)
      (overlapThirdMoment targetLaw)

theorem threeBlockOverlapConfigurationKernel_row_normalized
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (epsilon : Q') (source : Source) :
    listQSum
        (threeBlockOverlapConfigurationKernel
          sourceLaw targetLaw epsilon source) targetLaw.states ≈ 1 := by
  let a1 := overlapLeftCoordinate sourceLaw source
  let a2 := overlapSharedCoordinate sourceLaw source
  let a3 := overlapRightCoordinate sourceLaw source
  let a12 := a1 * a2 + -overlapLeftSharedMoment sourceLaw
  let a13 := a1 * a3 + -overlapLeftRightMoment sourceLaw
  let a23 := a2 * a3 + -overlapSharedRightMoment sourceLaw
  let a123 := a1 * (a2 * a3) + -overlapThirdMoment sourceLaw
  let epsilon2 := epsilon * epsilon
  let epsilon3 := epsilon2 * epsilon
  let f0 := fun target => epsilon3 *
    (a123 *
      (overlapLeftCoordinate targetLaw target *
          (overlapSharedCoordinate targetLaw target *
            overlapRightCoordinate targetLaw target) +
        -overlapThirdMoment targetLaw))
  let f1 := fun target =>
    epsilon * a1 * overlapLeftCoordinate targetLaw target
  let f2 := fun target =>
    epsilon * a2 * overlapSharedCoordinate targetLaw target
  let f3 := fun target =>
    epsilon * a3 * overlapRightCoordinate targetLaw target
  let f4 := fun target => epsilon2 *
    (a12 *
      (overlapLeftCoordinate targetLaw target *
          overlapSharedCoordinate targetLaw target +
        -overlapLeftSharedMoment targetLaw))
  let f5 := fun target => epsilon2 *
    (a13 *
      (overlapLeftCoordinate targetLaw target *
          overlapRightCoordinate targetLaw target +
        -overlapLeftRightMoment targetLaw))
  let f6 := fun target => epsilon2 *
    (a23 *
      (overlapSharedCoordinate targetLaw target *
          overlapRightCoordinate targetLaw target +
        -overlapSharedRightMoment targetLaw))
  have h0 :
      listQSum (fun target => targetLaw.mass target * f0 target)
        targetLaw.states ≈ 0 := by
    unfold f0 overlapLeftCoordinate overlapSharedCoordinate
      overlapRightCoordinate overlapThirdMoment
    exact nestedScaledCenteredThirdDeviation_total
      targetLaw.mass targetLaw.states
      targetLaw.leftParameter targetLaw.sharedParameter
      targetLaw.rightParameter
      (finiteCenteredThirdMoment targetLaw.mass targetLaw.states
        targetLaw.leftParameter targetLaw.sharedParameter
        targetLaw.rightParameter targetLaw.leftEvent
        targetLaw.sharedEvent targetLaw.rightEvent)
      epsilon3 a123
      targetLaw.leftEvent targetLaw.sharedEvent targetLaw.rightEvent
      (Q'.eqv_refl _) targetLaw.normalized
  have h1 :
      listQSum (fun target => targetLaw.mass target * f1 target)
        targetLaw.states ≈ 0 := by
    unfold f1 a1 overlapLeftCoordinate
    exact scaledCenteredCoordinate_total targetLaw.mass targetLaw.states
      targetLaw.leftParameter
      (epsilon * centeredEventCoordinate sourceLaw.leftParameter
        sourceLaw.leftEvent source)
      targetLaw.leftEvent targetLaw.left_mass targetLaw.normalized
  have h2 :
      listQSum (fun target => targetLaw.mass target * f2 target)
        targetLaw.states ≈ 0 := by
    unfold f2 a2 overlapSharedCoordinate
    exact scaledCenteredCoordinate_total targetLaw.mass targetLaw.states
      targetLaw.sharedParameter
      (epsilon * centeredEventCoordinate sourceLaw.sharedParameter
        sourceLaw.sharedEvent source)
      targetLaw.sharedEvent targetLaw.shared_mass targetLaw.normalized
  have h3 :
      listQSum (fun target => targetLaw.mass target * f3 target)
        targetLaw.states ≈ 0 := by
    unfold f3 a3 overlapRightCoordinate
    exact scaledCenteredCoordinate_total targetLaw.mass targetLaw.states
      targetLaw.rightParameter
      (epsilon * centeredEventCoordinate sourceLaw.rightParameter
        sourceLaw.rightEvent source)
      targetLaw.rightEvent targetLaw.right_mass targetLaw.normalized
  have h4 :
      listQSum (fun target => targetLaw.mass target * f4 target)
        targetLaw.states ≈ 0 := by
    unfold f4
      overlapLeftCoordinate overlapSharedCoordinate overlapLeftSharedMoment
    exact nestedScaledCenteredCrossDeviation_total
      targetLaw.mass targetLaw.states
      targetLaw.leftParameter targetLaw.sharedParameter
      (finiteCenteredCrossMoment targetLaw.mass targetLaw.states
        targetLaw.leftParameter targetLaw.sharedParameter
        targetLaw.leftEvent targetLaw.sharedEvent)
      epsilon2 a12
      targetLaw.leftEvent targetLaw.sharedEvent
      (Q'.eqv_refl _) targetLaw.normalized
  have h5 :
      listQSum (fun target => targetLaw.mass target * f5 target)
        targetLaw.states ≈ 0 := by
    unfold f5
      overlapLeftCoordinate overlapRightCoordinate overlapLeftRightMoment
    exact nestedScaledCenteredCrossDeviation_total
      targetLaw.mass targetLaw.states
      targetLaw.leftParameter targetLaw.rightParameter
      (finiteCenteredCrossMoment targetLaw.mass targetLaw.states
        targetLaw.leftParameter targetLaw.rightParameter
        targetLaw.leftEvent targetLaw.rightEvent)
      epsilon2 a13
      targetLaw.leftEvent targetLaw.rightEvent
      (Q'.eqv_refl _) targetLaw.normalized
  have h6 :
      listQSum (fun target => targetLaw.mass target * f6 target)
        targetLaw.states ≈ 0 := by
    unfold f6
      overlapSharedCoordinate overlapRightCoordinate overlapSharedRightMoment
    exact nestedScaledCenteredCrossDeviation_total
      targetLaw.mass targetLaw.states
      targetLaw.sharedParameter targetLaw.rightParameter
      (finiteCenteredCrossMoment targetLaw.mass targetLaw.states
        targetLaw.sharedParameter targetLaw.rightParameter
        targetLaw.sharedEvent targetLaw.rightEvent)
      epsilon2 a23
      targetLaw.sharedEvent targetLaw.rightEvent
      (Q'.eqv_refl _) targetLaw.normalized
  unfold threeBlockOverlapConfigurationKernel
  refine Q'.eqv_trans _
    (listQSum
      (fun target => targetLaw.mass target *
        scalarFeatureDensity
          ([f0, f1, f2, f3, f4, f5, f6].map
            (fun feature => feature target))) targetLaw.states) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    unfold f0 f1 f2 f3 f4 f5 f6 epsilon2 epsilon3
      a1 a2 a3 a12 a13 a23 a123
      threeBlockOverlapCorrectedDensity
      threeBlockPairwiseCorrectedBaseDensity
    exact Q'.eqv_refl _
  exact scalarFeatureDensity_total_seven
    targetLaw.mass targetLaw.states f0 f1 f2 f3 f4 f5 f6
    targetLaw.normalized h0 h1 h2 h3 h4 h5 h6

theorem threeBlockOverlapConfigurationKernel_pushforward
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (epsilon : Q') (target : Target) :
    configurationPushforward sourceLaw.mass sourceLaw.states
        (threeBlockOverlapConfigurationKernel sourceLaw targetLaw epsilon)
        target ≈ targetLaw.mass target := by
  unfold configurationPushforward
  refine Q'.eqv_trans _
    (listQSum
      (fun source => targetLaw.mass target *
        threeBlockOverlapConfigurationKernel
          targetLaw sourceLaw epsilon target source) sourceLaw.states) _
    ?_ ?_
  · apply listQSum_congr_on
    intro source _
    let a1 := overlapLeftCoordinate sourceLaw source
    let a2 := overlapSharedCoordinate sourceLaw source
    let a3 := overlapRightCoordinate sourceLaw source
    let b1 := overlapLeftCoordinate targetLaw target
    let b2 := overlapSharedCoordinate targetLaw target
    let b3 := overlapRightCoordinate targetLaw target
    let source12 := overlapLeftSharedMoment sourceLaw
    let source13 := overlapLeftRightMoment sourceLaw
    let source23 := overlapSharedRightMoment sourceLaw
    let target12 := overlapLeftSharedMoment targetLaw
    let target13 := overlapLeftRightMoment targetLaw
    let target23 := overlapSharedRightMoment targetLaw
    let source123 := overlapThirdMoment sourceLaw
    let target123 := overlapThirdMoment targetLaw
    let original := threeBlockOverlapCorrectedDensity epsilon
      a1 a2 a3 b1 b2 b3
      source12 source13 source23 target12 target13 target23
      source123 target123
    let swapped := threeBlockOverlapCorrectedDensity epsilon
      b1 b2 b3 a1 a2 a3
      target12 target13 target23 source12 source13 source23
      target123 source123
    have hswap : original ≈ swapped :=
      threeBlockOverlapCorrectedDensity_swap epsilon
        a1 a2 a3 b1 b2 b3
        source12 source13 source23 target12 target13 target23
        source123 target123
    unfold threeBlockOverlapConfigurationKernel
    change
      sourceLaw.mass source * (targetLaw.mass target * original) ≈
        targetLaw.mass target * (sourceLaw.mass source * swapped)
    refine Q'.eqv_trans _
      (targetLaw.mass target * (sourceLaw.mass source * original)) _
      (by ac_qeqv) ?_
    exact Q'.mul_eqv_congr_left (targetLaw.mass target) _ _
      (Q'.mul_eqv_congr_left (sourceLaw.mass source) _ _ hswap)
  refine Q'.eqv_trans _
    (targetLaw.mass target *
      listQSum
        (threeBlockOverlapConfigurationKernel
          targetLaw sourceLaw epsilon target) sourceLaw.states) _
    (listQSum_mul_left (targetLaw.mass target)
      (threeBlockOverlapConfigurationKernel
        targetLaw sourceLaw epsilon target) sourceLaw.states) ?_
  refine Q'.eqv_trans _ (targetLaw.mass target * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (targetLaw.mass target) _ _
      (threeBlockOverlapConfigurationKernel_row_normalized
        targetLaw sourceLaw epsilon target)
  exact Q'.mul_one_eqv (targetLaw.mass target)

/-! ## 5. A minimal parity witness for the cubic obstruction -/

abbrev MinimalParityState := Bool × Bool × Bool

def minimalParityStateSpace : List MinimalParityState :=
  [(false, false, false), (false, false, true),
    (false, true, false), (false, true, true),
    (true, false, false), (true, false, true),
    (true, true, false), (true, true, true)]

def minimalParityHalf : Q' := Q'.mkPos 1 2 (by decide)
def minimalParityQuarter : Q' := Q'.mkPos 1 4 (by decide)
def minimalParityEighth : Q' := Q'.mkPos 1 8 (by decide)

/-- Uniform law on the four states of even Boolean parity. -/
def minimalEvenParityMass : MinimalParityState → Q'
  | (false, false, false) => minimalParityQuarter
  | (false, true, true) => minimalParityQuarter
  | (true, false, true) => minimalParityQuarter
  | (true, true, false) => minimalParityQuarter
  | _ => 0

def minimalParityLeftEvent (state : MinimalParityState) : Bool := state.1
def minimalParitySharedEvent (state : MinimalParityState) : Bool := state.2.1
def minimalParityRightEvent (state : MinimalParityState) : Bool := state.2.2

theorem minimalEvenParityMass_normalized :
    listQSum minimalEvenParityMass minimalParityStateSpace ≈ 1 := by
  decide

theorem minimalEvenParity_left_mass :
    finiteEventMass minimalEvenParityMass minimalParityStateSpace
        minimalParityLeftEvent ≈ minimalParityHalf := by
  decide

theorem minimalEvenParity_shared_mass :
    finiteEventMass minimalEvenParityMass minimalParityStateSpace
        minimalParitySharedEvent ≈ minimalParityHalf := by
  decide

theorem minimalEvenParity_right_mass :
    finiteEventMass minimalEvenParityMass minimalParityStateSpace
        minimalParityRightEvent ≈ minimalParityHalf := by
  decide

theorem minimalEvenParity_left_shared_cross_zero :
    finiteCenteredCrossMoment minimalEvenParityMass minimalParityStateSpace
        minimalParityHalf minimalParityHalf
        minimalParityLeftEvent minimalParitySharedEvent ≈ 0 := by
  decide

theorem minimalEvenParity_left_right_cross_zero :
    finiteCenteredCrossMoment minimalEvenParityMass minimalParityStateSpace
        minimalParityHalf minimalParityHalf
        minimalParityLeftEvent minimalParityRightEvent ≈ 0 := by
  decide

theorem minimalEvenParity_shared_right_cross_zero :
    finiteCenteredCrossMoment minimalEvenParityMass minimalParityStateSpace
        minimalParityHalf minimalParityHalf
        minimalParitySharedEvent minimalParityRightEvent ≈ 0 := by
  decide

/-- All pair moments vanish, but the centered third moment is exactly
`-1/8`. -/
theorem minimalEvenParity_thirdMoment_eqv_neg_eighth :
    finiteCenteredThirdMoment minimalEvenParityMass minimalParityStateSpace
        minimalParityHalf minimalParityHalf minimalParityHalf
        minimalParityLeftEvent minimalParitySharedEvent
        minimalParityRightEvent ≈ -minimalParityEighth := by
  decide

theorem minimalEvenParity_thirdMoment_ne_zero :
    ¬ finiteCenteredThirdMoment minimalEvenParityMass minimalParityStateSpace
        minimalParityHalf minimalParityHalf minimalParityHalf
        minimalParityLeftEvent minimalParitySharedEvent
        minimalParityRightEvent ≈ 0 := by
  decide

def threeBlockOverlapEpsilon : Q' := Q'.mkPos 1 8 (by decide)

def minimalParityPairwiseRowTotal : Q' :=
  listQSum
    (fun target => minimalEvenParityMass target *
      threeBlockPairwiseCorrectedDensity threeBlockOverlapEpsilon
        minimalParityHalf minimalParityHalf minimalParityHalf
        (centeredEventCoordinate minimalParityHalf
          minimalParityLeftEvent target)
        (centeredEventCoordinate minimalParityHalf
          minimalParitySharedEvent target)
        (centeredEventCoordinate minimalParityHalf
          minimalParityRightEvent target)
        0 0 0 0 0 0) minimalParityStateSpace

/-- Kernel-checked obstruction: even with every pair covariance equal to
zero, the pairwise-only three-block row is not normalized. -/
theorem minimalParityPairwiseRowTotal_ne_one :
    ¬ minimalParityPairwiseRowTotal ≈ 1 := by
  decide

/-! ## 6. Uniform moment and product bounds -/

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ states : List A,
    (∀ state, state ∈ states → lower state ≤ upper state) →
      listQSum lower states ≤ listQSum upper states
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpointwise =>
      Q'.add_le_add
        (hpointwise head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun state hstate =>
            hpointwise state (List.mem_cons_of_mem head hstate)))

theorem finiteWeightedUnitFeature_bounds {A : Type}
    (mass : A → Q') (states : List A) (feature : A → Q')
    (hmass : ∀ state, (0 : Q') ≤ mass state)
    (hfeature : ∀ state, state ∈ states →
      -(1 : Q') ≤ feature state ∧ feature state ≤ (1 : Q'))
    (htotal : listQSum mass states ≈ 1) :
    -(1 : Q') ≤ listQSum (fun state => mass state * feature state) states ∧
      listQSum (fun state => mass state * feature state) states ≤
        (1 : Q') := by
  let weighted := fun state => mass state * feature state
  let lower := fun state => (-(1 : Q')) * mass state
  have hupperSum : listQSum weighted states ≤ listQSum mass states := by
    apply listQSum_mono_local weighted mass states
    intro state hstate
    exact Q'.le_trans' _ (mass state * 1) _
      (Q'.mul_le_mul_of_nonneg_left
        (feature state) 1 (mass state) (hfeature state hstate).2
        (hmass state))
      (Q'.le_of_eqv (Q'.mul_one_eqv (mass state)))
  have hlowerSum : listQSum lower states ≤ listQSum weighted states := by
    apply listQSum_mono_local lower weighted states
    intro state hstate
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      (-(1 : Q')) (feature state) (mass state)
      (hfeature state hstate).1 (hmass state)
    exact Q'.le_trans' _ (mass state * (-(1 : Q'))) _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv (-(1 : Q')) (mass state))) hscaled
  have hlowerTotal : listQSum lower states ≈ -(1 : Q') := by
    refine Q'.eqv_trans _
      ((-(1 : Q')) * listQSum mass states) _
      (listQSum_mul_left (-(1 : Q')) mass states) ?_
    refine Q'.eqv_trans _ ((-(1 : Q')) * 1) _
      (Q'.mul_eqv_congr_left (-(1 : Q')) _ _ htotal) ?_
    exact Q'.mul_one_eqv (-(1 : Q'))
  constructor
  · exact Q'.le_trans' _ (listQSum lower states) _
      (Q'.le_of_eqv (Q'.eqv_symm hlowerTotal)) hlowerSum
  · exact Q'.le_trans' _ (listQSum mass states) _ hupperSum
      (Q'.le_of_eqv htotal)

theorem qBoundedProduct_bounds
    (u v boundU boundV : Q')
    (hboundU0 : (0 : Q') ≤ boundU)
    (hboundV0 : (0 : Q') ≤ boundV)
    (huLower : -boundU ≤ u) (huUpper : u ≤ boundU)
    (hvLower : -boundV ≤ v) (hvUpper : v ≤ boundV) :
    -(boundU * boundV) ≤ u * v ∧
      u * v ≤ boundU * boundV := by
  have hupper := Q'.mul_le_of_bounds hboundU0 hboundV0
    huLower huUpper hvLower hvUpper
  have hnegULower : -boundU ≤ -u := Q'.neg_le_neg huUpper
  have hnegUUpper : -u ≤ boundU := by
    refine Q'.le_trans' _ (-(-boundU)) _
      (Q'.neg_le_neg huLower) ?_
    exact Q'.le_of_eqv (Q'.neg_neg_eqv boundU)
  have hnegProductRaw : (-u) * v ≤ boundU * boundV :=
    Q'.mul_le_of_bounds hboundU0 hboundV0
      hnegULower hnegUUpper hvLower hvUpper
  have hnegProduct : -(u * v) ≤ boundU * boundV :=
    Q'.le_trans' _ ((-u) * v) _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.neg_mul_eqv u v)))
      hnegProductRaw
  have hlowerNeg : -(boundU * boundV) ≤ -(-(u * v)) :=
    Q'.neg_le_neg hnegProduct
  exact
    ⟨Q'.le_trans' _ (-(-(u * v))) _ hlowerNeg
        (Q'.le_of_eqv (Q'.neg_neg_eqv (u * v))),
      hupper⟩

theorem scale_lower_bound
    (scale bound value : Q')
    (hscale0 : (0 : Q') ≤ scale)
    (hlower : -bound ≤ value) :
    -(scale * bound) ≤ scale * value := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left
    (-bound) value scale hlower hscale0
  refine Q'.le_trans' _ (scale * -bound) _ ?_ hscaled
  exact Q'.le_of_eqv
    (Q'.eqv_symm (Q'.mul_neg_eqv scale bound))

theorem overlapLeftSharedMoment_unit_bounds {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) :
    -(1 : Q') ≤ overlapLeftSharedMoment law ∧
      overlapLeftSharedMoment law ≤ (1 : Q') := by
  unfold overlapLeftSharedMoment
  exact finiteCenteredCrossMoment_unit_bounds
    law.mass law.states law.leftParameter law.sharedParameter
    law.leftEvent law.sharedEvent (fun state _ => law.mass_nonnegative state)
    law.left_nonnegative law.left_le_one
    law.shared_nonnegative law.shared_le_one
    law.left_mass law.shared_mass law.normalized

theorem overlapLeftRightMoment_unit_bounds {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) :
    -(1 : Q') ≤ overlapLeftRightMoment law ∧
      overlapLeftRightMoment law ≤ (1 : Q') := by
  unfold overlapLeftRightMoment
  exact finiteCenteredCrossMoment_unit_bounds
    law.mass law.states law.leftParameter law.rightParameter
    law.leftEvent law.rightEvent (fun state _ => law.mass_nonnegative state)
    law.left_nonnegative law.left_le_one
    law.right_nonnegative law.right_le_one
    law.left_mass law.right_mass law.normalized

theorem overlapSharedRightMoment_unit_bounds {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) :
    -(1 : Q') ≤ overlapSharedRightMoment law ∧
      overlapSharedRightMoment law ≤ (1 : Q') := by
  unfold overlapSharedRightMoment
  exact finiteCenteredCrossMoment_unit_bounds
    law.mass law.states law.sharedParameter law.rightParameter
    law.sharedEvent law.rightEvent
    (fun state _ => law.mass_nonnegative state)
    law.shared_nonnegative law.shared_le_one
    law.right_nonnegative law.right_le_one
    law.shared_mass law.right_mass law.normalized

theorem overlapThirdMoment_unit_bounds {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) :
    -(1 : Q') ≤ overlapThirdMoment law ∧
      overlapThirdMoment law ≤ (1 : Q') := by
  let cubic := fun state =>
    overlapLeftCoordinate law state *
      (overlapSharedCoordinate law state * overlapRightCoordinate law state)
  have hcubic : ∀ state, state ∈ law.states →
      -(1 : Q') ≤ cubic state ∧ cubic state ≤ (1 : Q') := by
    intro state _
    have hleft := centeredEventCoordinate_unit_bounds
      law.leftParameter law.leftEvent state
      law.left_nonnegative law.left_le_one
    have hshared := centeredEventCoordinate_unit_bounds
      law.sharedParameter law.sharedEvent state
      law.shared_nonnegative law.shared_le_one
    have hright := centeredEventCoordinate_unit_bounds
      law.rightParameter law.rightEvent state
      law.right_nonnegative law.right_le_one
    have hsharedRight := qUnitProduct_bounds
      (overlapSharedCoordinate law state)
      (overlapRightCoordinate law state)
      hshared.1 hshared.2 hright.1 hright.2
    exact qUnitProduct_bounds
      (overlapLeftCoordinate law state)
      (overlapSharedCoordinate law state * overlapRightCoordinate law state)
      hleft.1 hleft.2 hsharedRight.1 hsharedRight.2
  unfold overlapThirdMoment finiteCenteredThirdMoment
  exact finiteWeightedUnitFeature_bounds law.mass law.states cubic
    law.mass_nonnegative hcubic law.normalized

/-! ## 7. A closed nonnegative three-block overlap kernel -/

private theorem scalarFeatureDensity_seven_mono
    (lower0 lower1 lower2 lower3 lower4 lower5 lower6 : Q')
    (upper0 upper1 upper2 upper3 upper4 upper5 upper6 : Q')
    (h0 : lower0 ≤ upper0) (h1 : lower1 ≤ upper1)
    (h2 : lower2 ≤ upper2) (h3 : lower3 ≤ upper3)
    (h4 : lower4 ≤ upper4) (h5 : lower5 ≤ upper5)
    (h6 : lower6 ≤ upper6) :
    scalarFeatureDensity
        [lower0, lower1, lower2, lower3, lower4, lower5, lower6] ≤
      scalarFeatureDensity
        [upper0, upper1, upper2, upper3, upper4, upper5, upper6] := by
  unfold scalarFeatureDensity
  exact Q'.add_le_add
    (Q'.add_le_add
      (Q'.add_le_add
        (Q'.add_le_add
          (Q'.add_le_add
            (Q'.add_le_add
              (Q'.add_le_add (Q'.le_refl' 1) h6) h5) h4) h3) h2) h1) h0

/-- At the exact rational choice `epsilon = 1/8`, the fully centered
three-block overlap density is nonnegative for every admissible collection
of coordinates and complete-law moments.  The closed lower budget is

`1 - 3/8 - 3 * 4/64 - 4/512 = 55/128`.
-/
theorem threeBlockOverlapCorrectedDensity_eighth_nonnegative
    (a1 a2 a3 b1 b2 b3 : Q')
    (source12 source13 source23 : Q')
    (target12 target13 target23 : Q')
    (source123 target123 : Q')
    (ha1 : -(1 : Q') ≤ a1 ∧ a1 ≤ (1 : Q'))
    (ha2 : -(1 : Q') ≤ a2 ∧ a2 ≤ (1 : Q'))
    (ha3 : -(1 : Q') ≤ a3 ∧ a3 ≤ (1 : Q'))
    (hb1 : -(1 : Q') ≤ b1 ∧ b1 ≤ (1 : Q'))
    (hb2 : -(1 : Q') ≤ b2 ∧ b2 ≤ (1 : Q'))
    (hb3 : -(1 : Q') ≤ b3 ∧ b3 ≤ (1 : Q'))
    (hsource12 : -(1 : Q') ≤ source12 ∧ source12 ≤ (1 : Q'))
    (hsource13 : -(1 : Q') ≤ source13 ∧ source13 ≤ (1 : Q'))
    (hsource23 : -(1 : Q') ≤ source23 ∧ source23 ≤ (1 : Q'))
    (htarget12 : -(1 : Q') ≤ target12 ∧ target12 ≤ (1 : Q'))
    (htarget13 : -(1 : Q') ≤ target13 ∧ target13 ≤ (1 : Q'))
    (htarget23 : -(1 : Q') ≤ target23 ∧ target23 ≤ (1 : Q'))
    (hsource123 : -(1 : Q') ≤ source123 ∧ source123 ≤ (1 : Q'))
    (htarget123 : -(1 : Q') ≤ target123 ∧ target123 ≤ (1 : Q')) :
    (0 : Q') ≤ threeBlockOverlapCorrectedDensity threeBlockOverlapEpsilon
      a1 a2 a3 b1 b2 b3
      source12 source13 source23 target12 target13 target23
      source123 target123 := by
  let epsilon := threeBlockOverlapEpsilon
  let epsilon2 := epsilon * epsilon
  let epsilon3 := epsilon2 * epsilon
  let sourceDeviation12 := a1 * a2 + -source12
  let sourceDeviation13 := a1 * a3 + -source13
  let sourceDeviation23 := a2 * a3 + -source23
  let targetDeviation12 := b1 * b2 + -target12
  let targetDeviation13 := b1 * b3 + -target13
  let targetDeviation23 := b2 * b3 + -target23
  let sourceDeviation123 := a1 * (a2 * a3) + -source123
  let targetDeviation123 := b1 * (b2 * b3) + -target123
  have hepsilon0 : (0 : Q') ≤ epsilon := by
    unfold epsilon threeBlockOverlapEpsilon
    decide
  have hepsilon20 : (0 : Q') ≤ epsilon2 := by
    unfold epsilon2
    exact Q'.mul_nonneg epsilon epsilon hepsilon0 hepsilon0
  have hepsilon30 : (0 : Q') ≤ epsilon3 := by
    unfold epsilon3
    exact Q'.mul_nonneg epsilon2 epsilon hepsilon20 hepsilon0
  have ha12 := qUnitProduct_bounds a1 a2 ha1.1 ha1.2 ha2.1 ha2.2
  have ha13 := qUnitProduct_bounds a1 a3 ha1.1 ha1.2 ha3.1 ha3.2
  have ha23 := qUnitProduct_bounds a2 a3 ha2.1 ha2.2 ha3.1 ha3.2
  have hb12 := qUnitProduct_bounds b1 b2 hb1.1 hb1.2 hb2.1 hb2.2
  have hb13 := qUnitProduct_bounds b1 b3 hb1.1 hb1.2 hb3.1 hb3.2
  have hb23 := qUnitProduct_bounds b2 b3 hb2.1 hb2.2 hb3.1 hb3.2
  have hsourceDeviation12 := qUnitDifference_bounds
    (a1 * a2) source12 ha12.1 ha12.2 hsource12.1 hsource12.2
  have hsourceDeviation13 := qUnitDifference_bounds
    (a1 * a3) source13 ha13.1 ha13.2 hsource13.1 hsource13.2
  have hsourceDeviation23 := qUnitDifference_bounds
    (a2 * a3) source23 ha23.1 ha23.2 hsource23.1 hsource23.2
  have htargetDeviation12 := qUnitDifference_bounds
    (b1 * b2) target12 hb12.1 hb12.2 htarget12.1 htarget12.2
  have htargetDeviation13 := qUnitDifference_bounds
    (b1 * b3) target13 hb13.1 hb13.2 htarget13.1 htarget13.2
  have htargetDeviation23 := qUnitDifference_bounds
    (b2 * b3) target23 hb23.1 hb23.2 htarget23.1 htarget23.2
  have hpair12 := qBoundedProduct_bounds
    sourceDeviation12 targetDeviation12 2 2 (by decide) (by decide)
    hsourceDeviation12.1 hsourceDeviation12.2
    htargetDeviation12.1 htargetDeviation12.2
  have hpair13 := qBoundedProduct_bounds
    sourceDeviation13 targetDeviation13 2 2 (by decide) (by decide)
    hsourceDeviation13.1 hsourceDeviation13.2
    htargetDeviation13.1 htargetDeviation13.2
  have hpair23 := qBoundedProduct_bounds
    sourceDeviation23 targetDeviation23 2 2 (by decide) (by decide)
    hsourceDeviation23.1 hsourceDeviation23.2
    htargetDeviation23.1 htargetDeviation23.2
  have ha23Unit := qUnitProduct_bounds a2 a3 ha2.1 ha2.2 ha3.1 ha3.2
  have hb23Unit := qUnitProduct_bounds b2 b3 hb2.1 hb2.2 hb3.1 hb3.2
  have ha123 := qUnitProduct_bounds a1 (a2 * a3)
    ha1.1 ha1.2 ha23Unit.1 ha23Unit.2
  have hb123 := qUnitProduct_bounds b1 (b2 * b3)
    hb1.1 hb1.2 hb23Unit.1 hb23Unit.2
  have hsourceDeviation123 := qUnitDifference_bounds
    (a1 * (a2 * a3)) source123
    ha123.1 ha123.2 hsource123.1 hsource123.2
  have htargetDeviation123 := qUnitDifference_bounds
    (b1 * (b2 * b3)) target123
    hb123.1 hb123.2 htarget123.1 htarget123.2
  have hthird := qBoundedProduct_bounds
    sourceDeviation123 targetDeviation123 2 2 (by decide) (by decide)
    hsourceDeviation123.1 hsourceDeviation123.2
    htargetDeviation123.1 htargetDeviation123.2
  have hsingle1 : -(epsilon * 1) ≤ epsilon * a1 * b1 := by
    have hproduct := qUnitProduct_bounds a1 b1 ha1.1 ha1.2 hb1.1 hb1.2
    exact Q'.le_trans' _ (epsilon * (a1 * b1)) _
      (scale_lower_bound epsilon 1 (a1 * b1) hepsilon0 hproduct.1)
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv epsilon a1 b1)))
  have hsingle2 : -(epsilon * 1) ≤ epsilon * a2 * b2 := by
    have hproduct := qUnitProduct_bounds a2 b2 ha2.1 ha2.2 hb2.1 hb2.2
    exact Q'.le_trans' _ (epsilon * (a2 * b2)) _
      (scale_lower_bound epsilon 1 (a2 * b2) hepsilon0 hproduct.1)
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv epsilon a2 b2)))
  have hsingle3 : -(epsilon * 1) ≤ epsilon * a3 * b3 := by
    have hproduct := qUnitProduct_bounds a3 b3 ha3.1 ha3.2 hb3.1 hb3.2
    exact Q'.le_trans' _ (epsilon * (a3 * b3)) _
      (scale_lower_bound epsilon 1 (a3 * b3) hepsilon0 hproduct.1)
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv epsilon a3 b3)))
  have hpairFeature12 :
      -(epsilon2 * (2 * 2)) ≤
        epsilon2 * (sourceDeviation12 * targetDeviation12) :=
    scale_lower_bound epsilon2 (2 * 2)
      (sourceDeviation12 * targetDeviation12) hepsilon20 hpair12.1
  have hpairFeature13 :
      -(epsilon2 * (2 * 2)) ≤
        epsilon2 * (sourceDeviation13 * targetDeviation13) :=
    scale_lower_bound epsilon2 (2 * 2)
      (sourceDeviation13 * targetDeviation13) hepsilon20 hpair13.1
  have hpairFeature23 :
      -(epsilon2 * (2 * 2)) ≤
        epsilon2 * (sourceDeviation23 * targetDeviation23) :=
    scale_lower_bound epsilon2 (2 * 2)
      (sourceDeviation23 * targetDeviation23) hepsilon20 hpair23.1
  have hthirdFeature :
      -(epsilon3 * (2 * 2)) ≤
        epsilon3 * (sourceDeviation123 * targetDeviation123) :=
    scale_lower_bound epsilon3 (2 * 2)
      (sourceDeviation123 * targetDeviation123) hepsilon30 hthird.1
  have hclosed :
      (0 : Q') ≤ scalarFeatureDensity
        [-((epsilon3) * (2 * 2)),
          -(epsilon * 1), -(epsilon * 1), -(epsilon * 1),
          -(epsilon2 * (2 * 2)), -(epsilon2 * (2 * 2)),
          -(epsilon2 * (2 * 2))] := by
    unfold epsilon epsilon2 epsilon3 threeBlockOverlapEpsilon
    decide
  have hmono := scalarFeatureDensity_seven_mono
    (-(epsilon3 * (2 * 2))) (-(epsilon * 1)) (-(epsilon * 1))
    (-(epsilon * 1)) (-(epsilon2 * (2 * 2)))
    (-(epsilon2 * (2 * 2))) (-(epsilon2 * (2 * 2)))
    (epsilon3 * (sourceDeviation123 * targetDeviation123))
    (epsilon * a1 * b1) (epsilon * a2 * b2) (epsilon * a3 * b3)
    (epsilon2 * (sourceDeviation12 * targetDeviation12))
    (epsilon2 * (sourceDeviation13 * targetDeviation13))
    (epsilon2 * (sourceDeviation23 * targetDeviation23))
    hthirdFeature hsingle1 hsingle2 hsingle3
    hpairFeature12 hpairFeature13 hpairFeature23
  refine Q'.le_trans' _
    (scalarFeatureDensity
      [-((epsilon3) * (2 * 2)),
        -(epsilon * 1), -(epsilon * 1), -(epsilon * 1),
        -(epsilon2 * (2 * 2)), -(epsilon2 * (2 * 2)),
        -(epsilon2 * (2 * 2))]) _ hclosed ?_
  refine Q'.le_trans' _
    (scalarFeatureDensity
      [epsilon3 * (sourceDeviation123 * targetDeviation123),
        epsilon * a1 * b1, epsilon * a2 * b2, epsilon * a3 * b3,
        epsilon2 * (sourceDeviation12 * targetDeviation12),
        epsilon2 * (sourceDeviation13 * targetDeviation13),
        epsilon2 * (sourceDeviation23 * targetDeviation23)]) _ hmono ?_
  unfold epsilon epsilon2 epsilon3 sourceDeviation12 sourceDeviation13
    sourceDeviation23 targetDeviation12 targetDeviation13 targetDeviation23
    sourceDeviation123 targetDeviation123
    threeBlockOverlapCorrectedDensity
    threeBlockPairwiseCorrectedBaseDensity
  exact Q'.le_refl' _

/-- The exact overlap kernel is a constructive nonnegative kernel at the
closed coupling `epsilon = 1/8`. -/
theorem threeBlockOverlapConfigurationKernel_nonnegative
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (source : Source) (target : Target) :
    (0 : Q') ≤ threeBlockOverlapConfigurationKernel sourceLaw targetLaw
      threeBlockOverlapEpsilon source target := by
  unfold threeBlockOverlapConfigurationKernel
  apply Q'.mul_nonneg
  · exact targetLaw.mass_nonnegative target
  · apply threeBlockOverlapCorrectedDensity_eighth_nonnegative
    · exact centeredEventCoordinate_unit_bounds
        sourceLaw.leftParameter sourceLaw.leftEvent source
        sourceLaw.left_nonnegative sourceLaw.left_le_one
    · exact centeredEventCoordinate_unit_bounds
        sourceLaw.sharedParameter sourceLaw.sharedEvent source
        sourceLaw.shared_nonnegative sourceLaw.shared_le_one
    · exact centeredEventCoordinate_unit_bounds
        sourceLaw.rightParameter sourceLaw.rightEvent source
        sourceLaw.right_nonnegative sourceLaw.right_le_one
    · exact centeredEventCoordinate_unit_bounds
        targetLaw.leftParameter targetLaw.leftEvent target
        targetLaw.left_nonnegative targetLaw.left_le_one
    · exact centeredEventCoordinate_unit_bounds
        targetLaw.sharedParameter targetLaw.sharedEvent target
        targetLaw.shared_nonnegative targetLaw.shared_le_one
    · exact centeredEventCoordinate_unit_bounds
        targetLaw.rightParameter targetLaw.rightEvent target
        targetLaw.right_nonnegative targetLaw.right_le_one
    · exact overlapLeftSharedMoment_unit_bounds sourceLaw
    · exact overlapLeftRightMoment_unit_bounds sourceLaw
    · exact overlapSharedRightMoment_unit_bounds sourceLaw
    · exact overlapLeftSharedMoment_unit_bounds targetLaw
    · exact overlapLeftRightMoment_unit_bounds targetLaw
    · exact overlapSharedRightMoment_unit_bounds targetLaw
    · exact overlapThirdMoment_unit_bounds sourceLaw
    · exact overlapThirdMoment_unit_bounds targetLaw

/-! ### The induced positive exact coupling -/

def threeBlockOverlapJointMass {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (source : Source) (target : Target) : Q' :=
  sourceLaw.mass source *
    threeBlockOverlapConfigurationKernel sourceLaw targetLaw
      threeBlockOverlapEpsilon source target

theorem threeBlockOverlapJointMass_nonnegative {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (source : Source) (target : Target) :
    (0 : Q') ≤ threeBlockOverlapJointMass sourceLaw targetLaw source target := by
  unfold threeBlockOverlapJointMass
  exact Q'.mul_nonneg _ _ (sourceLaw.mass_nonnegative source)
    (threeBlockOverlapConfigurationKernel_nonnegative
      sourceLaw targetLaw source target)

theorem threeBlockOverlapJointMass_source_marginal {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (source : Source) :
    listQSum (threeBlockOverlapJointMass sourceLaw targetLaw source)
        targetLaw.states ≈ sourceLaw.mass source := by
  unfold threeBlockOverlapJointMass
  refine Q'.eqv_trans _
    (sourceLaw.mass source *
      listQSum
        (threeBlockOverlapConfigurationKernel sourceLaw targetLaw
          threeBlockOverlapEpsilon source) targetLaw.states) _ ?_ ?_
  · exact listQSum_mul_left (sourceLaw.mass source)
      (threeBlockOverlapConfigurationKernel sourceLaw targetLaw
        threeBlockOverlapEpsilon source) targetLaw.states
  refine Q'.eqv_trans _ (sourceLaw.mass source * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (sourceLaw.mass source) _ _
      (threeBlockOverlapConfigurationKernel_row_normalized
        sourceLaw targetLaw threeBlockOverlapEpsilon source)
  exact Q'.mul_one_eqv (sourceLaw.mass source)

theorem threeBlockOverlapJointMass_target_marginal {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (target : Target) :
    listQSum
        (fun source => threeBlockOverlapJointMass
          sourceLaw targetLaw source target) sourceLaw.states ≈
      targetLaw.mass target := by
  change configurationPushforward sourceLaw.mass sourceLaw.states
      (threeBlockOverlapConfigurationKernel sourceLaw targetLaw
        threeBlockOverlapEpsilon) target ≈ targetLaw.mass target
  exact threeBlockOverlapConfigurationKernel_pushforward
    sourceLaw targetLaw threeBlockOverlapEpsilon target

theorem threeBlockOverlapJointMass_normalized {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target) :
    listQSum
        (fun source => listQSum
          (threeBlockOverlapJointMass sourceLaw targetLaw source)
          targetLaw.states) sourceLaw.states ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum sourceLaw.mass sourceLaw.states) _ ?_ sourceLaw.normalized
  apply listQSum_congr_on
  intro source _
  exact threeBlockOverlapJointMass_source_marginal
    sourceLaw targetLaw source

def threeBlockOverlapPositiveFiniteConfigurationCoupling
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target) :
    PositiveFiniteConfigurationCoupling
      sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states
      (threeBlockOverlapJointMass sourceLaw targetLaw) where
  nonnegative := threeBlockOverlapJointMass_nonnegative sourceLaw targetLaw
  source_marginal :=
    threeBlockOverlapJointMass_source_marginal sourceLaw targetLaw
  target_marginal :=
    threeBlockOverlapJointMass_target_marginal sourceLaw targetLaw
  normalized := threeBlockOverlapJointMass_normalized sourceLaw targetLaw

#print axioms finiteCenteredThirdMoment
#print axioms finiteCenteredThirdDeviation_total
#print axioms threeBlockOverlapCorrectedDensity_eqv_pairwise_minus_cubic_defects
#print axioms threeBlockOverlapConfigurationKernel_row_normalized
#print axioms threeBlockOverlapConfigurationKernel_pushforward
#print axioms minimalEvenParity_left_shared_cross_zero
#print axioms minimalEvenParity_left_right_cross_zero
#print axioms minimalEvenParity_shared_right_cross_zero
#print axioms minimalEvenParity_thirdMoment_eqv_neg_eighth
#print axioms minimalParityPairwiseRowTotal_ne_one
#print axioms overlapThirdMoment_unit_bounds
#print axioms threeBlockOverlapCorrectedDensity_eighth_nonnegative
#print axioms threeBlockOverlapConfigurationKernel_nonnegative
#print axioms threeBlockOverlapPositiveFiniteConfigurationCoupling

end YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
