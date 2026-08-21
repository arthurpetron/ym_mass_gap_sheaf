/-
# Exact `L2` contraction of the physical BF4 Markov operator

The literal BF4 conditional kernel is already known to be nonnegative,
row-normalized, stationary, and reversible.  The transfer-form interval
`0 <= <f,Tf> <= <f,f>` does not by itself provide the squared-norm estimate
needed to descend `T` to the constructive GNS completion.  This module proves
that missing estimate directly.

The proof is finite and rational.  Its only analytic ingredient is the exact
weighted variance identity

  sum p_i (x_i - mean)^2 = sum p_i x_i^2 - mean^2,

for a nonnegative row of total mass one.  Applying this rowwise gives Jensen;
stationarity then collapses the outer marginal sum and yields

  <Tf,Tf> <= <f,f>.

This is a finite-cutoff macro-transfer law.  It neither constructs a continuum
operator nor proves a strict vacuum-complement gap.
-/

import YMGap.Continuum.BF4PhysicalMarkovTransferLaws

namespace YMGap.Continuum.BF4PhysicalMarkovL2Contraction

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic exact finite Jensen inequality -/

/-- A nonnegative exact-rational probability row satisfies the square Jensen
inequality.  No square roots or choice of support are used. -/
theorem finiteProbabilityRow_square_jensen
    {State : Type}
    (states : List State)
    (weight value : State → Q')
    (hweight : ∀ state, state ∈ states → (0 : Q') ≤ weight state)
    (hnormalized : listQSum weight states ≈ 1) :
    listQSum (fun state => weight state * value state) states *
          listQSum (fun state => weight state * value state) states ≤
      listQSum
        (fun state => weight state * (value state * value state))
        states := by
  let mean :=
    listQSum (fun state => weight state * value state) states
  let varianceTerm : State → Q' := fun state =>
    weight state *
      ((value state + -mean) * (value state + -mean))
  let squareTerm : State → Q' := fun state =>
    weight state * (value state * value state)
  let crossTerm : State → Q' := fun state =>
    (-(mean + mean)) * (weight state * value state)
  let constantTerm : State → Q' := fun state =>
    (mean * mean) * weight state
  have hvarianceNonnegative :
      (0 : Q') ≤ listQSum varianceTerm states := by
    apply listQSum_nonnegative_on
    intro state hstate
    exact Q'.mul_nonneg _ _
      (hweight state hstate)
      (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
        (value state + -mean))
  have hpointwise : ∀ state, state ∈ states →
      varianceTerm state ≈
        squareTerm state + (crossTerm state + constantTerm state) := by
    intro state _
    unfold varianceTerm squareTerm crossTerm constantTerm
    q_ring
  have hexpand :
      listQSum varianceTerm states ≈
        listQSum squareTerm states +
          (listQSum crossTerm states +
            listQSum constantTerm states) := by
    refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          squareTerm state +
            (crossTerm state + constantTerm state))
        states) _ ?_ ?_
    · exact listQSum_congr_on varianceTerm _ states hpointwise
    · refine Q'.eqv_trans _
        (listQSum squareTerm states +
          listQSum (fun state => crossTerm state + constantTerm state) states) _
        (listQSum_add squareTerm
          (fun state => crossTerm state + constantTerm state) states) ?_
      exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (listQSum_add crossTerm constantTerm states)
  have hcross :
      listQSum crossTerm states ≈
        (-(mean + mean)) * mean := by
    unfold crossTerm mean
    exact listQSum_mul_left
      (-(listQSum (fun state => weight state * value state) states +
        listQSum (fun state => weight state * value state) states))
      (fun state => weight state * value state) states
  have hconstant :
      listQSum constantTerm states ≈ mean * mean := by
    refine Q'.eqv_trans _
      ((mean * mean) * listQSum weight states) _ ?_ ?_
    · exact listQSum_mul_left (mean * mean) weight states
    · refine Q'.eqv_trans _ ((mean * mean) * 1) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left (mean * mean) _ _ hnormalized
      · exact Q'.mul_one_eqv _
  have hvarianceIdentity :
      listQSum varianceTerm states ≈
        listQSum squareTerm states + -(mean * mean) := by
    refine Q'.eqv_trans _
      (listQSum squareTerm states +
        (listQSum crossTerm states + listQSum constantTerm states)) _
      hexpand ?_
    refine Q'.eqv_trans _
      (listQSum squareTerm states +
        ((-(mean + mean)) * mean + mean * mean)) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' hcross hconstant)
    · apply Q'.add_eqv_congr'
      · exact Q'.eqv_refl _
      · have hdouble :
            (-(mean + mean)) * mean ≈
              (-(mean * mean)) + (-(mean * mean)) := by
          refine Q'.eqv_trans _ ((-mean + -mean) * mean) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ mean
              (Q'.neg_add_eqv mean mean)
          · refine Q'.eqv_trans _
              ((-mean) * mean + (-mean) * mean) _
              (Q'.add_mul_eqv (-mean) (-mean) mean) ?_
            exact Q'.add_eqv_congr'
              (Q'.neg_mul_eqv mean mean)
              (Q'.neg_mul_eqv mean mean)
        refine Q'.eqv_trans _
          (((-(mean * mean)) + (-(mean * mean))) + mean * mean) _
          (Q'.add_eqv_congr' hdouble (Q'.eqv_refl _)) ?_
        refine Q'.eqv_trans _
          ((-(mean * mean)) + ((-(mean * mean)) + mean * mean)) _
          (Q'.add_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _ ((-(mean * mean)) + 0) _ ?_ ?_
        · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.neg_add_self_eqv (mean * mean))
        · exact Q'.eqv_of_eq (Q'.add_zero' (-(mean * mean)))
  change mean * mean ≤ listQSum squareTerm states
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ hvarianceNonnegative
    (Q'.le_of_eqv hvarianceIdentity)

/-! ## 2. Jensen for every literal physical BF4 conditional row -/

theorem centralPhysicalMarkovApply_square_le
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (observable : EdgeLabelling → Q')
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    centralPhysicalMarkovApply w hw K half observable source *
          centralPhysicalMarkovApply w hw K half observable source ≤
      centralPhysicalMarkovApply w hw K half
        (fun target => observable target * observable target) source := by
  exact finiteProbabilityRow_square_jensen
    (centralPositiveHalfStates w hw K half)
    (centralPhysicalConditionalKernel w hw K half source)
    observable
    (fun target _ =>
      centralPhysicalConditionalKernel_nonnegative
        hw K half source target)
    (centralPhysicalConditionalKernel_row_normalized hsource)

/-! ## 3. Stationarity upgrades row Jensen to physical `L2` contraction -/

/-- The literal finite BF4 macro transfer is nonexpansive in the exact physical
stationary `L2` norm.  This is the carrier estimate required by the explicit
constructive GNS-completion lift. -/
theorem centralPhysicalMarkovApply_l2_contraction
    (w : Q') (hw : (0 : Q') ≤ w)
    (K half : Nat) (observable : EdgeLabelling → Q') :
    centralPhysicalWeightedInner w hw K half
        (centralPhysicalMarkovApply w hw K half observable)
        (centralPhysicalMarkovApply w hw K half observable) ≤
      centralPhysicalWeightedInner w hw K half observable observable := by
  let states := centralPositiveHalfStates w hw K half
  let squared : EdgeLabelling → Q' := fun state =>
    observable state * observable state
  have hrows :
      listQSum
          (fun source =>
            centralPhysicalRowMarginal w hw K half source *
              (centralPhysicalMarkovApply w hw K half observable source *
                centralPhysicalMarkovApply w hw K half observable source))
          states ≤
        listQSum
          (fun source =>
            centralPhysicalRowMarginal w hw K half source *
              centralPhysicalMarkovApply w hw K half squared source)
          states := by
    apply listQSum_mono
    intro source hsource
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (centralPhysicalMarkovApply_square_le
        w hw K half observable hsource)
      (centralPhysicalRowMarginal_nonnegative hw K half source)
  have hstationary :=
    centralPhysicalStationaryMean_markovApply
      w hw K half squared
  unfold centralPhysicalWeightedInner
  change
    listQSum
        (fun source =>
          centralPhysicalRowMarginal w hw K half source *
            (centralPhysicalMarkovApply w hw K half observable source *
              centralPhysicalMarkovApply w hw K half observable source))
        states ≤
      listQSum
        (fun source =>
          centralPhysicalRowMarginal w hw K half source *
            (observable source * observable source))
        states
  exact Q'.le_trans' _ _ _ hrows
    (Q'.le_of_eqv hstationary)

end YMGap.Continuum.BF4PhysicalMarkovL2Contraction

#print axioms YMGap.Continuum.BF4PhysicalMarkovL2Contraction.finiteProbabilityRow_square_jensen
#print axioms YMGap.Continuum.BF4PhysicalMarkovL2Contraction.centralPhysicalMarkovApply_square_le
#print axioms YMGap.Continuum.BF4PhysicalMarkovL2Contraction.centralPhysicalMarkovApply_l2_contraction
