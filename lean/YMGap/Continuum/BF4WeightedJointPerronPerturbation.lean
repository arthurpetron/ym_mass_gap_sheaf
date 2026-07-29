/-
# Weighted joint-law perturbation on the physical BF4 carrier

The normalized reflected BF4 kernel is a symmetric joint law with a
nonuniform marginal `pi`.  Consequently, a plain entrywise `epsilon / N`
estimate controls an unweighted Hilbert--Schmidt norm but does not by itself
control the physical `ell^2(pi)` Rayleigh quotient.

This module proves the finite constructive replacement.  If two symmetric
joint laws differ by `E` and every absolute row obeys

    sum_y |E(x,y)| <= epsilon * pi(x),

then their quadratic forms differ by at most

    epsilon * sum_x pi(x) * f(x)^2.

The proof is the rational Schur/Young argument

    2 |f(x) f(y)| <= f(x)^2 + f(y)^2.

Symmetry turns the column contribution into a second copy of the row
contribution.  No square root of `pi`, inverse marginal, eigenvector choice,
or classical finite-dimensional spectral theorem is used.

The second half identifies the exact physical Markov quadratic with the
quadratic of the normalized reflected joint law.  It then packages the exact
data that a distinct endpoint Mehler kernel must provide in order to transfer
its mean-zero Rayleigh bound to the physical BF4 operator.

Honest scope: this file proves the weighted comparison layer and its exact
physical specialization.  It does not construct the distinct five-holonomy
Mehler joint law and does not prove the Yang--Mills row-relative estimate.

## Axiom gate

Finite list recursion, decidable rational order, and exact `Q'` algebra only.
No `Classical.*`, `sorry`, `native_decide`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Constructive.CRealAlg
import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.BF4WeightedJointPerronPerturbation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

/-- Cancellation-free rational polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Finite weighted joint-law algebra -/

/-- The absolute row mass of the difference of two finite joint kernels. -/
def finiteJointDifferenceAbsRowMass {State : Type}
    (states : List State)
    (leftJoint rightJoint : State → State → Q')
    (source : State) : Q' :=
  listQSum
    (fun target =>
      Q'.abs
        (leftJoint source target +
          (-rightJoint source target)))
    states

/-- The corresponding absolute column mass. -/
def finiteJointDifferenceAbsColumnMass {State : Type}
    (states : List State)
    (leftJoint rightJoint : State → State → Q')
    (target : State) : Q' :=
  listQSum
    (fun source =>
      Q'.abs
        (leftJoint source target +
          (-rightJoint source target)))
    states

/-- Exact finite weighted square norm. -/
def finiteWeightedSquare {State : Type}
    (states : List State)
    (weight : State → Q')
    (coefficient : State → Q') : Q' :=
  listQSum
    (fun state =>
      weight state *
        (coefficient state * coefficient state))
    states

/-- Triangle inequality for one exact finite list sum. -/
theorem abs_listQSum_le_sum_abs {A : Type}
    (value : A → Q') :
    ∀ items : List A,
      Q'.abs (listQSum value items) ≤
        listQSum (fun item => Q'.abs (value item)) items
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail => by
      change
        Q'.abs (value head + listQSum value tail) ≤
          Q'.abs (value head) +
            listQSum (fun item => Q'.abs (value item)) tail
      exact Q'.le_trans' _ _ _
        (abs_add_le (value head) (listQSum value tail))
        (Q'.add_le_add_left _ _ _
          (abs_listQSum_le_sum_abs value tail))

/-- A pointwise finite-list bound pays exactly one factor of the list
cardinality. -/
theorem listQSum_le_length_mul
    {A : Type} (value : A → Q')
    {bound : Q'} (hboundNonnegative : (0 : Q') ≤ bound) :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≤ bound) →
        listQSum value items ≤
          Q'.ofNat items.length * bound
  | [], _ => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound => by
      have hhead :=
        hbound head List.mem_cons_self
      have htail :=
        listQSum_le_length_mul value hboundNonnegative tail
          (fun item hitem =>
            hbound item
              (List.mem_cons_of_mem head hitem))
      have hsum :
          value head + listQSum value tail ≤
            bound + Q'.ofNat tail.length * bound :=
        Q'.add_le_add hhead htail
      refine Q'.le_trans' _ _ _ hsum ?_
      refine Q'.le_of_eqv (Q'.eqv_symm ?_)
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ bound
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * bound +
          (1 : Q') * bound) _
        (Q'.add_mul_eqv
          (Q'.ofNat tail.length) 1 bound) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * bound + bound) _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.one_mul_eqv bound))
        (Q'.add_comm_eqv
          (Q'.ofNat tail.length * bound) bound)

/-- Entrywise-to-row-relative bridge.  An entry budget `delta(source)` is
sufficient exactly when the carrier factor
`|states| * delta(source)` fits below `epsilon * weight(source)`.

This theorem records the additional marginal information absent from a plain
unweighted `epsilon / N` Hilbert--Schmidt estimate.
-/
theorem finiteJointDifferenceAbsRowMass_le_of_entrywise_budget
    {State : Type}
    (states : List State)
    (leftJoint rightJoint : State → State → Q')
    (entryBudget weight : State → Q')
    (epsilon : Q')
    {source : State}
    (hentryBudgetNonnegative :
      (0 : Q') ≤ entryBudget source)
    (hentry :
      ∀ target, target ∈ states →
        Q'.abs
            (leftJoint source target +
              (-rightJoint source target)) ≤
          entryBudget source)
    (hcardinalityBudget :
      Q'.ofNat states.length *
          entryBudget source ≤
        epsilon * weight source) :
    finiteJointDifferenceAbsRowMass
        states leftJoint rightJoint source ≤
      epsilon * weight source := by
  unfold finiteJointDifferenceAbsRowMass
  exact Q'.le_trans' _ _ _
    (listQSum_le_length_mul
      (fun target =>
        Q'.abs
          (leftJoint source target +
            (-rightJoint source target)))
      hentryBudgetNonnegative states hentry)
    hcardinalityBudget

/-- Rational Young inequality in the exact normalization used below:
`|xy| <= (x^2+y^2)/2`. -/
theorem abs_mul_le_half_square_sum (x y : Q') :
    Q'.abs (x * y) ≤
      half * ((x * x) + (y * y)) := by
  have hproduct :=
    abs_mul_le x y
  have hdouble :
      Q'.abs (x * y) + Q'.abs (x * y) ≤
        (x * x) + (y * y) := by
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add hproduct hproduct) ?_
    refine Q'.le_trans' _ _ _
      (CRealAlg.amgm_two (Q'.abs x) (Q'.abs y)) ?_
    exact Q'.le_of_eqv
      (Q'.add_eqv_congr'
        (by
          by_cases hx : (0 : Q') ≤ x
          · have habsx : Q'.abs x = x := by
              unfold Q'.abs
              rw [if_pos hx]
            rw [habsx]
            exact Q'.eqv_refl _
          · have habsx : Q'.abs x = -x := by
              unfold Q'.abs
              rw [if_neg hx]
            rw [habsx]
            refine Q'.eqv_trans _ _ _
              (Q'.neg_mul_eqv x (-x)) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.neg_eqv_congr _ _
                (Q'.mul_neg_eqv x x)) ?_
            exact Q'.neg_neg_eqv (x * x))
        (by
          by_cases hy : (0 : Q') ≤ y
          · have habsy : Q'.abs y = y := by
              unfold Q'.abs
              rw [if_pos hy]
            rw [habsy]
            exact Q'.eqv_refl _
          · have habsy : Q'.abs y = -y := by
              unfold Q'.abs
              rw [if_neg hy]
            rw [habsy]
            refine Q'.eqv_trans _ _ _
              (Q'.neg_mul_eqv y (-y)) ?_
            refine Q'.eqv_trans _ _ _
              (Q'.neg_eqv_congr _ _
                (Q'.mul_neg_eqv y y)) ?_
            exact Q'.neg_neg_eqv (y * y)))
  have hscaled :
      half *
          (Q'.abs (x * y) + Q'.abs (x * y)) ≤
        half * ((x * x) + (y * y)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdouble half_nonneg
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hscaled
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (half * Q'.abs (x * y) +
        half * Q'.abs (x * y)) _
      (Q'.mul_add_eqv
        half (Q'.abs (x * y)) (Q'.abs (x * y)))
      (two_halves (Q'.abs (x * y))))

/-- Symmetry of both joint laws makes every difference column mass equal to
the corresponding difference row mass. -/
theorem finiteJointDifferenceAbsColumnMass_eqv_rowMass
    {State : Type}
    (states : List State)
    (leftJoint rightJoint : State → State → Q')
    (hsymmLeft :
      ∀ left right, left ∈ states → right ∈ states →
        leftJoint left right ≈ leftJoint right left)
    (hsymmRight :
      ∀ left right, left ∈ states → right ∈ states →
        rightJoint left right ≈ rightJoint right left)
    {state : State} (hstate : state ∈ states) :
    finiteJointDifferenceAbsColumnMass
        states leftJoint rightJoint state ≈
      finiteJointDifferenceAbsRowMass
        states leftJoint rightJoint state := by
  unfold finiteJointDifferenceAbsColumnMass
    finiteJointDifferenceAbsRowMass
  apply listQSum_congr_on
  intro other hother
  apply abs_eqv_congr
  exact Q'.add_eqv_congr'
    (Q'.eqv_symm
      (hsymmLeft state other hstate hother))
    (Q'.neg_eqv_congr _ _
      (Q'.eqv_symm
        (hsymmRight state other hstate hother)))

/-- The literal Young envelope of a symmetric joint-law difference. -/
def finiteJointDifferenceYoungEnvelope {State : Type}
    (states : List State)
    (coefficient : State → Q')
    (leftJoint rightJoint : State → State → Q') : Q' :=
  listQSum
    (fun left =>
      listQSum
        (fun right =>
          Q'.abs
              (leftJoint left right +
                (-rightJoint left right)) *
            (half *
              ((coefficient left * coefficient left) +
                (coefficient right * coefficient right))))
        states)
    states

/-- The Young envelope is exactly half the sum of its row-square and
column-square contributions. -/
theorem finiteJointDifferenceYoungEnvelope_eqv_rows_columns
    {State : Type}
    (states : List State)
    (coefficient : State → Q')
    (leftJoint rightJoint : State → State → Q') :
    finiteJointDifferenceYoungEnvelope
        states coefficient leftJoint rightJoint ≈
      half *
        (listQSum
            (fun state =>
              (coefficient state * coefficient state) *
                finiteJointDifferenceAbsRowMass
                  states leftJoint rightJoint state)
            states +
          listQSum
            (fun state =>
              (coefficient state * coefficient state) *
                finiteJointDifferenceAbsColumnMass
                  states leftJoint rightJoint state)
            states) := by
  let errorAbs : State → State → Q' := fun left right =>
    Q'.abs
      (leftJoint left right +
        (-rightJoint left right))
  let rowTerm : State → Q' := fun left =>
    (coefficient left * coefficient left) *
      listQSum (errorAbs left) states
  let mixedTerm : State → State → Q' := fun left right =>
    (coefficient right * coefficient right) *
      errorAbs left right
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        half *
          (rowTerm left +
            listQSum (mixedTerm left) states))
      states) _ ?_ ?_
  · unfold finiteJointDifferenceYoungEnvelope
      rowTerm mixedTerm errorAbs
    apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          half *
            (((coefficient left * coefficient left) *
                Q'.abs
                  (leftJoint left right +
                    (-rightJoint left right))) +
              ((coefficient right * coefficient right) *
                Q'.abs
                  (leftJoint left right +
                    (-rightJoint left right)))))
        states) _ ?_ ?_
    · apply listQSum_congr
      intro right
      q_ring
    refine Q'.eqv_trans _
      (half *
        listQSum
          (fun right =>
            ((coefficient left * coefficient left) *
                Q'.abs
                  (leftJoint left right +
                    (-rightJoint left right))) +
              ((coefficient right * coefficient right) *
                Q'.abs
                  (leftJoint left right +
                    (-rightJoint left right))))
          states) _
      (listQSum_mul_left half _ states) ?_
    refine Q'.mul_eqv_congr_left half _ _ ?_
    refine Q'.eqv_trans _
      (listQSum
          (fun right =>
            (coefficient left * coefficient left) *
              Q'.abs
                (leftJoint left right +
                  (-rightJoint left right)))
          states +
        listQSum
          (fun right =>
            (coefficient right * coefficient right) *
              Q'.abs
                (leftJoint left right +
                  (-rightJoint left right)))
          states) _ ?_ ?_
    · exact listQSum_add
        (fun right =>
          (coefficient left * coefficient left) *
            Q'.abs
              (leftJoint left right +
                (-rightJoint left right)))
        (fun right =>
          (coefficient right * coefficient right) *
            Q'.abs
              (leftJoint left right +
                (-rightJoint left right)))
        states
    exact Q'.add_eqv_congr'
      (listQSum_mul_left
        (coefficient left * coefficient left)
        (fun right =>
          Q'.abs
            (leftJoint left right +
              (-rightJoint left right)))
        states)
      (Q'.eqv_refl _)
  · refine Q'.eqv_trans _
      (half *
        listQSum
          (fun left =>
            rowTerm left +
              listQSum (mixedTerm left) states)
          states) _
      (listQSum_mul_left half _ states) ?_
    refine Q'.eqv_trans _
      (half *
        (listQSum rowTerm states +
          listQSum
            (fun left =>
              listQSum (mixedTerm left) states)
            states)) _
      (Q'.mul_eqv_congr_left half _ _
        (listQSum_add rowTerm
          (fun left => listQSum (mixedTerm left) states)
          states)) ?_
    refine Q'.mul_eqv_congr_left half _ _ ?_
    apply Q'.add_eqv_congr'
    · exact Q'.eqv_refl _
    · refine Q'.eqv_trans _
        (listQSum
          (fun right =>
            listQSum
              (fun left => mixedTerm left right)
              states)
          states) _
        (Q'.eqv_symm
          (listQSum_swap mixedTerm states states)) ?_
      unfold mixedTerm
      apply listQSum_congr
      intro right
      exact listQSum_mul_left
        (coefficient right * coefficient right)
        (fun left =>
          Q'.abs
            (leftJoint left right +
              (-rightJoint left right)))
        states

/-- A row-relative bound for a symmetric joint-law difference controls the
entire Young envelope in the physical weighted square norm. -/
theorem finiteJointDifferenceYoungEnvelope_le_weightedSquare
    {State : Type}
    (states : List State)
    (coefficient weight : State → Q')
    (leftJoint rightJoint : State → State → Q')
    (epsilon : Q')
    (hsymmLeft :
      ∀ left right, left ∈ states → right ∈ states →
        leftJoint left right ≈ leftJoint right left)
    (hsymmRight :
      ∀ left right, left ∈ states → right ∈ states →
        rightJoint left right ≈ rightJoint right left)
    (hrow :
      ∀ state, state ∈ states →
        finiteJointDifferenceAbsRowMass
            states leftJoint rightJoint state ≤
          epsilon * weight state) :
    finiteJointDifferenceYoungEnvelope
        states coefficient leftJoint rightJoint ≤
      epsilon *
        finiteWeightedSquare states weight coefficient := by
  let weightedBound :=
    epsilon * finiteWeightedSquare states weight coefficient
  have hrowContribution :
      listQSum
          (fun state =>
            (coefficient state * coefficient state) *
              finiteJointDifferenceAbsRowMass
                states leftJoint rightJoint state)
          states ≤
        weightedBound := by
    refine Q'.le_trans' _ _ _
      (listQSum_mono _ _ states
        (fun state hstate =>
          Q'.mul_le_mul_of_nonneg_left _ _ _
            (hrow state hstate)
            (SumOfSquares.q_mul_self_nonneg
              (coefficient state)))) ?_
    unfold weightedBound finiteWeightedSquare
    exact Q'.le_of_eqv
      (Q'.eqv_trans _
        (listQSum
          (fun state =>
            epsilon *
              (weight state *
                (coefficient state * coefficient state)))
          states) _
        (listQSum_congr
          (fun state => by q_ring)
          states)
        (listQSum_mul_left epsilon
          (fun state =>
            weight state *
              (coefficient state * coefficient state))
          states))
  have hcolumnContribution :
      listQSum
          (fun state =>
            (coefficient state * coefficient state) *
              finiteJointDifferenceAbsColumnMass
                states leftJoint rightJoint state)
          states ≤
        weightedBound := by
    refine Q'.le_trans' _ _ _
      (listQSum_mono _ _ states
        (fun state hstate =>
          Q'.mul_le_mul_of_nonneg_left _ _ _
            (Q'.le_trans' _ _ _
              (Q'.le_of_eqv
                (finiteJointDifferenceAbsColumnMass_eqv_rowMass
                  states leftJoint rightJoint
                  hsymmLeft hsymmRight hstate))
              (hrow state hstate))
            (SumOfSquares.q_mul_self_nonneg
              (coefficient state)))) ?_
    unfold weightedBound finiteWeightedSquare
    exact Q'.le_of_eqv
      (Q'.eqv_trans _
        (listQSum
          (fun state =>
            epsilon *
              (weight state *
                (coefficient state * coefficient state)))
          states) _
        (listQSum_congr
          (fun state => by q_ring)
          states)
        (listQSum_mul_left epsilon
          (fun state =>
            weight state *
              (coefficient state * coefficient state))
          states))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finiteJointDifferenceYoungEnvelope_eqv_rows_columns
        states coefficient leftJoint rightJoint)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.add_le_add hrowContribution hcolumnContribution)
      half_nonneg) ?_
  unfold weightedBound
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      (half *
          (epsilon *
              finiteWeightedSquare states weight coefficient) +
        half *
          (epsilon *
              finiteWeightedSquare states weight coefficient)) _
      (Q'.mul_add_eqv _ _ _)
      (two_halves
        (epsilon *
          finiteWeightedSquare states weight coefficient)))

/-- **Weighted joint-law perturbation theorem.**  A symmetric row-relative
error controls the difference of finite joint quadratics in `ell^2(weight)`.
-/
theorem finiteJointQuadratic_abs_sub_le_weightedSquare
    {State : Type}
    (states : List State)
    (coefficient weight : State → Q')
    (leftJoint rightJoint : State → State → Q')
    (epsilon : Q')
    (hsymmLeft :
      ∀ left right, left ∈ states → right ∈ states →
        leftJoint left right ≈ leftJoint right left)
    (hsymmRight :
      ∀ left right, left ∈ states → right ∈ states →
        rightJoint left right ≈ rightJoint right left)
    (hrow :
      ∀ state, state ∈ states →
        finiteJointDifferenceAbsRowMass
            states leftJoint rightJoint state ≤
          epsilon * weight state) :
    Q'.abs
        (finiteJointQuadratic states coefficient leftJoint +
          (-finiteJointQuadratic states coefficient rightJoint)) ≤
      epsilon *
        finiteWeightedSquare states weight coefficient := by
  let leftRow : State → Q' := fun left =>
    listQSum
      (fun right =>
        (coefficient left * coefficient right) *
          leftJoint left right)
      states
  let rightRow : State → Q' := fun left =>
    listQSum
      (fun right =>
        (coefficient left * coefficient right) *
          rightJoint left right)
      states
  have houter :=
    abs_listQSum_sub_le leftRow rightRow states
  have hrows :
      listQSum
          (fun left =>
            Q'.abs (leftRow left + (-rightRow left)))
          states ≤
        finiteJointDifferenceYoungEnvelope
          states coefficient leftJoint rightJoint := by
    apply listQSum_mono
    intro left hleft
    refine Q'.le_trans' _ _ _
      (abs_listQSum_sub_le
        (fun right =>
          (coefficient left * coefficient right) *
            leftJoint left right)
        (fun right =>
          (coefficient left * coefficient right) *
            rightJoint left right)
        states) ?_
    apply listQSum_mono
    intro right hright
    refine Q'.le_trans' _ _ _
      (abs_common_mul_sub_le
        (coefficient left * coefficient right)
        (leftJoint left right)
        (rightJoint left right)
        (Q'.abs
          (leftJoint left right +
            (-rightJoint left right)))
        (Q'.le_refl' _)) ?_
    have hcoefficient :=
      abs_mul_le_half_square_sum
        (coefficient left) (coefficient right)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        hcoefficient
        (Q'.abs_nonneg
          (leftJoint left right +
            (-rightJoint left right)))) ?_
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (half *
          ((coefficient left * coefficient left) +
            (coefficient right * coefficient right)))
        (Q'.abs
          (leftJoint left right +
            (-rightJoint left right))))
  unfold finiteJointQuadratic
  change
    Q'.abs
        (listQSum leftRow states +
          (-listQSum rightRow states)) ≤ _
  exact Q'.le_trans' _ _ _ houter
    (Q'.le_trans' _ _ _ hrows
      (finiteJointDifferenceYoungEnvelope_le_weightedSquare
        states coefficient weight leftJoint rightJoint epsilon
        hsymmLeft hsymmRight hrow))

/-! ## 2. Exact specialization to the physical BF4 Markov carrier -/

/-- Quadratic form of the exact partition-normalized physical BF4 joint law,
restricted to its positive-row carrier. -/
def centralPhysicalJointQuadratic
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (observable : EdgeLabelling → Q') : Q' :=
  finiteJointQuadratic
    (centralPositiveHalfStates w hw K halfExtent)
    observable
    (centralNormalizedPhysicalReflectedKernel
      w hw K halfExtent)

/-- On a retained row, multiplying the conditional physical kernel by its
own marginal recovers the normalized reflected joint entry. -/
theorem centralPhysicalMarginal_mul_conditional_eqv_joint
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source target : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K halfExtent) :
    centralPhysicalRowMarginal
          w hw K halfExtent source *
        centralPhysicalConditionalKernel
          w hw K halfExtent source target ≈
      centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent source target := by
  have hrow :=
    (mem_centralPositiveHalfStates_iff).1 hsource
  rw [centralPhysicalConditionalKernel_eq_divPos hrow.2]
  exact Q'.eqv_trans _
    (Q'.divPos
        (centralNormalizedPhysicalReflectedKernel
          w hw K halfExtent source target)
        (centralPhysicalRowMarginal
          w hw K halfExtent source)
        hrow.2 *
      centralPhysicalRowMarginal
        w hw K halfExtent source) _
    (Q'.mul_comm_eqv
      (centralPhysicalRowMarginal
        w hw K halfExtent source)
      (Q'.divPos
        (centralNormalizedPhysicalReflectedKernel
          w hw K halfExtent source target)
        (centralPhysicalRowMarginal
          w hw K halfExtent source)
        hrow.2))
    (Q'.divPos_mul_eqv
      (centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent source target)
      (centralPhysicalRowMarginal
        w hw K halfExtent source)
      hrow.2)

/-- The weighted Markov quadratic is exactly the quadratic of the symmetric
physical joint law.  This is the generalized-Rayleigh identification which
avoids conjugation by square roots of the marginal. -/
theorem centralPhysicalWeightedMarkovQuadratic_eq_joint
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (observable : EdgeLabelling → Q') :
    centralPhysicalWeightedInner w hw K halfExtent
        observable
        (centralPhysicalMarkovApply
          w hw K halfExtent observable) ≈
      centralPhysicalJointQuadratic
        w hw K halfExtent observable := by
  let states :=
    centralPositiveHalfStates w hw K halfExtent
  unfold centralPhysicalWeightedInner
    centralPhysicalMarkovApply
    centralPhysicalJointQuadratic
    finiteJointQuadratic
  apply listQSum_congr_on
  intro source hsource
  refine Q'.eqv_trans _
    ((centralPhysicalRowMarginal
          w hw K halfExtent source *
        observable source) *
      listQSum
        (fun target =>
          centralPhysicalConditionalKernel
              w hw K halfExtent source target *
            observable target)
        states) _ ?_ ?_
  · q_ring
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        (centralPhysicalRowMarginal
              w hw K halfExtent source *
            observable source) *
          (centralPhysicalConditionalKernel
              w hw K halfExtent source target *
            observable target))
      states) _
    (Q'.eqv_symm
      (listQSum_mul_left
        (centralPhysicalRowMarginal
            w hw K halfExtent source *
          observable source)
        (fun target =>
          centralPhysicalConditionalKernel
              w hw K halfExtent source target *
            observable target)
        states)) ?_
  apply listQSum_congr_on
  intro target htarget
  refine Q'.eqv_trans _
    ((observable source * observable target) *
      (centralPhysicalRowMarginal
          w hw K halfExtent source *
        centralPhysicalConditionalKernel
          w hw K halfExtent source target)) _ ?_ ?_
  · q_ring
  exact Q'.mul_eqv_congr_left
    (observable source * observable target) _ _
    (centralPhysicalMarginal_mul_conditional_eqv_joint
      hsource)

/-- The generic weighted square is definitionally the physical BF4 norm
square when instantiated with the physical row marginal. -/
theorem finiteWeightedSquare_physical_eqv_inner
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (observable : EdgeLabelling → Q') :
    finiteWeightedSquare
        (centralPositiveHalfStates w hw K halfExtent)
        (centralPhysicalRowMarginal w hw K halfExtent)
        observable ≈
      centralPhysicalWeightedInner
        w hw K halfExtent observable observable := by
  exact Q'.eqv_refl _

/-- The physical weighted norm square is nonnegative. -/
theorem centralPhysicalWeightedSquare_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (observable : EdgeLabelling → Q') :
    (0 : Q') ≤
      centralPhysicalWeightedInner
        w hw K halfExtent observable observable := by
  unfold centralPhysicalWeightedInner
  apply listQSum_nonnegative_on
  intro state hstate
  exact Q'.mul_nonneg _ _
    (centralPhysicalRowMarginal_nonnegative
      hw K halfExtent state)
    (SumOfSquares.q_mul_self_nonneg
      (observable state))

/-! ## 3. The exact endpoint-Mehler comparison interface -/

/-- Witness-bearing interface for a distinct marginal-matched endpoint
Mehler joint law on the exact positive-row BF4 carrier.

An inhabitant must provide the joint law itself, its positivity and symmetry,
its exact physical marginal, a mean-zero Rayleigh rate, and the genuinely
Yang--Mills row-relative comparison.  The structure is not inhabited here.
-/
structure CentralPhysicalMehlerComparison
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : Type where
  /-- The distinct endpoint joint law on physical source/target labels. -/
  mehlerJoint : EdgeLabelling → EdgeLabelling → Q'
  /-- The proposed endpoint joint law is nonnegative on the retained carrier. -/
  mehlerJoint_nonnegative :
    ∀ left, left ∈ centralPositiveHalfStates w hw K halfExtent →
      ∀ right, right ∈ centralPositiveHalfStates w hw K halfExtent →
        (0 : Q') ≤ mehlerJoint left right
  /-- Endpoint reversibility at the joint-law level. -/
  mehlerJoint_symmetric :
    ∀ left right,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      right ∈ centralPositiveHalfStates w hw K halfExtent →
        mehlerJoint left right ≈ mehlerJoint right left
  /-- Exact marginal matching with the nonlinear physical Choi law. -/
  mehlerJoint_rowMarginal :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K halfExtent →
        listQSum
            (mehlerJoint source)
            (centralPositiveHalfStates w hw K halfExtent) ≈
          centralPhysicalRowMarginal
            w hw K halfExtent source
  /-- Located rational upper bound for the endpoint mean-zero quadratic. -/
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  /-- Quantitative physical-versus-endpoint error. -/
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  /-- The row-relative estimate required by the nonuniform physical marginal. -/
  row_relative_error :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K halfExtent →
        finiteJointDifferenceAbsRowMass
            (centralPositiveHalfStates w hw K halfExtent)
            (centralNormalizedPhysicalReflectedKernel
              w hw K halfExtent)
            mehlerJoint
            source ≤
          epsilon *
            centralPhysicalRowMarginal
              w hw K halfExtent source
  /-- Endpoint contraction on the exact physical mean-zero carrier. -/
  mehler_meanZero_quadratic :
    ∀ observable,
      CentralPhysicalMeanZero
          w hw K halfExtent observable →
        Q'.abs
            (finiteJointQuadratic
              (centralPositiveHalfStates w hw K halfExtent)
              observable mehlerJoint) ≤
          rate *
            centralPhysicalWeightedInner
              w hw K halfExtent observable observable

namespace CentralPhysicalMehlerComparison

/-- The physical joint quadratic is close to the endpoint quadratic in the
exact physical weighted norm. -/
theorem physical_joint_close
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (comparison :
      CentralPhysicalMehlerComparison
        w hw K halfExtent)
    (observable : EdgeLabelling → Q') :
    Q'.abs
        (centralPhysicalJointQuadratic
            w hw K halfExtent observable +
          (-finiteJointQuadratic
            (centralPositiveHalfStates w hw K halfExtent)
            observable comparison.mehlerJoint)) ≤
      comparison.epsilon *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  refine Q'.le_trans' _ _ _
    (finiteJointQuadratic_abs_sub_le_weightedSquare
      (centralPositiveHalfStates w hw K halfExtent)
      observable
      (centralPhysicalRowMarginal w hw K halfExtent)
      (centralNormalizedPhysicalReflectedKernel
        w hw K halfExtent)
      comparison.mehlerJoint
      comparison.epsilon
      (fun left right hleft hright =>
        centralNormalizedPhysicalReflectedKernel_symm
          ((mem_centralPositiveHalfStates_iff).1 hleft).1
          ((mem_centralPositiveHalfStates_iff).1 hright).1)
      comparison.mehlerJoint_symmetric
      comparison.row_relative_error) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.le_of_eqv
      (finiteWeightedSquare_physical_eqv_inner
        w hw K halfExtent observable))
    comparison.epsilon_nonnegative

/-- The endpoint comparison transfers its Rayleigh bound to the exact
physical BF4 Markov quadratic, with additive loss `rate + epsilon`. -/
theorem physical_markov_quadratic_abs_le
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (comparison :
      CentralPhysicalMehlerComparison
        w hw K halfExtent)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    Q'.abs
        (centralPhysicalWeightedInner w hw K halfExtent
          observable
          (centralPhysicalMarkovApply
            w hw K halfExtent observable)) ≤
      (comparison.rate + comparison.epsilon) *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  let physicalQuadratic :=
    centralPhysicalJointQuadratic
      w hw K halfExtent observable
  let mehlerQuadratic :=
    finiteJointQuadratic
      (centralPositiveHalfStates w hw K halfExtent)
      observable comparison.mehlerJoint
  have hphysical :
      centralPhysicalWeightedInner w hw K halfExtent
          observable
          (centralPhysicalMarkovApply
            w hw K halfExtent observable) ≈
        physicalQuadratic :=
    centralPhysicalWeightedMarkovQuadratic_eq_joint
      w hw K halfExtent observable
  have hsplit :
      physicalQuadratic ≈
        (physicalQuadratic + (-mehlerQuadratic)) +
          mehlerQuadratic := by
    exact Q'.eqv_symm
      (Q'.eqv_trans _
        (physicalQuadratic +
          ((-mehlerQuadratic) + mehlerQuadratic)) _
        (Q'.add_assoc_eqv
          physicalQuadratic (-mehlerQuadratic) mehlerQuadratic)
        (Q'.eqv_trans _
          (physicalQuadratic + 0) _
          (Q'.add_eqv_congr_left physicalQuadratic _ _
            (Q'.neg_add_self_eqv mehlerQuadratic))
          (Q'.eqv_of_eq
            (Q'.add_zero' physicalQuadratic))))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (abs_eqv_congr hphysical)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (abs_eqv_congr hsplit)) ?_
  refine Q'.le_trans' _ _ _
    (abs_add_le
      (physicalQuadratic + (-mehlerQuadratic))
      mehlerQuadratic) ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add
      (physical_joint_close comparison observable)
      (comparison.mehler_meanZero_quadratic
        observable hmean)) ?_
  exact Q'.le_of_eqv (by q_ring)

/-- Quarter-bound consumer.  Once the endpoint rate plus the physical
row-relative error is at most `1/4`, the exact physical mean-zero Markov
quadratic has the required quarter contraction. -/
theorem physical_markov_quadratic_abs_le_quarter
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (comparison :
      CentralPhysicalMehlerComparison
        w hw K halfExtent)
    (hquarter :
      comparison.rate + comparison.epsilon ≤
        Q'.mkPos 1 4 (by decide))
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        w hw K halfExtent observable) :
    Q'.abs
        (centralPhysicalWeightedInner w hw K halfExtent
          observable
          (centralPhysicalMarkovApply
            w hw K halfExtent observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          w hw K halfExtent observable observable := by
  exact Q'.le_trans' _ _ _
    (physical_markov_quadratic_abs_le
      comparison observable hmean)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      hquarter
      (centralPhysicalWeightedSquare_nonnegative
        w hw K halfExtent observable))

end CentralPhysicalMehlerComparison

end YMGap.Continuum.BF4WeightedJointPerronPerturbation

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.abs_listQSum_le_sum_abs
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.listQSum_le_length_mul
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.finiteJointDifferenceAbsRowMass_le_of_entrywise_budget
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.abs_mul_le_half_square_sum
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.finiteJointDifferenceAbsColumnMass_eqv_rowMass
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.finiteJointDifferenceYoungEnvelope_eqv_rows_columns
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.finiteJointDifferenceYoungEnvelope_le_weightedSquare
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.finiteJointQuadratic_abs_sub_le_weightedSquare
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.centralPhysicalMarginal_mul_conditional_eqv_joint
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.centralPhysicalWeightedMarkovQuadratic_eq_joint
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.centralPhysicalWeightedSquare_nonnegative
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.CentralPhysicalMehlerComparison.physical_joint_close
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.CentralPhysicalMehlerComparison.physical_markov_quadratic_abs_le
#print axioms YMGap.Continuum.BF4WeightedJointPerronPerturbation.CentralPhysicalMehlerComparison.physical_markov_quadratic_abs_le_quarter
