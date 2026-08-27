/-
# Conditional variance is exactly the finite BF4 form-gap margin

For the physical finite BF4 vacuum sector, the previous law of total
variance identifies

    diagonal - transfer = (1/2) * conditionalPairwiseVariance.

This file performs the remaining exact order algebra.  For every rational
margin `epsilon`, the relative form estimate at rate `1 - epsilon` is
equivalent to the lower conditional-variance estimate with margin `epsilon`.
Thus a positive, at-most-one conditional-variance fraction returns the
strict rate and the complete finite mean-zero form bound as explicit data.

No conditional-variance fraction is constructed here.  In particular, no
cutoff-, volume-, coupling-, beta-, or lattice-spacing-uniform estimate is
asserted.  The new data structure is the precise nonvacuous analytic input
that such an estimate must inhabit.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance

namespace YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVariance

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

/-- Cancellation-free rational-semantic polynomial normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-- Move one summand to the other side of a rational inequality. -/
private theorem le_sub_of_add_le_local {left moved upper : Q'}
    (h : left + moved ≤ upper) :
    left ≤ upper + (-moved) := by
  have hshift :
      (left + moved) + (-moved) ≤ upper + (-moved) :=
    Q'.add_le_add_right (left + moved) upper (-moved) h
  have hcollapse : (left + moved) + (-moved) ≈ left := by
    refine Q'.eqv_trans _ (left + (moved + (-moved))) _
      (Q'.add_assoc_eqv left moved (-moved)) ?_
    refine Q'.eqv_trans _ (left + 0) _
      (Q'.add_eqv_congr_left left _ _ (Q'.add_neg_self_eqv moved)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' left)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse) hshift

private theorem one_sub_mul_eqv_sub_mul
    (margin diagonal : Q') :
    ((1 : Q') + (-margin)) * diagonal ≈
      diagonal + (-(margin * diagonal)) := by
  q_ring

/-! ## 1. Exact pointwise equivalence -/

/-- **Exact finite conditional-variance/form-gap equivalence.**  A margin
`epsilon` in the conditional pairwise variance is neither weaker nor stronger
than the same-object form rate `1 - epsilon`; the two statements differ only
by the already-proved law of total variance.  Centering is not needed for this
algebraic equivalence. -/
theorem centralPhysicalFiniteVacuumSector_formBound_iff_halfConditionalVarianceMargin
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') (epsilon : Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient ≤
        ((1 : Q') + (-epsilon)) *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient ↔
      epsilon *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient ≤
        Q'.mkPos 1 2 (by decide) *
          centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
            w hw cutoff half coefficient := by
  let diagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w hw cutoff half coefficient
  let matrix := centralPhysicalFiniteVacuumSectorMatrixQuadratic
    w hw cutoff half coefficient
  let conditional :=
    centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
      w hw cutoff half coefficient
  have hdeficit :
      diagonal + (-matrix) ≈ Q'.mkPos 1 2 (by decide) * conditional := by
    exact
      centralPhysicalFiniteVacuumSector_deficit_eqv_half_conditionalPairwiseVariance
        w hw cutoff half coefficient
  have hrate :
      ((1 : Q') + (-epsilon)) * diagonal ≈
        diagonal + (-(epsilon * diagonal)) :=
    one_sub_mul_eqv_sub_mul epsilon diagonal
  constructor
  · intro hform
    have hmatrixSub : matrix ≤ diagonal + (-(epsilon * diagonal)) :=
      Q'.le_trans' _ _ _ hform (Q'.le_of_eqv hrate)
    have hadd :
        matrix + epsilon * diagonal ≤
          (diagonal + (-(epsilon * diagonal))) +
            epsilon * diagonal :=
      Q'.add_le_add_right matrix
        (diagonal + (-(epsilon * diagonal)))
        (epsilon * diagonal) hmatrixSub
    have hright :
        (diagonal + (-(epsilon * diagonal))) +
            epsilon * diagonal ≈ diagonal := by
      refine Q'.eqv_trans _
        (diagonal + ((-(epsilon * diagonal)) + epsilon * diagonal)) _
        (Q'.add_assoc_eqv diagonal (-(epsilon * diagonal))
          (epsilon * diagonal)) ?_
      refine Q'.eqv_trans _ (diagonal + 0) _
        (Q'.add_eqv_congr_left diagonal _ _
          (Q'.neg_add_self_eqv (epsilon * diagonal))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' diagonal)
    have hsum : matrix + epsilon * diagonal ≤ diagonal :=
      Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright)
    have hreordered : epsilon * diagonal + matrix ≤ diagonal :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.add_comm_eqv (epsilon * diagonal) matrix)) hsum
    have hmargin :
        epsilon * diagonal ≤ diagonal + (-matrix) :=
      le_sub_of_add_le_local hreordered
    exact Q'.le_trans' _ _ _ hmargin (Q'.le_of_eqv hdeficit)
  · intro hmargin
    have hmarginSub :
        epsilon * diagonal ≤ diagonal + (-matrix) :=
      Q'.le_trans' _ _ _ hmargin
        (Q'.le_of_eqv (Q'.eqv_symm hdeficit))
    have hadd :
        epsilon * diagonal + matrix ≤
          (diagonal + (-matrix)) + matrix :=
      Q'.add_le_add_right (epsilon * diagonal)
        (diagonal + (-matrix)) matrix hmarginSub
    have hright : (diagonal + (-matrix)) + matrix ≈ diagonal := by
      refine Q'.eqv_trans _ (diagonal + ((-matrix) + matrix)) _
        (Q'.add_assoc_eqv diagonal (-matrix) matrix) ?_
      refine Q'.eqv_trans _ (diagonal + 0) _
        (Q'.add_eqv_congr_left diagonal _ _
          (Q'.neg_add_self_eqv matrix)) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' diagonal)
    have hsum : epsilon * diagonal + matrix ≤ diagonal :=
      Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright)
    have hreordered : matrix + epsilon * diagonal ≤ diagonal :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.add_comm_eqv matrix (epsilon * diagonal))) hsum
    have hmatrixSub : matrix ≤ diagonal + (-(epsilon * diagonal)) :=
      le_sub_of_add_le_local hreordered
    exact Q'.le_trans' _ _ _ hmatrixSub
      (Q'.le_of_eqv (Q'.eqv_symm hrate))

/-! ## 2. The exact named finite analytic input -/

/-- A fixed finite BF4 sector has a positive conditional-variance fraction.
The rational fraction is data; its complete mean-zero lower estimate is the
nontrivial analytic field.  No uniformity beyond the explicit parameters is
encoded in this structure. -/
structure CentralPhysicalFiniteConditionalVarianceGapData
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  conditionalVarianceMargin : ∀ coefficient : Nat → Q',
    centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0 →
      fraction *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient ≤
        Q'.mkPos 1 2 (by decide) *
          centralPhysicalFiniteVacuumSectorConditionalPairwiseVariance
            w hw cutoff half coefficient

/-- The explicit strict form rate returned by conditional-variance data. -/
def CentralPhysicalFiniteConditionalVarianceGapData.rate
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalVarianceGapData
      w hw cutoff half) : Q' :=
  (1 : Q') + (-data.fraction)

theorem CentralPhysicalFiniteConditionalVarianceGapData.rate_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalVarianceGapData
      w hw cutoff half) :
    (0 : Q') ≤ data.rate := by
  exact Q'.sub_nonneg_of_le data.fraction_le_one

theorem CentralPhysicalFiniteConditionalVarianceGapData.rate_lt_one
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalVarianceGapData
      w hw cutoff half) :
    data.rate < (1 : Q') := by
  unfold rate
  show ((1 : Q') + -data.fraction).num * ((1 : Q').den : Int) <
    (1 : Q').num * (((1 : Q') + -data.fraction).den : Int)
  have hnum : (0 : Int) < data.fraction.num :=
    Q'.num_pos_of_pos data.fraction_pos
  change
    (((1 : Int) * (data.fraction.den : Int) +
        (-data.fraction.num) * (1 : Int)) * (1 : Int)) <
      ((1 : Int) *
        (((1 : Nat) * data.fraction.den : Nat) : Int))
  push_cast
  omega

/-- Conditional-variance data proves the relative form inequality for every
finite mean-zero coefficient vector. -/
theorem CentralPhysicalFiniteConditionalVarianceGapData.formBound
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalVarianceGapData
      w hw cutoff half)
    (coefficient : Nat → Q')
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient ≤
        data.rate *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient := by
  exact
    (centralPhysicalFiniteVacuumSector_formBound_iff_halfConditionalVarianceMargin
      w hw cutoff half coefficient data.fraction).mpr
      (data.conditionalVarianceMargin coefficient hcenter)

/-- Return the strict rational rate and the complete finite mean-zero form
bound as explicit sigma data. -/
def CentralPhysicalFiniteConditionalVarianceGapData.toStrictFormGap
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (data : CentralPhysicalFiniteConditionalVarianceGapData
      w hw cutoff half) :
    Σ' rate : Q',
      (0 : Q') ≤ rate ∧ rate < (1 : Q') ∧
        ∀ coefficient : Nat → Q',
          centralPhysicalFiniteVacuumSectorWeightedMean
              w hw cutoff half coefficient ≈ 0 →
            centralPhysicalFiniteVacuumSectorMatrixQuadratic
                w hw cutoff half coefficient ≤
              rate *
                centralPhysicalFiniteVacuumSectorDiagonalQuadratic
                  w hw cutoff half coefficient :=
  ⟨data.rate, data.rate_nonnegative, data.rate_lt_one,
    data.formBound⟩

end YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge.centralPhysicalFiniteVacuumSector_formBound_iff_halfConditionalVarianceMargin
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge.CentralPhysicalFiniteConditionalVarianceGapData.rate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge.CentralPhysicalFiniteConditionalVarianceGapData.rate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge.CentralPhysicalFiniteConditionalVarianceGapData.formBound
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorConditionalVarianceGapBridge.CentralPhysicalFiniteConditionalVarianceGapData.toStrictFormGap
