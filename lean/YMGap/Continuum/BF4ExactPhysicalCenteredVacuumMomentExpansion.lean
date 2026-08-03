/-
# Exact moment expansion of the centered BF4 vacuum probe

This file expands the exact signed-Haar quadratic of the physically centered
vacuum code delta into four literal moments: the known vacuum diagonal, two
delta--constant cross moments, and the constant quadratic moment.  Kernel
symmetry will eventually identify the two cross moments, but keeping both in
the first expansion makes every use of finite bilinearity explicit.

The vacuum diagonal is already one.  The other moments are named rather than
assumed; evaluating them at cutoff one is the next analytic calculation.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe

namespace YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumProbe
open YMGap.Continuum.BF4ExactPhysicalPerronCenteredReroute
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic finite bilinear algebra -/

/-- Bilinear version of `finiteJointQuadratic`. -/
def finiteJointBilinear {State : Type}
    (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q') : Q' :=
  listQSum
    (fun left =>
      listQSum
        (fun right =>
          (leftCoefficient left * rightCoefficient right) *
            joint left right)
        states)
    states

theorem finiteJointQuadratic_eq_bilinear {State : Type}
    (states : List State) (coefficient : State → Q')
    (joint : State → State → Q') :
    finiteJointQuadratic states coefficient joint =
      finiteJointBilinear states coefficient coefficient joint := by
  rfl

theorem finiteJointBilinear_add_left {State : Type}
    (states : List State)
    (left₁ left₂ right : State → Q')
    (joint : State → State → Q') :
    finiteJointBilinear states
        (fun state => left₁ state + left₂ state) right joint ≈
      finiteJointBilinear states left₁ right joint +
        finiteJointBilinear states left₂ right joint := by
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
            (fun rightState =>
              (left₁ left * right rightState) * joint left rightState)
            states +
          listQSum
            (fun rightState =>
              (left₂ left * right rightState) * joint left rightState)
            states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _
    refine Q'.eqv_trans _
      (listQSum
        (fun rightState =>
          (left₁ left * right rightState) * joint left rightState +
            (left₂ left * right rightState) * joint left rightState)
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro rightState _
      ac_qeqv
    · exact listQSum_add _ _ states
  exact listQSum_add _ _ states

theorem finiteJointBilinear_add_right {State : Type}
    (states : List State)
    (left right₁ right₂ : State → Q')
    (joint : State → State → Q') :
    finiteJointBilinear states left
        (fun state => right₁ state + right₂ state) joint ≈
      finiteJointBilinear states left right₁ joint +
        finiteJointBilinear states left right₂ joint := by
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun leftState =>
        listQSum
            (fun right =>
              (left leftState * right₁ right) * joint leftState right)
            states +
          listQSum
            (fun right =>
              (left leftState * right₂ right) * joint leftState right)
            states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro leftState _
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          (left leftState * right₁ right) * joint leftState right +
            (left leftState * right₂ right) * joint leftState right)
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro right _
      ac_qeqv
    · exact listQSum_add _ _ states
  exact listQSum_add _ _ states

theorem finiteJointBilinear_constant_left {State : Type}
    (states : List State) (constant : Q')
    (right : State → Q') (joint : State → State → Q') :
    finiteJointBilinear states (fun _ => constant) right joint ≈
      constant *
        finiteJointBilinear states (fun _ => 1) right joint := by
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        constant *
          listQSum
            (fun rightState =>
              ((1 : Q') * right rightState) * joint left rightState)
            states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _
    refine Q'.eqv_trans _
      (listQSum
        (fun rightState =>
          constant *
            (((1 : Q') * right rightState) * joint left rightState))
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro rightState _
      ac_qeqv
    · exact listQSum_mul_left constant _ states
  exact listQSum_mul_left constant _ states

theorem finiteJointBilinear_constant_right {State : Type}
    (states : List State) (constant : Q')
    (left : State → Q') (joint : State → State → Q') :
    finiteJointBilinear states left (fun _ => constant) joint ≈
      constant *
        finiteJointBilinear states left (fun _ => 1) joint := by
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun leftState =>
        constant *
          listQSum
            (fun right =>
              (left leftState * (1 : Q')) * joint leftState right)
            states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro leftState _
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          constant *
            ((left leftState * (1 : Q')) * joint leftState right))
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro right _
      ac_qeqv
    · exact listQSum_mul_left constant _ states
  exact listQSum_mul_left constant _ states

/-- Exact four-moment expansion of an affine perturbation. -/
theorem finiteJointBilinear_affine_self {State : Type}
    (states : List State) (observable : State → Q')
    (constant : Q') (joint : State → State → Q') :
    finiteJointBilinear states
        (fun state => observable state + constant)
        (fun state => observable state + constant) joint ≈
      finiteJointBilinear states observable observable joint +
        (constant *
          finiteJointBilinear states observable (fun _ => 1) joint +
        (constant *
          finiteJointBilinear states (fun _ => 1) observable joint +
        (constant * constant) *
          finiteJointBilinear states (fun _ => 1) (fun _ => 1) joint)) := by
  refine Q'.eqv_trans _
    (finiteJointBilinear states observable
        (fun state => observable state + constant) joint +
      finiteJointBilinear states (fun _ => constant)
        (fun state => observable state + constant) joint) _
    (finiteJointBilinear_add_left states observable
      (fun _ => constant) (fun state => observable state + constant) joint) ?_
  refine Q'.eqv_trans _
    ((finiteJointBilinear states observable observable joint +
        finiteJointBilinear states observable (fun _ => constant) joint) +
      (finiteJointBilinear states (fun _ => constant) observable joint +
        finiteJointBilinear states (fun _ => constant)
          (fun _ => constant) joint)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (finiteJointBilinear_add_right states observable observable
        (fun _ => constant) joint)
      (finiteJointBilinear_add_right states (fun _ => constant) observable
        (fun _ => constant) joint)
  refine Q'.eqv_trans _
    ((finiteJointBilinear states observable observable joint +
        constant *
          finiteJointBilinear states observable (fun _ => 1) joint) +
      (constant *
          finiteJointBilinear states (fun _ => 1) observable joint +
        (constant * constant) *
          finiteJointBilinear states (fun _ => 1) (fun _ => 1) joint)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (finiteJointBilinear_constant_right
          states constant observable joint))
      (Q'.add_eqv_congr'
        (finiteJointBilinear_constant_left
          states constant observable joint)
        (Q'.eqv_trans _
          (constant *
            finiteJointBilinear states (fun _ => 1)
              (fun _ => constant) joint) _
          (finiteJointBilinear_constant_left
            states constant (fun _ => constant) joint)
          (Q'.eqv_trans _
          (constant *
            (constant *
              finiteJointBilinear states (fun _ => 1) (fun _ => 1) joint)) _
          (Q'.mul_eqv_congr_left constant _ _
            (finiteJointBilinear_constant_right
              states constant (fun _ => 1) joint))
          (Q'.eqv_symm
            (Q'.mul_assoc_eqv constant constant
              (finiteJointBilinear states
                (fun _ => 1) (fun _ => 1) joint))))))
  exact Q'.add_assoc_eqv _ _ _

/-- A symmetric joint swaps the two slots of the finite bilinear form. -/
theorem finiteJointBilinear_swap_of_symmetric {State : Type}
    (states : List State)
    (leftCoefficient rightCoefficient : State → Q')
    (joint : State → State → Q')
    (symmetric :
      ∀ left right,
        left ∈ states → right ∈ states →
          joint left right ≈ joint right left) :
    finiteJointBilinear states leftCoefficient rightCoefficient joint ≈
      finiteJointBilinear states rightCoefficient leftCoefficient joint := by
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun right =>
        listQSum
          (fun left =>
            (leftCoefficient left * rightCoefficient right) *
              joint left right)
          states)
      states) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun left right =>
          (leftCoefficient left * rightCoefficient right) *
            joint left right)
        states states)
  · apply listQSum_congr_on
    intro right hright
    apply listQSum_congr_on
    intro left hleft
    exact Q'.eqv_trans _
      ((rightCoefficient right * leftCoefficient left) *
        joint left right) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv
          (leftCoefficient left) (rightCoefficient right)))
      (Q'.mul_eqv_congr_left _ _ _
        (symmetric left right hleft hright))

/-- A vacuum delta in the left slot collapses a bilinear form to the vacuum
row sum. -/
theorem finiteJointBilinear_vacuumCodeDelta_one
    (K : Nat) (joint : EdgeLabelling → EdgeLabelling → Q') :
    finiteJointBilinear
        (centralHalfStates K 0)
        (vacuumCodeDelta K) (fun _ => 1) joint ≈
      listQSum
        (joint zeroEdgeLabelling)
        (centralHalfStates K 0) := by
  let states := centralHalfStates K 0
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        vacuumCodeDelta K left *
          listQSum (joint left) states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          vacuumCodeDelta K left * joint left right)
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro right _
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_one_eqv (vacuumCodeDelta K left))
    · exact listQSum_mul_left
        (vacuumCodeDelta K left) (joint left) states
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum (joint left) states * vacuumCodeDelta K left)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _
    exact Q'.mul_comm_eqv _ _
  exact listQSum_value_mul_vacuumCodeDelta
    K (fun left => listQSum (joint left) states)

/-- Positive-carrier version of the vacuum-row collapse. -/
theorem finiteJointBilinear_vacuumCodeDelta_one_positive
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (joint : EdgeLabelling → EdgeLabelling → Q') :
    finiteJointBilinear
        (centralPositiveHalfStates w hw K 0)
        (vacuumCodeDelta K) (fun _ => 1) joint ≈
      listQSum
        (joint zeroEdgeLabelling)
        (centralPositiveHalfStates w hw K 0) := by
  let states := centralPositiveHalfStates w hw K 0
  unfold finiteJointBilinear
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        vacuumCodeDelta K left *
          listQSum (joint left) states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          vacuumCodeDelta K left * joint left right)
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro right _
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_one_eqv (vacuumCodeDelta K left))
    · exact listQSum_mul_left
        (vacuumCodeDelta K left) (joint left) states
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum (joint left) states * vacuumCodeDelta K left)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _
    exact Q'.mul_comm_eqv _ _
  exact listQSum_value_mul_vacuumCodeDelta_positive
    hw K (fun left => listQSum (joint left) states)

/-! ## 2. Exact signed-Haar moments and centered expansion -/

def exactVacuumRightConstantCrossMoment
    (w : Q') (K : Nat) : Q' :=
  finiteJointBilinear
    (centralHalfStates K 0)
    (vacuumCodeDelta K) (fun _ => 1)
    (exactCorrectedSlabReflectedKernel w K 0)

def exactVacuumLeftConstantCrossMoment
    (w : Q') (K : Nat) : Q' :=
  finiteJointBilinear
    (centralHalfStates K 0)
    (fun _ => 1) (vacuumCodeDelta K)
    (exactCorrectedSlabReflectedKernel w K 0)

def exactConstantQuadraticMoment
    (w : Q') (K : Nat) : Q' :=
  finiteJointBilinear
    (centralHalfStates K 0)
    (fun _ => 1) (fun _ => 1)
    (exactCorrectedSlabReflectedKernel w K 0)

/-- Literal symmetry identifies the two delta--constant cross moments. -/
theorem exactVacuumLeftConstantCrossMoment_eq_right
    (w : Q') (K : Nat) :
    exactVacuumLeftConstantCrossMoment w K ≈
      exactVacuumRightConstantCrossMoment w K := by
  unfold exactVacuumLeftConstantCrossMoment
    exactVacuumRightConstantCrossMoment
  exact finiteJointBilinear_swap_of_symmetric
    (centralHalfStates K 0)
    (fun _ => 1) (vacuumCodeDelta K)
    (exactCorrectedSlabReflectedKernel w K 0)
    (fun left right _ _ =>
      exactCorrectedSlabReflectedKernel_symmetric
        w K left right)

/-- The remaining exact cross moment is literally the complete vacuum row
sum of the signed Haar kernel. -/
theorem exactVacuumRightConstantCrossMoment_eq_vacuumRowSum
    (w : Q') (K : Nat) :
    exactVacuumRightConstantCrossMoment w K ≈
      listQSum
        (exactCorrectedSlabReflectedKernel
          w K 0 zeroEdgeLabelling)
        (centralHalfStates K 0) := by
  unfold exactVacuumRightConstantCrossMoment
  exact finiteJointBilinear_vacuumCodeDelta_one
    K (exactCorrectedSlabReflectedKernel w K 0)

/-- The exact centered-vacuum quadratic is completely reduced to the known
unit vacuum diagonal and three named uncomputed moments. -/
theorem exactSlabAllCutoffQuadratic_centeredVacuum_moment_expansion
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    exactSlabAllCutoffQuadratic
        w K (centeredVacuumCodeDelta w hw K) ≈
      1 +
        ((-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) *
            exactVacuumRightConstantCrossMoment w K +
        ((-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) *
            exactVacuumLeftConstantCrossMoment w K +
        ((-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) *
          (-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling)) *
            exactConstantQuadraticMoment w K)) := by
  let states := centralHalfStates K 0
  let joint := exactCorrectedSlabReflectedKernel w K 0
  let vacuumMass :=
    centralPhysicalRowMarginal w hw K 0 zeroEdgeLabelling
  change finiteJointBilinear states
      (fun state => vacuumCodeDelta K state + (-vacuumMass))
      (fun state => vacuumCodeDelta K state + (-vacuumMass)) joint ≈ _
  refine Q'.eqv_trans _
    (finiteJointBilinear states (vacuumCodeDelta K) (vacuumCodeDelta K) joint +
      ((-vacuumMass) *
          finiteJointBilinear states (vacuumCodeDelta K) (fun _ => 1) joint +
      ((-vacuumMass) *
          finiteJointBilinear states (fun _ => 1) (vacuumCodeDelta K) joint +
      ((-vacuumMass) * (-vacuumMass)) *
          finiteJointBilinear states (fun _ => 1) (fun _ => 1) joint))) _
    (finiteJointBilinear_affine_self
      states (vacuumCodeDelta K) (-vacuumMass) joint) ?_
  exact Q'.add_eqv_congr'
    (exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one w K)
    (Q'.eqv_refl _)

/-- Symmetry-reduced expansion with one repeated cross moment. -/
theorem exactSlabAllCutoffQuadratic_centeredVacuum_symmetric_expansion
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    exactSlabAllCutoffQuadratic
        w K (centeredVacuumCodeDelta w hw K) ≈
      1 +
        ((-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) *
            exactVacuumRightConstantCrossMoment w K +
        ((-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) *
            exactVacuumRightConstantCrossMoment w K +
        ((-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) *
          (-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling)) *
            exactConstantQuadraticMoment w K)) := by
  refine Q'.eqv_trans _ _ _
    (exactSlabAllCutoffQuadratic_centeredVacuum_moment_expansion
      w hw K) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl 1)
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left
          (-centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling) _ _
          (exactVacuumLeftConstantCrossMoment_eq_right w K))
        (Q'.eqv_refl _)))

/-! ## 3. Closed physical side of the centered probe -/

/-- The physical delta--constant cross moment is exactly the stationary
vacuum mass. -/
theorem physicalVacuumDeltaConstantCross_eq_marginal
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    finiteJointBilinear
        (centralPositiveHalfStates w hw K 0)
        (vacuumCodeDelta K) (fun _ => 1)
        (centralNormalizedPhysicalReflectedKernel w hw K 0) ≈
      centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling := by
  refine Q'.eqv_trans _
    (listQSum
      (centralNormalizedPhysicalReflectedKernel
        w hw K 0 zeroEdgeLabelling)
      (centralPositiveHalfStates w hw K 0)) _
    (finiteJointBilinear_vacuumCodeDelta_one_positive
      w hw K (centralNormalizedPhysicalReflectedKernel w hw K 0)) ?_
  let marginal :=
    centralPhysicalRowMarginal w hw K 0 zeroEdgeLabelling
  let conditional :=
    centralPhysicalConditionalKernel
      w hw K 0 zeroEdgeLabelling
  have hvacuum :=
    zeroEdgeLabelling_mem_centralPositiveHalfStates hw K 0
  refine Q'.eqv_trans _
    (listQSum
      (fun target => marginal * conditional target)
      (centralPositiveHalfStates w hw K 0)) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    exact Q'.eqv_symm
      (marginal_mul_conditional_eqv_joint
        hvacuum)
  refine Q'.eqv_trans _
    (marginal *
      listQSum conditional
        (centralPositiveHalfStates w hw K 0)) _
    (listQSum_mul_left marginal conditional
      (centralPositiveHalfStates w hw K 0)) ?_
  exact Q'.eqv_trans _ (marginal * 1) _
    (Q'.mul_eqv_congr_left marginal _ _
      (centralPhysicalConditionalKernel_row_normalized hvacuum))
    (Q'.mul_one_eqv marginal)

private theorem centeredPhysicalMoment_scalar
    (diagonal vacuumMass : Q') :
    diagonal +
        ((-vacuumMass) * vacuumMass +
        ((-vacuumMass) * vacuumMass +
        ((-vacuumMass) * (-vacuumMass)) * 1)) ≈
      diagonal + (-(vacuumMass * vacuumMass)) := by
  let square := vacuumMass * vacuumMass
  have hnegative :
      (-vacuumMass) * vacuumMass ≈ -square := by
    exact Q'.neg_mul_eqv vacuumMass vacuumMass
  have hpositive :
      (-vacuumMass) * (-vacuumMass) ≈ square := by
    refine Q'.eqv_trans _ (-(vacuumMass * (-vacuumMass))) _
      (Q'.neg_mul_eqv vacuumMass (-vacuumMass)) ?_
    refine Q'.eqv_trans _ (-(-square)) _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_neg_eqv vacuumMass vacuumMass))
      (Q'.neg_neg_eqv square)
  refine Q'.eqv_trans _
    (diagonal + ((-square) + ((-square) + square))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_refl diagonal)
      (Q'.add_eqv_congr' hnegative
        (Q'.add_eqv_congr' hnegative
          (Q'.eqv_trans _ (square * 1) _
            (Q'.mul_eqv_congr_right _ _ _ hpositive)
            (Q'.mul_one_eqv square))))
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl diagonal)
    (Q'.eqv_trans _ ((-square) + 0) _
      (Q'.add_eqv_congr'
        (Q'.eqv_refl (-square))
        (Q'.neg_add_self_eqv square))
      (Q'.eqv_of_eq (Q'.add_zero' (-square))))

/-- The positive physical quadratic of the centered vacuum probe is its
vacuum diagonal minus the square of the vacuum marginal. -/
theorem centralNormalizedFull_centeredVacuum_eq_diagonal_sub_square
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralNormalizedFullPhysicalReflectionQuadratic
        w hw K 0 (centeredVacuumCodeDelta w hw K) ≈
      centralNormalizedPhysicalReflectedKernel
          w hw K 0 zeroEdgeLabelling zeroEdgeLabelling +
        (-(centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling *
          centralPhysicalRowMarginal
            w hw K 0 zeroEdgeLabelling)) := by
  let positiveStates := centralPositiveHalfStates w hw K 0
  let joint := centralNormalizedPhysicalReflectedKernel w hw K 0
  let vacuumMass :=
    centralPhysicalRowMarginal w hw K 0 zeroEdgeLabelling
  refine Q'.eqv_trans _
    (finiteJointBilinear positiveStates
      (centeredVacuumCodeDelta w hw K)
      (centeredVacuumCodeDelta w hw K) joint) _ ?_ ?_
  · exact Q'.eqv_symm
      (centralPhysicalJointQuadratic_eq_normalizedFull
        w hw K 0 (centeredVacuumCodeDelta w hw K))
  change finiteJointBilinear positiveStates
      (fun state => vacuumCodeDelta K state + (-vacuumMass))
      (fun state => vacuumCodeDelta K state + (-vacuumMass)) joint ≈ _
  refine Q'.eqv_trans _
    (finiteJointBilinear positiveStates (vacuumCodeDelta K) (vacuumCodeDelta K) joint +
      ((-vacuumMass) *
          finiteJointBilinear positiveStates (vacuumCodeDelta K) (fun _ => 1) joint +
      ((-vacuumMass) *
          finiteJointBilinear positiveStates (fun _ => 1) (vacuumCodeDelta K) joint +
      ((-vacuumMass) * (-vacuumMass)) *
          finiteJointBilinear positiveStates (fun _ => 1) (fun _ => 1) joint))) _
    (finiteJointBilinear_affine_self
      positiveStates (vacuumCodeDelta K) (-vacuumMass) joint) ?_
  refine Q'.eqv_trans _
    (joint zeroEdgeLabelling zeroEdgeLabelling +
      ((-vacuumMass) * vacuumMass +
      ((-vacuumMass) * vacuumMass +
      ((-vacuumMass) * (-vacuumMass)) * 1))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_trans _
        (centralNormalizedFullPhysicalReflectionQuadratic
          w hw K 0 (vacuumCodeDelta K)) _
        (centralPhysicalJointQuadratic_eq_normalizedFull
          w hw K 0 (vacuumCodeDelta K))
        (centralNormalizedFull_vacuumCodeDelta_eqv_diagonal
          w hw K))
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left (-vacuumMass) _ _
          (physicalVacuumDeltaConstantCross_eq_marginal w hw K))
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left (-vacuumMass) _ _
            (Q'.eqv_trans _ _ _
              (finiteJointBilinear_swap_of_symmetric
                positiveStates (fun _ => 1) (vacuumCodeDelta K) joint
                (fun left right hleft hright =>
                  centralNormalizedPhysicalReflectedKernel_symm
                    ((mem_centralPositiveHalfStates_iff.mp hleft).1)
                    ((mem_centralPositiveHalfStates_iff.mp hright).1)))
              (physicalVacuumDeltaConstantCross_eq_marginal w hw K)))
          (Q'.mul_eqv_congr_left
            ((-vacuumMass) * (-vacuumMass)) _ _
            (Q'.eqv_trans _
              (centralNormalizedFullPhysicalReflectionQuadratic
                w hw K 0 (fun _ => 1)) _
              (centralPhysicalJointQuadratic_eq_normalizedFull
                w hw K 0 (fun _ => 1))
              (centralNormalizedFullPhysicalReflectionQuadratic_one
                w hw K 0)))))
  exact centeredPhysicalMoment_scalar
    (joint zeroEdgeLabelling zeroEdgeLabelling) vacuumMass

/-! ## 4. Scalar balance forced by centered same action -/

/-- Fully expanded signed-Haar side of the centered vacuum test. -/
def exactCenteredVacuumMomentExpression
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  1 +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
        exactVacuumRightConstantCrossMoment w K +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
        exactVacuumRightConstantCrossMoment w K +
    ((-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling) *
      (-centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling)) *
        exactConstantQuadraticMoment w K))

/-- Closed positive-physical side of the centered vacuum test. -/
def physicalCenteredVacuumMomentExpression
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  centralNormalizedPhysicalReflectedKernel
      w hw K 0 zeroEdgeLabelling zeroEdgeLabelling +
    (-(centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling *
      centralPhysicalRowMarginal
        w hw K 0 zeroEdgeLabelling))

/-- Any centered same-action inhabitant must solve this explicit scalar
moment equation.  The only uncomputed quantities are the signed-Haar vacuum
row sum and constant quadratic moment. -/
theorem ExactHaarPhysicalPerronCenteredSameActionAt.vacuumMoment_balance
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (identification :
      ExactHaarPhysicalPerronCenteredSameActionAt w hw K) :
    exactCenteredVacuumMomentExpression w hw K ≈
      physicalCenteredVacuumMomentExpression w hw K := by
  unfold exactCenteredVacuumMomentExpression
    physicalCenteredVacuumMomentExpression
  exact Q'.eqv_trans _
    (exactSlabAllCutoffQuadratic
      w K (centeredVacuumCodeDelta w hw K)) _
    (Q'.eqv_symm
      (exactSlabAllCutoffQuadratic_centeredVacuum_symmetric_expansion
        w hw K))
    (Q'.eqv_trans _ _ _
      (identification.centered_same_action
        (centeredVacuumCodeDelta w hw K)
        (centeredVacuumCodeDelta_meanZero w hw K))
      (centralNormalizedFull_centeredVacuum_eq_diagonal_sub_square
        w hw K))

end YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.finiteJointBilinear_affine_self
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.finiteJointBilinear_swap_of_symmetric
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.finiteJointBilinear_vacuumCodeDelta_one
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.exactVacuumLeftConstantCrossMoment_eq_right
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.exactVacuumRightConstantCrossMoment_eq_vacuumRowSum
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.exactSlabAllCutoffQuadratic_centeredVacuum_moment_expansion
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.exactSlabAllCutoffQuadratic_centeredVacuum_symmetric_expansion
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.physicalVacuumDeltaConstantCross_eq_marginal
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.centralNormalizedFull_centeredVacuum_eq_diagonal_sub_square
#print axioms YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion.ExactHaarPhysicalPerronCenteredSameActionAt.vacuumMoment_balance
