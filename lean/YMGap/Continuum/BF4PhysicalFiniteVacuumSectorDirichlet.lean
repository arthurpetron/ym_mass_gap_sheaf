/-
# Exact Dirichlet identity on every finite BF4 vacuum sector

The canonical component now has positive stationary weights, exact restricted
row masses, symmetric nonnegative physical kernel entries, and explicit
positive-kernel paths.  This module supplies the algebraic hinge needed by a
path Poincare argument.

For a finite symmetric joint kernel whose row sums are the stationary weights,
the directed edge energy

  sum_{i,j} K_ij (f_i - f_j)^2

is exactly twice the transfer-form deficit `D(f) - M(f)`.  The theorem is first
proved for an arbitrary finite list and then specialized to the genuine BF4
canonical vacuum component at every cutoff.

This is an exact identity.  Positivity of paths has not yet been converted to
a quantitative Poincare constant or strict contraction.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic finite directed edge energy -/

/-- The directed finite Dirichlet edge energy.  For a symmetric kernel the two
orientations account for the conventional factor of two. -/
def finiteJointDirichletEnergy {State : Type}
    (states : List State) (coefficient : State → Q')
    (joint : State → State → Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right =>
        joint left right *
          ((coefficient left + -coefficient right) *
            (coefficient left + -coefficient right)))
      states)
    states

private def finiteDoubleSum {State : Type}
    (states : List State) (term : State → State → Q') : Q' :=
  listQSum (fun left => listQSum (term left) states) states

private theorem finiteDoubleSum_add {State : Type}
    (states : List State) (left right : State → State → Q') :
    finiteDoubleSum states (fun i j => left i j + right i j) ≈
      finiteDoubleSum states left + finiteDoubleSum states right := by
  unfold finiteDoubleSum
  refine Q'.eqv_trans _
    (listQSum
      (fun i => listQSum (left i) states + listQSum (right i) states)
      states) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _
    exact listQSum_add (left i) (right i) states
  · exact listQSum_add
      (fun i => listQSum (left i) states)
      (fun i => listQSum (right i) states) states

private theorem listQSum_neg_local {State : Type}
    (value : State → Q') : ∀ states : List State,
    listQSum (fun state => -(value state)) states ≈
      -(listQSum value states)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)
      · exact Q'.eqv_symm (Q'.neg_add_eqv _ _)

private theorem finiteDoubleSum_neg {State : Type}
    (states : List State) (term : State → State → Q') :
    finiteDoubleSum states (fun i j => -(term i j)) ≈
      -(finiteDoubleSum states term) := by
  unfold finiteDoubleSum
  refine Q'.eqv_trans _
    (listQSum (fun i => -(listQSum (term i) states)) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _
    exact listQSum_neg_local (term i) states
  · exact listQSum_neg_local
      (fun i => listQSum (term i) states) states

private theorem finiteDoubleSum_congr {State : Type}
    (states : List State) (left right : State → State → Q')
    (heq : ∀ i, i ∈ states → ∀ j, j ∈ states → left i j ≈ right i j) :
    finiteDoubleSum states left ≈ finiteDoubleSum states right := by
  unfold finiteDoubleSum
  apply listQSum_congr_on
  intro i hi
  apply listQSum_congr_on
  intro j hj
  exact heq i hi j hj

/-! ## 2. Exact generic Dirichlet identity -/

/-- A finite symmetric joint kernel with stationary row weights has directed
edge energy exactly equal to twice its diagonal-minus-transfer deficit. -/
theorem finiteJointDirichletEnergy_eqv_twice_deficit
    {State : Type} (states : List State)
    (weight coefficient : State → Q')
    (joint : State → State → Q')
    (hrow : ∀ state, state ∈ states →
      listQSum (joint state) states ≈ weight state)
    (hsymmetric : ∀ left, left ∈ states → ∀ right, right ∈ states →
      joint left right ≈ joint right left) :
    finiteJointDirichletEnergy states coefficient joint ≈
      (finiteWeightedSquare states weight coefficient +
          finiteWeightedSquare states weight coefficient) +
        -(finiteJointQuadratic states coefficient joint +
          finiteJointQuadratic states coefficient joint) := by
  let leftSquare : State → State → Q' := fun left right =>
    (coefficient left * coefficient left) * joint left right
  let rightSquare : State → State → Q' := fun left right =>
    (coefficient right * coefficient right) * joint left right
  let cross : State → State → Q' := fun left right =>
    (coefficient left * coefficient right) * joint left right
  have hpoint : ∀ left, left ∈ states → ∀ right, right ∈ states →
      joint left right *
          ((coefficient left + -coefficient right) *
            (coefficient left + -coefficient right)) ≈
        (leftSquare left right + rightSquare left right) +
          (-(cross left right) + -(cross left right)) := by
    intro left _ right _
    unfold leftSquare rightSquare cross
    q_ring
  have hexpand : finiteJointDirichletEnergy states coefficient joint ≈
      (finiteDoubleSum states leftSquare +
        finiteDoubleSum states rightSquare) +
      (finiteDoubleSum states (fun i j => -(cross i j)) +
        finiteDoubleSum states (fun i j => -(cross i j))) := by
    refine Q'.eqv_trans _
      (finiteDoubleSum states
        (fun i j =>
          (leftSquare i j + rightSquare i j) +
            (-(cross i j) + -(cross i j)))) _ ?_ ?_
    · unfold finiteJointDirichletEnergy
      exact finiteDoubleSum_congr states _ _ hpoint
    · refine Q'.eqv_trans _
        (finiteDoubleSum states
            (fun i j => leftSquare i j + rightSquare i j) +
          finiteDoubleSum states
            (fun i j => -(cross i j) + -(cross i j))) _
        (finiteDoubleSum_add states _ _) ?_
      exact Q'.add_eqv_congr'
        (finiteDoubleSum_add states leftSquare rightSquare)
        (finiteDoubleSum_add states
          (fun i j => -(cross i j)) (fun i j => -(cross i j)))
  have hleft : finiteDoubleSum states leftSquare ≈
      finiteWeightedSquare states weight coefficient := by
    unfold finiteDoubleSum finiteWeightedSquare leftSquare
    apply listQSum_congr_on
    intro left hleftMem
    refine Q'.eqv_trans _
      ((coefficient left * coefficient left) *
        listQSum (joint left) states) _
      (listQSum_mul_left
        (coefficient left * coefficient left) (joint left) states) ?_
    exact Q'.eqv_trans _
      ((coefficient left * coefficient left) * weight left) _
      (Q'.mul_eqv_congr_left _ _ _ (hrow left hleftMem))
      (Q'.mul_comm_eqv _ _)
  have hright : finiteDoubleSum states rightSquare ≈
      finiteWeightedSquare states weight coefficient := by
    refine Q'.eqv_trans _
      (listQSum
        (fun right => listQSum
          (fun left => rightSquare left right) states)
        states) _ ?_ ?_
    · unfold finiteDoubleSum
      exact Q'.eqv_symm (listQSum_swap rightSquare states states)
    unfold finiteWeightedSquare
    apply listQSum_congr_on
    intro right hrightMem
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          (coefficient right * coefficient right) * joint right left)
        states) _ ?_ ?_
    · apply listQSum_congr_on
      intro left hleftMem
      unfold rightSquare
      exact Q'.mul_eqv_congr_left _ _ _
        (hsymmetric left hleftMem right hrightMem)
    refine Q'.eqv_trans _
      ((coefficient right * coefficient right) *
        listQSum (joint right) states) _
      (listQSum_mul_left
        (coefficient right * coefficient right) (joint right) states) ?_
    exact Q'.eqv_trans _
      ((coefficient right * coefficient right) * weight right) _
      (Q'.mul_eqv_congr_left _ _ _ (hrow right hrightMem))
      (Q'.mul_comm_eqv _ _)
  have hcross : finiteDoubleSum states cross ≈
      finiteJointQuadratic states coefficient joint := by
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ hexpand ?_
  apply Q'.add_eqv_congr'
  · exact Q'.add_eqv_congr' hleft hright
  · refine Q'.eqv_trans _
      (-(finiteJointQuadratic states coefficient joint) +
        -(finiteJointQuadratic states coefficient joint)) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (finiteDoubleSum_neg states cross)
          (Q'.neg_eqv_congr _ _ hcross))
        (Q'.eqv_trans _ _ _
          (finiteDoubleSum_neg states cross)
          (Q'.neg_eqv_congr _ _ hcross))
    · exact Q'.eqv_symm (Q'.neg_add_eqv _ _)

/-- Half of the directed edge energy is the usual Dirichlet deficit. -/
theorem half_mul_finiteJointDirichletEnergy_eqv_deficit
    {State : Type} (states : List State)
    (weight coefficient : State → Q')
    (joint : State → State → Q')
    (hrow : ∀ state, state ∈ states →
      listQSum (joint state) states ≈ weight state)
    (hsymmetric : ∀ left, left ∈ states → ∀ right, right ∈ states →
      joint left right ≈ joint right left) :
    Q'.mkPos 1 2 (by decide) *
        finiteJointDirichletEnergy states coefficient joint ≈
      finiteWeightedSquare states weight coefficient +
        -(finiteJointQuadratic states coefficient joint) := by
  let diagonal := finiteWeightedSquare states weight coefficient
  let matrix := finiteJointQuadratic states coefficient joint
  refine Q'.eqv_trans _
    (Q'.mkPos 1 2 (by decide) *
      ((diagonal + diagonal) + -(matrix + matrix))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (finiteJointDirichletEnergy_eqv_twice_deficit
        states weight coefficient joint hrow hsymmetric)
  refine Q'.eqv_trans _
    (Q'.mkPos 1 2 (by decide) * (diagonal + diagonal) +
      Q'.mkPos 1 2 (by decide) * (-(matrix + matrix))) _
    (Q'.mul_add_eqv _ _ _) ?_
  apply Q'.add_eqv_congr'
  · exact Q'.eqv_trans _
      (Q'.mkPos 1 2 (by decide) * diagonal +
        Q'.mkPos 1 2 (by decide) * diagonal) _
      (Q'.mul_add_eqv _ _ _)
      (two_halves diagonal)
  · refine Q'.eqv_trans _
      (-(Q'.mkPos 1 2 (by decide) * (matrix + matrix))) _
      (Q'.mul_neg_eqv _ _) ?_
    refine Q'.eqv_trans _
      (-(Q'.mkPos 1 2 (by decide) * matrix +
        Q'.mkPos 1 2 (by decide) * matrix)) _
      (Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv _ _ _)) ?_
    exact Q'.neg_eqv_congr _ _ (two_halves matrix)

/-! ## 3. The actual BF4 canonical-sector identity -/

/-- At every cutoff, the genuine canonical BF4 vacuum-sector edge energy is
exactly twice its physical diagonal-minus-reflected-form deficit. -/
theorem centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        coefficient
        (centralPhysicalFiniteKernel w hw cutoff half) ≈
      (centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient +
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient) +
      -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient +
        centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  let joint := centralPhysicalFiniteKernel w hw cutoff half
  have hgeneric := finiteJointDirichletEnergy_eqv_twice_deficit
    states weight coefficient joint
    (fun state hstate =>
      centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight hstate)
    (fun left hleft right hright => by
      have hleftPositive := centralPhysicalFiniteStateAt_mem_positive
        w hw cutoff half
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw cutoff half hleft)
      have hrightPositive := centralPhysicalFiniteStateAt_mem_positive
        w hw cutoff half
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw cutoff half hright)
      unfold joint centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_symm
        (mem_centralPositiveHalfStates_iff.mp hleftPositive).1
        (mem_centralPositiveHalfStates_iff.mp hrightPositive).1)
  have hdiagonal : finiteWeightedSquare states weight coefficient ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
    unfold finiteWeightedSquare
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic states weight
    apply listQSum_congr_on
    intro state _
    exact Q'.mul_comm_eqv _ _
  have hmatrix : finiteJointQuadratic states coefficient joint ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient := by
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ hgeneric ?_
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' hdiagonal hdiagonal)
    (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hmatrix hmatrix))

/-- Conventional half-energy form of the same BF4 identity. -/
theorem half_mul_centralPhysicalFiniteVacuumSectorDirichlet_eqv_deficit
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    Q'.mkPos 1 2 (by decide) *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient +
        -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  let joint := centralPhysicalFiniteKernel w hw cutoff half
  have hgeneric := half_mul_finiteJointDirichletEnergy_eqv_deficit
    states weight coefficient joint
    (fun state hstate =>
      centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight hstate)
    (fun left hleft right hright => by
      have hleftPositive := centralPhysicalFiniteStateAt_mem_positive
        w hw cutoff half
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw cutoff half hleft)
      have hrightPositive := centralPhysicalFiniteStateAt_mem_positive
        w hw cutoff half
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw cutoff half hright)
      unfold joint centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_symm
        (mem_centralPositiveHalfStates_iff.mp hleftPositive).1
        (mem_centralPositiveHalfStates_iff.mp hrightPositive).1)
  have hdiagonal : finiteWeightedSquare states weight coefficient ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
    unfold finiteWeightedSquare
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic states weight
    apply listQSum_congr_on
    intro state _
    exact Q'.mul_comm_eqv _ _
  have hmatrix : finiteJointQuadratic states coefficient joint ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient := by
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hgeneric
    (Q'.add_eqv_congr' hdiagonal (Q'.neg_eqv_congr _ _ hmatrix))

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet.finiteJointDirichletEnergy_eqv_twice_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet.half_mul_finiteJointDirichletEnergy_eqv_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet.centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet.half_mul_centralPhysicalFiniteVacuumSectorDirichlet_eqv_deficit
