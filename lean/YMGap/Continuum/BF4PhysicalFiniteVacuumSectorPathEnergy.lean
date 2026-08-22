/-
# Constructive path-energy domination on finite BF4 vacuum sectors

The exact BF4 Dirichlet identity exposes a sum of physical edge squares.  To
turn connectedness into a Poincare estimate, endpoint differences must be
controlled by the energies along the explicit positive-kernel chains.

This module proves the local quantitative compiler.  A chain is assigned a
recursively amplified energy: each step doubles the current edge energy plus
the remaining path budget.  If a nonnegative rational `floor` lies below
every positive edge used by the chain, then

  floor * (f(first) - f(last))^2 <= amplifiedPathEnergy.

The exponential amplification is intentionally crude but fully explicit and
finite.  A later finite maximum will turn it into one common path factor, and
a finite minimum over positive BF4 entries will supply a strictly positive
floor.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem square_nonnegative (value : Q') :
    (0 : Q') ≤ value * value :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg value

private theorem square_eqv_congr {left right : Q'}
    (heq : left ≈ right) :
    left * left ≈ right * right := by
  exact Q'.eqv_trans _ (right * left) _
    (Q'.mul_eqv_congr_right left right left heq)
    (Q'.mul_eqv_congr_left right left right heq)

private def youngSquareL : PolyExpr :=
  let left := PolyExpr.var 0
  let right := PolyExpr.var 1
  .mul (.add left (.neg right)) (.add left (.neg right))

private def youngSquareR : PolyExpr :=
  let left := PolyExpr.var 0
  let right := PolyExpr.var 1
  let squares := .add (.mul left left) (.mul right right)
  .add (.add squares squares)
    (.neg (.mul (.add left right) (.add left right)))

private theorem youngSquare_normal :
    normalize youngSquareL = normalize youngSquareR := by
  decide

private theorem youngSquare_identity (left right : Q') :
    (left + -right) * (left + -right) ≈
      ((left * left + right * right) +
        (left * left + right * right)) +
      -((left + right) * (left + right)) := by
  let valuation : Nat → Q' := fun index =>
    if index = 0 then left else right
  have h := poly_identity_of_normal_eq
    youngSquareL youngSquareR youngSquare_normal valuation
  simpa [youngSquareL, youngSquareR, RingNormaliser.eval, valuation] using h

/-- The elementary two-term Cauchy bound used at every path step. -/
theorem square_add_le_double_square_sum (left right : Q') :
    (left + right) * (left + right) ≤
      (left * left + right * right) +
        (left * left + right * right) := by
  have hnonnegative : (0 : Q') ≤
      (left + -right) * (left + -right) :=
    square_nonnegative _
  have hidentity := youngSquare_identity left right
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ hnonnegative
    (Q'.le_of_eqv hidentity)

/-! ## 1. Amplified energy of one positive-kernel chain -/

namespace PositiveKernelChainIn

/-- The explicit path length, retained for the later finite ceiling. -/
def length {State : Type} {kernel : State → State → Q'}
    {support : List State} {first last : State} :
    PositiveKernelChainIn kernel support first last → Nat
  | PositiveKernelChainIn.refl _ => 0
  | PositiveKernelChainIn.step _ _ rest => length rest + 1

/-- Recursively amplified sum of the actual kernel-weighted edge squares. -/
def amplifiedEnergy {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      PositiveKernelChainIn kernel support first last → Q'
  | _, _, PositiveKernelChainIn.refl _ => 0
  | first, _, PositiveKernelChainIn.step (next := next) _ _ rest =>
      (kernel first next *
            ((coefficient first + -coefficient next) *
              (coefficient first + -coefficient next)) +
          amplifiedEnergy coefficient rest) +
        (kernel first next *
            ((coefficient first + -coefficient next) *
              (coefficient first + -coefficient next)) +
          amplifiedEnergy coefficient rest)

theorem amplifiedEnergy_nonnegative
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q') :
    {first last : State} →
      (path : PositiveKernelChainIn kernel support first last) →
      (0 : Q') ≤ amplifiedEnergy coefficient path
  | _, _, PositiveKernelChainIn.refl _ => Q'.le_refl' 0
  | _, _, PositiveKernelChainIn.step positive _ rest => by
      apply Q'.zero_le_add
      · apply Q'.zero_le_add
        · exact Q'.mul_nonneg _ _ (Q'.le_of_lt positive)
            (square_nonnegative _)
        · exact amplifiedEnergy_nonnegative coefficient rest
      · apply Q'.zero_le_add
        · exact Q'.mul_nonneg _ _ (Q'.le_of_lt positive)
            (square_nonnegative _)
        · exact amplifiedEnergy_nonnegative coefficient rest

private theorem endpointDifference_step
    {State : Type} (coefficient : State → Q')
    (first next last : State) :
    coefficient first + -coefficient last ≈
      (coefficient first + -coefficient next) +
        (coefficient next + -coefficient last) := by
  have hinner :
      (-coefficient next) +
          (coefficient next + -coefficient last) ≈
        -coefficient last := by
    refine Q'.eqv_trans _
      ((-coefficient next + coefficient next) +
        -coefficient last) _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv
          (-coefficient next) (coefficient next)
          (-coefficient last))) ?_
    refine Q'.eqv_trans _ (0 + -coefficient last) _
      (Q'.add_eqv_congr'
        (Q'.neg_add_self_eqv (coefficient next))
        (Q'.eqv_refl _)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' _)
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (coefficient first +
        ((-coefficient next) +
          (coefficient next + -coefficient last))) _
      (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hinner))

/-- A uniform lower bound on the positive entries used by a chain controls its
endpoint difference by the recursively amplified physical path energy. -/
theorem floor_mul_endpointDifference_sq_le_amplifiedEnergy
    {State : Type} {kernel : State → State → Q'}
    {support : List State} (coefficient : State → Q')
    (floor : Q') (hfloor0 : (0 : Q') ≤ floor)
    (edgeFloor : ∀ first next,
      first ∈ support → next ∈ support →
      (0 : Q') < kernel first next →
      floor ≤ kernel first next) :
    {first last : State} → first ∈ support →
      (path : PositiveKernelChainIn kernel support first last) →
      floor *
          ((coefficient first + -coefficient last) *
            (coefficient first + -coefficient last)) ≤
        amplifiedEnergy coefficient path
  | first, _, _hfirst, PositiveKernelChainIn.refl _ => by
      have hzero : coefficient first + -coefficient first ≈ 0 :=
        Q'.add_neg_self_eqv _
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ (floor * (0 * 0)) _
          (Q'.mul_eqv_congr_left floor _ _
            (square_eqv_congr hzero))
          (Q'.eqv_trans _ (floor * 0) _
            (Q'.mul_eqv_congr_left floor _ _
              (Q'.zero_mul_eqv 0))
            (Q'.mul_zero_eqv floor)))
  | first, last, hfirst,
      PositiveKernelChainIn.step (next := next) positive hnext rest => by
      let leftDifference := coefficient first + -coefficient next
      let restDifference := coefficient next + -coefficient last
      let restEnergy := amplifiedEnergy coefficient rest
      have hrest : floor * (restDifference * restDifference) ≤ restEnergy :=
        floor_mul_endpointDifference_sq_le_amplifiedEnergy
          coefficient floor hfloor0 edgeFloor hnext rest
      have hedge : floor * (leftDifference * leftDifference) ≤
          kernel first next * (leftDifference * leftDifference) :=
        Q'.mul_le_mul_of_nonneg_right floor (kernel first next)
          (leftDifference * leftDifference)
          (edgeFloor first next hfirst hnext positive)
          (square_nonnegative leftDifference)
      have hadd :
          floor * (leftDifference * leftDifference) +
              floor * (restDifference * restDifference) ≤
            kernel first next * (leftDifference * leftDifference) +
              restEnergy :=
        Q'.add_le_add hedge hrest
      have htwice :
          (floor * (leftDifference * leftDifference) +
              floor * (restDifference * restDifference)) +
            (floor * (leftDifference * leftDifference) +
              floor * (restDifference * restDifference)) ≤
          (kernel first next * (leftDifference * leftDifference) +
              restEnergy) +
            (kernel first next * (leftDifference * leftDifference) +
              restEnergy) :=
        Q'.add_le_add hadd hadd
      have htel := endpointDifference_step
        coefficient first next last
      have hendpointSquare :
          (coefficient first + -coefficient last) *
              (coefficient first + -coefficient last) ≈
            (leftDifference + restDifference) *
              (leftDifference + restDifference) :=
        square_eqv_congr htel
      have hyoung := square_add_le_double_square_sum
        leftDifference restDifference
      have hscaledYoung :
          floor *
              ((leftDifference + restDifference) *
                (leftDifference + restDifference)) ≤
            floor *
              ((leftDifference * leftDifference +
                  restDifference * restDifference) +
                (leftDifference * leftDifference +
                  restDifference * restDifference)) :=
        Q'.mul_le_mul_of_nonneg_left _ _ floor hyoung hfloor0
      have hcollect :
          floor *
              ((leftDifference * leftDifference +
                  restDifference * restDifference) +
                (leftDifference * leftDifference +
                  restDifference * restDifference)) ≈
            (floor * (leftDifference * leftDifference) +
                floor * (restDifference * restDifference)) +
              (floor * (leftDifference * leftDifference) +
                floor * (restDifference * restDifference)) := by
        refine Q'.eqv_trans _
          (floor *
              (leftDifference * leftDifference +
                restDifference * restDifference) +
            floor *
              (leftDifference * leftDifference +
                restDifference * restDifference)) _
          (Q'.mul_add_eqv _ _ _) ?_
        exact Q'.add_eqv_congr'
          (Q'.mul_add_eqv _ _ _) (Q'.mul_add_eqv _ _ _)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left floor _ _ hendpointSquare))
        (Q'.le_trans' _ _ _ hscaledYoung
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect) htwice))

end PositiveKernelChainIn

/-! ## 2. Specialization to the canonical BF4 physical paths -/

/-- The canonical positive-kernel path selected by the constructive component
compiler. -/
def centralPhysicalFiniteVacuumSectorPositivePath
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      left right :=
  centralPhysicalFiniteVacuumSector_positiveKernelConnected
    w hw cutoff half left right hleft hright

/-- Any common lower bound on positive physical sector entries controls every
endpoint difference along the explicit canonical BF4 path. -/
theorem centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_pathEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (floor : Q') (hfloor0 : (0 : Q') ≤ floor)
    (edgeFloor : ∀ left right,
      left ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      right ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      (0 : Q') < centralPhysicalFiniteKernel
        w hw cutoff half left right →
      floor ≤ centralPhysicalFiniteKernel
        w hw cutoff half left right)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    floor *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      PositiveKernelChainIn.amplifiedEnergy coefficient
        (centralPhysicalFiniteVacuumSectorPositivePath
          w hw cutoff half left right hleft hright) := by
  exact PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_amplifiedEnergy
    coefficient floor hfloor0 edgeFloor hleft
    (centralPhysicalFiniteVacuumSectorPositivePath
      w hw cutoff half left right hleft hright)

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy.square_add_le_double_square_sum
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.floor_mul_endpointDifference_sq_le_amplifiedEnergy
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy.centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_pathEnergy
