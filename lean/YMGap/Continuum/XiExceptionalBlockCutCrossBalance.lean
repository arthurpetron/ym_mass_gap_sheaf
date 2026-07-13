/-
# Cross-balanced allocation for two unequal ear blocks

Two blocks with the same unequal arm profile can be oriented oppositely.  In
each cross orientation, the selected-pair excess of one block is exactly the
reserve-pair excess of the other, so the aggregate occurrence budget fits.
The two cross-oriented monomials dominate the product of the two source
weights by applying the constructive square inequality to the cross terms.

This is the first compositional multicode rule that survives the unequal-ear
fuel fence: capacity is balanced across block-cut children, rather than
required separately at each child.
-/

import YMGap.Continuum.XiExceptionalUnequalEarFuelFence

namespace YMGap.Continuum.XiExceptionalBlockCutCrossBalance

open YMGap.Constructive
open YMGap.Continuum.XiExceptionalMixedEarAbsorption

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- Exact fuel profile for two blocks sharing one articulation.  The two
selected arms contribute their bounced interiors; all four arms contribute
distinct interior reserve. -/
structure TwoBlockFuel where
  firstSelected : Nat
  firstReserve : Nat
  secondSelected : Nat
  secondReserve : Nat
deriving DecidableEq

def TwoBlockFuel.bouncedVertexLength (fuel : TwoBlockFuel) : Nat :=
  3 + 4 * (fuel.firstSelected + fuel.secondSelected)

def TwoBlockFuel.availableOccurrenceCount (fuel : TwoBlockFuel) : Nat :=
  3 + 2 * (fuel.firstSelected + fuel.firstReserve +
    fuel.secondSelected + fuel.secondReserve)

/-- Select the first arm in the first block and the second arm in the second
block. -/
def crossForwardFuel (selected reserve : Nat) : TwoBlockFuel :=
  ⟨selected, reserve, reserve, selected⟩

/-- The complementary cross orientation. -/
def crossReverseFuel (selected reserve : Nat) : TwoBlockFuel :=
  ⟨reserve, selected, selected, reserve⟩

/-- Cross-child cancellation is exact, with no extra occurrence assigned to
the shared articulation. -/
theorem crossForward_exact_budget (selected reserve : Nat) :
    (crossForwardFuel selected reserve).bouncedVertexLength =
      (crossForwardFuel selected reserve).availableOccurrenceCount := by
  simp only [crossForwardFuel, TwoBlockFuel.bouncedVertexLength,
    TwoBlockFuel.availableOccurrenceCount]
  omega

theorem crossReverse_exact_budget (selected reserve : Nat) :
    (crossReverseFuel selected reserve).bouncedVertexLength =
      (crossReverseFuel selected reserve).availableOccurrenceCount := by
  simp only [crossReverseFuel, TwoBlockFuel.bouncedVertexLength,
    TwoBlockFuel.availableOccurrenceCount]
  omega

theorem both_cross_codes_fit (selected reserve : Nat) :
    ((crossForwardFuel selected reserve).bouncedVertexLength ≤
        (crossForwardFuel selected reserve).availableOccurrenceCount) ∧
      ((crossReverseFuel selected reserve).bouncedVertexLength ≤
        (crossReverseFuel selected reserve).availableOccurrenceCount) := by
  constructor
  · exact Nat.le_of_eq (crossForward_exact_budget selected reserve)
  · exact Nat.le_of_eq (crossReverse_exact_budget selected reserve)

/-! ## Exact two-block weight domination -/

/-- If the two source blocks have arm weights `(A₁,B₁)` and `(A₂,B₂)`,
the two valid cross codes have weights `(A₁B₂)²` and `(B₁A₂)²`.
Their sum dominates the product of both source block weights. -/
theorem cross_balanced_pair_weight_bound
    {A₁ B₁ A₂ B₂ : Q'}
    (hA₁ : (0 : Q') ≤ A₁) (hB₁ : (0 : Q') ≤ B₁)
    (hA₂ : (0 : Q') ≤ A₂) (hB₂ : (0 : Q') ≤ B₂) :
    (A₁ * B₁) * (A₂ * B₂) ≤
      (A₁ * B₂) * (A₁ * B₂) +
        (B₁ * A₂) * (B₁ * A₂) := by
  let X := A₁ * B₂
  let Y := B₁ * A₂
  have hX : (0 : Q') ≤ X := Q'.mul_nonneg _ _ hA₁ hB₂
  have hY : (0 : Q') ≤ Y := Q'.mul_nonneg _ _ hB₁ hA₂
  have hsquare := prod_le_square_sum hX hY
  have hsource : (A₁ * B₁) * (A₂ * B₂) ≈ X * Y := by
    unfold X Y
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource) hsquare

/-- Pairing a list of identical-profile block pairs contributes exactly two
cross orientations per pair; this is the local source-fiber multiplicity. -/
def crossChoiceCount : Nat → Nat
  | 0 => 1
  | pairs + 1 => 2 * crossChoiceCount pairs

theorem crossChoiceCount_succ (pairs : Nat) :
    crossChoiceCount (pairs + 1) = 2 * crossChoiceCount pairs := rfl

theorem crossChoiceCount_positive : ∀ pairs : Nat, 0 < crossChoiceCount pairs
  | 0 => by simp [crossChoiceCount]
  | pairs + 1 => by
      simp only [crossChoiceCount]
      have ih := crossChoiceCount_positive pairs
      omega

#print axioms crossForward_exact_budget
#print axioms crossReverse_exact_budget
#print axioms both_cross_codes_fit
#print axioms cross_balanced_pair_weight_bound
#print axioms crossChoiceCount_positive

end YMGap.Continuum.XiExceptionalBlockCutCrossBalance
