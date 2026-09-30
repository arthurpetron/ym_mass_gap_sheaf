/-
# A two-dimensional rational normalization witness

Two orthogonal projections give strict normalized order-one Chebyshev
contraction while the reverse-energy margin is negative. This is only a
finite rational operator example; it has no physical or Yang--Mills
interpretation.
-/

import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.RationalChebyshevNormalizationWitness

set_option autoImplicit false

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

abbrev Vec2 := Fin 2 → Q'
abbrev Mat2 := Fin 2 → Fin 2 → Q'

def r9_25 : Q' := Q'.mkPos 9 25 (by decide)
def r12_25 : Q' := Q'.mkPos 12 25 (by decide)
def r16_25 : Q' := Q'.mkPos 16 25 (by decide)
def r256_625 : Q' := Q'.mkPos 256 625 (by decide)

def P : Mat2 := fun i j =>
  if i.val = 0 ∧ j.val = 0 then 1 else 0

def Q : Mat2 := fun i j =>
  match i.val, j.val with
  | 0, 0 => r16_25
  | 0, 1 => r12_25
  | 1, 0 => r12_25
  | 1, 1 => r9_25
  | _, _ => 0

def matMul (A B : Mat2) : Mat2 := fun i j =>
  A i 0 * B 0 j + A i 1 * B 1 j

def matVec (A : Mat2) (x : Vec2) : Vec2 := fun i =>
  A i 0 * x 0 + A i 1 * x 1

def normSq (x : Vec2) : Q' := x 0 * x 0 + x 1 * x 1

/-- The two matrices are the explicit orthogonal projections onto `e₁` and
the line spanned by `(4/5,3/5)`. -/
theorem P_symmetric : ∀ i j, P i j ≈ P j i := by decide
theorem P_idempotent : ∀ i j, matMul P P i j ≈ P i j := by decide
theorem Q_symmetric : ∀ i j, Q i j ≈ Q j i := by decide
theorem Q_idempotent : ∀ i j, matMul Q Q i j ≈ Q i j := by decide

def W : Mat2 := matMul Q P
def B : Mat2 := matMul P (matMul Q P)
def x : Vec2 := fun i => if i.val = 0 then 1 else 0

theorem balanced_is_adjoint_square :
    ∀ i j, B i j ≈ matMul (fun i j => W j i) W i j := by decide

theorem source_normSq : normSq x ≈ 1 := by decide

def reverseMargin : Q' :=
  2 * normSq (matVec W x) + -(4 * normSq (matVec B x))

/-- `T₁(cB-I)x` for `c=4`, with `T₁(t)=t`. -/
def chebyshevNumerator : Vec2 := fun i =>
  4 * matVec B x i + -x i

def normalizedChebyshevNormSq : Q' :=
  normSq chebyshevNumerator * Q'.mkPos 1 9 (by decide)

/-- The proposed reverse-margin budget at `eta=1/3`, `c=4`, and `n=1`. -/
def marginBudget : Q' :=
  4 * reverseMargin +
    ((Q'.mkPos 1 3 (by decide) * 9) + -1) * normSq x

theorem forward_normSq : normSq (matVec W x) ≈ r16_25 := by decide

theorem balanced_normSq : normSq (matVec B x) ≈ r256_625 := by decide

theorem reverse_margin_value : reverseMargin ≈ -(Q'.mkPos 224 625 (by decide)) := by
  decide

/-- Here `T₁(c-1)=3`; the unnormalized squared norm is `1521/625`. -/
theorem chebyshev_unnormalized_value :
    normSq chebyshevNumerator ≈ Q'.mkPos 1521 625 (by decide) := by
  decide

theorem chebyshev_normalized_value :
    normalizedChebyshevNormSq ≈ Q'.mkPos 169 625 (by decide) := by decide

/-- Despite the negative reverse margin, the normalized squared norm is
strictly below `eta=1/3`. -/
theorem strict_normalized_contraction_with_negative_margin :
    normalizedChebyshevNormSq < Q'.mkPos 1 3 (by decide) ∧
      reverseMargin < (0 : Q') := by
  decide

theorem margin_budget_value : marginBudget ≈ Q'.mkPos 354 625 (by decide) := by
  decide

theorem margin_budget_positive : (0 : Q') < marginBudget := by decide

#print axioms P_symmetric
#print axioms P_idempotent
#print axioms Q_symmetric
#print axioms Q_idempotent
#print axioms balanced_is_adjoint_square
#print axioms source_normSq
#print axioms forward_normSq
#print axioms balanced_normSq
#print axioms reverse_margin_value
#print axioms chebyshev_unnormalized_value
#print axioms chebyshev_normalized_value
#print axioms strict_normalized_contraction_with_negative_margin
#print axioms margin_budget_value
#print axioms margin_budget_positive

end YMGap.Continuum.RationalChebyshevNormalizationWitness
