/-
# A finite rational order-one / order-two Chebyshev auxiliary obstruction

This is a four-dimensional Euclidean rational model, not an original-action
Yang--Mills estimate. Two symmetric idempotent matrices give projections P,Q;
the balanced operator is B=PQP and the forward word is W=QP. For c=4, the
actual coupled recurrence has positive reverse-energy margin at its first
auxiliary vector and negative margin at its second. Thus an order-one check
alone cannot replace the order-by-order auxiliary hypothesis in the
Chebyshev norm consumer. No physical gap or Yang--Mills counterexample is
claimed.
-/

import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.RationalChebyshevAuxiliaryObstruction

set_option autoImplicit false

open YMGap.Constructive

local infix:50 " ≈ " => Q'.eqv

abbrev Vec4 := Fin 4 → Q'
abbrev Mat4 := Fin 4 → Fin 4 → Q'

def r9_25 : Q' := Q'.mkPos 9 25 (by decide)
def r12_25 : Q' := Q'.mkPos 12 25 (by decide)
def r16_25 : Q' := Q'.mkPos 16 25 (by decide)

def P : Mat4 := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1
  | 2, 2 => 1
  | _, _ => 0

def Q : Mat4 := fun i j =>
  match i.val, j.val with
  | 0, 0 => r9_25
  | 0, 1 => r12_25
  | 1, 0 => r12_25
  | 1, 1 => r16_25
  | 2, 2 => r16_25
  | 2, 3 => r12_25
  | 3, 2 => r12_25
  | 3, 3 => r9_25
  | _, _ => 0

def matMul (A B : Mat4) : Mat4 := fun i j =>
  A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j

def matVec (A : Mat4) (x : Vec4) : Vec4 := fun i =>
  A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2 + A i 3 * x 3

def vecAdd (x y : Vec4) : Vec4 := fun i => x i + y i
def vecSub (x y : Vec4) : Vec4 := fun i => x i + -y i
def vecZero : Vec4 := fun _ => 0

def normSq (x : Vec4) : Q' := x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3

/-! `P` is `diag(1,0,1,0)`. `Q` is the direct sum of the rank-one
orthogonal projections onto `(3/5,4/5)` and `(4/5,3/5)`. These finite
coefficient laws are the projection certificate. -/

theorem P_symmetric : ∀ i j, P i j ≈ P j i := by decide
theorem P_idempotent : ∀ i j, matMul P P i j ≈ P i j := by decide
theorem Q_symmetric : ∀ i j, Q i j ≈ Q j i := by decide
theorem Q_idempotent : ∀ i j, matMul Q Q i j ≈ Q i j := by decide

def W : Mat4 := matMul Q P
def B : Mat4 := matMul P (matMul Q P)

def balancedDiagonal : Mat4 := fun i j =>
  match i.val, j.val with
  | 0, 0 => r9_25
  | 2, 2 => r16_25
  | _, _ => 0

theorem balanced_matrix_pin : ∀ i j, B i j ≈ balancedDiagonal i j := by decide

/-- The displayed balanced matrix really is the Gram matrix of W. -/
theorem balanced_is_gram : ∀ i j, matMul (fun k l => W l k) W i j ≈ B i j := by
  decide

def x : Vec4 := fun i =>
  match i.val with
  | 0 => 1
  | 2 => Q'.mkPos 1 2 (by decide)
  | _ => 0

def X : Mat4 := fun i j => 4 * B i j + -((if i = j then 1 else 0 : Q'))

def coupledStep (t u : Vec4) : Vec4 × Vec4 :=
  let u' := vecAdd t (matVec X u)
  (vecSub (matVec X u') u, u')

def coupledState : Nat → Vec4 × Vec4
  | 0 => (x, vecZero)
  | n + 1 => coupledStep (coupledState n).1 (coupledState n).2

def reverseMargin (u : Vec4) : Q' :=
  2 * normSq (matVec W u) + -(4 * normSq (matVec B u))

def u1 : Vec4 := (coupledState 1).2
def u2 : Vec4 := (coupledState 2).2

theorem first_auxiliary_value : ∀ i, u1 i ≈ x i := by decide

theorem second_auxiliary_value : ∀ i, u2 i ≈
    (match i.val with
     | 0 => Q'.mkPos 22 25 (by decide)
     | 2 => Q'.mkPos 39 25 (by decide)
     | _ => 0) := by decide

theorem first_reverse_margin : reverseMargin u1 ≈ Q'.mkPos 14 125 (by decide) := by
  decide

theorem second_reverse_margin : reverseMargin u2 ≈ -(Q'.mkPos 55944 78125 (by decide)) := by
  decide

theorem first_margin_positive : (0 : Q') < reverseMargin u1 := by decide

theorem second_margin_negative : reverseMargin u2 < (0 : Q') := by decide

/-- The inequalities concern the actual recurrence vectors and projection
words above, not just the signs of separately supplied rational numbers. -/
theorem first_pass_later_failure :
    4 * normSq (matVec B u1) ≤ 2 * normSq (matVec W u1) ∧
      ¬ (4 * normSq (matVec B u2) ≤ 2 * normSq (matVec W u2)) := by
  decide

/-- Even for this single pair of orthogonal projections, success at the
first auxiliary does not imply success at the second. -/
theorem no_first_to_second_bootstrap :
    ¬ (4 * normSq (matVec B u1) ≤ 2 * normSq (matVec W u1) →
      4 * normSq (matVec B u2) ≤ 2 * normSq (matVec W u2)) := by
  intro h
  exact first_pass_later_failure.2 (h first_pass_later_failure.1)

/-- The first-component norm test likewise passes at one and fails at two. -/
theorem first_component_norm_tests :
    normSq (coupledState 1).1 ≤ normSq x ∧
      ¬ (normSq (coupledState 2).1 ≤ normSq x) := by
  decide

#print axioms P_symmetric
#print axioms P_idempotent
#print axioms Q_symmetric
#print axioms Q_idempotent
#print axioms balanced_matrix_pin
#print axioms balanced_is_gram
#print axioms first_auxiliary_value
#print axioms second_auxiliary_value
#print axioms first_reverse_margin
#print axioms second_reverse_margin
#print axioms first_margin_positive
#print axioms second_margin_negative
#print axioms first_pass_later_failure
#print axioms no_first_to_second_bootstrap
#print axioms first_component_norm_tests

end YMGap.Continuum.RationalChebyshevAuxiliaryObstruction
