/-
# Constructive three-by-three adjugate identities

This module proves both division-free adjugate identities for an arbitrary
three-by-three matrix over `Q'`.  The proof is one kernel-checked reflective
polynomial calculation with nine independent entries; no determinant
nonvanishing premise is used.
-/

import YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge

namespace YMGap.Continuum.SU2ThreeByThreeAdjugate

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2SpinOneCentralHahnDeterminant

/-- The classical adjugate, written using constructive rational operations. -/
def adj3 (A : Nat -> Nat -> Q') : Nat -> Nat -> Q'
  | 0, 0 => A 1 1 * A 2 2 + -(A 1 2 * A 2 1)
  | 0, 1 => A 0 2 * A 2 1 + -(A 0 1 * A 2 2)
  | 0, _ => A 0 1 * A 1 2 + -(A 0 2 * A 1 1)
  | 1, 0 => A 1 2 * A 2 0 + -(A 1 0 * A 2 2)
  | 1, 1 => A 0 0 * A 2 2 + -(A 0 2 * A 2 0)
  | 1, _ => A 0 2 * A 1 0 + -(A 0 0 * A 1 2)
  | _, 0 => A 1 0 * A 2 1 + -(A 1 1 * A 2 0)
  | _, 1 => A 0 1 * A 2 0 + -(A 0 0 * A 2 1)
  | _, _ => A 0 0 * A 1 1 + -(A 0 1 * A 1 0)

/-- Three-term matrix multiplication. -/
def matMul3 (A B : Nat -> Nat -> Q') (r c : Nat) : Q' :=
  A r 0 * B 0 c + A r 1 * B 1 c + A r 2 * B 2 c

private def entryExpr (r c : Nat) : PolyExpr := .var (3 * r + c)

private def adj3Expr (A : Nat -> Nat -> PolyExpr) : Nat -> Nat -> PolyExpr
  | 0, 0 => .add (.mul (A 1 1) (A 2 2)) (.neg (.mul (A 1 2) (A 2 1)))
  | 0, 1 => .add (.mul (A 0 2) (A 2 1)) (.neg (.mul (A 0 1) (A 2 2)))
  | 0, _ => .add (.mul (A 0 1) (A 1 2)) (.neg (.mul (A 0 2) (A 1 1)))
  | 1, 0 => .add (.mul (A 1 2) (A 2 0)) (.neg (.mul (A 1 0) (A 2 2)))
  | 1, 1 => .add (.mul (A 0 0) (A 2 2)) (.neg (.mul (A 0 2) (A 2 0)))
  | 1, _ => .add (.mul (A 0 2) (A 1 0)) (.neg (.mul (A 0 0) (A 1 2)))
  | _, 0 => .add (.mul (A 1 0) (A 2 1)) (.neg (.mul (A 1 1) (A 2 0)))
  | _, 1 => .add (.mul (A 0 1) (A 2 0)) (.neg (.mul (A 0 0) (A 2 1)))
  | _, _ => .add (.mul (A 0 0) (A 1 1)) (.neg (.mul (A 0 1) (A 1 0)))

private def matMul3Expr (A B : Nat -> Nat -> PolyExpr) (r c : Nat) : PolyExpr :=
  .add (.add (.mul (A r 0) (B 0 c)) (.mul (A r 1) (B 1 c)))
    (.mul (A r 2) (B 2 c))

private def det3Expr (A : Nat -> Nat -> PolyExpr) : PolyExpr :=
  .add
    (.add
      (.mul (A 0 0)
        (.add (.mul (A 1 1) (A 2 2)) (.neg (.mul (A 1 2) (A 2 1)))))
      (.neg
        (.mul (A 0 1)
          (.add (.mul (A 1 0) (A 2 2)) (.neg (.mul (A 1 2) (A 2 0)))))))
    (.mul (A 0 2)
      (.add (.mul (A 1 0) (A 2 1)) (.neg (.mul (A 1 1) (A 2 0)))))

private def zeroExpr : PolyExpr := .const 0

private def rightProductExpr (r c : Nat) : PolyExpr :=
  matMul3Expr entryExpr (adj3Expr entryExpr) r c

private def leftProductExpr (r c : Nat) : PolyExpr :=
  matMul3Expr (adj3Expr entryExpr) entryExpr r c

private def diagonalExpr (r c : Nat) : PolyExpr :=
  if r = c then det3Expr entryExpr else zeroExpr

private theorem right00 : normalize (rightProductExpr 0 0) = normalize (diagonalExpr 0 0) := by decide
private theorem right01 : normalize (rightProductExpr 0 1) = normalize (diagonalExpr 0 1) := by decide
private theorem right02 : normalize (rightProductExpr 0 2) = normalize (diagonalExpr 0 2) := by decide
private theorem right10 : normalize (rightProductExpr 1 0) = normalize (diagonalExpr 1 0) := by decide
private theorem right11 : normalize (rightProductExpr 1 1) = normalize (diagonalExpr 1 1) := by decide
private theorem right12 : normalize (rightProductExpr 1 2) = normalize (diagonalExpr 1 2) := by decide
private theorem right20 : normalize (rightProductExpr 2 0) = normalize (diagonalExpr 2 0) := by decide
private theorem right21 : normalize (rightProductExpr 2 1) = normalize (diagonalExpr 2 1) := by decide
private theorem right22 : normalize (rightProductExpr 2 2) = normalize (diagonalExpr 2 2) := by decide

private theorem left00 : normalize (leftProductExpr 0 0) = normalize (diagonalExpr 0 0) := by decide
private theorem left01 : normalize (leftProductExpr 0 1) = normalize (diagonalExpr 0 1) := by decide
private theorem left02 : normalize (leftProductExpr 0 2) = normalize (diagonalExpr 0 2) := by decide
private theorem left10 : normalize (leftProductExpr 1 0) = normalize (diagonalExpr 1 0) := by decide
private theorem left11 : normalize (leftProductExpr 1 1) = normalize (diagonalExpr 1 1) := by decide
private theorem left12 : normalize (leftProductExpr 1 2) = normalize (diagonalExpr 1 2) := by decide
private theorem left20 : normalize (leftProductExpr 2 0) = normalize (diagonalExpr 2 0) := by decide
private theorem left21 : normalize (leftProductExpr 2 1) = normalize (diagonalExpr 2 1) := by decide
private theorem left22 : normalize (leftProductExpr 2 2) = normalize (diagonalExpr 2 2) := by decide

private def matrixEnv (A : Nat -> Nat -> Q') (j : Nat) : Q' :=
  match j with
  | 0 => A 0 0
  | 1 => A 0 1
  | 2 => A 0 2
  | 3 => A 1 0
  | 4 => A 1 1
  | 5 => A 1 2
  | 6 => A 2 0
  | 7 => A 2 1
  | _ => A 2 2

private theorem right_cell (A : Nat -> Nat -> Q') (r c : Nat)
    (hr : r < 3) (hc : c < 3) :
    (matMul3 A (adj3 A) r c).eqv (if r = c then det3 A else 0) := by
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hr' with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl
  all_goals
    first
    | have h := poly_identity_of_normal_eq _ _ right00 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ right01 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ right02 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ right10 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ right11 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ right12 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ right20 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ right21 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ right22 (matrixEnv A)
      simpa [rightProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h

private theorem left_cell (A : Nat -> Nat -> Q') (r c : Nat)
    (hr : r < 3) (hc : c < 3) :
    (matMul3 (adj3 A) A r c).eqv (if r = c then det3 A else 0) := by
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hr' with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl
  all_goals
    first
    | have h := poly_identity_of_normal_eq _ _ left00 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ left01 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ left02 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ left10 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ left11 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ left12 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ left20 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ left21 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h
    | have h := poly_identity_of_normal_eq _ _ left22 (matrixEnv A)
      simpa [leftProductExpr, diagonalExpr, matMul3Expr, adj3Expr, entryExpr,
        det3Expr, zeroExpr, matrixEnv, matMul3, adj3, det3, eval] using h

/-- Right division-free inverse identity `A * adj(A) = det(A) I`. -/
theorem mul_adjugate (A : Nat -> Nat -> Q') (r c : Nat)
    (hr : r < 3) (hc : c < 3) :
    (matMul3 A (adj3 A) r c).eqv (if r = c then det3 A else 0) :=
  right_cell A r c hr hc

/-- Left division-free inverse identity `adj(A) * A = det(A) I`. -/
theorem adjugate_mul (A : Nat -> Nat -> Q') (r c : Nat)
    (hr : r < 3) (hc : c < 3) :
    (matMul3 (adj3 A) A r c).eqv (if r = c then det3 A else 0) :=
  left_cell A r c hr hc

end YMGap.Continuum.SU2ThreeByThreeAdjugate

#print axioms YMGap.Continuum.SU2ThreeByThreeAdjugate.adj3
#print axioms YMGap.Continuum.SU2ThreeByThreeAdjugate.matMul3
#print axioms YMGap.Continuum.SU2ThreeByThreeAdjugate.mul_adjugate
#print axioms YMGap.Continuum.SU2ThreeByThreeAdjugate.adjugate_mul
