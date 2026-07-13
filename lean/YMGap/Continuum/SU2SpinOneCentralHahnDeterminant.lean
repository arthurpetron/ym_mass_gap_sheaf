/-
# The spin-one central-shell Hahn determinant

The first genuinely multi-order shell has three source columns and the three
contraction rows `0,1,2`.  After writing `N` for the second label and `T` for
the total shell weight, its constant/affine/quadratic Hahn matrix has determinant

`2 * N * (N+1) * (N+2)`.

The shell variable cancels completely.  The identity is proved by the checked
reflective `Q'` normaliser, not by sampling labels.  A following bridge can
identify this symbolic matrix with `hahnEntry 2 n t` on the central physical
range and use the adjugate division-free.
-/

import YMGap.Continuum.SU2GeneralShellHahnMatrix
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2SpinOneCentralHahnDeterminant

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

/-- The symbolic three-by-three central-shell matrix. -/
def centralHahn (N T : Q') : Nat → Nat → Q'
  | 0, _ => 1
  | 1, 0 => -((2 : Q') * T)
  | 1, 1 => N + -((2 : Q') * T) + 2
  | 1, _ => (2 : Q') * (N + -T + 2)
  | _, 0 => (2 : Q') * T * (T + (-1 : Q'))
  | _, 1 => -((2 : Q') * (T + (-1 : Q')) * (N + -T + 1))
  | _, _ => (2 : Q') * (N + -T + 2) * (N + -T + 1)

/-- Leibniz determinant for a three-by-three `Q'` matrix, written with the
project's constructive addition/negation operations. -/
def det3 (A : Nat → Nat → Q') : Q' :=
  A 0 0 * (A 1 1 * A 2 2 + -(A 1 2 * A 2 1)) +
  -(A 0 1 * (A 1 0 * A 2 2 + -(A 1 2 * A 2 0))) +
  A 0 2 * (A 1 0 * A 2 1 + -(A 1 1 * A 2 0))

private def eN : PolyExpr := .var 0
private def eT : PolyExpr := .var 1
private def eTwo : PolyExpr := .const 2
private def eOne : PolyExpr := .const 1
private def eNegOne : PolyExpr := .const (-1)

private def centralHahnExpr : Nat → Nat → PolyExpr
  | 0, _ => eOne
  | 1, 0 => .neg (.mul eTwo eT)
  | 1, 1 => .add (.add eN (.neg (.mul eTwo eT))) eTwo
  | 1, _ => .mul eTwo (.add (.add eN (.neg eT)) eTwo)
  | _, 0 => .mul (.mul eTwo eT) (.add eT eNegOne)
  | _, 1 => .neg
      (.mul (.mul eTwo (.add eT eNegOne))
        (.add (.add eN (.neg eT)) eOne))
  | _, _ =>
      .mul (.mul eTwo (.add (.add eN (.neg eT)) eTwo))
        (.add (.add eN (.neg eT)) eOne)

private def det3Expr (A : Nat → Nat → PolyExpr) : PolyExpr :=
  .add
    (.add
      (.mul (A 0 0)
        (.add (.mul (A 1 1) (A 2 2)) (.neg (.mul (A 1 2) (A 2 1)))))
      (.neg
        (.mul (A 0 1)
          (.add (.mul (A 1 0) (A 2 2)) (.neg (.mul (A 1 2) (A 2 0)))))))
    (.mul (A 0 2)
      (.add (.mul (A 1 0) (A 2 1)) (.neg (.mul (A 1 1) (A 2 0)))))

private def centralDetExpr : PolyExpr := det3Expr centralHahnExpr

private def centralDetProductExpr : PolyExpr :=
  .mul
    (.mul (.mul eTwo eN) (.add eN eOne))
    (.add eN eTwo)

private theorem centralDet_normal :
    normalize centralDetExpr = normalize centralDetProductExpr := by decide

private def centralEnv (N T : Q') : Nat → Q'
  | 0 => N
  | _ => T

/-- Exact shell-independent determinant of the first multi-order Hahn matrix. -/
theorem centralHahn_det (N T : Q') :
    (det3 (centralHahn N T)).eqv
      ((((2 : Q') * N) * (N + 1)) * (N + 2)) := by
  have h := poly_identity_of_normal_eq centralDetExpr centralDetProductExpr
    centralDet_normal (centralEnv N T)
  simpa only [centralDetExpr, centralDetProductExpr, det3Expr,
    centralHahnExpr, centralHahn, det3, centralEnv, eN, eT, eTwo, eOne,
    eNegOne, eval] using h

/-- Specialization records explicitly that the determinant does not depend on
which central shell is chosen. -/
theorem centralHahn_det_shell_independent (N T U : Q') :
    (det3 (centralHahn N T)).eqv (det3 (centralHahn N U)) := by
  exact Q'.eqv_trans _ ((((2 : Q') * N) * (N + 1)) * (N + 2)) _
    (centralHahn_det N T) (Q'.eqv_symm (centralHahn_det N U))

end YMGap.Continuum.SU2SpinOneCentralHahnDeterminant

#print axioms YMGap.Continuum.SU2SpinOneCentralHahnDeterminant.centralHahn_det
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnDeterminant.centralHahn_det_shell_independent
