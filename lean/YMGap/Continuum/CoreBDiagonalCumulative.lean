/-
# Core-B diagonal cumulative normal form

The all-row residual scout identified the diagonal cumulative, rather than
termwise residual positivity, as the promising low-region target.  This file
banks the exact arbitrary-length index normal form consumed by that strategy:

  C(s,r,n) ≈ sum_{t<n} R(s+t, r+n-1-t).

It is an algebraic/indexing identity only.  The coefficient-mass inequality
suggested by the exact scout remains open and no Core-B frontier type is
inhabited here.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.Continuum.CoreBStructuralRecurrence

namespace YMGap.Continuum.CoreBDiagonalCumulative

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CoreBStructuralRecurrence
open YMGap.Continuum.CubeRatioBounds

local infix:50 " ≈ " => Q'.eqv

/-- The closed finite-sum presentation of a length-`n` diagonal residual. -/
def diagonalResidualSum (w h : Q') (s r n : Nat) : Q' :=
  fsum (fun t => boundaryResidualAt w h (s + t) (r + n - 1 - t)) n

/-- Exact arbitrary-length diagonal normal form.

This strengthens the already-banked length-two identity to the index scheme
used by the diagonal-cumulative scout. -/
theorem cumulativeResidual_eq_diagonalResidualSum
    (w h : Q') (s r : Nat) : ∀ n,
    cumulativeResidual w h s r n ≈ diagonalResidualSum w h s r n
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
      simp only [cumulativeResidual, diagonalResidualSum, fsum_succ]
      have ih := cumulativeResidual_eq_diagonalResidualSum w h s (r + 1) n
      have hterms : ∀ t,
          boundaryResidualAt w h (s + t) (r + 1 + n - 1 - t) ≈
            boundaryResidualAt w h (s + t) (r + (n + 1) - 1 - t) := by
        intro t
        exact Q'.eqv_of_eq (by
          congr 1
          omega)
      have hprefix : cumulativeResidual w h s (r + 1) n ≈
          fsum
            (fun t => boundaryResidualAt w h (s + t)
              (r + (n + 1) - 1 - t)) n :=
        Q'.eqv_trans _ _ _ ih
          (fsum_eqv_congr _ _ hterms n)
      rw [show r + (n + 1) - 1 - n = r by omega]
      exact Q'.add_eqv_congr_right _ _ _ hprefix

/-- The scout's length formula as executable data.  Proving that this length
pays the all-index low-region adverse mass is the next analytic obligation. -/
def predictedPaymentLength (s r : Nat) : Nat :=
  max 1 (s - r - 2)

theorem predictedPaymentLength_positive (s r : Nat) :
    1 ≤ predictedPaymentLength s r := by
  exact Nat.le_max_left _ _

#print axioms diagonalResidualSum
#print axioms cumulativeResidual_eq_diagonalResidualSum
#print axioms predictedPaymentLength
#print axioms predictedPaymentLength_positive

end YMGap.Continuum.CoreBDiagonalCumulative
