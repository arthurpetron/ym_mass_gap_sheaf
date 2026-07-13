/-
# A division-free Hahn inverse for every spin-half tensor shell

For `V_(1/2) tensor V_(n/2)`, each interior weight shell has two source
coordinates.  Order zero reads their sum; order one reads
`(n+1-s) * right - s * left`.  The corresponding two-by-two matrix has
determinant `n+1`.  This module proves its adjugate identities for arbitrary
`n,s`, using the checked reflective rational ring normaliser, and then proves
the required natural-coefficient sum.  No reciprocal or choice is used.

This is the first infinite-label simultaneous-channel inversion mechanism;
the next module connects it to the actual Cayley transvectants.
-/

import YMGap.Continuum.SU2SpinHalfSpinOneDirectSumCoordinateBasis
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2SpinHalfShellHahnInverse

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser

/-- The two channel coordinates on one spin-half weight shell. -/
def shellForward (A B left right : Q') : Q' × Q' :=
  (left + right, B * right + -(A * left))

/-- The division-free adjugate reconstruction. -/
def shellAdjugate (A B top lower : Q') : Q' × Q' :=
  (B * top + -lower, A * top + lower)

private def leftAdjForwardLHS : PolyExpr :=
  .add
    (.mul (.var 1) (.add (.var 2) (.var 3)))
    (.neg (.add (.mul (.var 1) (.var 3))
      (.neg (.mul (.var 0) (.var 2)))))

private def leftAdjForwardRHS : PolyExpr :=
  .mul (.add (.var 1) (.var 0)) (.var 2)

private theorem leftAdjForward_normal :
    normalize leftAdjForwardLHS = normalize leftAdjForwardRHS := by decide

private def rightAdjForwardLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.var 2) (.var 3)))
    (.add (.mul (.var 1) (.var 3))
      (.neg (.mul (.var 0) (.var 2))))

private def rightAdjForwardRHS : PolyExpr :=
  .mul (.add (.var 0) (.var 1)) (.var 3)

private theorem rightAdjForward_normal :
    normalize rightAdjForwardLHS = normalize rightAdjForwardRHS := by decide

private def shellEnv (A B left right : Q') : Nat → Q'
  | 0 => A
  | 1 => B
  | 2 => left
  | _ => right

/-- First adjugate coordinate after the forward shell map. -/
theorem shellAdjugate_forward_left (A B left right : Q') :
    (shellAdjugate A B (shellForward A B left right).1
      (shellForward A B left right).2).1.eqv
      ((B + A) * left) := by
  have h := poly_identity_of_normal_eq leftAdjForwardLHS leftAdjForwardRHS
    leftAdjForward_normal (shellEnv A B left right)
  simpa only [shellAdjugate, shellForward, shellEnv, eval,
    Prod.fst, Prod.snd] using h

/-- Second adjugate coordinate after the forward shell map. -/
theorem shellAdjugate_forward_right (A B left right : Q') :
    (shellAdjugate A B (shellForward A B left right).1
      (shellForward A B left right).2).2.eqv
      ((A + B) * right) := by
  have h := poly_identity_of_normal_eq rightAdjForwardLHS rightAdjForwardRHS
    rightAdjForward_normal (shellEnv A B left right)
  simpa only [shellAdjugate, shellForward, shellEnv, eval,
    Prod.fst, Prod.snd] using h

/-- On a physical shell the two natural coefficients sum exactly to `n+1`. -/
theorem shellCoeff_sum (n s : Nat) (hs : s ≤ n + 1) :
    (Q'.ofNat (n + 1 - s) + Q'.ofNat s).eqv (Q'.ofNat (n + 1)) := by
  have h := Q'.ofNat_add_eqv (n + 1 - s) s
  have hsum : n + 1 - s + s = n + 1 := Nat.sub_add_cancel hs
  rw [hsum] at h
  exact Q'.eqv_symm h

/-- The left source coordinate is recovered up to the positive determinant
`n+1` on every physical shell. -/
theorem spinHalfShell_left_scaled (n s : Nat) (hs : s ≤ n + 1)
    (left right : Q') :
    (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
      (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).1
      (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).2).1.eqv
      (Q'.ofNat (n + 1) * left) := by
  refine Q'.eqv_trans _
    ((Q'.ofNat (n + 1 - s) + Q'.ofNat s) * left) _
    (shellAdjugate_forward_left _ _ _ _) ?_
  exact Q'.mul_eqv_congr_right _ _ left (shellCoeff_sum n s hs)

/-- The right source coordinate is recovered up to the same determinant. -/
theorem spinHalfShell_right_scaled (n s : Nat) (hs : s ≤ n + 1)
    (left right : Q') :
    (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
      (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).1
      (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).2).2.eqv
      (Q'.ofNat (n + 1) * right) := by
  refine Q'.eqv_trans _
    ((Q'.ofNat s + Q'.ofNat (n + 1 - s)) * right) _
    (shellAdjugate_forward_right _ _ _ _) ?_
  have hsum := shellCoeff_sum n s hs
  have hcomm := Q'.add_comm_eqv (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
  exact Q'.mul_eqv_congr_right _ _ right
    (Q'.eqv_trans _ _ _ hcomm hsum)

end YMGap.Continuum.SU2SpinHalfShellHahnInverse

#print axioms YMGap.Continuum.SU2SpinHalfShellHahnInverse.shellAdjugate_forward_left
#print axioms YMGap.Continuum.SU2SpinHalfShellHahnInverse.shellAdjugate_forward_right
#print axioms YMGap.Continuum.SU2SpinHalfShellHahnInverse.shellCoeff_sum
#print axioms YMGap.Continuum.SU2SpinHalfShellHahnInverse.spinHalfShell_left_scaled
#print axioms YMGap.Continuum.SU2SpinHalfShellHahnInverse.spinHalfShell_right_scaled
