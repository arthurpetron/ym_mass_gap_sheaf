/-
# Constructive three-term uniqueness for the signed Racah coordinate

The ordered Racah residual is a normalization problem for a signed Schur
coordinate.  The faithful factorial object `racahKernel6` is instead its
Gram-normalized square.  This file isolates the finite-Jacobi uniqueness
principle needed by a Casimir/Hahn proof and records, on the fundamental
block, why the squared kernel itself cannot be substituted for the signed
coordinate in that recurrence.

The uniqueness theorem is division-free: a strictly positive forward pivot
is cancelled only after both recurrence equations have been compared.  One
boundary value suffices because the endpoint equation has no predecessor
term; every later value is then forced by the interior three-term equation.
-/

import YMGap.Continuum.SixJKernel

namespace YMGap.Continuum.SU2RacahThreeTermUniqueness

open YMGap.Constructive
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

/-- A division-free forward presentation of a finite Jacobi recurrence.

At the left endpoint, `A 0 * x 1 = B 0 * x 0`.  At the next sites, the
three terms are `x (n+2)`, `x (n+1)`, and `x n`.  This indexing makes the
single-boundary-value uniqueness statement constructive and avoids an
artificial value at index `-1`. -/
def SatisfiesForwardThreeTerm
    (A B C x : Nat → Q') : Prop :=
  A 0 * x 1 ≈ B 0 * x 0 ∧
  ∀ n : Nat,
    A (n + 1) * x (n + 2) ≈
      B (n + 1) * x (n + 1) + C (n + 1) * x n

/-- The same recurrence restricted to the physical window `0..N`.  For the
one-point window the endpoint equation is not requested; for every larger
window it determines coordinate `1`, and the interior equation is requested
exactly where `n+2` is still physical. -/
def SatisfiesForwardThreeTermThrough
    (N : Nat) (A B C x : Nat → Q') : Prop :=
  (1 ≤ N → A 0 * x 1 ≈ B 0 * x 0) ∧
  ∀ n : Nat, n + 2 ≤ N →
    A (n + 1) * x (n + 2) ≈
      B (n + 1) * x (n + 1) + C (n + 1) * x n

/-- **Finite one-boundary Jacobi uniqueness.**  Positivity is required only
for the pivots actually used inside `0..N`; no zero extension or recurrence
beyond the physical channel window is assumed. -/
theorem forwardThreeTermThrough_unique
    (N : Nat) (A B C x y : Nat → Q')
    (hA : ∀ n : Nat, n < N → (0 : Q') < A n)
    (hx : SatisfiesForwardThreeTermThrough N A B C x)
    (hy : SatisfiesForwardThreeTermThrough N A B C y)
    (hzero : x 0 ≈ y 0) :
    ∀ n : Nat, n ≤ N → x n ≈ y n := by
  have hpair : ∀ n : Nat, n + 1 ≤ N →
      x n ≈ y n ∧ x (n + 1) ≈ y (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro hN
        refine ⟨hzero, ?_⟩
        apply Q'.mul_left_cancel_of_pos (hA 0 (by omega))
        exact Q'.eqv_trans _ _ _ (hx.1 hN)
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (B 0) _ _ hzero)
            (Q'.eqv_symm (hy.1 hN)))
    | succ n ih =>
        intro hN
        have hprev := ih (by omega)
        refine ⟨hprev.2, ?_⟩
        apply Q'.mul_left_cancel_of_pos (hA (n + 1) (by omega))
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using
          Q'.eqv_trans _ _ _ (hx.2 n (by omega))
            (Q'.eqv_trans _
              (B (n + 1) * y (n + 1) + C (n + 1) * y n) _
              (Q'.add_eqv_congr'
                (Q'.mul_eqv_congr_left (B (n + 1)) _ _ hprev.2)
                (Q'.mul_eqv_congr_left (C (n + 1)) _ _ hprev.1))
              (Q'.eqv_symm (hy.2 n (by omega))))
  intro n hn
  cases n with
  | zero => exact hzero
  | succ n => exact (hpair n (by omega)).2

/-- **One-boundary constructive Jacobi uniqueness.**  If every forward pivot
is strictly positive, two solutions of the same endpoint/interior recurrence
which agree at the left boundary agree at every index. -/
theorem forwardThreeTerm_unique
    (A B C x y : Nat → Q')
    (hA : ∀ n : Nat, (0 : Q') < A n)
    (hx : SatisfiesForwardThreeTerm A B C x)
    (hy : SatisfiesForwardThreeTerm A B C y)
    (hzero : x 0 ≈ y 0) :
    ∀ n : Nat, x n ≈ y n := by
  have hone : x 1 ≈ y 1 := by
    apply Q'.mul_left_cancel_of_pos (hA 0)
    exact Q'.eqv_trans _ _ _ hx.1
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (B 0) _ _ hzero)
        (Q'.eqv_symm hy.1))
  have hpair : ∀ n : Nat, x n ≈ y n ∧ x (n + 1) ≈ y (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨hzero, hone⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        apply Q'.mul_left_cancel_of_pos (hA (n + 1))
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using
          Q'.eqv_trans _ _ _ (hx.2 n)
            (Q'.eqv_trans _
              (B (n + 1) * y (n + 1) + C (n + 1) * y n) _
              (Q'.add_eqv_congr'
                (Q'.mul_eqv_congr_left (B (n + 1)) _ _ ih.2)
                (Q'.mul_eqv_congr_left (C (n + 1)) _ _ ih.1))
              (Q'.eqv_symm (hy.2 n)))
  intro n
  exact (hpair n).1

/-! ## Fundamental normalization fence -/

private def oneThird : Q' := Q'.mkPos 1 3 (by decide)
private def oneQuarter : Q' := Q'.mkPos 1 4 (by decide)

/-- The squared inverse-Schur entry obtained from the faithful fundamental
kernel after the exact left/right Gram ratio is applied.  In contraction-order
coordinates, `p=0` has ratio `4/12=1/3` and right label `f=2`, while `p=1`
has ratio `4/4=1` and right label `f=0`.

Only these two physical orders are relevant; the zero extension is included
so the object can be tested against a recurrence on `Nat`. -/
def fundamentalSingletInverseSquareByOrder (p : Nat) : Q' :=
  if p = 0 then oneThird * racahKernel6 1 1 1 1 0 2
  else if p = 1 then racahKernel6 1 1 1 1 0 0
  else 0

/-- Both fundamental inverse-coordinate squares are `1/4`. -/
theorem fundamentalSingletInverseSquare_values :
    fundamentalSingletInverseSquareByOrder 0 ≈ oneQuarter ∧
    fundamentalSingletInverseSquareByOrder 1 ≈ oneQuarter := by
  decide

/-- **Squared-kernel recurrence fence.**  The signed fundamental singlet row
has the endpoint sign relation `x 1 = -x 0`; its Gram-normalized squares are
both `1/4` and therefore violate that relation.  Consequently a Casimir/Hahn
uniqueness proof must recur on a signed weight-corrected factorial amplitude
and square only after identification.  Applying the signed recurrence
directly to `racahKernel6` (or to its Gram-corrected square above) is a false
normalization route. -/
theorem squaredKernel_cannot_satisfy_signed_fundamental_boundary :
    ¬ (fundamentalSingletInverseSquareByOrder 1 ≈
        -fundamentalSingletInverseSquareByOrder 0) := by
  decide

end YMGap.Continuum.SU2RacahThreeTermUniqueness

#print axioms YMGap.Continuum.SU2RacahThreeTermUniqueness.forwardThreeTerm_unique
#print axioms YMGap.Continuum.SU2RacahThreeTermUniqueness.forwardThreeTermThrough_unique
#print axioms YMGap.Continuum.SU2RacahThreeTermUniqueness.fundamentalSingletInverseSquare_values
#print axioms YMGap.Continuum.SU2RacahThreeTermUniqueness.squaredKernel_cannot_satisfy_signed_fundamental_boundary
