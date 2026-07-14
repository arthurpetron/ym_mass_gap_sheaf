/-
# A genuine physical row outside the current lowest-inner-shell closure

The outer-closure theorem for the Omega correction assumes `j+l=q.p`.
This module exhibits a smallest nontrivial physical coordinate satisfying all
of its other bulk and total-shell hypotheses but not that inner-shell
equality.  The desired correction and final Jacobi row are both evaluated
exactly there, proving that the residual is coverage rather than a false
identity.
-/

import YMGap.Continuum.SU2OrderedRacahRightJacobiIntervalFence

namespace YMGap.Continuum.SU2OrderedRacahRightJacobiOffShellFence

open YMGap.Constructive
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionThreeCarrier
open YMGap.Continuum.SU2OrderedRacahRightJacobiInduction

/-- Lower neighbour in the physical `(2,2,2,2)` three-channel block. -/
def offShellLower : FixedRightCGChannel 2 2 2 2 where
  p := 0
  p_le := by decide
  r := 2
  r_le := by decide
  degree_eq := by decide

/-- Middle order-one channel in the physical `(2,2,2,2)` block. -/
def offShellMiddle : FixedRightCGChannel 2 2 2 2 where
  p := 1
  p_le := by decide
  r := 1
  r_le := by decide
  degree_eq := by decide

/-- Upper neighbour in the physical `(2,2,2,2)` three-channel block. -/
def offShellUpper : FixedRightCGChannel 2 2 2 2 where
  p := 2
  p_le := by decide
  r := 0
  r_le := by decide
  degree_eq := by decide

/-- The coordinate `(i,j,l,s)=(1,1,1,1)` satisfies every physical,
adjacency, strict-coordinate, total-shell, and outer-interval premise used by
the current closure, but it lies one level above `j+l=q.p`. -/
theorem off_shell_coordinate_has_all_other_outer_closure_data :
    0 < offShellMiddle.p ∧
    offShellMiddle.p = offShellLower.p + 1 ∧
    offShellUpper.p = offShellMiddle.p + 1 ∧
    0 < (1 : Nat) ∧ 0 < (1 : Nat) ∧ 0 < (1 : Nat) ∧
    1 + offShellMiddle.r + offShellMiddle.p = 1 + 1 + 1 ∧
    offShellMiddle.p < 2 ∧ offShellMiddle.p < 2 ∧
    offShellMiddle.r ≤ 1 ∧ 1 ≤ (2 : Nat) ∧
    ¬ (1 + 1 = offShellMiddle.p) := by
  decide

/-- The exact Omega correction identity is true at the uncovered coordinate.
Thus the missing general theorem is not repairing a counterexample; it must
extend the proof beyond the lowest inner shell. -/
theorem off_shell_correction_identity_is_true :
    OmegaCorrectionThreeCarrierAt
      offShellLower offShellMiddle offShellUpper 1 1 1 1 := by
  unfold OmegaCorrectionThreeCarrierAt offShellLower offShellMiddle
    offShellUpper
  decide

/-- The final transpose-Jacobi row is likewise exactly true at this physical
off-shell coordinate. -/
theorem off_shell_right_transpose_jacobi_row_is_true :
    RightTransposeJacobiAt
      offShellLower offShellMiddle offShellUpper 1 1 1 1 := by
  unfold RightTransposeJacobiAt offShellLower offShellMiddle offShellUpper
  decide

end YMGap.Continuum.SU2OrderedRacahRightJacobiOffShellFence

#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiOffShellFence.off_shell_coordinate_has_all_other_outer_closure_data
#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiOffShellFence.off_shell_correction_identity_is_true
#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiOffShellFence.off_shell_right_transpose_jacobi_row_is_true
