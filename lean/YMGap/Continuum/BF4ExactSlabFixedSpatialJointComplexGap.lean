/-
# Positive discrete time and the SAME strict gap on complex joint states

Both real components of complex vacuum orthogonality are retained. The
actual real time-positivity theorem and the actual fixed-width norm-decay
estimate therefore apply to every complex state, not just embedded real
states. No spatial-union carrier or conditional BF4 dynamics is substituted.

The rate still depends on nome and spatial width. This is not a complete
complex Hilbert/OS interface, a continuous Hamiltonian, a scaling-uniform
bound, or continuum Yang--Mills. Complex scalars keep explicit Cauchy data.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap (completed_twoStep_form_gap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse (completedInner_time_sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation (time_norm_decay)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_add_zero rc_sub_zero rc_sub_self)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "VC" => ComplexCarrier hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "I" => inner hw0 hw1 width
local notation "E" => embedReal hw0 hw1 width
local notation "CT" => complexTime hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width

/-- Embed the existing unit, rather than supplying a new vacuum. -/
def complexUnit : VC := E U

local notation "CU" => complexUnit hw0 hw1 width

theorem complexUnit_fixed (n : Nat) : CT n CU = CU := by
  unfold complexUnit
  rw [complexTime_embedReal, jointCompletedUnit_fixed]

theorem inner_unit_left (x : VC) : I CU x = (B x.1 U, B x.2 U) := by
  simp only [inner, complexUnit, embedReal, completedInner_zero_left,
    rc_add_zero, rc_sub_zero]
  rw [completedInner_symm hw0 hw1 width U x.1,
    completedInner_symm hw0 hw1 width U x.2]

/-- Vanishing complex vacuum coefficient means BOTH real coefficients vanish. -/
theorem complex_orthogonal_iff (x : VC) :
    I CU x = (RCzero, RCzero) ↔ B x.1 U = RCzero ∧ B x.2 U = RCzero := by
  rw [inner_unit_left]
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext h1 h2

theorem complexTime_preserves_orthogonal (n : Nat) (x : VC)
    (hx : I CU x = (RCzero, RCzero)) : I CU (CT n x) = (RCzero, RCzero) := by
  obtain ⟨h1, h2⟩ := (complex_orthogonal_iff hw0 hw1 width x).mp hx
  apply (complex_orthogonal_iff hw0 hw1 width (CT n x)).mpr
  exact ⟨completedTime_preserves_orthogonal hw0 hw1 width n x.1 h1,
    completedTime_preserves_orthogonal hw0 hw1 width n x.2 h2⟩

theorem inner_time_sum (m n : Nat) (x y : VC) :
    I (CT m x) (CT n y) = I x (CT (m+n) y) := by
  simp only [inner, complexTime, completedInner_time_sum]

/-- Exact complex-valued even-lag norm identity, not only its real part. -/
theorem inner_even_diagonal (n : Nat) (x : VC) :
    I x (CT (2*n) x) = I (CT n x) (CT n x) := by
  simpa only [Nat.two_mul] using (inner_time_sum hw0 hw1 width n n x x).symm

/-- Symmetry cancels the imaginary cross term; the original-action positivity
theorem supplies the real sign, including at odd discrete times. -/
theorem inner_time_nonnegative (n : Nat) (x : VC) :
    RCnonneg (I x (CT n x)).1 ∧ (I x (CT n x)).2 = RCzero := by
  constructor
  · have h := RCadd_le_add (completedInner_time_nonnegative hw0 hw1 width n x.1)
      (completedInner_time_nonnegative hw0 hw1 width n x.2)
    rw [rc_add_zero] at h
    exact h
  · change RCsub (B x.1 (jointCompletedTime hw0 hw1 width n x.2))
      (B x.2 (jointCompletedTime hw0 hw1 width n x.1)) = RCzero
    rw [← completedInner_time_balance hw0 hw1 width n x.1 x.2,
      completedInner_symm hw0 hw1 width (jointCompletedTime hw0 hw1 width n x.1) x.2,
      rc_sub_self]

/-- The original q^n controls EVERY complex vacuum-orthogonal state. -/
theorem complexTime_norm_decay (x : VC) (hx : I CU x = (RCzero, RCzero)) (n : Nat) :
    RCle (I (CT n x) (CT n x)).1 (RCscale (q^n) (I x x).1) := by
  obtain ⟨h1, h2⟩ := (complex_orthogonal_iff hw0 hw1 width x).mp hx
  have h := RCadd_le_add (time_norm_decay hw0 hw1 width x.1 h1 n)
    (time_norm_decay hw0 hw1 width x.2 h2 n)
  rw [← RCscale_RCadd] at h
  exact h

theorem complex_even_form_decay (x : VC) (hx : I CU x = (RCzero, RCzero)) (n : Nat) :
    RCle (I x (CT (2*n) x)).1 (RCscale (q^n) (I x x).1) := by
  rw [inner_even_diagonal]
  exact complexTime_norm_decay hw0 hw1 width x hx n

/-- The fixed-width strict form estimate, without a new complex gap premise. -/
theorem complex_twoStep_form_gap (x : VC) (hx : I CU x = (RCzero, RCzero)) :
    RCle (I x (CT 2 x)).1 (RCscale q (I x x).1) := by
  obtain ⟨h1, h2⟩ := (complex_orthogonal_iff hw0 hw1 width x).mp hx
  have h1' := completed_twoStep_form_gap hw0 hw1 width x.1 h1
  have h2' := completed_twoStep_form_gap hw0 hw1 width x.2 h2
  change RCle (B x.1 (jointCompletedTime hw0 hw1 width 2 x.1))
    (RCscale q (B x.1 x.1)) at h1'
  change RCle (B x.2 (jointCompletedTime hw0 hw1 width 2 x.2))
    (RCscale q (B x.2 x.2)) at h2'
  have h := RCadd_le_add h1' h2'
  rw [← RCscale_RCadd] at h
  exact h

#print axioms complexUnit
#print axioms complexUnit_fixed
#print axioms inner_unit_left
#print axioms complex_orthogonal_iff
#print axioms complexTime_preserves_orthogonal
#print axioms inner_time_sum
#print axioms inner_even_diagonal
#print axioms inner_time_nonnegative
#print axioms complexTime_norm_decay
#print axioms complex_even_form_decay
#print axioms complex_twoStep_form_gap

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexGap
