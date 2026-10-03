/-
# The constructed half-anchor preimage has least norm

Every exact half-time preimage of the EXISTING normalized anchor is the
constructed preimage plus a vector in the original half-time kernel. Actual
time symmetry makes this difference orthogonal to the constructed preimage.
Its squared norm therefore cannot be smaller.

The original completion, action, normalizer and ambient fringe kernel are
unchanged. No transfer inverse, injectivity, macro ratio, uniform norm floor,
changing-family estimate or physical-time calibration is assumed or proved.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedAnchorContinuity
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BF4WilsonAllNomeLinearLaws

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicMinimalPreimage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner completedInner_symm completedInner_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedInner_time_balance)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedSub completedNeg completedZero)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedAdd_comm completedNeg_add completedAdd_zero completedSub_self)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedTime_sub completedInner_zero_right completedInner_add_left completedInner_add_right)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (completedRealSmul completedInner_realSmul_left)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation (dyadicUnitExcitation)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedBondAnchor
  (anchorNormalizer anchorNormalizerCauchy normalizedVacuumExcitation)
open YMGap.Continuum.BF4WilsonAllNomeDyadicNormalizedAnchorContinuity
  (halfAnchorPreimage halfAnchorPreimage_pin)

private theorem rc_mul_zero (a : RC) : RCmul a RCzero = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_zero_eqv (A.approx n)))

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "Zero" => completedZero hw0 hw1 width
local notation "h" => side scale/2
local notation "y0" => halfAnchorPreimage hw0 hw1 scale width hwidth
local notation "z" => Subtype.val (normalizedVacuumExcitation hw0 hw1 scale width hwidth)
local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "alpha" => anchorNormalizer hw0 hw1 scale width hwidth
local notation "alphaCauchy" => anchorNormalizerCauchy hw0 hw1 scale width hwidth

attribute [local irreducible] anchorNormalizer normalizedVacuumExcitation dyadicUnitExcitation
  completedInner completedTime

private theorem reconstruct (x y : V) : A x (Sub y x) = y := by
  unfold completedSub
  rw [← completedAdd_assoc, completedAdd_comm hw0 hw1 x y,
    completedAdd_assoc, completedAdd_comm hw0 hw1 x (completedNeg hw0 hw1 x),
    completedNeg_add, completedAdd_zero]

/-- The difference from the literal constructed preimage lies in the actual
half-time kernel and is orthogonal to that preimage. -/
theorem halfAnchorPreimage_difference_orthogonal (y : V) (hs2 : 2 ≤ side scale)
    (hy : T h y = z) : B y0 (Sub y y0) = RCzero := by
  let d := Sub y y0
  have hkernel : T h d = Zero := by
    change T h (Sub y y0) = Zero
    rw [completedTime_sub, hy, halfAnchorPreimage_pin hw0 hw1 scale width hwidth hs2,
      completedSub_self]
  have hscaled : B y0 d = RCmul (Quotient.mk crealSetoid alpha) (B (T h u) d) := by
    change B (completedRealSmul hw0 hw1 alpha alphaCauchy (T h u)) d = _
    exact completedInner_realSmul_left hw0 hw1 alpha alphaCauchy (T h u) d
  change B y0 d = RCzero
  rw [hscaled, completedInner_time_balance, hkernel, completedInner_zero_right, rc_mul_zero]

/-- Exact Pythagoras on the SAME original completion, including its kernel. -/
theorem halfAnchorPreimage_norm_decomposition (y : V) (hs2 : 2 ≤ side scale)
    (hy : T h y = z) :
    B y y = RCadd (B y0 y0) (B (Sub y y0) (Sub y y0)) := by
  let d := Sub y y0
  have ho : B y0 d = RCzero :=
    halfAnchorPreimage_difference_orthogonal hw0 hw1 scale width hwidth y hs2 hy
  have hor : B d y0 = RCzero := (completedInner_symm hw0 hw1 d y0).trans ho
  have hr : A y0 d = y := reconstruct hw0 hw1 width y0 y
  calc
    B y y = B (A y0 d) (A y0 d) := congrArg (fun v : V => B v v) hr.symm
    _ = RCadd (B y0 y0) (B d d) := by
      rw [completedInner_add_left, completedInner_add_right, completedInner_add_right,
        ho, hor, rc_add_zero, rc_zero_add]

/-- Any exact preimage has at least the constructed preimage's squared norm;
no injectivity or inverse transfer is needed. -/
theorem halfAnchorPreimage_norm_minimal (y : V) (hs2 : 2 ≤ side scale)
    (hy : T h y = z) : RCle (B y0 y0) (B y y) := by
  have hnon := RCadd_le_add (RCle_refl (B y0 y0))
    (completedInner_nonnegative hw0 hw1 (Sub y y0))
  rw [rc_add_zero] at hnon
  rw [halfAnchorPreimage_norm_decomposition hw0 hw1 scale width hwidth y hs2 hy]
  exact hnon

#print axioms halfAnchorPreimage_difference_orthogonal
#print axioms halfAnchorPreimage_norm_decomposition
#print axioms halfAnchorPreimage_norm_minimal

end YMGap.Continuum.BF4WilsonAllNomeDyadicMinimalPreimage
