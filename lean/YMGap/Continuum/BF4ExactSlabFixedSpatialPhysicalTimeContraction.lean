/-
# Actual physical time contracts the intrinsic reflected seminorm

The same-object sum-of-times law identifies the diagonal at n with the
mixed moment at 2*n. Reflection positivity of the signed difference gives
the midpoint inequality. The computed coefficient cap is independent of
lag. Bounded midpoint doubling therefore proves contraction with constant
one, without a supplied OS-norm bound or strict-gap envelope.

Linearity gives squared-distance nonexpansiveness and radical preservation.
The literal normalized unit is fixed, and every even physical advance has
nonnegative quadratic form. One-step positivity, a strict vacuum-complement
gap, cutoff removal and the continuum/physical mass-gap theorem are not
asserted. Nome, spatial width and retained cutoff remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap
import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference
import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit
import YMGap.Continuum.BoundedMidpointDoublingEventual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit

/-- The actual translated reflected diagonal, with its existing CReal data. -/
def timeNorm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (stage : Nat) : CReal :=
  pairing hw0 hw1 width (advanceSpan n xs) (advanceSpan n xs) stage

theorem timeNorm_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (hx : Physical width xs) (stage : Nat) :
    leEv (ofQ' 0) (timeNorm hw0 hw1 width n xs stage) :=
  pairing_self_nonnegative hw0 hw1 width (advanceSpan n xs) (advanceSpan_physical n xs hx) stage

/-- The rational ceiling contains no physical lag. It is a scalar cap,
not itself a bound relative to the original reflected norm. -/
theorem timeNorm_bounded {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (stage : Nat) :
    leEv (timeNorm hw0 hw1 width n xs stage) (ofQ' (uniformCap width xs xs)) :=
  (pairing_relabel_bounds hw0 hw1 width (fun d => d+n) (fun d => d+n) xs xs stage).2

/-- Reflection positivity and exact time balance supply the entire midpoint
family consumed below; it is not assumed as an operator hypothesis. -/
theorem timeNorm_midpoint {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (hx : Physical width xs) (stage : Nat) :
    leEv (mul (ofQ' 2) (timeNorm hw0 hw1 width n xs stage))
      (add (timeNorm hw0 hw1 width 0 xs stage) (timeNorm hw0 hw1 width (2*n) xs stage)) := by
  have hm : Equiv (timeNorm hw0 hw1 width n xs stage)
      (pairing hw0 hw1 width xs (advanceSpan (2*n) xs) stage) := by
    simpa only [timeNorm, Nat.two_mul] using
      pairing_time_sum hw0 hw1 width n n xs xs hx hx stage
  have hb := pairing_midpoint_bound hw0 hw1 width xs (advanceSpan (2*n) xs)
    hx (advanceSpan_physical (2*n) xs hx) stage
  exact leEv_trans (leEv_of_equiv (TrigSignedAdd.mul_congr_right hm))
    (by simpa only [timeNorm, advanceSpan_zero] using hb)

/-- Bounded midpoint doubling turns the absolute scalar cap into actual
OS-seminorm contraction, without dividing by a possibly zero norm. -/
theorem timeNorm_le_anchor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (hx : Physical width xs) (stage : Nat) :
    leEv (timeNorm hw0 hw1 width n xs stage) (timeNorm hw0 hw1 width 0 xs stage) :=
  BoundedMidpointDoublingEventual.bounded_midpointDoubling_leEv_anchor
    (fun k => timeNorm hw0 hw1 width k xs stage) (uniformCap width xs xs)
    (fun k => timeNorm_bounded hw0 hw1 width k xs stage)
    (timeNorm_nonnegative hw0 hw1 width 0 xs hx stage)
    (fun k => timeNorm_midpoint hw0 hw1 width k xs hx stage) n

theorem pairing_advance_contraction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (hx : Physical width xs) (stage : Nat) :
    leEv (pairing hw0 hw1 width (advanceSpan n xs) (advanceSpan n xs) stage)
      (pairing hw0 hw1 width xs xs stage) := by
  simpa only [timeNorm, advanceSpan_zero] using timeNorm_le_anchor hw0 hw1 width n xs hx stage

/-- The same physical advance is nonexpansive on every signed difference. -/
theorem difference_contraction {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs ys : DistanceSpan)
    (hx : Physical width xs) (hy : Physical width ys) (stage : Nat) :
    leEv (pairing hw0 hw1 width (difference (advanceSpan n xs) (advanceSpan n ys))
      (difference (advanceSpan n xs) (advanceSpan n ys)) stage)
      (pairing hw0 hw1 width (difference xs ys) (difference xs ys) stage) := by
  simpa only [difference, advanceSpan_append, advanceSpan_scale] using
    pairing_advance_contraction hw0 hw1 width n (difference xs ys) (physical_difference hx hy) stage

theorem advance_preserves_radical {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (hx : Physical width xs) (stage : Nat)
    (hnull : Equiv (pairing hw0 hw1 width xs xs stage) (ofQ' 0)) :
    Equiv (pairing hw0 hw1 width (advanceSpan n xs) (advanceSpan n xs) stage) (ofQ' 0) :=
  equiv_of_leEv_leEv
    (leEv_trans (pairing_advance_contraction hw0 hw1 width n xs hx stage) (leEv_of_equiv hnull))
    (timeNorm_nonnegative hw0 hw1 width n xs hx stage)

/-- Site reflection proves positivity at every even advance; this does
not assert positivity of the one-step operator. -/
theorem pairing_even_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (hx : Physical width xs) (stage : Nat) :
    leEv (ofQ' 0) (pairing hw0 hw1 width xs (advanceSpan (2*n) xs) stage) := by
  have hm := pairing_time_sum hw0 hw1 width n n xs xs hx hx stage
  rw [← Nat.two_mul] at hm
  exact leEv_trans (timeNorm_nonnegative hw0 hw1 width n xs hx stage) (leEv_of_equiv hm)

/-- The original constant observable is fixed by every genuine physical advance. -/
theorem advanceSpan_unit (n : Nat) : advanceSpan n unitSpan = unitSpan := rfl

/-- Its pairing with any physical observable is invariant under that
observable's physical time advance. This is not vacuum isolation. -/
theorem pairing_unit_invariant {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width n : Nat) (xs : DistanceSpan) (hx : Physical width xs) (stage : Nat) :
    Equiv (pairing hw0 hw1 width (advanceSpan n xs) unitSpan stage)
      (pairing hw0 hw1 width xs unitSpan stage) := by
  simpa only [advanceSpan_zero, Nat.add_zero, advanceSpan_unit] using
    pairing_time_sum hw0 hw1 width n 0 xs unitSpan hx (unit_physical width) stage

end YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.timeNorm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.timeNorm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.timeNorm_bounded
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.timeNorm_midpoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.timeNorm_le_anchor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.pairing_advance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.difference_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.advance_preserves_radical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.pairing_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.advanceSpan_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction.pairing_unit_invariant
