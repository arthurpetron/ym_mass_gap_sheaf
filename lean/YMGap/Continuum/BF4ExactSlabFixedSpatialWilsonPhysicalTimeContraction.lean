/-
# Actual Wilson physical time is nonexpansive

The original-action sum-of-times identity and reflection positivity give
the midpoint inequality for the actual intrinsic Wilson diagonal. Its
computed expression cap is unchanged by every physical time advance.
Bounded midpoint doubling therefore proves contraction with constant one,
without division by a possibly zero norm or an assumed operator bound.

Literal compatibility with differences gives squared-distance contraction
and radical preservation on the SAME carrier. Every even physical advance
has nonnegative quadratic form. These are fixed-spacing small-nome SU(2)
results after the existing regulator limits. They assert neither one-step
positivity nor a strict vacuum-complement gap nor a continuum mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap
import YMGap.Continuum.BoundedMidpointDoublingEventual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicCap
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Actual physical advance changes the radius but not the expression cap. -/
theorem intrinsicCap_advance {base : Nat} (n : Nat) (x : IntrinsicExpression base) :
    intrinsicCap (advance n x) = intrinsicCap x := rfl

attribute [local irreducible] intrinsicForm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "F" => intrinsicForm hw0 hw1 hsmall hd hs hb
local notation "D" => distSq hw0 hw1 hsmall hd hs hb

/-- The actual intrinsic reflected diagonal, retaining its existing CReal data. -/
def timeNorm (n : Nat) (x : IntrinsicExpression base) : CReal :=
  F (advance n x) (advance n x)

theorem timeNorm_nonnegative (n : Nat) (x : IntrinsicExpression base) :
    leEv (ofQ' 0) (timeNorm hw0 hw1 hsmall hd hs hb n x) :=
  intrinsicForm_nonnegative hw0 hw1 hsmall hd hs hb (advance n x)

/-- This absolute scalar ceiling contains no time lag or expression radius. -/
theorem timeNorm_bounded (n : Nat) (x : IntrinsicExpression base) :
    leEv (timeNorm hw0 hw1 hsmall hd hs hb n x)
      (ofQ' (intrinsicCap x*intrinsicCap x)) := by
  simpa only [timeNorm, intrinsicCap_advance] using
    intrinsicForm_upper_bound hw0 hw1 hsmall hd hs hb (advance n x) (advance n x)

/-- Same-object time balance and positivity supply the whole midpoint family. -/
theorem timeNorm_midpoint (n : Nat) (x : IntrinsicExpression base) :
    leEv (mul (ofQ' 2) (timeNorm hw0 hw1 hsmall hd hs hb n x))
      (add (timeNorm hw0 hw1 hsmall hd hs hb 0 x)
        (timeNorm hw0 hw1 hsmall hd hs hb (2*n) x)) := by
  have hm : Equiv (timeNorm hw0 hw1 hsmall hd hs hb n x)
      (F x (advance (2*n) x)) := by
    simpa only [timeNorm, Nat.two_mul] using
      intrinsicForm_time_sum hw0 hw1 hsmall hd hs hb n n x x
  have hmid := intrinsicForm_midpoint_bound hw0 hw1 hsmall hd hs hb x (advance (2*n) x)
  exact leEv_trans (leEv_of_equiv (TrigSignedAdd.mul_congr_right hm))
    (by simpa only [timeNorm, advance_zero] using hmid)

/-- Bounded midpoint doubling removes the expression-dependent cap without
requiring a positive original norm or any uniform representative threshold. -/
theorem timeNorm_le_anchor (n : Nat) (x : IntrinsicExpression base) :
    leEv (timeNorm hw0 hw1 hsmall hd hs hb n x)
      (timeNorm hw0 hw1 hsmall hd hs hb 0 x) :=
  BoundedMidpointDoublingEventual.bounded_midpointDoubling_leEv_anchor
    (fun k => timeNorm hw0 hw1 hsmall hd hs hb k x) (intrinsicCap x*intrinsicCap x)
    (fun k => timeNorm_bounded hw0 hw1 hsmall hd hs hb k x)
    (timeNorm_nonnegative hw0 hw1 hsmall hd hs hb 0 x)
    (fun k => timeNorm_midpoint hw0 hw1 hsmall hd hs hb k x) n

theorem intrinsicForm_advance_contraction (n : Nat) (x : IntrinsicExpression base) :
    leEv (F (advance n x) (advance n x)) (F x x) := by
  simpa only [timeNorm, advance_zero] using
    timeNorm_le_anchor hw0 hw1 hsmall hd hs hb n x

/-- The literal physical advance contracts the actual squared distance. -/
theorem distSq_advance_contraction (n : Nat) (x y : IntrinsicExpression base) :
    leEv (D (advance n x) (advance n y)) (D x y) := by
  simpa only [distSq, advance_difference] using
    intrinsicForm_advance_contraction hw0 hw1 hsmall hd hs hb n (difference x y)

theorem advance_preserves_radical (n : Nat) (x : IntrinsicExpression base)
    (hnull : Equiv (F x x) (ofQ' 0)) :
    Equiv (F (advance n x) (advance n x)) (ofQ' 0) :=
  equiv_of_leEv_leEv
    (leEv_trans (intrinsicForm_advance_contraction hw0 hw1 hsmall hd hs hb n x)
      (leEv_of_equiv hnull))
    (timeNorm_nonnegative hw0 hw1 hsmall hd hs hb n x)

/-- Null-equivalent inputs remain null-equivalent under actual time advance. -/
theorem advance_preserves_null (n : Nat) (x y : IntrinsicExpression base)
    (hnull : Equiv (D x y) czero) :
    Equiv (D (advance n x) (advance n y)) czero :=
  equiv_of_leEv_leEv
    (leEv_trans (distSq_advance_contraction hw0 hw1 hsmall hd hs hb n x y)
      (leEv_of_equiv hnull))
    (distSq_nonnegative hw0 hw1 hsmall hd hs hb (advance n x) (advance n y))

/-- Site reflection gives every even-time quadratic form, not one-step positivity. -/
theorem intrinsicForm_even_nonnegative (n : Nat) (x : IntrinsicExpression base) :
    leEv (ofQ' 0) (F x (advance (2*n) x)) := by
  have hm := intrinsicForm_time_sum hw0 hw1 hsmall hd hs hb n n x x
  rw [← Nat.two_mul] at hm
  exact leEv_trans (timeNorm_nonnegative hw0 hw1 hsmall hd hs hb n x) (leEv_of_equiv hm)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.intrinsicCap_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.timeNorm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.timeNorm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.timeNorm_bounded
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.timeNorm_midpoint
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.timeNorm_le_anchor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.intrinsicForm_advance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.distSq_advance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.advance_preserves_radical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.advance_preserves_null
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction.intrinsicForm_even_nonnegative
