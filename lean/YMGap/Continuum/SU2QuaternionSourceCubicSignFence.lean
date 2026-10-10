/-
# Opposite signs in the finite one-link source cubic

At the existing half-nome one-link fixture, the two certified positive
sources have opposite signs for the signed cubic correction. Both source
centers are already zero, so mean subtraction does not repair a universal
sign-only cancellation claim. This is a finite one-link obstruction only;
it is not a BF4 counterexample or a statement about the interacting
four-dimensional marginal.
-/

import YMGap.Continuum.SU2QuaternionSourceDefectSignFence
import YMGap.Continuum.SU2QuaternionCyclicSourceShift
import YMGap.Continuum.SU2QuaternionCyclicSecondOrder

namespace YMGap.Continuum.SU2QuaternionSourceCubicSignFence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionAngularOnlyEnergyFence (half fundamental)
open YMGap.Continuum.SU2QuaternionSourceDefectSignFence
  (sourcePlus sourceMinus sourceCenter plusMass_positive minusMass_positive
    plusCenter_zero minusCenter_zero)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceCubic)

local infix:50 " ≈ " => Q'.eqv

/-- Exact cubic value for the certified positive `sourcePlus` at the
fundamental test and the existing half-nome. -/
theorem plus_sourceCubic_value :
    sourceCubic 0 half sourcePlus fundamental ≈
      -(Q'.mkPos 36097 524288 (by decide)) := by decide +kernel

/-- Exact cubic value for the certified positive `sourceMinus` at the
fundamental test and the existing half-nome. -/
theorem minus_sourceCubic_value :
    sourceCubic 0 half sourceMinus fundamental ≈
      Q'.mkPos 945919 524288 (by decide) := by decide +kernel

/-- The `sourcePlus` cubic correction is strictly negative. -/
theorem plus_sourceCubic_negative :
    sourceCubic 0 half sourcePlus fundamental < 0 :=
  Q'.lt_of_le_of_lt (Q'.le_of_eqv plus_sourceCubic_value) (by decide)

private theorem positive_of_eqv {a b : Q'} (h : a ≈ b)
    (hb : (0 : Q') < b) : (0 : Q') < a := by
  have hn : ¬ a ≤ (0 : Q') := by
    intro ha
    exact (Int.not_le.mpr hb) (Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) ha)
  exact Int.not_le.mp hn

/-- The `sourceMinus` cubic correction is strictly positive. -/
theorem minus_sourceCubic_positive :
    (0 : Q') < sourceCubic 0 half sourceMinus fundamental :=
  positive_of_eqv minus_sourceCubic_value (by decide)

/-- These are the already-certified centers of the same two source
densities; no centering premise is introduced by this finite sign fence. -/
theorem sourceCenters_zero :
    sourceCenter sourcePlus plusMass_positive ≈ 0 ∧
      sourceCenter sourceMinus minusMass_positive ≈ 0 :=
  ⟨plusCenter_zero, minusCenter_zero⟩

end YMGap.Continuum.SU2QuaternionSourceCubicSignFence

#print axioms YMGap.Continuum.SU2QuaternionSourceCubicSignFence.plus_sourceCubic_value
#print axioms YMGap.Continuum.SU2QuaternionSourceCubicSignFence.minus_sourceCubic_value
#print axioms YMGap.Continuum.SU2QuaternionSourceCubicSignFence.plus_sourceCubic_negative
#print axioms YMGap.Continuum.SU2QuaternionSourceCubicSignFence.minus_sourceCubic_positive
#print axioms YMGap.Continuum.SU2QuaternionSourceCubicSignFence.sourceCenters_zero
