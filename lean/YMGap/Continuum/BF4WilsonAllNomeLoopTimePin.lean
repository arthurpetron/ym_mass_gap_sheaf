/-
# Actual Wilson time moments in the SAME all-nome reflected form

The literal fundamental loop is an existing intrinsic Wilson expression of
radius zero. Two time advances have reflected pairing equal to the original
joint lag moment at the sum of their distances from the reflection plane.
Consequently the already proved squared-increment estimate controls the loss
of this SAME reflected pairing, including the explicit dyadic square family.

This is a dense reflected-form identity, not an embedding into the separate
face-span completion. No completed operator, centered norm floor, coupling
trajectory, cross-scale convergence, or continuum survival is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeReflectedForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
import YMGap.Continuum.BF4DyadicWilsonSquare

namespace YMGap.Continuum.BF4WilsonAllNomeLoopTimePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_zero)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.BF4DyadicWilsonSquare

attribute [local irreducible] originalJointLimit lagMoment timeIncrement

/-- The actual fundamental Wilson word at the reflection slice. -/
def loopState {width : Nat} (loop : SourceLoop width) : IntrinsicExpression width :=
  ⟨0, .loop 0 loop 1, Nat.le_refl 0⟩

/-- Both time advances belong to the same literal-width reflected form.
This also supplies the two-lag pin needed for finite linear combinations. -/
theorem time_pairing_lag {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (m n : Nat) :
    Equiv (intrinsicForm hw0 hw1 (advance m (loopState loop))
      (advance n (loopState loop))) (lagMoment hw0 hw1 loop (m+n)) := by
  let H := max m n
  have hm : m ≤ H := Nat.le_max_left _ _
  have hn : n ≤ H := Nat.le_max_right _ _
  have hmirror : 2*H-(H-m) = H+m := by omega
  have hlag : (H+m)-(H-n) = m+n := by omega
  have h := pair_lag hw0 hw1 loop (2*H) (H-n) (H+m) (by omega) (by omega)
  simpa only [intrinsicForm, commonForm, loopState, advance, chart, shift,
    mirror, mapOffsets, Nat.zero_add, hmirror, hlag, H] using h

theorem pairing_lag {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    Equiv (intrinsicForm hw0 hw1 (loopState loop) (advance n (loopState loop)))
      (lagMoment hw0 hw1 loop n) := by
  simpa only [advance_zero, Nat.zero_add] using time_pairing_lag hw0 hw1 loop 0 n

theorem norm_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) :
    Equiv (intrinsicForm hw0 hw1 (loopState loop) (loopState loop))
      (lagMoment hw0 hw1 loop 0) := by
  simpa only [advance_zero] using pairing_lag hw0 hw1 loop 0

/-- Exact identification of the original squared increment with twice the
loss of the SAME reflected pairing. It is not a relative-energy bound. -/
theorem timeIncrement_reflected_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (n : Nat) :
    Equiv (timeIncrement hw0 hw1 loop n)
      (mul (ofQ' 2) (sub (intrinsicForm hw0 hw1 (loopState loop) (loopState loop))
        (intrinsicForm hw0 hw1 (loopState loop) (advance n (loopState loop))))) :=
  (timeIncrement_pin hw0 hw1 loop n).trans
    (Pivot2.mul_congr_right (equiv_sub (norm_pin hw0 hw1 loop).symm
      (pairing_lag hw0 hw1 loop n).symm))

/-- The geometric family's existing absolute scalar estimate now has a
proved SAME-observable reflected-form consumer, at each width and nome. -/
theorem dyadic_reflected_loss_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width) :
    let x := loopState (paddedSquare scale width hwidth)
    leEv (mul (ofQ' 2) (sub (intrinsicForm hw0 hw1 x x)
      (intrinsicForm hw0 hw1 x (advance (side scale) x))))
      (ofQ' ((384 : Q') * (Q'.ofNat (side scale) *
        (Q'.ofNat (side scale)*Q'.ofNat (side scale))) * (1 + -w))) :=
  leEv_trans (leEv_of_equiv
    (timeIncrement_reflected_pin hw0 hw1 (paddedSquare scale width hwidth) (side scale)).symm)
    (unitTimeIncrement_bound hw0 hw1 scale width hwidth)

#print axioms loopState
#print axioms time_pairing_lag
#print axioms pairing_lag
#print axioms norm_pin
#print axioms timeIncrement_reflected_pin
#print axioms dyadic_reflected_loss_bound

end YMGap.Continuum.BF4WilsonAllNomeLoopTimePin
