/-
# Computed positive SU(2) heat windows at every positive subunit nome

The proved finite-prefix floor and the explicit geometric-tail modulus give
one common depth for all rational class coordinates in [-1,1]. The lower
endpoint retains half the finite-prefix floor; the upper endpoint uses the
existing all-prefix squared-dimension majorant. All three are computed from
the nome alone, and no finite window estimate is supplied as a hypothesis.

These are actual `PointwiseHeatTailWindow` values for the original character
series. No bound on their upper/lower ratio by a prescribed bit budget is
asserted. In particular, this does not prove an AF window-spread estimate,
an interacting comparison, an OS transfer gap, or a continuum conclusion.
-/

import YMGap.Continuum.SU2PointwiseHeatStrictFloor
import YMGap.Continuum.SU2PointwiseHeatDynamicWindow
import YMGap.Continuum.BF4ExactSlabAllNomeTailInterval

namespace YMGap.Continuum.SU2PointwiseHeatPositiveWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
open YMGap.Continuum.SU2PointwiseHeatDynamicWindow
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval

local infix:50 " ≈ " => Q'.eqv

/-- Half the proved finite-prefix floor, reserved after paying the tail. -/
def lower (w : Q') : Q' := SU2PointwiseHeatStrictFloor.finiteFloor w * HalfPow.half

/-- Common shifted-prefix depth, independent of the class coordinate. -/
def depth (w : Q') : Nat :=
  max (SU2PointwiseHeatStrictFloor.finiteCutoff w)
    (spacingTailCauchyCutoff w (lower w))

/-- A nome-dependent ceiling for the selected prefix plus its closed tail. -/
def upper (w : Q') : Q' := prefixCap w + lower w

theorem lower_pos {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < lower w :=
  Q'.mul_pos (SU2PointwiseHeatStrictFloor.finiteFloor_pos hw0 hw1) (by decide)

theorem upper_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') ≤ upper w :=
  Q'.zero_le_add _ _ (prefixCap_nonnegative hw0) (Q'.le_of_lt (lower_pos hw0 hw1))

/-- The common depth pays precisely the positive lower-endpoint budget. -/
theorem tail_le_lower {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    spacingClosedTail w (depth w) ≤ lower w :=
  closedTail_small hw0 hw1 (lower w) (lower_pos hw0 hw1) (depth w)
    (Nat.le_max_right _ _)

/-- Every selected original prefix retains the old finite floor. -/
theorem finiteFloor_le_prefix {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    SU2PointwiseHeatStrictFloor.finiteFloor w ≤
      spacingPointwiseHeatPartial w x (depth w) := by
  apply SU2PointwiseHeatStrictFloor.finiteFloor_le_standardPointwiseHeatPartial
    hw0 hw1 hxLower hxUpper
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ _)

/-- The lower endpoint is uniform over the whole rational class-coordinate box. -/
theorem lower_le_prefix_sub_tail {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    lower w ≤ spacingPointwiseHeatPartial w x (depth w) +
      -spacingClosedTail w (depth w) := by
  have hsplit : lower w + lower w ≈ SU2PointwiseHeatStrictFloor.finiteFloor w :=
    Q'.eqv_trans _ _ _
      (Cheb.add_eqv_congr _ _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_comm_eqv _ _))
      (ExpNeg.two_halves _)
  apply BareAFDiagnostic.le_sub_of_add_le
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (tail_le_lower hw0 hw1) (Q'.le_refl' (lower w)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (finiteFloor_le_prefix hw0 hw1 hxLower hxUpper))

/-- The existing positive majorant bounds every chosen signed prefix. -/
theorem prefix_le_cap {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    spacingPointwiseHeatPartial w x (depth w) ≤ prefixCap w :=
  Q'.le_trans' _ _ _
    (ExpNeg.finSum_le_finSum_of_termwise _ _
      (fun n => (pointwiseHeatTerm_twoSided (Q'.le_of_lt hw0) hxLower hxUpper n).2)
      (spacingLabelCutoff w + depth w))
    (majorant_prefix_bound hw0 hw1 _)

/-- The upper endpoint is uniform over the same rational box. -/
theorem prefix_add_tail_le_upper {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    spacingPointwiseHeatPartial w x (depth w) +
      spacingClosedTail w (depth w) ≤ upper w :=
  Q'.add_le_add (prefix_le_cap hw0 hw1 hxLower hxUpper) (tail_le_lower hw0 hw1)

/-- An actual positive finite-tail window, constructed without a window premise. -/
def window {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    PointwiseHeatTailWindow w x (lower w) (upper w) where
  M := depth w
  lower_le_prefix_sub_tail := lower_le_prefix_sub_tail hw0 hw1 hxLower hxUpper
  prefix_add_tail_le_upper := prefix_add_tail_le_upper hw0 hw1 hxLower hxUpper

/-- Every coordinate uses literally the same computed approximation depth. -/
theorem window_depth {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    (window hw0 hw1 hxLower hxUpper).M = depth w := rfl

#print axioms lower
#print axioms depth
#print axioms upper
#print axioms lower_pos
#print axioms upper_nonnegative
#print axioms tail_le_lower
#print axioms finiteFloor_le_prefix
#print axioms lower_le_prefix_sub_tail
#print axioms prefix_le_cap
#print axioms prefix_add_tail_le_upper
#print axioms window
#print axioms window_depth

end YMGap.Continuum.SU2PointwiseHeatPositiveWindow
