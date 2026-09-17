/-
# Centered-window compatibility of the same original Wilson spatial limit

The exact finite padding identity increases BOTH external time distances
on the smaller-window side. Its already constructed joint cutoff/time
modulus controls that shifted sequence. At every fixed spatial margin the
two original joint limits therefore agree. Their proved spatial convergence
then identifies the existing spatial limits, despite different window caps,
support budgets, row moduli and CReal representative reindexings.

Both observable offsets and the reflection center move by d. Changing the
center alone is not asserted. Nome and physical spacing are fixed; the
existing small-nome guards remain. This is scalar/form chart compatibility,
not a new state, completed carrier, transfer bound or continuum theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (centeredExpression centered_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenter_mapOffsets)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local infix:50 " ≈ " => Q'.eqv

private theorem shift_within_outer {width : Nat} (L d : Nat)
    (e : WindowExpression width) (he : Within L e) : Within (L+2*d) (shift d e) :=
  within_mono (by omega : L+d ≤ L+2*d) _ (shift_within L d e he)

private theorem shift_within_centered {width : Nat} (H d : Nat)
    (e : WindowExpression width) (he : Within (2*H) e) :
    Within (2*(H+d)) (shift d e) :=
  within_mono (by omega : 2*H+d ≤ 2*(H+d)) _ (shift_within (2*H) d e he)

/-- SAME original finite law, with both boundary distances redistributed. -/
theorem originalScalar_centered_shift {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L d : Nat) (e : WindowExpression width) (he : Within L e)
    (stage m n : Nat) :
    originalWindowScalar hw0 hw1 (L+2*d) (shift d e) stage m n ≈
      originalWindowScalar hw0 hw1 L e stage (m+d) (n+d) :=
  Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 (L+2*d) (shift d e)
      (shift_within_outer L d e he) stage m n)
    (Q'.eqv_trans _ _ _
      (windowRatio_centered_shift hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) m L n d e he)
      (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L e he stage (m+d) (n+d))))

private theorem originalJoint_offset_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L d : Nat) (e : WindowExpression width) (he : Within L e) :
    ConvergesTo (fun s => ofQ' (originalWindowScalar hw0 hw1 L e s (s+d) (s+d)))
      (originalJointLimit hw0 hw1 L e he) := by
  intro epsilon heps
  refine ⟨jointModulus hw0 hw1 L e epsilon, fun s hs =>
    ⟨jointModulus hw0 hw1 L e epsilon, fun i hi => ?_⟩⟩
  exact originalJoint_approx hw0 hw1 L e he epsilon heps s (s+d) i
    (Nat.le_trans (Nat.le_max_right _ _) hs)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hs) (Nat.le_add_right s d)) hi

/-- Existing original joint limits agree; no new time or cutoff estimate. -/
theorem originalJoint_centered_shift {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L d : Nat) (e : WindowExpression width) (he : Within L e) :
    Equiv (originalJointLimit hw0 hw1 (L+2*d) (shift d e) (shift_within_outer L d e he))
      (originalJointLimit hw0 hw1 L e he) :=
  Equiv_of_limit_of_equal
    (fun s => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => originalScalar_centered_shift hw0 hw1 L d e he s s s))
    (originalJoint_diagonal_converges hw0 hw1 (L+2*d) (shift d e) (shift_within_outer L d e he))
    (originalJoint_offset_converges hw0 hw1 L d e he)

private theorem centered_shift {base : Nat} (r d : Nat) (e : WindowExpression base) :
    centeredExpression r (shift d e) = shift d (centeredExpression r e) :=
  recenter_mapOffsets _ (fun offset => offset+d) e

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0<base)

/-- Changing a valid observation window changes its representative modulus,
not the same centered limiting scalar. Spatial row moduli may depend on r. -/
theorem spatialLimit_centered_shift (H d : Nat) (e : WindowExpression base)
    (he : Within (2*H) e) :
    Equiv (spatialLimit hw0 hw1 (H+d) (shift d e) (shift_within_centered H d e he)
      hsmall hd hs hb)
      (spatialLimit hw0 hw1 H e he hsmall hd hs hb) := by
  apply Equiv_of_limit_of_equal
    (hA := jointLimits_spatial_converge hw0 hw1 (H+d) (shift d e)
      (shift_within_centered H d e he) hsmall hd hs hb)
    (hB := jointLimits_spatial_converge hw0 hw1 H e he hsmall hd hs hb)
  intro r
  have h := originalJoint_centered_shift hw0 hw1 (2*H) d (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he)
  have hlen : 2*H+2*d = 2*(H+d) := by omega
  simpa only [hlen, centered_shift] using h

/-- BOTH operands move with the reflection plane, preserving the complete
mixed reflected product in the existing spatial limit. -/
theorem spatialReflected_centered_shift (H d : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) :
    Equiv (spatialLimit hw0 hw1 (H+d)
      (.mul (mirror (H+d) (shift d e)) (shift d f))
      ⟨mirror_within (H+d) (shift d e),
        within_mono (by omega : H+d ≤ 2*(H+d)) _ (shift_within H d f hf)⟩ hsmall hd hs hb)
      (spatialLimit hw0 hw1 H (.mul (mirror H e) f)
        ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩ hsmall hd hs hb) := by
  have h := spatialLimit_centered_shift hw0 hw1 hsmall hd hs hb H d (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩
  have hp : WindowExpression.mul (mirror (H+d) (shift d e)) (shift d f) =
      shift d (.mul (mirror H e) f) := by
    change WindowExpression.mul (mirror (H+d) (shift d e)) (shift d f) =
      WindowExpression.mul (shift d (mirror H e)) (shift d f)
    rw [mirror_shift H d e he]
  simpa only [← hp] using h

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit.originalScalar_centered_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit.originalJoint_centered_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit.spatialLimit_centered_shift
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit.spatialReflected_centered_shift
