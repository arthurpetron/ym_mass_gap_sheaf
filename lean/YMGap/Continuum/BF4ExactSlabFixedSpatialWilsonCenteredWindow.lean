/-
# Exact centered inclusion of the same signed Wilson window

Increasing a half-window by d and every observable offset by d retains
all physical distances from the reflection plane. The complete signed
expression has one common source-coordinate lift, including both factors
of a reflected product. The existing finite left/right padding identities
then redistribute d transitions from each boundary into the window.

The finite ratio still has the SAME full chronological action, retained
heat cutoff and partition. This is not finite stationarity: the smaller
window has boundary distances m+d and n+d, not m and n. No new estimate,
limit, seminorm, completed carrier or mass-gap claim is introduced.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence (windowRatio_padded_congr)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHeadChainMiddleInsertion (liftBoundary_add)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- Shift only the named offsets; loop words, spins and coefficients are retained. -/
def shift {width : Nat} (d : Nat) (e : WindowExpression width) : WindowExpression width :=
  mapOffsets (fun offset => offset+d) e

theorem shift_zero {width : Nat} (e : WindowExpression width) : shift 0 e = e := by
  induction e <;> simp_all only [shift, mapOffsets, Nat.add_zero]

theorem shift_comp {width : Nat} (d s : Nat) (e : WindowExpression width) :
    shift s (shift d e) = shift (d+s) e := by
  induction e <;> simp_all only [shift, mapOffsets, Nat.add_assoc]

theorem shift_within {width : Nat} (L d : Nat) (e : WindowExpression width)
    (he : Within L e) : Within (L+d) (shift d e) :=
  within_mapOffsets (fun offset => offset+d)
    (fun _ h => Nat.add_le_add_right h d) e he

/-- The half-window guard prevents truncated subtraction from changing a time. -/
theorem mirror_shift {width : Nat} (H d : Nat) :
    ∀ e : WindowExpression width, Within H e →
    mirror (H+d) (shift d e) = shift d (mirror H e)
  | .one, _ => rfl
  | .loop offset value spin, he => by
      have ho : offset ≤ H := he
      have ht : 2*(H+d)-(offset+d) = (2*H-offset)+d := by omega
      change WindowExpression.loop (2*(H+d)-(offset+d)) value spin =
        WindowExpression.loop ((2*H-offset)+d) value spin
      rw [ht]
  | .add e f, he => by
      change WindowExpression.add (mirror (H+d) (shift d e)) (mirror (H+d) (shift d f)) =
        WindowExpression.add (shift d (mirror H e)) (shift d (mirror H f))
      rw [mirror_shift H d e he.1, mirror_shift H d f he.2]
  | .mul e f, he => by
      change WindowExpression.mul (mirror (H+d) (shift d e)) (mirror (H+d) (shift d f)) =
        WindowExpression.mul (shift d (mirror H e)) (shift d (mirror H f))
      rw [mirror_shift H d e he.1, mirror_shift H d f he.2]
  | .smul c e, he => by
      change WindowExpression.smul c (mirror (H+d) (shift d e)) =
        WindowExpression.smul c (shift d (mirror H e))
      rw [mirror_shift H d e he]

private theorem scheduled_shift (width offset d : Nat) (p : RatPoly) :
    liftBoundary ((offset+d)*(N width)) p =
      liftBoundary (d*(N width)) (liftBoundary (offset*(N width)) p) := by
  rw [Nat.add_mul, Nat.add_comm (offset*(N width)) (d*(N width)), liftBoundary_add]

/-- One lift of the complete signed source, including the padded unit case. -/
theorem source_shift {width : Nat} (blocks d : Nat) :
    ∀ e : WindowExpression width,
    PaddedPolynomialCoeffEqv blocks (sourcePolynomial (shift d e))
      (liftBoundary (d*(N width)) (sourcePolynomial e))
  | .one => (lift_one blocks (d*(N width))).symm
  | .loop offset value spin => by
      change PaddedPolynomialCoeffEqv blocks
        (liftBoundary ((offset+d)*(N width)) _)
        (liftBoundary (d*(N width)) (liftBoundary (offset*(N width)) _))
      rw [scheduled_shift]
      exact .refl _ _
  | .add e f => by
      change PaddedPolynomialCoeffEqv blocks
        (polyAdd (sourcePolynomial (shift d e)) (sourcePolynomial (shift d f)))
        (liftBoundary (d*(N width)) (polyAdd (sourcePolynomial e) (sourcePolynomial f)))
      rw [lift_add]
      exact (source_shift blocks d e).add (source_shift blocks d f)
  | .mul e f => by
      change PaddedPolynomialCoeffEqv blocks
        (polyMul (sourcePolynomial (shift d e)) (sourcePolynomial (shift d f)))
        (liftBoundary (d*(N width)) (polyMul (sourcePolynomial e) (sourcePolynomial f)))
      rw [lift_product]
      exact (source_shift blocks d e).mul (source_shift blocks d f)
  | .smul c e => by
      change PaddedPolynomialCoeffEqv blocks (polySmul c (sourcePolynomial (shift d e)))
        (liftBoundary (d*(N width)) (polySmul c (sourcePolynomial e)))
      rw [lift_smul]
      exact (source_shift blocks d e).smul c

/-- Both mixed reflected factors share the SAME coordinate lift. -/
theorem mixed_source_shift {width : Nat} (blocks H d : Nat)
    (e f : WindowExpression width) (he : Within H e) :
    PaddedPolynomialCoeffEqv blocks
      (sourcePolynomial (.mul (mirror (H+d) (shift d e)) (shift d f)))
      (liftBoundary (d*(N width)) (sourcePolynomial (.mul (mirror H e) f))) := by
  rw [mirror_shift H d e he]
  exact source_shift blocks d (.mul (mirror H e) f)

private theorem windowRatio_shift_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (e : WindowExpression width) (he : Within L e) :
    windowRatio hw0 hw1 K width hK m (L+2) n (sourcePolynomial (shift 1 e)) ≈
      windowRatio hw0 hw1 K width hK (m+1) L (n+1) (sourcePolynomial e) := by
  have hp := source_supported L e he
  have hleft := windowSupport_left hp
  have hright := windowSupport_right hleft
  have hq := source_supported (L+2) (shift 1 e)
    (within_mono (by omega : L+1 ≤ L+2) _ (shift_within L 1 e he))
  have hpin := source_shift ((L+2+1)*(N width)) 1 e
  have hcongr := windowRatio_padded_congr hw0 hw1 K width hK m (L+2) n hq
    (by simpa only [Nat.add_assoc] using hright)
    (by simpa only [Nat.one_mul] using hpin)
  have hpad := Q'.eqv_trans _ _ _
    (windowRatio_pad_right hw0 hw1 K width hK m (L+1) n hleft)
    (windowRatio_pad_left hw0 hw1 K width hK m L (n+1) hp)
  exact Q'.eqv_trans _ _ _ hcongr (by simpa only [Nat.add_assoc] using hpad)

/-- Exact finite centered padding. Boundary lengths grow on the smaller
window side; the actual cutoff and complete selected-chain ratio are unchanged. -/
theorem windowRatio_centered_shift {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n d : Nat)
    (e : WindowExpression width) (he : Within L e) :
    windowRatio hw0 hw1 K width hK m (L+2*d) n (sourcePolynomial (shift d e)) ≈
      windowRatio hw0 hw1 K width hK (m+d) L (n+d) (sourcePolynomial e) := by
  induction d generalizing m n with
  | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, shift_zero]
      exact Q'.eqv_refl _
  | succ d ih =>
      have hed : Within (L+2*d) (shift d e) :=
        within_mono (by omega : L+d ≤ L+2*d) _ (shift_within L d e he)
      have hstep := windowRatio_shift_one hw0 hw1 K width hK m (L+2*d) n (shift d e) hed
      have hleft : windowRatio hw0 hw1 K width hK m (L+2*(d+1)) n
          (sourcePolynomial (shift (d+1) e)) ≈
          windowRatio hw0 hw1 K width hK (m+1) (L+2*d) (n+1)
            (sourcePolynomial (shift d e)) := by
        simpa only [shift_comp, Nat.mul_succ, Nat.add_assoc] using hstep
      have hm : (m+1)+d = m+(d+1) := by omega
      have hn : (n+1)+d = n+(d+1) := by omega
      exact Q'.eqv_trans _ _ _ hleft (by simpa only [hm, hn] using ih (m+1) (n+1))

#print axioms shift
#print axioms shift_zero
#print axioms shift_comp
#print axioms shift_within
#print axioms mirror_shift
#print axioms source_shift
#print axioms mixed_source_shift
#print axioms windowRatio_centered_shift

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
