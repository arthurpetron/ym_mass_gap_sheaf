/-
# Exact unequal padding of an original signed Wilson window

The left and right empty portions of a displayed observation window may be
redistributed independently into the external transition chains. The complete
signed Wilson expression is shifted only by the left padding. The retained
heat cutoff, chronological action and partition are unchanged.

This is an exact finite identity with changed boundary distances, not finite
stationarity. Its consumer removes both boundaries using the already explicit
time/cutoff limits; no interacting spatial-translation claim is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence (windowRatio_padded_congr)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

theorem shift_within_padding {width : Nat} (L left right : Nat)
    (e : WindowExpression width) (he : Within L e) :
    Within (L+left+right) (shift left e) :=
  within_mono (Nat.le_add_right (L+left) right) _ (shift_within L left e he)

private theorem windowRatio_shift_left_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n : Nat)
    (e : WindowExpression width) (he : Within L e) :
    windowRatio hw0 hw1 K width hK m (L+1) n (sourcePolynomial (shift 1 e)) ≈
      windowRatio hw0 hw1 K width hK (m+1) L n (sourcePolynomial e) := by
  have hp := source_supported L e he
  have hleft := windowSupport_left hp
  have hq := source_supported (L+1) (shift 1 e) (shift_within L 1 e he)
  have hpin := source_shift ((L+1+1)*(N width)) 1 e
  have hcongr := windowRatio_padded_congr hw0 hw1 K width hK m (L+1) n hq hleft
    (by simpa only [Nat.one_mul] using hpin)
  exact Q'.eqv_trans _ _ _ hcongr
    (windowRatio_pad_left hw0 hw1 K width hK m L n hp)

/-- All left padding is absorbed by the left external transition chain. -/
theorem windowRatio_shift_left {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n left : Nat)
    (e : WindowExpression width) (he : Within L e) :
    windowRatio hw0 hw1 K width hK m (L+left) n (sourcePolynomial (shift left e)) ≈
      windowRatio hw0 hw1 K width hK (m+left) L n (sourcePolynomial e) := by
  induction left generalizing m n with
  | zero =>
      simp only [Nat.add_zero, shift_zero]
      exact Q'.eqv_refl _
  | succ left ih =>
      have hstep := windowRatio_shift_left_one hw0 hw1 K width hK m (L+left) n
        (shift left e) (shift_within L left e he)
      have hfirst : windowRatio hw0 hw1 K width hK m (L+(left+1)) n
          (sourcePolynomial (shift (left+1) e)) ≈
          windowRatio hw0 hw1 K width hK (m+1) (L+left) n
            (sourcePolynomial (shift left e)) := by
        simpa only [shift_comp, Nat.add_assoc] using hstep
      have hm : (m+1)+left = m+(left+1) := by omega
      exact Q'.eqv_trans _ _ _ hfirst (by simpa only [hm] using ih (m+1) n)

/-- Right padding does not shift any observable coordinate. -/
theorem windowRatio_pad_right_many {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n right : Nat)
    (e : WindowExpression width) (he : Within L e) :
    windowRatio hw0 hw1 K width hK m (L+right) n (sourcePolynomial e) ≈
      windowRatio hw0 hw1 K width hK m L (n+right) (sourcePolynomial e) := by
  induction right generalizing m n with
  | zero =>
      simp only [Nat.add_zero]
      exact Q'.eqv_refl _
  | succ right ih =>
      have hp := source_supported (L+right) e
        (within_mono (Nat.le_add_right L right) e he)
      have hstep := windowRatio_pad_right hw0 hw1 K width hK m (L+right) n hp
      have hn : (n+1)+right = n+(right+1) := by omega
      exact Q'.eqv_trans _ _ _ (by simpa only [Nat.add_assoc] using hstep)
        (by simpa only [hn] using ih m (n+1))

/-- SAME finite normalized action, allowing unequal left and right padding. -/
theorem windowRatio_padding {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (m L n left right : Nat)
    (e : WindowExpression width) (he : Within L e) :
    windowRatio hw0 hw1 K width hK m (L+left+right) n
        (sourcePolynomial (shift left e)) ≈
      windowRatio hw0 hw1 K width hK (m+left) L (n+right) (sourcePolynomial e) :=
  Q'.eqv_trans _ _ _
    (windowRatio_pad_right_many hw0 hw1 K width hK m (L+left) n right
      (shift left e) (shift_within L left e he))
    (windowRatio_shift_left hw0 hw1 K width hK m L (n+right) left e he)

/-- The polynomial identity pins the two actual original finite expectations. -/
theorem originalScalar_padding {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L left right : Nat) (e : WindowExpression width) (he : Within L e)
    (stage m n : Nat) :
    originalWindowScalar hw0 hw1 (L+left+right) (shift left e) stage m n ≈
      originalWindowScalar hw0 hw1 L e stage (m+left) (n+right) :=
  Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 (L+left+right) (shift left e)
      (shift_within_padding L left right e he) stage m n)
    (Q'.eqv_trans _ _ _
      (windowRatio_padding hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) m L n left right e he)
      (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L e he stage (m+left) (n+right))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity.shift_within_padding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity.windowRatio_shift_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity.windowRatio_pad_right_many
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity.windowRatio_padding
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowStationarity.originalScalar_padding
