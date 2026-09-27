/-
# The original Wilson expectation on signed-time expressions

Every expression is evaluated in its computed symmetric window. Changing
that window uses the existing centered-limit theorem; physical time changes
use the distinct unequal-padding theorem. No CReal representative is chosen
from a quotient: the original Cauchy construction supplies it and its modulus.

Reflection and both directions of discrete time preserve this SAME original
expectation. The reflected mixed expectation of the original supported
expressions is exactly their existing spatial-union pairing, including its
dense image in the current completion. This is a source-side identification,
not a canonical rational GNSData producer or an algebra quotient. Raw signed
syntax is not being asserted to be an associative algebra in literal equality.
Changing spacing, full QFT and the Clay target remain open.
-/

import YMGap.Continuum.BF4WilsonSignedTimeExpression
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
import YMGap.Continuum.BF4WilsonSpatialUnionPairingData

namespace YMGap.Continuum.BF4WilsonSignedTimeExpectation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression mirror)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit (spatialLimit_centered_shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonFullReflection (spatialLimit_mirror)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity (spatialLimit_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_square_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within intrinsicForm intrinsicForm_chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm (embedStage completedTime completedTime_embedStage)
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner completedInner_embedStage)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0 < base)

/-- The original constructive limit at the radius computed from this expression. -/
def mean (e : Expression base) : CReal :=
  spatialLimit hw0 hw1 (radius e) (window (radius e) e)
    (window_within (radius e) e (within_radius e)) hsmall hd hs hb

/-- Explicit rational Cauchy data for the selected mean representative. -/
def meanCauchy (e : Expression base) : QCauchy (mean hw0 hw1 hsmall hd hs hb e).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _
    (spatialCauchy hw0 hw1 (radius e) (window (radius e) e)
      (window_within (radius e) e (within_radius e)) hsmall hd hs hb)

/-- Any witnessed symmetric window realizes the same original expectation. -/
theorem mean_at (H : Nat) (e : Expression base) (he : Within H e) :
    Equiv (mean hw0 hw1 hsmall hd hs hb e)
      (spatialLimit hw0 hw1 H (window H e) (window_within H e he) hsmall hd hs hb) := by
  have hR := radius_le_of_within H e he
  have hH : radius e+(H-radius e)=H := by omega
  have h := spatialLimit_centered_shift hw0 hw1 hsmall hd hs hb (radius e) (H-radius e)
    (window (radius e) e) (window_within (radius e) e (within_radius e))
  simp only [← window_enlarge (radius e) (H-radius e) e (within_radius e)] at h
  simpa only [hH, mean] using h.symm

attribute [local irreducible] spatialLimit

/-- Actual time reflection, not real conjugation, preserves the mean. -/
theorem mean_reflect (e : Expression base) :
    Equiv (mean hw0 hw1 hsmall hd hs hb (reflect e))
      (mean hw0 hw1 hsmall hd hs hb e) := by
  have h := mean_at hw0 hw1 hsmall hd hs hb (radius e) (reflect e)
    (reflect_within (radius e) e (within_radius e))
  simp only [window_reflect (radius e) e (within_radius e)] at h
  exact h.trans (spatialLimit_mirror hw0 hw1 (radius e) (window (radius e) e)
    (window_within (radius e) e (within_radius e)) hsmall hd hs hb).symm

/-- Forward physical time adds empty room on the opposite side, not a new action. -/
theorem mean_forward (n : Nat) (e : Expression base) :
    Equiv (mean hw0 hw1 hsmall hd hs hb (forward n e))
      (mean hw0 hw1 hsmall hd hs hb e) := by
  have h := mean_at hw0 hw1 hsmall hd hs hb (radius e+n) (forward n e)
    (forward_within (radius e) n e (within_radius e))
  simp only [window_forward (radius e) n e (within_radius e)] at h
  have hp := spatialLimit_padding hw0 hw1 hsmall hd hs hb (radius e) (radius e+n) 0 (2*n)
    (by omega) (window (radius e) e) (window_within (radius e) e (within_radius e))
  exact h.trans (by simpa only [shift_zero, mean] using hp)

/-- The inverse physical time is equally stationary on the same expression carrier. -/
theorem mean_backward (n : Nat) (e : Expression base) :
    Equiv (mean hw0 hw1 hsmall hd hs hb (backward n e))
      (mean hw0 hw1 hsmall hd hs hb e) := by
  have h := mean_at hw0 hw1 hsmall hd hs hb (radius e+n) (backward n e)
    (backward_within (radius e) n e (within_radius e))
  simp only [window_backward (radius e) n e (within_radius e)] at h
  exact h.trans (spatialLimit_padding hw0 hw1 hsmall hd hs hb (radius e) (radius e+n)
    (2*n) 0 (by omega) (window (radius e) e) (window_within (radius e) e (within_radius e)))

theorem mean_one : Equiv (mean hw0 hw1 hsmall hd hs hb .one) (ofQ' 1) := by
  exact (mean_at hw0 hw1 hsmall hd hs hb 0 .one True.intro).trans
    (spatialLimit_one hw0 hw1 hsmall hd hs hb 0)

theorem mean_add (e f : Expression base) :
    Equiv (mean hw0 hw1 hsmall hd hs hb (.add e f))
      (add (mean hw0 hw1 hsmall hd hs hb e) (mean hw0 hw1 hsmall hd hs hb f)) := by
  let H := max (radius e) (radius f)
  have he : Within H e := within_mono (Nat.le_max_left _ _) e (within_radius e)
  have hf : Within H f := within_mono (Nat.le_max_right _ _) f (within_radius f)
  exact (mean_at hw0 hw1 hsmall hd hs hb H (.add e f) ⟨he,hf⟩).trans
    ((spatialLimit_add hw0 hw1 hsmall hd hs hb H (window H e) (window H f)
      (window_within H e he) (window_within H f hf)).trans
      (Equiv_add (mean_at hw0 hw1 hsmall hd hs hb H e he).symm
        (mean_at hw0 hw1 hsmall hd hs hb H f hf).symm))

theorem mean_smul (c : Q') (e : Expression base) :
    Equiv (mean hw0 hw1 hsmall hd hs hb (.smul c e))
      (mul (ofQ' c) (mean hw0 hw1 hsmall hd hs hb e)) := by
  exact (mean_at hw0 hw1 hsmall hd hs hb (radius e) (.smul c e) (within_radius e)).trans
    (spatialLimit_smul hw0 hw1 hsmall hd hs hb (radius e) c (window (radius e) e)
      (window_within (radius e) e (within_radius e)))

private theorem chart_square_nonnegative (H : Nat) (e : WindowExpression base)
    (he : BF4ExactSlabFixedSpatialWilsonWindow.Within (2*H) e) (r stage t : Nat) :
    (0 : Q') ≤ chartScalar hw0 hw1 H (.mul e e) r stage t := by
  have hp := chartScalar_original_pin hw0 hw1 H (.mul e e) ⟨he,he⟩ r stage t
  have hc := (centered_within r (2*H) (.mul e e)).mpr ⟨he,he⟩
  have hq := originalWindowScalar_pin hw0 hw1 (2*H) (centeredExpression r (.mul e e)) hc stage t t
  have hsupport := BF4ExactSlabFixedSpatialWilsonWindow.source_supported (2*H)
    (centeredExpression r e) ((centered_within r (2*H) e).mpr he)
  have hfinite := windowRatio_square_nonnegative hw0 hw1 (headCutoff w+stage)
    (BF4ExactSlabFixedSpatialSpatialRecenter.paddedWidth base r)
    (Nat.le_add_right _ _) t (2*H) t hsupport
  exact Q'.le_trans' _ _ _ hfinite (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hq) (Q'.ge_of_eqv hp))

/-- Ordinary-square positivity uses the full original finite expectation,
not the reflected-form diagonal and not an assumed ambient state. -/
theorem mean_square_nonnegative (e : Expression base) :
    leEv (ofQ' 0) (mean hw0 hw1 hsmall hd hs hb (.mul e e)) := by
  let H := radius e
  let g := window H e
  have hg := window_within H e (within_radius e)
  let c := spatialCauchy hw0 hw1 H (.mul g g) ⟨hg,hg⟩ hsmall hd hs hb
  have hpos : leEv (ofQ' 0)
      (spatialLimit hw0 hw1 H (.mul g g) ⟨hg,hg⟩ hsmall hd hs hb) := by
    unfold spatialLimit
    exact leEv_ofQ'_of_approx_ge (fun k => chart_square_nonnegative hw0 hw1 H g hg
      (QMhat _ c k) (QMhat _ c k) (QMhat _ c k))
  exact leEv_trans hpos (leEv_of_equiv
    (mean_at hw0 hw1 hsmall hd hs hb H (.mul e e) ⟨within_radius e,within_radius e⟩).symm)

/-- A supported intrinsic Wilson expression retains its literal time relative
to the reflection plane; no new observable or normalized probe is selected. -/
def fromIntrinsic (x : IntrinsicExpression base) : Expression base :=
  ofWindow x.radius x.expression

theorem fromIntrinsic_within (x : IntrinsicExpression base) :
    Within x.radius (fromIntrinsic x) :=
  ofWindow_within x.radius x.expression
    (BF4ExactSlabFixedSpatialWilsonWindow.within_mono (by omega) x.expression x.within)

theorem window_fromIntrinsic (H : Nat) (x : IntrinsicExpression base) (hx : x.radius ≤ H) :
    window H (fromIntrinsic x) = chart H x :=
  window_ofWindow x.radius H x.expression hx

/-- The signed-time action represents the existing supported physical advance. -/
theorem fromIntrinsic_advance (n : Nat) (x : IntrinsicExpression base) :
    fromIntrinsic (advance n x) = forward n (fromIntrinsic x) :=
  ofWindow_forward x.radius n x.expression

/-- The ambient reflected mixed expectation is the existing physical form,
not an ordinary GNS norm silently substituted for it. -/
theorem mean_reflected_intrinsic (x y : IntrinsicExpression base) :
    Equiv (mean hw0 hw1 hsmall hd hs hb (.mul (reflect (fromIntrinsic x)) (fromIntrinsic y)))
      (intrinsicForm hw0 hw1 hsmall hd hs hb x y) := by
  let H := max x.radius y.radius
  have hx := within_mono (Nat.le_max_left x.radius y.radius) (fromIntrinsic x)
    (fromIntrinsic_within x)
  have hy := within_mono (Nat.le_max_right x.radius y.radius) (fromIntrinsic y)
    (fromIntrinsic_within y)
  have h := mean_at hw0 hw1 hsmall hd hs hb H
    (.mul (reflect (fromIntrinsic x)) (fromIntrinsic y)) ⟨reflect_within H _ hx,hy⟩
  have hp : window H (.mul (reflect (fromIntrinsic x)) (fromIntrinsic y)) =
      WindowExpression.mul (mirror H (chart H x)) (chart H y) := by
    change WindowExpression.mul (window H (reflect (fromIntrinsic x))) (window H (fromIntrinsic y)) = _
    rw [window_reflect H _ hx, window_fromIntrinsic H x (Nat.le_max_left _ _),
      window_fromIntrinsic H y (Nat.le_max_right _ _)]
  simp only [hp] at h
  exact h

/-- Every pair in the ALL-finite-base union is represented by one common-base
signed expression, with its original reflected pairing unchanged. -/
theorem pairing_as_mean (x y : Stage) :
    Equiv (pairing hw0 hw1 hsmall hd hs x y)
      (mean hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
        (.mul (reflect (fromIntrinsic (atBase x (Nat.le_max_left _ _))))
          (fromIntrinsic (atBase y (Nat.le_max_right _ _))))) :=
  (mean_reflected_intrinsic hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))).symm

/-- Literal equality of the current completed dense pairing and the RC class
of that same reflected ambient expression's original mean. -/
theorem completedInner_as_mean (x y : Stage) :
    completedInner hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (embedStage hw0 hw1 hsmall hd hs y) =
      Quotient.mk crealSetoid (mean hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
        (.mul (reflect (fromIntrinsic (atBase x (Nat.le_max_left _ _))))
          (fromIntrinsic (atBase y (Nat.le_max_right _ _))))) := by
  rw [completedInner_embedStage]
  exact Quotient.sound (pairing_as_mean hw0 hw1 hsmall hd hs x y)

/-- Same-object dense transfer correlators: the existing completed operator
acts by the constructed forward time on the original signed observable. -/
theorem completedTime_correlator_as_mean (n : Nat) (x y : Stage) :
    completedInner hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (completedTime hw0 hw1 hsmall hd hs n (embedStage hw0 hw1 hsmall hd hs y)) =
      Quotient.mk crealSetoid (mean hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
        (.mul (reflect (fromIntrinsic (atBase x (Nat.le_max_left _ _))))
          (forward n (fromIntrinsic (atBase y (Nat.le_max_right _ _)))))) := by
  rw [completedTime_embedStage, completedInner_as_mean]
  simp only [atBase_time, fromIntrinsic_advance]
  rfl

end YMGap.Continuum.BF4WilsonSignedTimeExpectation

#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.meanCauchy
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_reflect
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_one
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_square_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.fromIntrinsic
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.fromIntrinsic_within
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.window_fromIntrinsic
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.fromIntrinsic_advance
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.mean_reflected_intrinsic
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.pairing_as_mean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.completedInner_as_mean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeExpectation.completedTime_correlator_as_mean
