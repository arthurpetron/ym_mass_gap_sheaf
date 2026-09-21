/-
# Linear time control of a complete signed time-zero Wilson observable

Site and bond reflection positivity act on the ENTIRE adjacent difference
of an arbitrary time-zero expression. Original joint-limit stationarity
identifies the four terms with its actual lag moments. Convexity therefore
controls n-step loss by n times the one-step loss, retaining every signed
cross term inside the observable. No coefficient norm or family-size cost
is inserted.

All expressions, limits and partitions belong to the same original state
at a fixed strict nome and spatial width. This does not estimate its
one-step energy relative to variance, construct a spatial/scaling family,
or prove continuum survival or a physical mass gap.
-/

import YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws
import YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
import YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_zero shift_comp)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow (reverse oddPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonTimePositive (originalJoint_odd_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity (originalJoint_padding)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws
open YMGap.Continuum.BF4WilsonJointOrdinaryCauchySchwarz
open YMGap.Continuum.BF4WilsonTimeZeroOffsetLaws
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

attribute [local irreducible] originalJointLimit

def lagExpression {width : Nat} (e : WindowExpression width) (n : Nat) : WindowExpression width :=
  .mul (shift n e) e

theorem lag_within {width : Nat} (e : WindowExpression width) (he : Within 0 e) (n : Nat) :
    Within n (lagExpression e n) :=
  ⟨timeZero_shift_within n e he, within_mono (Nat.zero_le n) e he⟩

def lagMoment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) (n : Nat) : CReal :=
  originalJointLimit hw0 hw1 n (lagExpression e n) (lag_within e he n)

/-- Unequal original padding identifies translated pairs without a new
stationary-state hypothesis. The entire expression is shifted together. -/
theorem pair_lag {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e)
    (L s t : Nat) (hst : s ≤ t) (ht : t ≤ L) :
    Equiv (originalJointLimit hw0 hw1 L (.mul (shift t e) (shift s e))
      ⟨within_mono ht _ (timeZero_shift_within t e he),
        within_mono (Nat.le_trans hst ht) _ (timeZero_shift_within s e he)⟩)
      (lagMoment hw0 hw1 e he (t-s)) := by
  have h := originalJoint_padding hw0 hw1 (t-s) s (L-t)
    (lagExpression e (t-s)) (lag_within e he (t-s))
  have htime : (t-s)+s+(L-t)=L := by omega
  have hsource : shift s (lagExpression e (t-s)) = .mul (shift t e) (shift s e) := by
    change WindowExpression.mul (shift s (shift (t-s) e)) (shift s e) = _
    rw [shift_comp, Nat.sub_add_cancel hst]
  simpa only [htime, hsource, lagMoment] using h

def timeDifference {width : Nat} (e : WindowExpression width) (n : Nat) : WindowExpression width :=
  difference e (shift n e)

theorem timeDifference_within {width : Nat} (e : WindowExpression width)
    (he : Within 0 e) (n : Nat) : Within n (timeDifference e n) :=
  ⟨within_mono (Nat.zero_le n) e he, timeZero_shift_within n e he⟩

def secondDifference {width : Nat} (e : WindowExpression width) (n : Nat) : WindowExpression width :=
  .mul (difference (shift (n+2) e) (shift (n+1) e)) (timeDifference e 1)

theorem secondDifference_within {width : Nat} (e : WindowExpression width)
    (he : Within 0 e) (n : Nat) : Within (n+2) (secondDifference e n) :=
  ⟨⟨timeZero_shift_within (n+2) e he,
      within_mono (by omega : n+1 ≤ n+2) _ (timeZero_shift_within (n+1) e he)⟩,
    within_mono (by omega : 1 ≤ n+2) _ (timeDifference_within e he 1)⟩

theorem secondDifference_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) (n : Nat) :
    Equiv (originalJointLimit hw0 hw1 (n+2) (secondDifference e n)
      (secondDifference_within e he n))
      (CRealDiscreteConvexity.curvature (lagMoment hw0 hw1 e he) n) := by
  have hexp := joint_difference_product hw0 hw1 (n+2)
    (shift (n+2) e) (shift (n+1) e) e (shift 1 e)
    (timeZero_shift_within (n+2) e he)
    (within_mono (by omega : n+1 ≤ n+2) _ (timeZero_shift_within (n+1) e he))
    (within_mono (Nat.zero_le _) e he)
    (within_mono (by omega : 1 ≤ n+2) _ (timeZero_shift_within 1 e he))
  have hp := equiv_add
    (equiv_sub (pair_lag hw0 hw1 e he (n+2) 0 (n+2) (by omega) (Nat.le_refl _))
      (pair_lag hw0 hw1 e he (n+2) 1 (n+2) (by omega) (Nat.le_refl _)))
    (equiv_sub (pair_lag hw0 hw1 e he (n+2) 1 (n+1) (by omega) (by omega))
      (pair_lag hw0 hw1 e he (n+2) 0 (n+1) (by omega) (by omega)))
  simp only [shift_zero] at hp
  exact hexp.trans (hp.trans
    (SumOfSquares.Equiv_of_approx_eqv (fun k => Q'.add_comm_eqv _ _)))

private theorem even_expression {width : Nat} (e : WindowExpression width)
    (he : Within 0 e) (k : Nat) :
    WindowExpression.mul (mirror (k+1) (timeDifference e 1)) (timeDifference e 1) =
      secondDifference e (2*k) := by
  have h0 := mirror_shift_timeZero (k+1) 0 e he
  simp only [shift_zero, Nat.sub_zero] at h0
  change WindowExpression.mul
    (difference (mirror (k+1) e) (mirror (k+1) (shift 1 e))) (timeDifference e 1) = _
  rw [h0, mirror_shift_timeZero (k+1) 1 e he]
  rw [show 2*(k+1)=2*k+2 by omega, show 2*k+2-1=2*k+1 by omega]
  rfl

private theorem odd_expression {width : Nat} (e : WindowExpression width)
    (he : Within 0 e) (k : Nat) :
    oddPair (k+1) (timeDifference e 1) = secondDifference e (2*k+1) := by
  have h0 := reverse_shift_timeZero (k+1) 0 e he
  simp only [shift_zero, Nat.sub_zero] at h0
  change WindowExpression.mul
    (difference (shift (k+1+1) (reverse (k+1) e))
      (shift (k+1+1) (reverse (k+1) (shift 1 e)))) (timeDifference e 1) = _
  rw [h0, reverse_shift_timeZero (k+1) 1 e he, shift_comp, shift_comp]
  rw [show (k+1)+(k+1+1)=(2*k+1)+2 by omega,
    show (k+1-1)+(k+1+1)=(2*k+1)+1 by omega]
  rfl

/-- Both parities are positive for the WHOLE signed expression, not just
for its separate loop summands. No small-nome guard is used. -/
theorem lagMoment_convex {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) (n : Nat) :
    leEv (ofQ' 0) (CRealDiscreteConvexity.curvature (lagMoment hw0 hw1 e he) n) := by
  have hpos : leEv (ofQ' 0)
      (originalJointLimit hw0 hw1 (n+2) (secondDifference e n) (secondDifference_within e he n)) := by
    by_cases hn : n % 2 = 0
    · have h := originalJoint_reflected_nonnegative hw0 hw1 (n/2+1)
        (timeDifference e 1)
        (within_mono (by omega : 1 ≤ n/2+1) _ (timeDifference_within e he 1))
      have hindex : n=2*(n/2) := by omega
      simpa only [even_expression e he, show 2*(n/2+1)=2*(n/2)+2 by omega, ←hindex] using h
    · have h := originalJoint_odd_nonnegative hw0 hw1 (n/2+1)
        (timeDifference e 1)
        (within_mono (by omega : 1 ≤ n/2+1) _ (timeDifference_within e he 1))
      have hindex : n=2*(n/2)+1 := by omega
      simpa only [odd_expression e he,
        show 2*(n/2+1)+1=(2*(n/2)+1)+2 by omega, ←hindex] using h
  exact leEv_trans hpos (leEv_of_equiv (secondDifference_pin hw0 hw1 e he n))

def timeIncrement {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) (n : Nat) : CReal :=
  originalJointLimit hw0 hw1 n (.mul (timeDifference e n) (timeDifference e n))
    ⟨timeDifference_within e he n, timeDifference_within e he n⟩

theorem timeIncrement_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) (n : Nat) :
    leEv (ofQ' 0) (timeIncrement hw0 hw1 e he n) :=
  joint_square_nonnegative hw0 hw1 n _ (timeDifference_within e he n)

theorem timeIncrement_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) (n : Nat) :
    Equiv (timeIncrement hw0 hw1 e he n)
      (mul (ofQ' 2) (sub (lagMoment hw0 hw1 e he 0) (lagMoment hw0 hw1 e he n))) := by
  have h0 := within_mono (Nat.zero_le n) e he
  have hn := timeZero_shift_within n e he
  have hexp := joint_difference_product hw0 hw1 n e (shift n e) e (shift n e) h0 hn h0 hn
  have hcomm := joint_congr hw0 hw1 n (.mul e (shift n e)) (.mul (shift n e) e)
    ⟨h0,hn⟩ ⟨hn,h0⟩ (RatPolyCoeffEqv.mul_comm _ _)
  have h00 := pair_lag hw0 hw1 e he n 0 0 (Nat.le_refl _) (Nat.zero_le _)
  have hnn := pair_lag hw0 hw1 e he n n n (Nat.le_refl _) (Nat.le_refl _)
  have hn0 := pair_lag hw0 hw1 e he n 0 n (Nat.zero_le _) (Nat.le_refl _)
  simp only [shift_zero, Nat.sub_zero, Nat.sub_self] at h00 hnn hn0
  have hp := equiv_add (equiv_sub h00 (hcomm.trans hn0)) (equiv_sub hnn hn0)
  exact hexp.trans (hp.trans (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.neg (.var 1))))
      (.mul (.const 2) (.add (.var 0) (.neg (.var 1)))) (by decide)
      (fun | 0 => (lagMoment hw0 hw1 e he 0).approx k | _ => (lagMoment hw0 hw1 e he n).approx k))))

/-- Linear multi-step bound for every signed time-zero Wilson polynomial.
The one-step energy remains that of the ENTIRE SAME observable. -/
theorem timeIncrement_linear {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (e : WindowExpression width) (he : Within 0 e) (n : Nat) :
    leEv (timeIncrement hw0 hw1 e he n)
      (mul (ofQ' (Q'.ofNat n)) (timeIncrement hw0 hw1 e he 1)) := by
  have h := leEv_smul_nonneg (by decide : (0 : Q') ≤ 2)
    (CRealDiscreteConvexity.endpoint_drop_le_nat_mul_first (lagMoment hw0 hw1 e he)
      (lagMoment_convex hw0 hw1 e he) n)
  have hr : Equiv
      (mul (ofQ' 2) (mul (ofQ' (Q'.ofNat n)) (sub (lagMoment hw0 hw1 e he 0) (lagMoment hw0 hw1 e he 1))))
      (mul (ofQ' (Q'.ofNat n)) (mul (ofQ' 2) (sub (lagMoment hw0 hw1 e he 0) (lagMoment hw0 hw1 e he 1)))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun k =>
      poly_identity_of_normal_eq
        (.mul (.const 2) (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.mul (.const 2) (.var 1))) (by decide)
        (fun | 0 => Q'.ofNat n
             | _ => (sub (lagMoment hw0 hw1 e he 0) (lagMoment hw0 hw1 e he 1)).approx k))
  exact leEv_trans (leEv_of_equiv (timeIncrement_pin hw0 hw1 e he n))
    (leEv_trans h (leEv_trans (leEv_of_equiv hr)
      (leEv_smul_nonneg (Q'.ofNat_nonneg n) (leEv_of_equiv (timeIncrement_pin hw0 hw1 e he 1).symm))))

end YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity

#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.lag_within
#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.pair_lag
#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.timeDifference_within
#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.secondDifference_within
#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.secondDifference_pin
#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.lagMoment_convex
#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.timeIncrement_nonnegative
#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.timeIncrement_pin
#print axioms YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity.timeIncrement_linear
