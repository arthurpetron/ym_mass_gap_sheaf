/-
# Positive one-step time on the actual all-nome joint completion

The original signed-span one-step chart is identified with a bond-reflected
odd window. Its finite numerator is the already proved positive quadratic
of the original kinetic/spatial transfer. The extra unobserved slice is
removed by the actual boundary-limit padding theorem, not by a finite
stationarity assertion. Cutoff convergence and the supplied Cauchy pairing
limits then give positivity on the SAME JointCompletion.

This joins a previously finite-action positivity theorem to the constructed
physical operator. Nome and width remain fixed. No near-one response,
spatial/spacing-uniform estimate, continuous Hamiltonian or continuum theory
is constructed by this join.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal
import YMGap.Continuum.BF4ExactSlabFixedSpatialOddWindowPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan sourceSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (mixedProduct mixedProduct_supported form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpanReversal
open YMGap.Continuum.BF4ExactSlabFixedSpatialOddWindowPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowState
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
  (jointPairing pairing_converges_jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm (jointSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse (completedInner_time_sum)

attribute [local irreducible] baseLinks

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width

/-- Positivity of the existing odd-window time limit, with its original
polynomial cap, explicit modulus and original partition. -/
theorem oddWindowLimit_nonnegative (h : Nat) (xs : DistanceSpan)
    (hx : radius xs ≤ h) (stage : Nat) :
    leEv czero
      (polynomialWindowLimit hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) (2*h+1) (oddProduct width h xs)
        (oddProduct_supported width h xs hx)) := by
  apply leEv_ofQ'_of_approx_ge
  intro k
  exact reversed_windowRatio_nonnegative hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) _ h (sourceSpan width (encodeChart h xs))
    (sourceSpan_supported width h (encodeChart h xs) (encodeChart_within h xs hx))

/-- The one-step natural-distance pairing uses one extra unobserved right
slice. Only the proved time-limit padding law removes it. -/
theorem pairing_oneStep_nonnegative (xs : DistanceSpan) (stage : Nat) :
    leEv czero (pairing hw0 hw1 width xs (advanceSpan 1 xs) stage) := by
  let h := radius xs
  have hx : radius xs ≤ h := Nat.le_refl _
  have hxH : radius xs ≤ h+1 := Nat.le_succ _
  have haH : radius (advanceSpan 1 xs) ≤ h+1 := radius_advance_le 1 xs
  have hp := oddProduct_supported width h xs hx
  have hsize : 2*(h+1) = (2*h+1)+1 := by omega
  have hcongr := windowLimit_padded_congr hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) (2*(h+1))
    (mixedProduct_supported width (h+1) (encodeChart (h+1) xs)
      (encodeChart (h+1) (advanceSpan 1 xs)) (encodeChart_within (h+1) _ haH))
    (by simpa only [hsize] using windowSupport_right hp)
    (mixedProduct_oneStep width h xs hx)
  have hpad := windowLimit_pad_right hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) (2*h+1) (oddProduct width h xs) hp
  have hpin := (pairing_chart hw0 hw1 width (h+1) xs (advanceSpan 1 xs)
    hxH haH stage).trans (hcongr.trans (by simpa only [hsize] using hpad))
  exact leEv_trans (oddWindowLimit_nonnegative hw0 hw1 width h xs hx stage)
    (leEv_of_equiv hpin.symm)

/-- The physical face guard belongs to the actual dense carrier; no
small-nome spatial-limit carrier is substituted here. -/
theorem jointPairing_oneStep_nonnegative (x : PhysicalSpan width) :
    leEv czero (jointPairing hw0 hw1 width x (physicalTime 1 x)) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairing_converges_jointPairing hw0 hw1 width x (physicalTime 1 x))
    (fun stage => pairing_oneStep_nonnegative hw0 hw1 width x.val stage)

/-- Positivity for every supplied Cauchy stream, through its actual
representative pairing limit and unchanged time-map modulus. -/
theorem representativeInner_oneStep_nonnegative (X : (D).Cauchy) :
    leEv czero (representativeInner hw0 hw1 width X
      ((jointTimeNonexpansive hw0 hw1 width 1).mapCauchy X)) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (pairSequence_converges hw0 hw1 width X
      ((jointTimeNonexpansive hw0 hw1 width 1).mapCauchy X))
    (fun n => jointPairing_oneStep_nonnegative hw0 hw1 width (X.seq n))

/-- Positive semidefiniteness of the ACTUAL completed one-step transfer,
not merely positivity of its even powers or of its kernel as a function. -/
theorem completedInner_oneStep_nonnegative (x : V) : RCnonneg (B x (T 1 x)) := by
  refine Quotient.inductionOn x ?_
  exact representativeInner_oneStep_nonnegative hw0 hw1 width

/-- Every integer-time autocorrelation is nonnegative. The odd case uses
the original-action one-step theorem; symmetry alone would not suffice. -/
theorem completedInner_time_nonnegative (n : Nat) (x : V) : RCnonneg (B x (T n x)) := by
  by_cases he : n % 2 = 0
  · have hn : n/2+n/2=n := by omega
    have h := completedInner_nonnegative hw0 hw1 width (T (n/2) x)
    simpa only [completedInner_time_sum, hn] using h
  · have hn : n/2+(1+n/2)=n := by omega
    have h := completedInner_oneStep_nonnegative hw0 hw1 width (T (n/2) x)
    rw [← jointCompletedTime_add, completedInner_time_sum, hn] at h
    exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive.oddWindowLimit_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive.pairing_oneStep_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive.jointPairing_oneStep_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive.representativeInner_oneStep_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive.completedInner_oneStep_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive.completedInner_time_nonnegative
