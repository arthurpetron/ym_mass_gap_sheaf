/-
# Explicit centered moments of the actual physical-time form

The representative is the original intrinsic pairing at physical lag n,
minus the product of the SAME two unit coefficients. It is computed from
the given dense physical presentations, not selected from an RC class.
Its exact pin identifies the actual centered completed-time pairing.

At even lag 2*k, this moment is the reflected diagonal after advance k.
Actual positivity, constant-one contraction and Cauchy--Schwarz therefore
give the three scalar moment inequalities used by the dyadic prefactor
argument. No decay envelope, positive-norm hypothesis, strict form bound,
one-step positivity or continuum claim is introduced here. Nome, width
and retained heat stage remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry
import YMGap.Constructive.CRealAlg

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift (advanceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredCompletion (center)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredPhysicalTime

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width stage : Nat)

local notation "B" => completedInner hw0 hw1 width stage
local notation "C" => center hw0 hw1 width stage
local notation "T" => completedTime hw0 hw1 width stage
local notation "E" => embedSpan hw0 hw1 width stage

/-- Computed CReal covariance at the actual physical lag n. The two unit
coefficients are unshifted, using their proved time invariance in the pin. -/
def centeredMoment (n : Nat) (x y : PhysicalSpan width) : CReal :=
  sub (pairing hw0 hw1 width x.val (advanceSpan n y.val) stage)
    (mul (pairing hw0 hw1 width x.val (unit width).val stage)
      (pairing hw0 hw1 width (unit width).val y.val stage))

/-- Exact same-object identification; no RC representative is chosen. -/
theorem centeredMoment_pin (n : Nat) (x y : PhysicalSpan width) :
    B (C (E x)) (T n (C (E y))) =
      Quotient.mk crealSetoid (centeredMoment hw0 hw1 width stage n x y) := by
  rw [centered_time_pairing, completedTime_correlator]
  unfold completedUnit
  rw [completedInner_embedSpan, completedInner_embedSpan]
  rfl

/-- The even-lag moment sequence, whose index is half the physical lag. -/
def evenMoment (x : PhysicalSpan width) (k : Nat) : CReal :=
  centeredMoment hw0 hw1 width stage (2*k) x x

theorem evenMoment_pin (x : PhysicalSpan width) (k : Nat) :
    B (C (E x)) (T (2*k) (C (E x))) =
      Quotient.mk crealSetoid (evenMoment hw0 hw1 width stage x k) :=
  centeredMoment_pin hw0 hw1 width stage (2*k) x x

/-- Time balance identifies the even moment with the actual translated
reflected diagonal, including k=0 and zero vectors. -/
theorem evenMoment_diagonal_pin (x : PhysicalSpan width) (k : Nat) :
    B (T k (C (E x))) (T k (C (E x))) =
      Quotient.mk crealSetoid (evenMoment hw0 hw1 width stage x k) :=
  (completedInner_even_diagonal hw0 hw1 width stage k (C (E x))).symm.trans
    (evenMoment_pin hw0 hw1 width stage x k)

theorem evenMoment_zero_pin (x : PhysicalSpan width) :
    B (C (E x)) (C (E x)) =
      Quotient.mk crealSetoid (evenMoment hw0 hw1 width stage x 0) := by
  have h := evenMoment_diagonal_pin hw0 hw1 width stage x 0
  rw [completedTime_zero] at h
  exact h

/-- First scalar input for dyadic prefactor removal: even-time positivity
of the SAME centered completed form. -/
theorem evenMoment_nonnegative (x : PhysicalSpan width) (k : Nat) :
    leEv czero (evenMoment hw0 hw1 width stage x k) := by
  have h := centered_even_nonnegative hw0 hw1 width stage k (E x)
  rw [evenMoment_pin] at h
  exact h

/-- Second scalar input: each even moment is bounded by its time-zero
reflected norm. This retains the existing non-strict constant one. -/
theorem evenMoment_le_zero (x : PhysicalSpan width) (k : Nat) :
    leEv (evenMoment hw0 hw1 width stage x k) (evenMoment hw0 hw1 width stage x 0) := by
  have h := centered_even_le_identity hw0 hw1 width stage k (E x)
  rw [evenMoment_pin, evenMoment_zero_pin] at h
  exact h

/-- Third scalar input: sharp dyadic log-convexity follows from the actual
completed Cauchy--Schwarz inequality and time balance, not a moment axiom. -/
theorem evenMoment_dyadic (x : PhysicalSpan width) (k : Nat) :
    leEv (mul (evenMoment hw0 hw1 width stage x k) (evenMoment hw0 hw1 width stage x k))
      (mul (evenMoment hw0 hw1 width stage x (k+k)) (evenMoment hw0 hw1 width stage x 0)) := by
  let v := C (E x)
  have hm : B v (T (2*k) v) =
      Quotient.mk crealSetoid (evenMoment hw0 hw1 width stage x k) :=
    evenMoment_pin hw0 hw1 width stage x k
  have hz : B v v = Quotient.mk crealSetoid (evenMoment hw0 hw1 width stage x 0) :=
    evenMoment_zero_pin hw0 hw1 width stage x
  have hd : B (T (2*k) v) (T (2*k) v) =
      Quotient.mk crealSetoid (evenMoment hw0 hw1 width stage x (k+k)) := by
    simpa only [Nat.two_mul] using evenMoment_diagonal_pin hw0 hw1 width stage x (k+k)
  have h := completedInner_cauchySchwarz hw0 hw1 width stage v (T (2*k) v)
  rw [hm, hz, hd] at h
  exact leEv_trans h (leEv_of_equiv (CRealAlg.cmul_comm _ _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.centeredMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.centeredMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.evenMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.evenMoment_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.evenMoment_diagonal_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.evenMoment_zero_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.evenMoment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.evenMoment_le_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments.evenMoment_dyadic
