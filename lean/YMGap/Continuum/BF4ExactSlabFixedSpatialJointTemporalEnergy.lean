/-
# Whole-observable temporal energy on the actual joint carrier

Original-action positivity of every integer time is applied to the actual
signed difference x-Tx. Bilinearity and time balance identify its pairing
with the second difference of the SAME autocorrelation. Discrete convexity
therefore bounds the n-step energy by n times the one-step energy, for every
state in the actual JointCompletion, including signed time filters.

The bound retains the WHOLE observable's energy. It does not estimate it by
separate absolute summand budgets, supply a small relative one-step energy,
or prove physical-time survival under changing width/nome/spacing. Those
quantitative original-action inputs remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection
import YMGap.Continuum.CRealDiscreteConvexity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm (jointSeminorm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLimit (representativeInner)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear (completedSub)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse (completedInner_time_sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointTimePositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection
  (center centered_time_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedGap (completedCenteredScalar)

private theorem curvature_rearrange (a b c : RC) :
    RCsub (RCsub a b) (RCsub b c) = RCadd (RCsub a b) (RCsub c b) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 2) (.neg (.var 1)))) (by decide)
      (fun | 0 => A.approx k | 1 => B.approx k | _ => C.approx k)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "C" => center hw0 hw1 width

/-- Actual pairing of a signed time difference; neither cross term is
discarded. The n=0 case is a squared norm, the odd cases use positive T. -/
theorem timeDifference_pairing (n : Nat) (x : V) :
    B (completedSub hw0 hw1 width x (T 1 x))
        (T n (completedSub hw0 hw1 width x (T 1 x))) =
      RCadd (RCsub (B x (T n x)) (B x (T (n+1) x)))
        (RCsub (B x (T (n+2) x)) (B x (T (n+1) x))) := by
  rw [completedTime_sub, completedInner_sub_left,
    completedInner_sub_right, completedInner_sub_right]
  simp only [← jointCompletedTime_add, completedInner_time_sum,
    show 1+n=n+1 by omega, show 1+(n+1)=n+2 by omega]
  exact curvature_rearrange _ _ _

/-- Convexity at EVERY integer lag for the original completed state. -/
theorem response_convex (n : Nat) (x : V) :
    RCnonneg (RCadd (RCsub (B x (T n x)) (B x (T (n+1) x)))
      (RCsub (B x (T (n+2) x)) (B x (T (n+1) x)))) := by
  have h := completedInner_time_nonnegative hw0 hw1 width n
    (completedSub hw0 hw1 width x (T 1 x))
  rwa [timeDifference_pairing] at h

/-- A supplied state representative gives the entire response sequence
without selecting representatives of quotient reals. -/
def representativeResponse (X : (D).Cauchy) (n : Nat) : CReal :=
  representativeInner hw0 hw1 width X ((jointTimeNonexpansive hw0 hw1 width n).mapCauchy X)

theorem representativeResponse_pin (X : (D).Cauchy) (n : Nat) :
    Quotient.mk crealSetoid (representativeResponse hw0 hw1 width X n) =
      B (Quotient.mk (D).completionSetoid X)
        (T n (Quotient.mk (D).completionSetoid X)) := rfl

theorem representativeResponse_convex (X : (D).Cauchy) (n : Nat) :
    leEv czero (CRealDiscreteConvexity.curvature
      (representativeResponse hw0 hw1 width X) n) :=
  response_convex hw0 hw1 width n (Quotient.mk (D).completionSetoid X)

/-- The actual autocorrelation drop, without an absolute-value relaxation. -/
def temporalEnergy (n : Nat) (x : V) : RC := RCsub (B x x) (B x (T n x))

/-- Linear multi-step control on the SAME completed carrier. The factor n
is explicit; the right side is the energy of the WHOLE original state. -/
theorem temporalEnergy_linear (n : Nat) (x : V) :
    RCle (temporalEnergy hw0 hw1 width n x)
      (RCscale (Q'.ofNat n) (temporalEnergy hw0 hw1 width 1 x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := CRealDiscreteConvexity.endpoint_drop_le_nat_mul_first
    (representativeResponse hw0 hw1 width X)
    (representativeResponse_convex hw0 hw1 width X) n
  have h' : RCle
      (RCsub (B (Quotient.mk (D).completionSetoid X) (T 0 (Quotient.mk (D).completionSetoid X)))
        (B (Quotient.mk (D).completionSetoid X) (T n (Quotient.mk (D).completionSetoid X))))
      (RCscale (Q'.ofNat n)
        (RCsub (B (Quotient.mk (D).completionSetoid X) (T 0 (Quotient.mk (D).completionSetoid X)))
          (B (Quotient.mk (D).completionSetoid X) (T 1 (Quotient.mk (D).completionSetoid X))))) := h
  simpa only [jointCompletedTime_zero] using h'

/-- The preceding projection identifies these positive responses with the
existing SAME-object connected scalar, at odd as well as even times. -/
theorem completedCenteredScalar_nonnegative (n : Nat) (x : V) :
    RCnonneg (completedCenteredScalar hw0 hw1 width n x x) := by
  rw [← centered_time_pairing]
  exact completedInner_time_nonnegative hw0 hw1 width n (C x)

/-- The causal scaling consumer: any supplied bound on this WHOLE centered
state's one-step energy propagates linearly, without changing the variance
on the right. Supplying a useful width/spacing family of bounds remains open. -/
theorem centered_relative_energy (n : Nat) (x : V) (delta : Q')
    (h : RCle (temporalEnergy hw0 hw1 width 1 (C x))
      (RCscale delta (B (C x) (C x)))) :
    RCle (temporalEnergy hw0 hw1 width n (C x))
      (RCscale (Q'.ofNat n * delta) (B (C x) (C x))) := by
  have hn := RCle_trans (temporalEnergy_linear hw0 hw1 width n (C x))
    (RCscale_mono (Q'.ofNat_nonneg n) h)
  rwa [RCscale_RCscale] at hn

/-- Signed filtering keeps its complete energy, rather than a sum of
absolute single-time budgets. Repeated times and cancellations are allowed. -/
theorem orbitSum_temporalEnergy_linear (n : Nat) (x : V) (cs : List (Q' × Nat)) :
    RCle (temporalEnergy hw0 hw1 width n (orbitSum hw0 hw1 width x cs))
      (RCscale (Q'.ofNat n)
        (temporalEnergy hw0 hw1 width 1 (orbitSum hw0 hw1 width x cs))) :=
  temporalEnergy_linear hw0 hw1 width n (orbitSum hw0 hw1 width x cs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.timeDifference_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.response_convex
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.representativeResponse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.representativeResponse_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.representativeResponse_convex
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.temporalEnergy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.temporalEnergy_linear
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.completedCenteredScalar_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.centered_relative_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointTemporalEnergy.orbitSum_temporalEnergy_linear
