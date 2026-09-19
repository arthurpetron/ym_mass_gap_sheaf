/-
# Finite geometric approximate preimages on the SAME Wilson completion

The finite geometric sum of the actual two-step transfer orbit is an explicit
constructive approximate preimage for `I - T^2`.  The identity is proved on
the current completed Wilson carrier, with no inverse, choice, spectral
theorem, or auxiliary transfer.  On the existing vacuum complement the
actual approximation error is bounded by the already checked geometric norm
decay.

This is a fixed-spacing SU(2) range approximation.  It is not a completed
spectral-gap theorem, a changing-spacing estimate, a physical mass
calibration, or a continuum Yang--Mills construction.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
import YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws

namespace YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionRelaxation
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap (twoStepRate)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_sub_self)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "A" => completedAdd hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "Z" => completedZero hw0 hw1 hsmall hd hs
local notation "q" => twoStepRate w hd

/-- The finite orbit sum `x + T²x + ... + T^(2(n-1))x`. -/
def evenOrbitSum (x : V) : Nat → V
  | 0 => Z
  | n + 1 => A (evenOrbitSum x n) (T (2*n) x)

@[simp] theorem evenOrbitSum_zero (x : V) : evenOrbitSum hw0 hw1 hsmall hd hs x 0 = Z := rfl

@[simp] theorem evenOrbitSum_succ (x : V) (n : Nat) :
    evenOrbitSum hw0 hw1 hsmall hd hs x (n+1) =
      A (evenOrbitSum hw0 hw1 hsmall hd hs x n) (T (2*n) x) := rfl

private theorem rc_telescope (a b c : RC) :
    RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro repA repB repC
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1)))
        (.add (.var 1) (.neg (.var 2))))
      (.add (.var 0) (.neg (.var 2))) (by decide)
      (fun | 0 => repA.approx n | 1 => repB.approx n | _ => repC.approx n)))

private theorem rc_sub_add_exchange (a b c d : RC) :
    RCsub (RCadd a b) (RCadd c d) =
      RCadd (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro repA repB
  refine Quotient.inductionOn₂ c d ?_
  intro repC repD
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1))
        (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2)))
        (.add (.var 1) (.neg (.var 3)))) (by decide)
      (fun | 0 => repA.approx n | 1 => repB.approx n
            | 2 => repC.approx n | _ => repD.approx n)))

private theorem rc_sub_sub_left (a b : RC) :
    RCsub a (RCsub a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro repA repB
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1)))))
      (.var 1) (by decide)
      (fun | 0 => repA.approx n | _ => repB.approx n)))

/-- The exact finite geometric resolvent identity on the current carrier. -/
theorem evenOrbitSum_sub_twoStep (x : V) (n : Nat) :
    completedSub hw0 hw1 hsmall hd hs
        (evenOrbitSum hw0 hw1 hsmall hd hs x n)
        (T 2 (evenOrbitSum hw0 hw1 hsmall hd hs x n)) =
      completedSub hw0 hw1 hsmall hd hs x (T (2*n) x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  induction n with
  | zero =>
      rw [evenOrbitSum_zero, completedInner_sub_left,
        completedInner_sub_left, completedInner_zero_left,
        completedTime_zero_vector, completedInner_zero_left,
        Nat.mul_zero, completedTime_zero, rc_sub_self]
      exact (rc_sub_self (B x test)).symm
  | succ n ih =>
      have htime : T 2 (T (2*n) x) = T (2*(n+1)) x := by
        rw [← completedTime_add]
        congr 1
        omega
      have ih' := ih
      rw [completedInner_sub_left] at ih'
      rw [evenOrbitSum_succ, completedTime_addition, htime,
        completedInner_sub_left]
      simp only [completedInner_add_left]
      rw [rc_sub_add_exchange, ih']
      rw [completedInner_sub_left, completedInner_sub_left]
      exact rc_telescope _ _ _

/-- The actual error of the explicit preimage has a directly quantified
    squared-norm bound on the same vacuum complement. -/
theorem evenOrbitSum_error_bound (x : V)
    (hx : B x (completedUnit hw0 hw1 hsmall hd hs) = RCzero) (n : Nat) :
    RCle
    (completedDist hw0 hw1 hsmall hd hs x
      (completedSub hw0 hw1 hsmall hd hs
        (evenOrbitSum hw0 hw1 hsmall hd hs x n)
        (T 2 (evenOrbitSum hw0 hw1 hsmall hd hs x n))))
      (RCscale (q^(2*n)) (B x x)) := by
  have herr : completedSub hw0 hw1 hsmall hd hs x
      (completedSub hw0 hw1 hsmall hd hs
        (evenOrbitSum hw0 hw1 hsmall hd hs x n)
        (T 2 (evenOrbitSum hw0 hw1 hsmall hd hs x n))) =
      T (2*n) x := by
    rw [evenOrbitSum_sub_twoStep]
    apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
    intro test
    rw [completedInner_sub_left, completedInner_sub_left]
    exact rc_sub_sub_left _ _
  unfold completedDist
  rw [herr]
  exact norm_decay hw0 hw1 hsmall hd hs x hx (2*n)

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum_sub_twoStep
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation.evenOrbitSum_error_bound

end YMGap.Continuum.BF4WilsonSpatialUnionRangeApproximation
