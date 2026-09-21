/-
# Orbit-moment geometry on the SAME all-nome joint completion

Positivity of the actual scaled-difference form propagates a supplied
two-step Rayleigh floor to all even response moments, without division,
a spectral representation, or an identification with a spatial-union or
legacy thermodynamic carrier. Sharp CS also gives adjacent log-convexity.

These statements preserve a proved lower certificate under time translation;
they do not manufacture a near-one certificate. The concrete plaquette
consumer supplies its initial floor in a separate module.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointQuadraticForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
import YMGap.Continuum.BF4SpatialUnionBilinear

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement (completedInner_time_balance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointQuadraticForm
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_sub_self rc_sub_add)

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv 0 (A.approx n)) (QPoly.q_add_zero_eqv _)))

private theorem sub_nonnegative_of_le {a b : RC} (h : RCle b a) : RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [rc_sub_self] at h'

private theorem le_of_sub_nonnegative {a b : RC} (h : RCnonneg (RCsub a b)) : RCle b a := by
  have h' := RCadd_le_add h (RCle_refl b)
  rwa [rc_zero_add, rc_sub_add] at h'

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width

/-- Exact sum of the two physical lags, on this original completion. -/
theorem completedInner_time_sum (m n : Nat) (x y : V) :
    B (T m x) (T n y) = B x (T (m+n) y) := by
  rw [completedInner_time_balance, ← jointCompletedTime_add]

/-- The orbit norm and original even-lag autocorrelation are the same scalar. -/
theorem completedInner_even_diagonal (n : Nat) (x : V) :
    B (T n x) (T n x) = B x (T (2*n) x) := by
  simpa only [Nat.two_mul] using completedInner_time_sum hw0 hw1 width n n x x

/-- Adjacent log-convexity, expressed without division by possibly zero
moments. Positive concrete orbit floors permit later ratio interpretation. -/
theorem evenResponse_adjacent_logconvex (x : V) (n : Nat) :
    RCle (RCmul (B x (T (2*(n+1)) x)) (B x (T (2*(n+1)) x)))
      (RCmul (B x (T (2*n) x)) (B x (T (2*(n+2)) x))) := by
  have h := completedInner_cauchySchwarz hw0 hw1 width (T n x) (T (n+2) x)
  have h0 : n+n = 2*n := by omega
  have h1 : n+(n+2) = 2*(n+1) := by omega
  have h2 : (n+2)+(n+2) = 2*(n+2) := by omega
  simpa only [completedInner_time_sum, h0, h1, h2] using h

/-- Positivity of the full signed difference retains both cross terms. -/
theorem evenResponse_second_difference (x : V) (rho : Q') (n : Nat) :
    RCle (RCscale rho (RCsub (B x (T (2*(n+1)) x))
      (RCscale rho (B x (T (2*n) x)))))
      (RCsub (B x (T (2*(n+2)) x)) (RCscale rho (B x (T (2*(n+1)) x)))) := by
  have h := completedInner_scaledDifference_nonnegative hw0 hw1 width (T (n+2) x) (T n x) rho
  have h0 : n+n = 2*n := by omega
  have h1 : (n+2)+n = 2*(n+1) := by omega
  have h2 : n+(n+2) = 2*(n+1) := by omega
  have h3 : (n+2)+(n+2) = 2*(n+2) := by omega
  simp only [completedInner_time_sum, h0, h1, h2, h3] at h
  exact le_of_sub_nonnegative h

/-- Any supplied rational two-step floor persists under every time advance.
The initial inequality is explicit; no low-energy input is silently assumed. -/
theorem evenResponse_step_lower (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hfloor : RCle (RCscale rho (B x x)) (B x (T 2 x))) : ∀ n : Nat,
    RCle (RCscale rho (B x (T (2*n) x))) (B x (T (2*(n+1)) x))
  | 0 => by
      simpa only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, jointCompletedTime_zero] using hfloor
  | n+1 => by
      have h := RCscale_mono hrho
        (sub_nonnegative_of_le (evenResponse_step_lower x rho hrho hfloor n))
      rw [RCscale_RCzero] at h
      exact le_of_sub_nonnegative (RCle_trans h
        (evenResponse_second_difference hw0 hw1 width x rho n))

/-- Explicit lower response at every even physical lag, from the original two-step input. -/
theorem evenResponse_geometric_lower (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hfloor : RCle (RCscale rho (B x x)) (B x (T 2 x))) : ∀ n : Nat,
    RCle (RCscale (rho^n) (B x x)) (B x (T (2*n) x))
  | 0 => by
      rw [Nat.mul_zero, jointCompletedTime_zero, show rho^0 = (1 : Q') from rfl, RCscale_one]
      exact RCle_refl _
  | n+1 => by
      have h := RCle_trans (RCscale_mono hrho (evenResponse_geometric_lower x rho hrho hfloor n))
        (evenResponse_step_lower hw0 hw1 width x rho hrho hfloor n)
      rwa [RCscale_RCscale] at h

/-- Same-vector relative certificate on the actual time-translated state,
not a claim that translation has made that certificate approach one. -/
theorem timeImage_relative_floor (x : V) (rho : Q') (hrho : (0 : Q') ≤ rho)
    (hfloor : RCle (RCscale rho (B x x)) (B x (T 2 x))) (n : Nat) :
    RCle (RCscale rho (B (T n x) (T n x))) (B (T n x) (T 2 (T n x))) := by
  rw [← jointCompletedTime_add, completedInner_even_diagonal, completedInner_time_sum]
  have he : n+(2+n) = 2*(n+1) := by omega
  rw [he]
  exact evenResponse_step_lower hw0 hw1 width x rho hrho hfloor n

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse.completedInner_time_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse.completedInner_even_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse.evenResponse_adjacent_logconvex
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse.evenResponse_second_difference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse.evenResponse_step_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse.evenResponse_geometric_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitResponse.timeImage_relative_floor
