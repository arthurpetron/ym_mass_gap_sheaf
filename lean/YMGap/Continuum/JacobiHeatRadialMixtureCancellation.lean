/-
# Finite rational radial-mixture cancellation

For any finite nonnegative sequence, the first three moments construct
M1^2-M2 >= 0 and M1*M3-M2^2 >= 0. Their exact signed cancellation lowers
the cleared radial-mixture bound to the PRODUCT cost D <= C, without
dividing by M1, omitting variance, or excluding the empty prefix.

This is finite rational algebra only. No Jacobi/Poisson identity, heat or
angular derivative pin, original-action estimate, OS statement, scaling
bound or physical gap is asserted. The analytic PRODUCT bound remains an
input to this reduction, not a produced estimate.
-/

import YMGap.Constructive.RationalTail
import YMGap.Constructive.SumOfSquares
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CRealMulMono

namespace YMGap.Continuum.JacobiHeatRadialMixtureCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail (finSum)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

def M1 (r : Nat → Q') (N : Nat) : Q' := finSum r N
def M2 (r : Nat → Q') (N : Nat) : Q' := finSum (fun i => r i*r i) N
def M3 (r : Nat → Q') (N : Nat) : Q' := finSum (fun i => r i*r i*r i) N

private theorem nonneg_of_eqv {p q : Q'} (h : p ≈ q) (hq : (0 : Q') ≤ q) :
    (0 : Q') ≤ p :=
  Q'.le_trans' _ _ _ hq (Q'.le_of_eqv (Q'.eqv_symm h))

private theorem add_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a b c hab)
    (Q'.add_eqv_congr_left b c d hcd)

private theorem sum_nonneg (f : Nat → Q') : ∀ N,
    (∀ i, i < N → (0 : Q') ≤ f i) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N+1, hf => Q'.zero_le_add _ _
      (sum_nonneg f N (fun i hi => hf i (Nat.lt_succ_of_lt hi)))
      (hf N (Nat.lt_succ_self N))

theorem M1_nonneg (r : Nat → Q') (N : Nat)
    (hr : ∀ i, i < N → (0 : Q') ≤ r i) : (0 : Q') ≤ M1 r N :=
  sum_nonneg r N hr

theorem M2_nonneg (r : Nat → Q') (N : Nat) : (0 : Q') ≤ M2 r N :=
  sum_nonneg _ N (fun i _ => SumOfSquares.q_mul_self_nonneg (r i))

theorem M3_nonneg (r : Nat → Q') (N : Nat)
    (hr : ∀ i, i < N → (0 : Q') ≤ r i) : (0 : Q') ≤ M3 r N :=
  sum_nonneg _ N (fun i hi => Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg (r i)) (hr i hi))

/-- The finite off-diagonal pair mass is constructed, also at N=0. -/
theorem first_square_gap_nonneg (r : Nat → Q') : ∀ N,
    (∀ i, i < N → (0 : Q') ≤ r i) →
    (0 : Q') ≤ M1 r N*M1 r N + -(M2 r N)
  | 0, _ => by
      change (0 : Q') ≤ 0*0 + -0
      decide
  | N+1, hr => by
      have hn : ∀ i, i < N → (0 : Q') ≤ r i :=
        fun i hi => hr i (Nat.lt_succ_of_lt hi)
      have hstep : M1 r (N+1)*M1 r (N+1) + -(M2 r (N+1)) ≈
          (M1 r N*M1 r N + -(M2 r N)) + (2*M1 r N)*r N :=
        poly_identity_of_normal_eq
          (.add (.mul (.add (.var 0) (.var 2)) (.add (.var 0) (.var 2)))
            (.neg (.add (.var 1) (.mul (.var 2) (.var 2)))))
          (.add (.add (.mul (.var 0) (.var 0)) (.neg (.var 1)))
            (.mul (.mul (.const 2) (.var 0)) (.var 2)))
          (by decide) (fun | 0 => M1 r N | 1 => M2 r N | _ => r N)
      exact nonneg_of_eqv hstep (Q'.zero_le_add _ _
        (first_square_gap_nonneg r N hn)
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (M1_nonneg r N hn))
          (hr N (Nat.lt_succ_self N))))

private def shiftedSquareSum (r : Nat → Q') (z : Q') (N : Nat) : Q' :=
  finSum (fun i => r i*((r i + -z)*(r i + -z))) N

private theorem shiftedSquareSum_pin (r : Nat → Q') (z : Q') : ∀ N,
    shiftedSquareSum r z N ≈ (M3 r N + -((2*z)*M2 r N)) + (z*z)*M1 r N
  | 0 => poly_identity_of_normal_eq (.const 0)
      (.add (.add (.const 0) (.neg (.mul (.mul (.const 2) (.var 0)) (.const 0))))
        (.mul (.mul (.var 0) (.var 0)) (.const 0)))
      (by decide) (fun _ => z)
  | N+1 => Q'.eqv_trans _ _ _
      (add_congr (shiftedSquareSum_pin r z N) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add
          (.add (.add (.var 2) (.neg (.mul (.mul (.const 2) (.var 3)) (.var 1))))
            (.mul (.mul (.var 3) (.var 3)) (.var 0)))
          (.mul (.var 4) (.mul (.add (.var 4) (.neg (.var 3)))
            (.add (.var 4) (.neg (.var 3))))))
        (.add
          (.add (.add (.var 2) (.mul (.mul (.var 4) (.var 4)) (.var 4)))
            (.neg (.mul (.mul (.const 2) (.var 3))
              (.add (.var 1) (.mul (.var 4) (.var 4))))))
          (.mul (.mul (.var 3) (.var 3)) (.add (.var 0) (.var 4))))
        (by decide) (fun | 0 => M1 r N | 1 => M2 r N | 2 => M3 r N | 3 => z | _ => r N))

/-- The genuine weighted mixture variance, by positive square increments
r_N*sum_(i<N) r_i*(r_i-r_N)^2. No moment inverse or CS premise is used. -/
theorem moment_variance_nonneg (r : Nat → Q') : ∀ N,
    (∀ i, i < N → (0 : Q') ≤ r i) →
    (0 : Q') ≤ M1 r N*M3 r N + -(M2 r N*M2 r N)
  | 0, _ => by
      change (0 : Q') ≤ 0*0 + -(0*0)
      decide
  | N+1, hr => by
      have hn : ∀ i, i < N → (0 : Q') ≤ r i :=
        fun i hi => hr i (Nat.lt_succ_of_lt hi)
      have hs : (0 : Q') ≤ shiftedSquareSum r (r N) N :=
        sum_nonneg _ N (fun i hi => Q'.mul_nonneg _ _ (hn i hi)
          (SumOfSquares.q_mul_self_nonneg (r i + -(r N))))
      have hstep : M1 r (N+1)*M3 r (N+1) + -(M2 r (N+1)*M2 r (N+1)) ≈
          (M1 r N*M3 r N + -(M2 r N*M2 r N)) +
            r N*((M3 r N + -((2*r N)*M2 r N)) + (r N*r N)*M1 r N) :=
        poly_identity_of_normal_eq
          (.add
            (.mul (.add (.var 0) (.var 3))
              (.add (.var 2) (.mul (.mul (.var 3) (.var 3)) (.var 3))))
            (.neg (.mul (.add (.var 1) (.mul (.var 3) (.var 3)))
              (.add (.var 1) (.mul (.var 3) (.var 3))))))
          (.add (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
            (.mul (.var 3) (.add
              (.add (.var 2) (.neg (.mul (.mul (.const 2) (.var 3)) (.var 1))))
              (.mul (.mul (.var 3) (.var 3)) (.var 0)))))
          (by decide) (fun | 0 => M1 r N | 1 => M2 r N | 2 => M3 r N | _ => r N)
      have hsum := add_congr (Q'.eqv_refl (M1 r N*M3 r N + -(M2 r N*M2 r N)))
        (Q'.mul_eqv_congr_left (r N) _ _ (Q'.eqv_symm (shiftedSquareSum_pin r (r N) N)))
      exact nonneg_of_eqv (Q'.eqv_trans _ _ _ hstep hsum)
        (Q'.zero_le_add _ _ (moment_variance_nonneg r N hn)
          (Q'.mul_nonneg _ _ (hr N (Nat.lt_succ_self N)) hs))

def radialA (x : Q') : Q' := 1 + -(x*x)

/-- The PRODUCT radial cost, not a derivative-mixture absolute cap. -/
def productRadialCost (r : Nat → Q') (N : Nat) (x : Q') : Q' :=
  radialA x*M2 r N + x*M1 r N

/-- The cleared radial log-Hessian numerator. For positive M1 its quotient
by M1^2 is the usual expression; no quotient is used in any theorem here. -/
def radialNumerator (r : Nat → Q') (N : Nat) (x : Q') : Q' :=
  radialA x*((2*M1 r N)*M3 r N + -(M2 r N*M2 r N) + -((M1 r N*M1 r N)*M2 r N)) +
    x*(M1 r N*M2 r N + -((M1 r N*M1 r N)*M1 r N))

/-- Exact cancellation retains the entire mixture variance and pair mass. -/
theorem radialNumerator_cancellation (r : Nat → Q') (N : Nat) (x : Q') :
    radialNumerator r N x ≈
      -(M1 r N*M1 r N + -(M2 r N))*productRadialCost r N x +
        (2*radialA x)*(M1 r N*M3 r N + -(M2 r N*M2 r N)) :=
  poly_identity_of_normal_eq
    (.add
      (.mul (.var 3) (.add
        (.add (.mul (.mul (.const 2) (.var 0)) (.var 2)) (.neg (.mul (.var 1) (.var 1))))
        (.neg (.mul (.mul (.var 0) (.var 0)) (.var 1)))))
      (.mul (.var 4) (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.mul (.var 0) (.var 0)) (.var 0))))))
    (.add
      (.mul (.neg (.add (.mul (.var 0) (.var 0)) (.neg (.var 1))))
        (.add (.mul (.var 3) (.var 1)) (.mul (.var 4) (.var 0))))
      (.mul (.mul (.const 2) (.var 3))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 1))))))
    (by decide) (fun | 0 => M1 r N | 1 => M2 r N | 2 => M3 r N | 3 => radialA x | _ => x)

/-- A PRODUCT cost ceiling pays the full cleared derivative-mixture cost,
including N=0. Neither M1 nor a source/density normalizer is inverted. -/
theorem radialMixture_payment_nonneg (r : Nat → Q') (N : Nat) (x C : Q')
    (hr : ∀ i, i < N → (0 : Q') ≤ r i) (hC : (0 : Q') ≤ C)
    (ha : (0 : Q') ≤ radialA x) (hD : productRadialCost r N x ≤ C) :
    (0 : Q') ≤ C*(M1 r N*M1 r N) + radialNumerator r N x := by
  have hsplit : C*(M1 r N*M1 r N) + radialNumerator r N x ≈
      (C + -(productRadialCost r N x))*(M1 r N*M1 r N + -(M2 r N)) +
        (C*M2 r N + (2*radialA x)*(M1 r N*M3 r N + -(M2 r N*M2 r N))) :=
    Q'.eqv_trans _ _ _
      (add_congr (Q'.eqv_refl _) (radialNumerator_cancellation r N x))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 1)))
          (.add (.mul (.neg (.add (.mul (.var 1) (.var 1)) (.neg (.var 2)))) (.var 3))
            (.mul (.mul (.const 2) (.var 4)) (.var 5))))
        (.add
          (.mul (.add (.var 0) (.neg (.var 3)))
            (.add (.mul (.var 1) (.var 1)) (.neg (.var 2))))
          (.add (.mul (.var 0) (.var 2)) (.mul (.mul (.const 2) (.var 4)) (.var 5))))
        (by decide) (fun
          | 0 => C
          | 1 => M1 r N
          | 2 => M2 r N
          | 3 => productRadialCost r N x
          | 4 => radialA x
          | _ => M1 r N*M3 r N + -(M2 r N*M2 r N)))
  exact nonneg_of_eqv hsplit (Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hD) (first_square_gap_nonneg r N hr))
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hC (M2_nonneg r N))
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) ha)
        (moment_variance_nonneg r N hr))))

end YMGap.Continuum.JacobiHeatRadialMixtureCancellation

#print axioms YMGap.Continuum.JacobiHeatRadialMixtureCancellation.M1_nonneg
#print axioms YMGap.Continuum.JacobiHeatRadialMixtureCancellation.M2_nonneg
#print axioms YMGap.Continuum.JacobiHeatRadialMixtureCancellation.M3_nonneg
#print axioms YMGap.Continuum.JacobiHeatRadialMixtureCancellation.first_square_gap_nonneg
#print axioms YMGap.Continuum.JacobiHeatRadialMixtureCancellation.moment_variance_nonneg
#print axioms YMGap.Continuum.JacobiHeatRadialMixtureCancellation.radialNumerator_cancellation
#print axioms YMGap.Continuum.JacobiHeatRadialMixtureCancellation.radialMixture_payment_nonneg
