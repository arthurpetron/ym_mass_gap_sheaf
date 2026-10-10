/-
Finite raw-grid to rational-unit repair for the ACTUAL joint Bernstein weights.
The input polynomial computes its own cube Lipschitz constant. The resulting
bound has no continuous Haar, supplied modulus, or independent marginals.
-/

import YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
import YMGap.Continuum.RatPolyCubeLipschitz
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialRepair

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.QuaternionHaarTensorBernsteinCubature
open YMGap.Continuum.QuaternionHaarTensorBernsteinRepair
open YMGap.Continuum.RatPolyCubeLipschitz
open YMGap.RepTheory.RationalQuaternionNormRepair
open YMGap.RepTheory.RationalQuaternionSphereNets

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem abs_square (d : Q') : Q'.abs d * Q'.abs d ≈ d*d := by
  unfold Q'.abs
  split
  · exact Q'.eqv_refl _
  · exact poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0)) (by decide) (fun _ => d)

/-- Rational Young without a square root or sign restriction on the difference. -/
private theorem young_abs_cleared (tau d D : Q') (hD : d*d ≤ D) :
    2*tau*Q'.abs d ≤ tau*tau+D := by
  let u := Q'.abs d
  have hs := SumOfSquares.q_mul_self_nonneg (tau + -u)
  have hring : 2*tau*u+(tau+-u)*(tau+-u) ≈ tau*tau+u*u :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (.mul (.add (.var 0) (.neg (.var 1)))
          (.add (.var 0) (.neg (.var 1)))))
      (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => tau | _ => u)
  have hu : u*u ≤ D := Q'.le_trans' _ _ _ (Q'.le_of_eqv (abs_square d)) hD
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (2*tau*u) ((tau+-u)*(tau+-u)) hs)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hring)
      (Q'.add_le_add (Q'.le_refl' (tau*tau)) hu))

private theorem two_tau_positive (tau : Q') (htau : (0 : Q') < tau) :
    (0 : Q') < 2*tau := Q'.mul_pos (by decide) htau

private def coordinateBudget (tau : Q') (htau : (0 : Q') < tau) (D : Q') : Q' :=
  (tau*tau+D) * Q'.recipPos (2*tau) (two_tau_positive tau htau)

private theorem coordinateBudget_cancel (tau : Q') (htau : (0 : Q') < tau)
    (D : Q') :
    2*tau*coordinateBudget tau htau D ≈ tau*tau+D := by
  let A := tau*tau+D
  let T := 2*tau
  let r := Q'.recipPos T (two_tau_positive tau htau)
  have hring : T*(A*r) ≈ (T*r)*A :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => T | 1 => A | _ => r)
  exact Q'.eqv_trans _ _ _ hring
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv T (two_tau_positive tau htau)))
      (Q'.one_mul_eqv A))

private theorem abs_le_coordinateBudget (tau : Q') (htau : (0 : Q') < tau)
    (d D : Q') (hD : d*d ≤ D) :
    Q'.abs d ≤ coordinateBudget tau htau D := by
  apply Q'.le_of_mul_le_mul_left (c := 2*tau) _ (two_tau_positive tau htau)
  exact Q'.le_trans' _ _ _ (young_abs_cleared tau d D hD)
    (Q'.ge_of_eqv (coordinateBudget_cancel tau htau D))

private theorem coordinate_difference_square (n k0 k1 k2 k3 index : Nat) :
    (rawEnvironment n k0 k1 k2 k3 index +
      -(repairedEnvironment n k0 k1 k2 k3 index)) *
    (rawEnvironment n k0 k1 k2 k3 index +
      -(repairedEnvironment n k0 k1 k2 k3 index)) ≤
      distSq (repairedQuaternion n k0 k1 k2 k3).val
      (rawQuaternion n k0 k1 k2 k3) := by
  by_cases h : index < 4
  · let i : Fin 4 := ⟨index,h⟩
    have hs := coordinate_difference_square_le
      (rawQuaternion n k0 k1 k2 k3)
      (repairedQuaternion n k0 k1 k2 k3).val i
    have hsym := distance_symm
      (rawQuaternion n k0 k1 k2 k3)
      (repairedQuaternion n k0 k1 k2 k3).val
    have hp :
        (rawEnvironment n k0 k1 k2 k3 index +
          -(repairedEnvironment n k0 k1 k2 k3 index)) *
        (rawEnvironment n k0 k1 k2 k3 index +
          -(repairedEnvironment n k0 k1 k2 k3 index)) ≤
        distSq (rawQuaternion n k0 k1 k2 k3)
        (repairedQuaternion n k0 k1 k2 k3).val := by
      change (environmentOf (rawQuaternion n k0 k1 k2 k3) index +
        -(environmentOf (repairedQuaternion n k0 k1 k2 k3).val index)) *
        (environmentOf (rawQuaternion n k0 k1 k2 k3) index +
        -(environmentOf (repairedQuaternion n k0 k1 k2 k3).val index)) ≤ _
      rw [show index = i.val from rfl]
      rw [environmentOf_coordinate, environmentOf_coordinate]
      exact hs
    exact Q'.le_trans' _ _ _ hp (Q'.le_of_eqv hsym)
  · have hzero : rawEnvironment n k0 k1 k2 k3 index +
        -(repairedEnvironment n k0 k1 k2 k3 index) ≈ 0 := by
      change Q'.eqv
        (environmentOf (rawQuaternion n k0 k1 k2 k3) index +
          -(environmentOf (repairedQuaternion n k0 k1 k2 k3).val index)) 0
      simp only [environmentOf, h, dite_false]
      decide
    have hsq :
        (rawEnvironment n k0 k1 k2 k3 index +
          -(repairedEnvironment n k0 k1 k2 k3 index)) *
        (rawEnvironment n k0 k1 k2 k3 index +
          -(repairedEnvironment n k0 k1 k2 k3 index)) ≈ 0 :=
      Q'.eqv_trans _ _ _ (mul_congr hzero hzero) (Q'.zero_mul_eqv 0)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsq)
      (distance_nonnegative _ _)

private theorem pointwise_polynomial_cleared (n k0 k1 k2 k3 : Nat)
    (h0 : k0 ≤ n+1) (h1 : k1 ≤ n+1)
    (h2 : k2 ≤ n+1) (h3 : k3 ≤ n+1)
    (p : RatPoly) (tau : Q') (htau : (0 : Q') < tau) :
    2*tau * Q'.abs
      (evalRatPoly (rawEnvironment n k0 k1 k2 k3) p +
        -(evalRatPoly (repairedEnvironment n k0 k1 k2 k3) p)) ≤
      polynomialLipschitz p *
        (tau*tau + distSq (repairedQuaternion n k0 k1 k2 k3).val
          (rawQuaternion n k0 k1 k2 k3)) := by
  let D := distSq (repairedQuaternion n k0 k1 k2 k3).val
    (rawQuaternion n k0 k1 k2 k3)
  let delta := coordinateBudget tau htau D
  have hd (index : Nat) : Q'.abs
      (rawEnvironment n k0 k1 k2 k3 index +
        -(repairedEnvironment n k0 k1 k2 k3 index)) ≤ delta :=
    abs_le_coordinateBudget tau htau _ D
      (coordinate_difference_square n k0 k1 k2 k3 index)
  have hp := polynomial_difference
    (rawEnvironment n k0 k1 k2 k3)
    (repairedEnvironment n k0 k1 k2 k3)
    (rawEnvironment_cube n k0 k1 k2 k3 h0 h1 h2 h3)
    (repairedEnvironment_cube n k0 k1 k2 k3) delta hd p
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hp
    (Q'.le_of_lt (two_tau_positive tau htau))
  have hright : (2*tau)*(polynomialLipschitz p*delta) ≈
      polynomialLipschitz p*(tau*tau+D) := by
    have hring : (2*tau)*(polynomialLipschitz p*delta) ≈
        polynomialLipschitz p*((2*tau)*delta) :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => 2*tau | 1 => polynomialLipschitz p | _ => delta)
    exact Q'.eqv_trans _ _ _ hring
      (Q'.mul_eqv_congr_left _ _ _ (coordinateBudget_cancel tau htau D))
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright)

/-- Literal weighted absolute raw-grid-to-repaired-sphere polynomial cost.
All four indices range from zero through `N=n+1`, including endpoints. -/
def repairPolynomialCost (n : Nat) (p : RatPoly) : Q' :=
  sum4 (fun k0 k1 k2 k3 =>
    jointWeightRaw n k0 k1 k2 k3 *
      Q'.abs (evalRatPoly (rawEnvironment n k0 k1 k2 k3) p +
        -(evalRatPoly (repairedEnvironment n k0 k1 k2 k3) p))) (n+2)

/-- The computed finite polynomial Lipschitz constant pays the ACTUAL
same-weight repair loss. `tau` is rational tolerance data; no square root,
degree cutoff, or continuous-Haar premise is hidden here. -/
theorem repairPolynomialCost_cleared (n : Nat) (p : RatPoly)
    (tau : Q') (htau : (0 : Q') < tau) :
    2*tau*repairPolynomialCost n p ≤
      polynomialLipschitz p*(tau*tau+48*Q'.invSucc n) := by
  let L := polynomialLipschitz p
  let w := fun k0 k1 k2 k3 => jointWeightRaw n k0 k1 k2 k3
  let D := fun k0 k1 k2 k3 =>
    distSq (repairedQuaternion n k0 k1 k2 k3).val
      (rawQuaternion n k0 k1 k2 k3)
  let E := fun k0 k1 k2 k3 => Q'.abs
    (evalRatPoly (rawEnvironment n k0 k1 k2 k3) p +
      -(evalRatPoly (repairedEnvironment n k0 k1 k2 k3) p))
  have hpoint (k0 k1 k2 k3 : Nat)
      (h0 : k0<n+2) (h1 : k1<n+2) (h2 : k2<n+2) (h3 : k3<n+2) :
      2*tau*(w k0 k1 k2 k3*E k0 k1 k2 k3) ≤
        L*(tau*tau*w k0 k1 k2 k3+w k0 k1 k2 k3*D k0 k1 k2 k3) := by
    have hp := pointwise_polynomial_cleared n k0 k1 k2 k3
      (by omega) (by omega) (by omega) (by omega) p tau htau
    have hw := jointWeightRaw_nonnegative n k0 k1 k2 k3
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ _ hp hw
    have hleft : 2*tau*(w k0 k1 k2 k3*E k0 k1 k2 k3) ≈
        w k0 k1 k2 k3*(2*tau*E k0 k1 k2 k3) :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide)
        (fun
          | 0 => 2*tau
          | 1 => w k0 k1 k2 k3
          | _ => E k0 k1 k2 k3)
    have hright : w k0 k1 k2 k3*(L*(tau*tau+D k0 k1 k2 k3)) ≈
        L*(tau*tau*w k0 k1 k2 k3+w k0 k1 k2 k3*D k0 k1 k2 k3) :=
      poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.add (.var 2) (.var 3))))
        (.mul (.var 1) (.add (.mul (.var 2) (.var 0))
          (.mul (.var 0) (.var 3))))
        (by decide)
        (fun
          | 0 => w k0 k1 k2 k3
          | 1 => L
          | 2 => tau*tau
          | _ => D k0 k1 k2 k3)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hright))
  have hsum := sum4_le_lt
    (fun a b c d => 2*tau*(w a b c d*E a b c d))
    (fun a b c d => L*(tau*tau*w a b c d+w a b c d*D a b c d))
    (n+2) hpoint
  have hleft : 2*tau*repairPolynomialCost n p ≈
      sum4 (fun a b c d => 2*tau*(w a b c d*E a b c d)) (n+2) :=
    sum4_const_mul (2*tau) _ (n+2)
  have hright :
      sum4 (fun a b c d => L*(tau*tau*w a b c d+w a b c d*D a b c d)) (n+2) ≈
      L*(tau*tau*jointMass n+jointRepairDistance n) := by
    have hfactor := Q'.eqv_symm (sum4_const_mul L
      (fun a b c d => tau*tau*w a b c d+w a b c d*D a b c d) (n+2))
    have hadd := sum4_add
      (fun a b c d => tau*tau*w a b c d)
      (fun a b c d => w a b c d*D a b c d) (n+2)
    have hmass : sum4 (fun a b c d => tau*tau*w a b c d) (n+2) ≈
        tau*tau*jointMass n := by
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (sum4_const_mul (tau*tau) w (n+2)))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_refl _))
    exact Q'.eqv_trans _ _ _ hfactor
      (Q'.mul_eqv_congr_left L _ _
        (Q'.eqv_trans _ _ _ hadd
          (Q'.add_eqv_congr' hmass (Q'.eqv_refl _))))
  have hmass : jointMass n ≈ 1 := jointMass_one n
  have hD : jointRepairDistance n ≤ 48*Q'.invSucc n := jointRepairDistance_le n
  have hbound : L*(tau*tau*jointMass n+jointRepairDistance n) ≤
      L*(tau*tau+48*Q'.invSucc n) := by
    have hterm : tau*tau*jointMass n+jointRepairDistance n ≤
        tau*tau+48*Q'.invSucc n := by
      have hpin : tau*tau*jointMass n ≈ tau*tau :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hmass)
          (Q'.mul_one_eqv _)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.add_eqv_congr' hpin (Q'.eqv_refl _)))
        (Q'.add_le_add (Q'.le_refl' _) hD)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hterm
      (polynomialLipschitz_nonnegative p)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright) hbound))

end YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialRepair

#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialRepair.repairPolynomialCost
#print axioms YMGap.Continuum.QuaternionHaarTensorBernsteinPolynomialRepair.repairPolynomialCost_cleared
