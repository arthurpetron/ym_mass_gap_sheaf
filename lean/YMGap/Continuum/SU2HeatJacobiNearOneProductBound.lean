/-
# A computed nome-gap bound on original finite Jacobi products

The block start, count and amplitude bounds are produced by
`SU2HeatJacobiActiveFactorCount`, not supplied as assumptions. Retaining its
quadratic amplification yields the original cross-normalized finite bound

  (1-x)^2 P_q(x) P_(q*q)(1)
    <= 24576^2 (1-q)^2 P_q(1) P_(q*q)(x).

The cutoff must actually contain the computed block. All original Euler
prefactors are present. No heat-floor reciprocal or global product estimate
is assumed. Passing original limits, theta-height comparison, an ORIGINAL
Haar square certificate and survival are separate obligations.
-/

import YMGap.Continuum.SU2HeatJacobiActiveFactorCount
import YMGap.Continuum.SU2HeatJacobiProductAmplification

namespace YMGap.Continuum.SU2HeatJacobiNearOneProductBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount
open YMGap.Continuum.SU2HeatJacobiProductAmplification
open YMGap.Continuum.ThetaConv (Ppart)
open YMGap.Continuum.HKConv (mul_le_mul')
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem count_le_three_halves (N : Nat) (hN : 2 ≤ N) : N ≤ 3*(N/2) := by
  have hd := Nat.div_add_mod N 2
  have hr := Nat.mod_lt N (by decide : 0 < 2)
  omega

/-- The computed floor-half count still carries a positive nome-gap mass. -/
theorem activeFactorHalfCount_mass {q : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q')) :
    Q'.mkPos 1 48 (by decide) ≤ Q'.ofNat (activeFactorCount q/2)*(1-q) := by
  let N := activeFactorCount q
  let n := N/2
  let r : Q' := Q'.mkPos 1 3 (by decide)
  have hc : Q'.ofNat N ≤ 3*Q'.ofNat n := by
    have hn := count_le_three_halves N (activeFactorCount_two hq hq1)
    show (N : Int)*1 ≤ (3*(n : Int))*1
    dsimp only [n]
    omega
  have hm : Q'.mkPos 1 16 (by decide) ≤ (3*Q'.ofNat n)*(1-q) :=
    Q'.le_trans' _ _ _ (activeFactorCount_mass hq hq1)
      (Q'.mul_le_mul_of_nonneg_right _ _ (1-q) hc
        (Q'.le_of_lt (HKPos.one_sub_pos hq1)))
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ r hm (by decide)
  have hp : r*((3*Q'.ofNat n)*(1-q)) ≈ Q'.ofNat n*(1-q) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.const 3) (.var 1)) (.var 2)))
      (.mul (.mul (.var 0) (.const 3)) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => r | 1 => Q'.ofNat n | _ => 1-q))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide : r*3 ≈ (1 : Q')))
        (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (by decide : r*(Q'.mkPos 1 16 (by decide)) ≈ Q'.mkPos 1 48 (by decide)))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hp))

/-- Actual finite original products with no supplied block or global bound.
Both x endpoints and equality at q=16/17 are included. -/
theorem Ppart_nome_gap_bound {q x : Q'}
    (hq : Q'.mkPos 16 17 (by decide) ≤ q) (hq1 : q < (1 : Q'))
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (M : Nat) (hM : activeFactorStart q+activeFactorCount q ≤ M) :
    ((1-x)*(1-x))*(Ppart q x M*Ppart (q*q) 1 M) ≤
      ((24576 : Q')*24576)*((1-q)*(1-q))*(Ppart q 1 M*Ppart (q*q) x M) := by
  let n := Q'.ofNat (activeFactorCount q/2)
  let r : Q' := Q'.mkPos 1 512 (by decide)
  let k : Q' := 24576
  let z := 1-x
  let d := 1-q
  let L := Ppart q x M*Ppart (q*q) 1 M
  let R := Ppart q 1 M*Ppart (q*q) x M
  have hq0 : (0 : Q') < q := by
    have h := hq
    change 16*(q.den : Int) ≤ q.num*17 at h
    have hd0 : (0 : Int) < (q.den : Int) := by exact_mod_cast q.den_pos
    exact CReal.pos_of_num_pos (by omega)
  have hd : (0 : Q') ≤ d := Q'.le_of_lt (HKPos.one_sub_pos hq1)
  have hz : (0 : Q') ≤ z := Q'.sub_nonneg_of_le hxhi
  have hn : (0 : Q') ≤ n := by
    show (0 : Int)*1 ≤ ((activeFactorCount q/2 : Nat) : Int)*1
    omega
  have hkd : (0 : Q') ≤ k*d := Q'.mul_nonneg _ _ (by decide) hd
  have hnr : (0 : Q') ≤ n*r*z := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ hn (by decide)) hz
  have hL : (0 : Q') ≤ L := Q'.mul_nonneg _ _
    (ThetaConv.Ppart_nonneg hq0 hq1 hxlo M)
    (ThetaConv.Ppart_nonneg (HKPos.q_mul_pos hq0 hq0)
      (HKPos.q_lt_of_le_of_lt
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right q 1 q (Q'.le_of_lt hq1) (Q'.le_of_lt hq0))
          (Q'.le_of_eqv (Q'.one_mul_eqv q))) hq1) (by decide) M)
  have hmass := activeFactorHalfCount_mass hq hq1
  have h48 := Q'.mul_le_mul_of_nonneg_left _ _ (48 : Q') hmass (by decide)
  have he : (k*d)*(n*r) ≈ 48*(n*d) := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => k | 1 => d | 2 => n | _ => r))
    (Q'.mul_eqv_congr_right _ _ _ (by decide : k*r ≈ (48 : Q')))
  have hc : (1 : Q') ≤ (k*d)*(n*r) := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (by decide : (48 : Q')*(Q'.mkPos 1 48 (by decide)) ≈ (1 : Q')))
    (Q'.le_trans' _ _ _ h48 (Q'.ge_of_eqv he))
  have hlin : z ≤ (k*d)*(n*r*z) := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv z))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ z hc hz)
      (Q'.le_of_eqv (Q'.mul_assoc_eqv (k*d) (n*r) z)))
  have hsquare := mul_le_mul' hz (Q'.mul_nonneg _ _ hkd hnr) hlin hlin
  have hweighted := Q'.mul_le_mul_of_nonneg_right _ _ L hsquare hL
  have hquad := Ppart_block_quadratic_amplification hq0 hq1 hxlo hxhi
    (activeFactorStart q) (activeFactorCount q) M hM
    (activeFactor_amplitude_bounds hq hq1)
  have hscale : (0 : Q') ≤ (k*k)*(d*d) := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (by decide) (by decide)) (Q'.mul_nonneg _ _ hd hd)
  have hprod := Q'.mul_le_mul_of_nonneg_left _ _ ((k*k)*(d*d)) hquad hscale
  have hp : (((k*d)*(n*r*z))*((k*d)*(n*r*z)))*L ≈
      ((k*k)*(d*d))*(L*quadraticAmplification x (activeFactorCount q)) := by
    change (((k*d)*(n*r*z))*((k*d)*(n*r*z)))*L ≈
      ((k*k)*(d*d))*(L*((n*(r*z))*(n*(r*z))))
    exact poly_identity_of_normal_eq
      (.mul (.mul
        (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.var 2) (.var 3)) (.var 4)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.var 2) (.var 3)) (.var 4)))) (.var 5))
      (.mul (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.var 5) (.mul
          (.mul (.var 2) (.mul (.var 3) (.var 4)))
          (.mul (.var 2) (.mul (.var 3) (.var 4))))))
      (by decide) (fun | 0 => k | 1 => d | 2 => n | 3 => r | 4 => z | _ => L)
  have hl : (z*z)*L ≤ ((k*k)*(d*d))*R := Q'.le_trans' _ _ _ hweighted
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) hprod)
  exact hl

#print axioms activeFactorHalfCount_mass
#print axioms Ppart_nome_gap_bound

end YMGap.Continuum.SU2HeatJacobiNearOneProductBound
