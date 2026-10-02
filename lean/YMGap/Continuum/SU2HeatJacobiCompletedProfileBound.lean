/-
# Original completed SU(2) heat profile under nome squaring

The computed original Jacobi block, the original theta-height comparison,
and the original logarithmic derivative imply, for 16/17 <= q < 1,

  [2(1-x)]^2 K_q(x) <= 40*24576^2*(1-q)^2 K_(q*q)(x).

K is the EXISTING pointwiseHeatCReal, including its original spacing-cutoff
completion. Both x endpoints are included. The differentiated Jacobi and
nome/heat pins are the proved original identities, not new hypotheses.
No heat-minimum reciprocal is used: only positive theta-height and rational
nome factors are cancelled. This is a POINTWISE profile; an ORIGINAL Haar
square certificate, interacting variance alignment and survival remain OPEN.
-/

import YMGap.Continuum.SU2HeatJacobiNearOneProductBound
import YMGap.Continuum.SU2HeatJacobiHeightComparison
import YMGap.Continuum.SU2HeatJacobiNomeWidening
import YMGap.Continuum.JacobiDifferentiatedIdentityOnBox
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.SU2HeatJacobiCompletedProfileBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.SU2HeatJacobiActiveFactorCount
open YMGap.Continuum.SU2HeatJacobiNearOneProductBound
open YMGap.Continuum.SU2HeatJacobiHeightComparison
open YMGap.Continuum.SU2HeatJacobiNomeWidening
open YMGap.Continuum.JacobiTripleProductOnBox
open YMGap.Continuum.JacobiDifferentiatedIdentityOnBox
open YMGap.Continuum.SU2PointwiseHeatPositiveCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion (pointwiseHeatCReal)
open YMGap.Continuum.TuranPositivity (PosEv)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] ThetaConvGen.thetaConvCRealGen
  HKConvGen.sConvCReal_general pointwiseHeatCReal JTPIdentity.dSeriesCReal

private theorem order_of_approx {A B : CReal} (h : ∀ n, A.approx n ≤ B.approx n) :
    leEv A B := by
  intro e he
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _ (h n)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

private theorem transport_order {A B A' B' : CReal}
    (hA : Equiv A A') (hB : Equiv B B') (h : leEv A' B') : leEv A B :=
  leEv_trans (leEv_of_equiv hA) (leEv_trans h (leEv_of_equiv hB.symm))

private theorem T_at_one : ∀ n, Cheb.T n 1 ≈ 1 ∧ Cheb.T (n+1) 1 ≈ 1
  | 0 => ⟨Q'.eqv_refl _,Q'.eqv_refl _⟩
  | n+1 => by
      have h := T_at_one n
      refine ⟨h.2,?_⟩
      rw [Cheb.T_succ_succ]
      exact Q'.eqv_trans _ _ _
        (Cheb.add_eqv_congr _ _ _ _ (Q'.mul_eqv_congr_left _ _ _ h.2)
          (Q'.neg_eqv_congr _ _ h.1))
        (by decide : ((2 : Q')*1)*1 + -1 ≈ (1 : Q'))

private theorem bareTheta_one_le {q : Q'} (hq0 : (0 : Q') ≤ q) : ∀ n,
    (1 : Q') ≤ FiniteJacobiSeriesComparison.bareTheta q 1 n
  | 0 => Q'.le_refl' 1
  | n+1 => by
      have hT : (0 : Q') ≤ Cheb.T (n+1) 1 :=
        Q'.le_trans' _ _ _ Q'.zero_le_one (Q'.ge_of_eqv (T_at_one n).2)
      have hp : (0 : Q') ≤ (2 : Q')*q^((n+1)*(n+1))*Cheb.T (n+1) 1 :=
        Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide)
          (Q'.pow_nonneg q hq0 _)) hT
      exact Q'.le_trans' _ _ _ (bareTheta_one_le hq0 n)
        (Q'.add_le_self_of_nonneg _ _ hp)

private theorem theta_height_positive {q : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) :
    PosEv (ThetaConvGen.thetaConvCRealGen hq0 hq1 (by decide) (Q'.le_refl' 1)) := by
  have hfloor : leEv cone (fullThetaSeries hq0 hq1 (Q'.le_refl' 1) (by decide)) :=
    leEv_ofQ'_of_approx_ge (fun n => Q'.le_trans' _ _ _
      (bareTheta_one_le (Q'.le_of_lt hq0) n)
      (Q'.ge_of_eqv (fullThetaSeries_approx hq0 hq1 (Q'.le_refl' 1) (by decide) n)))
  exact ⟨1,by decide,leEv_trans hfloor (leEv_of_equiv
    (thetaProduct_eq_fullThetaSeries hq0 hq1 (Q'.le_refl' 1) (by decide)).symm)⟩

/-- The actual original completed theta products have a nome-gap-squared
profile, after cancelling their original positive widened height. -/
theorem thetaProduct_nome_gap_bound {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    leEv (mul (ofQ' ((1-x)*(1-x))) (ThetaConvGen.thetaConvCRealGen hq0 hq1 hxlo hxhi))
      (mul (ofQ' (2*(((24576 : Q')*24576)*((1-q)*(1-q)))))
        (ThetaConvGen.thetaConvCRealGen (HKPos.q_mul_pos hq0 hq0)
          (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi)) := by
  let T := ThetaConvGen.thetaConvCRealGen hq0 hq1 hxlo hxhi
  let T2 := ThetaConvGen.thetaConvCRealGen (HKPos.q_mul_pos hq0 hq0)
    (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi
  let H := ThetaConvGen.thetaConvCRealGen hq0 hq1 (by decide) (Q'.le_refl' 1)
  let H2 := ThetaConvGen.thetaConvCRealGen (HKPos.q_mul_pos hq0 hq0)
    (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) (by decide) (Q'.le_refl' 1)
  let z := (1-x)*(1-x)
  let c := ((24576 : Q')*24576)*((1-q)*(1-q))
  have hcross : leEv (mul (mul (ofQ' z) T) H2) (mul (mul (ofQ' c) T2) H) := by
    intro e he
    refine ⟨activeFactorStart q+activeFactorCount q,fun n hn => ?_⟩
    have h := Ppart_nome_gap_bound hq hq1 hxlo hxhi n hn
    have hl : (z*ThetaConv.Ppart q x n)*ThetaConv.Ppart (q*q) 1 n ≈
        z*(ThetaConv.Ppart q x n*ThetaConv.Ppart (q*q) 1 n) := Q'.mul_assoc_eqv _ _ _
    have hr : (c*ThetaConv.Ppart (q*q) x n)*ThetaConv.Ppart q 1 n ≈
        c*(ThetaConv.Ppart q 1 n*ThetaConv.Ppart (q*q) x n) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.var 0) (.mul (.var 2) (.var 1)))
        (by decide) (fun
          | 0 => c
          | 1 => ThetaConv.Ppart (q*q) x n
          | _ => ThetaConv.Ppart q 1 n)
    change (z*T.approx n)*H2.approx n ≤ (c*T2.approx n)*H.approx n+e
    simp only [T,T2,H,H2,ThetaConvGen.thetaConvCRealGen_approx]
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hr)
        (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))))
  have hc0 : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide)
    (SumOfSquares.q_mul_self_nonneg (1-q))
  have hB0 : leEv czero (mul (ofQ' c) T2) :=
    leEv_ofQ'_of_approx_ge (fun n => Q'.mul_nonneg _ _ hc0
      (ThetaConvGen.thetaConvCRealGen_approx_nonneg _ _ hxlo hxhi n))
  have hh := CReal.leEv_mul_nonneg_left hB0 (thetaProduct_squared_nome_height hq0 hq1)
  have he : Equiv (mul (mul (ofQ' c) T2) (mul (ofQ' 2) H2))
      (mul (mul (ofQ' (2*c)) T2) H2) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.const 2) (.var 2)))
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 2))
      (by decide) (fun | 0 => c | 1 => T2.approx n | _ => H2.approx n))
  exact leEv_cancel_mul_right_posEv
    (theta_height_positive (HKPos.q_mul_pos hq0 hq0)
      (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1))
    (leEv_trans hcross (leEv_trans hh (leEv_of_equiv he)))

private theorem Spart_add_le {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) (n : Nat) : ∀ d,
    HKConv.Spart q x n ≤ HKConv.Spart q x (n+d)
  | 0 => Q'.le_refl' _
  | d+1 => by
      rw [show n+(d+1)=n+d+1 from by omega,HKConv.Spart_succ]
      exact Q'.le_trans' _ _ _ (Spart_add_le hq0 hq1 hxlo n d)
        (Q'.add_le_self_of_nonneg _ _ (HKConv.sTerm_nonneg hq0 hq1 hxlo (n+d)))

/-- The existing completed original logarithmic derivative widens with
coefficient five; positive-term monotonicity removes the finite doubled prefix. -/
theorem sFactor_nome_widening {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) :
    leEv (mul (ofQ' q) (HKConvGen.sConvCReal_general hq0 hq1 hxlo))
      (mul (ofQ' 5) (HKConvGen.sConvCReal_general (HKPos.q_mul_pos hq0 hq0)
        (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo)) := by
  apply order_of_approx
  intro n
  change q*(HKConvGen.sConvCReal_general hq0 hq1 hxlo).approx n ≤
    5*(HKConvGen.sConvCReal_general (HKPos.q_mul_pos hq0 hq0)
      (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo).approx n
  simp only [HKConvGen.sConvCReal_general_approx]
  have hm := Spart_add_le hq0 hq1 hxlo n n
  rw [show n+n=2*n from by omega] at hm
  have hq5 : 4+q ≤ (5 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 4 _ _ (Q'.le_of_lt hq1)) (by decide : (4 : Q')+1 ≤ 5)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ q hm (Q'.le_of_lt hq0))
    (Q'.le_trans' _ _ _ (Spart_nome_widening hq0 hq1 hxlo n)
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hq5 (HKConv.Spart_nonneg
        (HKPos.q_mul_pos hq0 hq0) (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo n)))

/-- The SAME original completed theta/derivative product retains the
quadratic profile. This is before undoing the exact original nome scaling. -/
theorem Rproduct_nome_gap_bound {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    leEv (mul (ofQ' (((1-x)*(1-x))*q)) (JTPIdentity.Rproduct hq0 hq1 hxlo hxhi))
      (mul (ofQ' (10*(((24576 : Q')*24576)*((1-q)*(1-q)))))
        (JTPIdentity.Rproduct (HKPos.q_mul_pos hq0 hq0)
          (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi)) := by
  let T := ThetaConvGen.thetaConvCRealGen hq0 hq1 hxlo hxhi
  let T2 := ThetaConvGen.thetaConvCRealGen (HKPos.q_mul_pos hq0 hq0)
    (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi
  let S := HKConvGen.sConvCReal_general hq0 hq1 hxlo
  let S2 := HKConvGen.sConvCReal_general (HKPos.q_mul_pos hq0 hq0)
    (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo
  let z := (1-x)*(1-x)
  let c := ((24576 : Q')*24576)*((1-q)*(1-q))
  have hc0 : (0 : Q') ≤ c := Q'.mul_nonneg _ _ (by decide)
    (SumOfSquares.q_mul_self_nonneg (1-q))
  have hSq : leEv czero (mul (ofQ' q) S) := leEv_ofQ'_of_approx_ge (fun n =>
    Q'.mul_nonneg _ _ (Q'.le_of_lt hq0) (HKConvGen.sConvCReal_general_approx_nonneg hq0 hq1 hxlo n))
  have hT2 : leEv czero (mul (ofQ' (2*c)) T2) := leEv_ofQ'_of_approx_ge (fun n =>
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hc0)
      (ThetaConvGen.thetaConvCRealGen_approx_nonneg _ _ hxlo hxhi n))
  have ht := CReal.leEv_mul_nonneg_left hSq (thetaProduct_nome_gap_bound hq0 hq1 hq hxlo hxhi)
  have hs := CReal.leEv_mul_nonneg_left hT2 (sFactor_nome_widening hq0 hq1 hxlo)
  have hl : Equiv (mul (ofQ' (z*q)) (mul T S))
      (mul (mul (ofQ' q) S) (mul (ofQ' z) T)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 1) (.var 3)) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => z | 1 => q | 2 => T.approx n | _ => S.approx n))
  have hr : Equiv (mul (ofQ' (10*c)) (mul T2 S2))
      (mul (mul (ofQ' (2*c)) T2) (mul (ofQ' 5) S2)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.mul (.mul (.const 10) (.var 0)) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.mul (.const 5) (.var 2)))
      (by decide) (fun | 0 => c | 1 => T2.approx n | _ => S2.approx n))
  exact transport_order hl hr (leEv_trans ht
    (leEv_trans (leEv_of_equiv (CRealAlg.cmul_comm _ _)) hs))

private theorem original_heat_product_pin {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    Equiv (JTPIdentity.Rproduct hq0 hq1 hxlo hxhi)
      (mul (ofQ' (2*q)) (pointwiseHeatCReal hq0 hq1 hxlo hxhi)) := by
  let K := pointwiseHeatCReal hq0 hq1 hxlo hxhi
  let R := JTPIdentity.Rproduct hq0 hq1 hxlo hxhi
  have hj : Equiv (mul (ofQ' q) K) (JTPIdentity.Rhalf hq0 hq1 hxlo hxhi) :=
    (nomeScaledPointwiseHeatCReal_equiv_dSeriesCReal hq0 hq1 hxlo hxhi).trans
      (diffJTP hq0 hq1 hxlo hxhi)
  have hdouble := CRealContinuumAlg.cmul_congr_right (A := ofQ' 2) hj
  have hr : Equiv (mul (ofQ' 2) (JTPIdentity.Rhalf hq0 hq1 hxlo hxhi)) R :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv 2 HalfPow.half (R.approx n)))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (by decide : (2 : Q')*HalfPow.half ≈ 1)) (Q'.one_mul_eqv _)))
  have hk : Equiv (mul (ofQ' 2) (mul (ofQ' q) K)) (mul (ofQ' (2*q)) K) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_symm (Q'.mul_assoc_eqv 2 q (K.approx n)))
  exact (hdouble.trans hr).symm.trans hk

/-- The original completed heat kernel, not merely the derivative series,
has the nome-gap-squared pointwise profile. -/
theorem pointwiseHeat_nome_gap_bound {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    leEv (mul (ofQ' ((1-x)*(1-x))) (pointwiseHeatCReal hq0 hq1 hxlo hxhi))
      (mul (ofQ' (10*(((24576 : Q')*24576)*((1-q)*(1-q)))))
        (pointwiseHeatCReal (HKPos.q_mul_pos hq0 hq0)
          (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi)) := by
  let K := pointwiseHeatCReal hq0 hq1 hxlo hxhi
  let K2 := pointwiseHeatCReal (HKPos.q_mul_pos hq0 hq0)
    (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi
  let z := (1-x)*(1-x)
  let c := 10*(((24576 : Q')*24576)*((1-q)*(1-q)))
  let f := 2*(q*q)
  have hRq := original_heat_product_pin hq0 hq1 hxlo hxhi
  have hR2 := original_heat_product_pin (HKPos.q_mul_pos hq0 hq0)
    (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi
  have hL : Equiv (mul (ofQ' (z*q)) (JTPIdentity.Rproduct hq0 hq1 hxlo hxhi))
      (mul (mul (ofQ' z) K) (ofQ' f)) :=
    (CRealContinuumAlg.cmul_congr_right hRq).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.mul (.const 2) (.mul (.var 1) (.var 1))))
        (by decide) (fun | 0 => z | 1 => q | _ => K.approx n)))
  have hR : Equiv (mul (ofQ' c) (JTPIdentity.Rproduct (HKPos.q_mul_pos hq0 hq0)
      (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi))
      (mul (mul (ofQ' c) K2) (ofQ' f)) :=
    (CRealContinuumAlg.cmul_congr_right hR2).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.mul (.var 0) (.var 2)) (.var 1))
        (by decide) (fun | 0 => c | 1 => f | _ => K2.approx n)))
  have hf : (0 : Q') < f := HKPos.q_mul_pos (by decide) (HKPos.q_mul_pos hq0 hq0)
  exact leEv_cancel_mul_right_posEv ⟨f,hf,leEv_refl _⟩
    (transport_order hL.symm hR.symm (Rproduct_nome_gap_bound hq0 hq1 hq hxlo hxhi))

/-- Actual chord r=2(1-x)=2-chi_1 has a uniform quartic completed profile.
This pointwise order does NOT construct a Haar polynomial certificate. -/
theorem pointwiseHeat_chord_quartic_bound {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hq : Q'.mkPos 16 17 (by decide) ≤ q)
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) :
    leEv (mul (ofQ' ((2*(1-x))*(2*(1-x)))) (pointwiseHeatCReal hq0 hq1 hxlo hxhi))
      (mul (ofQ' (40*(((24576 : Q')*24576)*((1-q)*(1-q)))))
        (pointwiseHeatCReal (HKPos.q_mul_pos hq0 hq0)
          (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi)) := by
  have h4 : leEv czero (ofQ' 4) :=
    leEv_ofQ'_of_approx_ge (fun _ => (by decide : (0 : Q') ≤ 4))
  have h := CReal.leEv_mul_nonneg_left h4
    (pointwiseHeat_nome_gap_bound hq0 hq1 hq hxlo hxhi)
  apply transport_order (B' := mul (ofQ' 4)
    (mul (ofQ' (10*(((24576 : Q')*24576)*((1-q)*(1-q)))))
      (pointwiseHeatCReal (HKPos.q_mul_pos hq0 hq0)
        (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi))) ?_ ?_ h
  · exact SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0))) (.var 1))
      (.mul (.const 4) (.mul (.mul (.var 0) (.var 0)) (.var 1)))
      (by decide) (fun | 0 => 1-x | _ => (pointwiseHeatCReal hq0 hq1 hxlo hxhi).approx n))
  · exact SumOfSquares.Equiv_of_approx_eqv (fun n => poly_identity_of_normal_eq
      (.mul (.mul (.const 40) (.var 0)) (.var 1))
      (.mul (.const 4) (.mul (.mul (.const 10) (.var 0)) (.var 1)))
      (by decide) (fun
        | 0 => ((24576 : Q')*24576)*((1-q)*(1-q))
        | _ => (pointwiseHeatCReal (HKPos.q_mul_pos hq0 hq0)
          (FiniteJacobiCoefficients.square_base_lt_one hq0 hq1) hxlo hxhi).approx n))

#print axioms thetaProduct_nome_gap_bound
#print axioms sFactor_nome_widening
#print axioms Rproduct_nome_gap_bound
#print axioms pointwiseHeat_nome_gap_bound
#print axioms pointwiseHeat_chord_quartic_bound

end YMGap.Continuum.SU2HeatJacobiCompletedProfileBound
