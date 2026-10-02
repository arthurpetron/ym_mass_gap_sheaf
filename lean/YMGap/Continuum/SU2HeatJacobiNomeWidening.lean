/-
# Finite Jacobi logarithmic-derivative nome widening

Pair the ACTUAL terms with amplitudes q^(4n+1), q^(4n+3) against
(q*q)^(2n+1). Clearing q gives q*S_q(2N) <= (4+q)*S_(q*q)(N),
for every strict nome and x >= -1, including the class endpoint -1.
No heat floor, source assumption, or near-one guard is used.

This supplies the logarithmic-derivative factor of the prospective original
heat-profile comparison. The normalized theta-product comparison and the
original Haar polynomial shape certificate remain separate OPEN tasks.
No original-source energy, relative variance or survival bound follows here.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatJacobiNomeWidening

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.HKPos (factor factorLB two geoAmp)
open YMGap.Continuum.HKConv (sTerm Spart)

local infix:50 " ≈ " => Q'.eqv

private theorem add_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ c hab)
    (Q'.add_eqv_congr_left b _ _ hcd)

private theorem factor_congr {a b : Q'} (h : a ≈ b) (x : Q') :
    factor a x ≈ factor b x :=
  Q'.add_eqv_congr_left 1 _ _ (add_congr
    (Q'.mul_eqv_congr_right _ _ x (add_congr h h))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a h)
      (Q'.mul_eqv_congr_left b _ _ h)))

private theorem square_mono {a b : Q'} (ha : (0 : Q') ≤ a) (h : a ≤ b) :
    a*a ≤ b*b :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ a h ha)
    (Q'.mul_le_mul_of_nonneg_left _ _ b h (Q'.le_trans' _ _ _ ha h))

private theorem quotient_scaled_le (na nb da db c d : Q')
    (hda : (0 : Q') < da) (hdb : (0 : Q') < db)
    (h : (c*na)*db ≤ (d*nb)*da) :
    c*HKConv.divPos na da ≤ d*HKConv.divPos nb db := by
  have pa := HKConv.divPos_mul_eqv (p := na) (CReal.num_pos_of_pos hda)
  have pb := HKConv.divPos_mul_eqv (p := nb) (CReal.num_pos_of_pos hdb)
  have transport (z v a b : Q') (hz : z*a ≈ v) :
      (a*b)*(c*z) ≈ (c*v)*b :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 2) (.mul (.var 3) (.var 0))) (.var 1))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => z))
      (Q'.mul_eqv_congr_right _ _ b (Q'.mul_eqv_congr_left c _ _ hz))
  have left := transport (HKConv.divPos na da) na da db pa
  have right : (da*db)*(d*HKConv.divPos nb db) ≈ (d*nb)*da :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 2) (.mul (.var 3) (.var 1))) (.var 0))
      (by decide) (fun | 0 => da | 1 => db | 2 => d | _ => HKConv.divPos nb db))
      (Q'.mul_eqv_congr_right _ _ da (Q'.mul_eqv_congr_left d _ _ pb))
  exact HKConvGen.mul_le_mul_left_cancel (HKPos.q_mul_pos hda hdb)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv left)
      (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv right)))

/-- Increasing the positive Jacobi amplitude increases its actual quotient.
The cleared difference is 2*(b-a)*(1-a*b), uniformly for x >= -1. -/
private theorem quotient_amplitude_mono {a b x : Q'}
    (ha : (0 : Q') ≤ a) (hb : b < (1 : Q')) (hab : a ≤ b)
    (hx : (-1 : Q') ≤ x) :
    HKConv.divPos (two a) (factor a x) ≤
      HKConv.divPos (two b) (factor b x) := by
  have hb0 := Q'.le_trans' _ _ _ ha hab
  have ha1 := HKPos.q_lt_of_le_of_lt hab hb
  have hab1 : a*b ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right a 1 b (Q'.le_of_lt ha1) hb0)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv b)) (Q'.le_of_lt hb))
  have hn : (0 : Q') ≤ 2*((b-a)*(1-a*b)) :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hab) (Q'.sub_nonneg_of_le hab1))
  have hp : (0 : Q') ≤ (two b)*factor a x + -((two a)*factor b x) :=
    Q'.le_trans' _ _ _ hn (Q'.ge_of_eqv (poly_identity_of_normal_eq
      (.add
        (.mul (.add (.var 1) (.var 1))
          (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.var 2))
            (.mul (.var 0) (.var 0)))))
        (.neg (.mul (.add (.var 0) (.var 0))
          (.add (.const 1) (.add (.mul (.add (.var 1) (.var 1)) (.var 2))
            (.mul (.var 1) (.var 1)))))))
      (.mul (.const 2) (.mul (.add (.var 1) (.neg (.var 0)))
        (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))))
      (by decide) (fun | 0 => a | 1 => b | _ => x)))
  have H := quotient_scaled_le (two a) (two b) (factor a x) (factor b x) 1 1
    (HKPos.factor_pos ha ha1 hx) (HKPos.factor_pos hb0 hb hx)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
        (Q'.one_mul_eqv (two a))))
      (Q'.le_trans' _ _ _ (Q'.le_of_sub_nonneg hp)
        (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (two b))))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _))
    (Q'.le_trans' _ _ _ H (Q'.le_of_eqv (Q'.one_mul_eqv _)))

private theorem factor_contract_four {a q x : Q'}
    (ha : (0 : Q') ≤ a) (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ (1 : Q'))
    (haq : a ≤ q) (hx : (-1 : Q') ≤ x) :
    factor (a*q) x ≤ 4*factor a x := by
  have ha1 := Q'.le_trans' _ _ _ haq hq1
  have hgap := Q'.sub_nonneg_of_le hq1
  have hfirst : a*(1-q) ≤ 1-a :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ haq hgap)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right q 1 (1-q) hq1 hgap)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
          (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg haq))))
  have htwice : 1-a*q ≤ 2*(1-a) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.const 1) (.neg (.var 0)))
        (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))))
      (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => a | _ => q)))
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left (1-a) _ _ hfirst)
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0))
          (by decide) (fun _ => 1-a))))
  have haq1 : a*q ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right a 1 q ha1 hq0)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv q)) hq1)
  have hs := square_mono (Q'.sub_nonneg_of_le haq1) htwice
  have hbase : (0 : Q') ≤ (2*(1-a))*(2*(1-a)) + -((1-a*q)*(1-a*q)) :=
    Q'.sub_nonneg_of_le hs
  have hx0 : (0 : Q') ≤ x+1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q') ≈ (-1)+1))
      (Q'.add_le_add_right _ _ 1 hx)
  have hc : (0 : Q') ≤ 2*a*(4-q) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) ha)
      (Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _ hq1 (by decide)))
  have hp := Q'.zero_le_add _ _ hbase (Q'.mul_nonneg _ _ hc hx0)
  have he : 4*factor a x + -(factor (a*q) x) ≈
      ((2*(1-a))*(2*(1-a)) + -((1-a*q)*(1-a*q))) +
        (2*a*(4-q))*(x+1) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 4) (.add (.const 1)
        (.add (.mul (.add (.var 0) (.var 0)) (.var 2)) (.mul (.var 0) (.var 0)))))
        (.neg (.add (.const 1) (.add
          (.mul (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 2))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))))
      (.add (.add
        (.mul (.mul (.const 2) (.add (.const 1) (.neg (.var 0))))
          (.mul (.const 2) (.add (.const 1) (.neg (.var 0)))))
        (.neg (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))
          (.add (.const 1) (.neg (.mul (.var 0) (.var 1)))))))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.add (.const 4) (.neg (.var 1))))
          (.add (.var 2) (.const 1))))
      (by decide) (fun | 0 => a | 1 => q | _ => x)
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv he))

private theorem square_power (q : Q') : ∀ n : Nat, (q*q)^n ≈ q^(2*n)
  | 0 => Q'.eqv_refl 1
  | n+1 => by
      have htwo : q*q ≈ q^2 :=
        Q'.eqv_symm (Q'.mul_eqv_congr_left q _ _ (Q'.mul_one_eqv q))
      have he : 2*(n+1)=2+2*n := by omega
      rw [he]
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (q*q) _ _ (square_power q n))
          (Q'.mul_eqv_congr_right _ _ (q^(2*n)) htwo))
        (Q'.eqv_symm (Q'.pow_add_eqv q 2 (2*n)))

private theorem amplitude_pins (q : Q') (n : Nat) :
    geoAmp (q*q) n ≈ geoAmp q (2*n)*q ∧
      geoAmp q (2*n+1) ≈ geoAmp (q*q) n*q := by
  have e0 : 2*(2*n)+1=4*n+1 := by omega
  have e1 : 2*(2*n+1)=4*n+2 := by omega
  have e2 : 2*(2*n+1)+1=4*n+3 := by omega
  have hm : geoAmp (q*q) n ≈ q^(4*n+2) := by
    unfold geoAmp
    simpa only [e1] using square_power q (2*n+1)
  constructor
  · unfold geoAmp
    rw [e0]
    exact Q'.eqv_trans _ _ _ hm (Q'.mul_comm_eqv q (q^(4*n+1)))
  · unfold geoAmp at ⊢
    rw [e2]
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q (q^(4*n+2)))
      (Q'.mul_eqv_congr_right _ _ q (Q'.eqv_symm hm))

/-- Two literal original Jacobi terms are paid by the matching widened term.
The leading nome is cleared; no reciprocal nome or heat floor appears. -/
theorem sTerm_pair_bound {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hx : (-1 : Q') ≤ x) (n : Nat) :
    q*(sTerm q x (2*n)+sTerm q x (2*n+1)) ≤ (4+q)*sTerm (q*q) x n := by
  let a := geoAmp q (2*n)
  let b := geoAmp (q*q) n
  let d := geoAmp q (2*n+1)
  have hq0' := Q'.le_of_lt hq0
  have hq1' := Q'.le_of_lt hq1
  have hq2 : q*q < (1 : Q') := HKPos.q_lt_of_le_of_lt
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right q 1 q hq1' hq0')
      (Q'.le_of_eqv (Q'.one_mul_eqv q))) hq1
  have ha := HKPos.pow_succ_pos_lt_one hq0 hq1 (2*(2*n))
  have hb := HKPos.pow_succ_pos_lt_one (HKPos.q_mul_pos hq0 hq0) hq2 (2*n)
  have hd := HKPos.pow_succ_pos_lt_one hq0 hq1 (2*(2*n+1))
  have haq : a ≤ q := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone hq0' hq1' (by omega : 1 ≤ 2*(2*n)+1))
    (Q'.le_of_eqv (Q'.mul_one_eqv q))
  have pins := amplitude_pins q n
  have hevenFactor : factor b x ≤ 4*factor a x :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (factor_congr pins.1 x))
      (factor_contract_four (Q'.le_of_lt ha.1) hq0' hq1' haq hx)
  have hnum : q*two a ≈ two b :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.var 1) (.var 1)))
      (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0)))
      (by decide) (fun | 0 => q | _ => a))
      (add_congr (Q'.eqv_symm pins.1) (Q'.eqv_symm pins.1))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (two b) hevenFactor
    (HKPos.two_nonneg (Q'.le_of_lt hb.1))
  have heven : q*sTerm q x (2*n) ≤ 4*sTerm (q*q) x n :=
    quotient_scaled_le (two a) (two b) (factor a x) (factor b x) q 4
      (HKPos.factor_pos (Q'.le_of_lt ha.1) ha.2 hx)
      (HKPos.factor_pos (Q'.le_of_lt hb.1) hb.2 hx)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hnum))
        (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv
          (poly_identity_of_normal_eq
            (.mul (.var 0) (.mul (.const 4) (.var 1)))
            (.mul (.mul (.const 4) (.var 0)) (.var 1))
            (by decide) (fun | 0 => two b | _ => factor a x)))))
  have hdb : d ≤ b := Q'.le_trans' _ _ _ (Q'.le_of_eqv pins.2)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left q 1 b hq1' (Q'.le_of_lt hb.1))
      (Q'.le_of_eqv (Q'.mul_one_eqv b)))
  have hodd : sTerm q x (2*n+1) ≤ sTerm (q*q) x n :=
    quotient_amplitude_mono (Q'.le_of_lt hd.1) hb.2 hdb hx
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
    (Q'.le_trans' _ _ _
      (Q'.add_le_add heven (Q'.mul_le_mul_of_nonneg_left _ _ q hodd hq0'))
      (Q'.ge_of_eqv (Q'.add_mul_eqv 4 q (sTerm (q*q) x n))))

/-- Uniform finite logarithmic-derivative factor for the actual Jacobi heat
product. Includes N=0 and x=-1, and requires no near-one restriction. -/
theorem Spart_nome_widening {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hx : (-1 : Q') ≤ x) : ∀ N : Nat,
    q*Spart q x (2*N) ≤ (4+q)*Spart (q*q) x N
  | 0 => by
      change q*0 ≤ (4+q)*0
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv q))
        (Q'.ge_of_eqv (Q'.mul_zero_eqv (4+q)))
  | N+1 => by
      have he : 2*(N+1)=2*N+1+1 := by omega
      rw [he, HKConv.Spart_succ, HKConv.Spart_succ, HKConv.Spart_succ]
      have h := Q'.add_le_add (Spart_nome_widening hq0 hq1 hx N)
        (sTerm_pair_bound hq0 hq1 hx N)
      have left : q*((Spart q x (2*N)+sTerm q x (2*N))+sTerm q x (2*N+1)) ≈
          q*Spart q x (2*N)+q*(sTerm q x (2*N)+sTerm q x (2*N+1)) :=
        poly_identity_of_normal_eq
          (.mul (.var 0) (.add (.add (.var 1) (.var 2)) (.var 3)))
          (.add (.mul (.var 0) (.var 1))
            (.mul (.var 0) (.add (.var 2) (.var 3))))
          (by decide) (fun
            | 0 => q
            | 1 => Spart q x (2*N)
            | 2 => sTerm q x (2*N)
            | _ => sTerm q x (2*N+1))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv left)
        (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv
          (Q'.mul_add_eqv (4+q) (Spart (q*q) x N) (sTerm (q*q) x N))))

#print axioms sTerm_pair_bound
#print axioms Spart_nome_widening

end YMGap.Continuum.SU2HeatJacobiNomeWidening
