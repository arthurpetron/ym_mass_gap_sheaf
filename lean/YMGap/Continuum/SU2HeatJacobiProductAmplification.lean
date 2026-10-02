/-
# Retained original Jacobi factors amplify a finite normalized comparison

All factors below are the literal `ThetaConv.gFac` and `ThetaConv.Ppart`.
The Euler prefactors are retained on BOTH sides of the cross multiplication.
A contiguous block of amplitudes in [1/4,3/4] pays the computed multiplier
`(1+(1-x)/512)^N`. No reciprocal heat floor, supplied product inequality,
or near-one analytic estimate is used. Empty products, empty blocks, partial
blocks, and both spatial endpoints are included.

Counting a useful block, controlling theta heights, passing the original
limits and producing an ORIGINAL Haar square certificate are separate joins.
This finite theorem alone claims neither a full heat profile nor survival.
-/

import YMGap.Continuum.SU2HeatJacobiProductWidening
import YMGap.Continuum.HeatKernelConvGen

namespace YMGap.Continuum.SU2HeatJacobiProductAmplification

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HKPos (factor geoAmp)
open YMGap.Continuum.HKConv (mul_le_mul')
open YMGap.Continuum.ThetaConv (gFac Ppart)
open YMGap.Continuum.SU2HeatJacobiProductWidening
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- The exact retained-factor multiplier; 1/512 is rational data. -/
def amplification (x : Q') : Q' := 1+(Q'.mkPos 1 512 (by decide))*(1-x)

theorem amplification_nonnegative {x : Q'} (hx : x ≤ (1 : Q')) :
    (0 : Q') ≤ amplification x :=
  Q'.zero_le_add _ _ Q'.zero_le_one
    (Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le hx))

private theorem shuffle (a b c d : Q') : (a*b)*(c*d) ≈ (a*c)*(b*d) :=
  poly_identity_of_normal_eq
    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
    (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)

private theorem squared_power (q : Q') : ∀ n : Nat,
    (q*q)^n ≈ q^n*q^n
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n+1 => by
      simp only [Q'.pow_succ]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (q*q) _ _ (squared_power q n))
        (shuffle q q (q^n) (q^n))

private theorem factor_congr {a b : Q'} (hab : a ≈ b) (x : Q') :
    factor a x ≈ factor b x := by
  unfold factor HKPos.two
  have htwo : a+a ≈ b+b := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ a hab) (Q'.add_eqv_congr_left b _ _ hab)
  have hmul : a*a ≈ b*b := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ a hab) (Q'.mul_eqv_congr_left b _ _ hab)
  exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (a*a) (Q'.mul_eqv_congr_right _ _ x htwo))
    (Q'.add_eqv_congr_left ((b+b)*x) _ _ hmul))

private theorem squared_nome_lt_one {q : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) : q*q < (1 : Q') :=
  HKPos.q_lt_of_le_of_lt
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right q 1 q (Q'.le_of_lt hq1) (Q'.le_of_lt hq0))
      (Q'.le_of_eqv (Q'.one_mul_eqv q))) hq1

private theorem scaled_block {a x : Q'}
    (hl : Q'.mkPos 1 4 (by decide) ≤ a)
    (hu : a ≤ Q'.mkPos 3 4 (by decide)) (hx : x ≤ (1 : Q')) :
    (factor a x*factor (a*a) 1)*amplification x ≤ factor a 1*factor (a*a) x := by
  let r : Q' := Q'.mkPos 1 512 (by decide)
  have hr : r*512 ≈ (1 : Q') := by decide
  have h := Q'.mul_le_mul_of_nonneg_left _ _ r
    (factor_squared_nome_block hl hu hx) (by decide)
  have hlpin : r*((factor a x*factor (a*a) 1)*(512+(1-x))) ≈
      (factor a x*factor (a*a) 1)*amplification x := by
    have he := poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.add (.const 512) (.var 2))))
      (.mul (.var 1) (.add (.mul (.var 0) (.const 512)) (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => r | 1 => factor a x*factor (a*a) 1 | _ => 1-x)
    exact Q'.eqv_trans _ _ _ he
      (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr_right _ _ _ hr))
  have hrpin : r*(512*(factor a 1*factor (a*a) x)) ≈
      factor a 1*factor (a*a) x :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r 512 _))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hr) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hlpin)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hrpin))

private theorem full_factor_bound {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (k : Nat) (c : Q')
    (hf : (factor (geoAmp q k) x*factor ((geoAmp q k)*(geoAmp q k)) 1)*c ≤
      factor (geoAmp q k) 1*factor ((geoAmp q k)*(geoAmp q k)) x) :
    (gFac q x k*gFac (q*q) 1 k)*c ≤ gFac q 1 k*gFac (q*q) x k := by
  let e := 1+ -(ThetaConv.uAmp q k)
  let d := 1+ -(ThetaConv.uAmp (q*q) k)
  have hq20 := HKPos.q_mul_pos hq0 hq0
  have hq21 := squared_nome_lt_one hq0 hq1
  have he : (0 : Q') ≤ e := Q'.le_of_lt
    (HKPos.one_sub_pos (ThetaConv.uAmp_pos_lt_one hq0 hq1 k).2)
  have hd : (0 : Q') ≤ d := Q'.le_of_lt
    (HKPos.one_sub_pos (ThetaConv.uAmp_pos_lt_one hq20 hq21 k).2)
  have hb : geoAmp (q*q) k ≈ geoAmp q k*geoAmp q k := squared_power q (2*k+1)
  have hleft : (gFac q x k*gFac (q*q) 1 k)*c ≈
      (e*d)*((factor (geoAmp q k) x*factor ((geoAmp q k)*(geoAmp q k)) 1)*c) := by
    unfold gFac
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ c (shuffle e (factor (geoAmp q k) x) d
        (factor (geoAmp (q*q) k) 1)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ c
          (Q'.mul_eqv_congr_left (e*d) _ _
            (Q'.mul_eqv_congr_left _ _ _ (factor_congr hb 1))))
        (Q'.mul_assoc_eqv _ _ c))
  have hright : gFac q 1 k*gFac (q*q) x k ≈
      (e*d)*(factor (geoAmp q k) 1*factor ((geoAmp q k)*(geoAmp q k)) x) := by
    unfold gFac
    exact Q'.eqv_trans _ _ _ (shuffle e (factor (geoAmp q k) 1) d
      (factor (geoAmp (q*q) k) x))
      (Q'.mul_eqv_congr_left (e*d) _ _
        (Q'.mul_eqv_congr_left _ _ _ (factor_congr hb x)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (e*d) hf (Q'.mul_nonneg _ _ he hd))
      (Q'.ge_of_eqv hright))

private def pairedProduct (q x y : Q') (M : Nat) : Q' := Ppart q x M*Ppart (q*q) y M

private theorem pairedProduct_succ (q x y : Q') (M : Nat) :
    pairedProduct q x y (M+1) ≈
      pairedProduct q x y M*(gFac q x M*gFac (q*q) y M) := by
  unfold pairedProduct
  rw [ThetaConv.Ppart_succ, ThetaConv.Ppart_succ]
  exact shuffle _ _ _ _

/-- Number of retained indices strictly below the actual finite cutoff. -/
def retainedCount (start N M : Nat) : Nat := min N (M-start)

private theorem partial_bound {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (start N : Nat)
    (hblock : ∀ j : Nat, j < N →
      Q'.mkPos 1 4 (by decide) ≤ geoAmp q (start+j) ∧
      geoAmp q (start+j) ≤ Q'.mkPos 3 4 (by decide)) : ∀ M : Nat,
    pairedProduct q x 1 M*(amplification x)^retainedCount start N M ≤
      pairedProduct q 1 x M
  | 0 => by
      simp only [retainedCount, Nat.zero_sub, Nat.min_zero, Q'.pow_zero,
        pairedProduct, Ppart]
      decide
  | M+1 => by
      have ih := partial_bound hq0 hq1 hxlo hxhi start N hblock M
      have hq20 := HKPos.q_mul_pos hq0 hq0
      have hq21 := squared_nome_lt_one hq0 hq1
      have hleft0 : (0 : Q') ≤ pairedProduct q x 1 M := Q'.mul_nonneg _ _
        (ThetaConv.Ppart_nonneg hq0 hq1 hxlo M)
        (ThetaConv.Ppart_nonneg hq20 hq21 (by decide) M)
      have hright0 : (0 : Q') ≤ gFac q 1 M*gFac (q*q) x M := Q'.mul_nonneg _ _
        (ThetaConv.gFac_nonneg hq0 hq1 (by decide) M)
        (ThetaConv.gFac_nonneg hq20 hq21 hxlo M)
      have hweighted0 : (0 : Q') ≤
          pairedProduct q x 1 M*(amplification x)^retainedCount start N M :=
        Q'.mul_nonneg _ _ hleft0
          (Q'.pow_nonneg _ (amplification_nonnegative hxhi) _)
      have inactive (hc : retainedCount start N (M+1)=retainedCount start N M) :
          pairedProduct q x 1 (M+1)*(amplification x)^retainedCount start N (M+1) ≤
            pairedProduct q 1 x (M+1) := by
        have hf0 := factor_squared_nome_order
          (Q'.le_of_lt (HKPos.pow_succ_pos_lt_one hq0 hq1 (2*M)).1) hxhi
        have hf := full_factor_bound hq0 hq1 M 1
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) hf0)
        rw [hc]
        have h := mul_le_mul' hweighted0 hright0 ih
          (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _)) hf)
        have he : pairedProduct q x 1 (M+1)*
            (amplification x)^retainedCount start N M ≈
            (pairedProduct q x 1 M*(amplification x)^retainedCount start N M)*
              (gFac q x M*gFac (q*q) 1 M) :=
          Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (pairedProduct_succ q x 1 M))
            (poly_identity_of_normal_eq
              (.mul (.mul (.var 0) (.var 1)) (.var 2))
              (.mul (.mul (.var 0) (.var 2)) (.var 1))
              (by decide) (fun
                | 0 => pairedProduct q x 1 M
                | 1 => gFac q x M*gFac (q*q) 1 M
                | _ => (amplification x)^retainedCount start N M))
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
          (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (pairedProduct_succ q 1 x M)))
      cases (inferInstance : Decidable (start ≤ M)) with
      | isFalse hs =>
          apply inactive
          unfold retainedCount
          omega
      | isTrue hs =>
          cases (inferInstance : Decidable (M < start+N)) with
          | isFalse ht =>
              apply inactive
              unfold retainedCount
              omega
          | isTrue ht =>
              have hj : M-start < N := by omega
              have hind : start+(M-start)=M := by omega
              have hb := hblock (M-start) hj
              rw [hind] at hb
              have hf := full_factor_bound hq0 hq1 M (amplification x)
                (scaled_block hb.1 hb.2 hxhi)
              have hc : retainedCount start N (M+1)=retainedCount start N M+1 := by
                unfold retainedCount
                omega
              rw [hc, Q'.pow_succ]
              have h := mul_le_mul' hweighted0 hright0 ih hf
              have he : pairedProduct q x 1 (M+1)*
                  (amplification x*(amplification x)^retainedCount start N M) ≈
                  (pairedProduct q x 1 M*(amplification x)^retainedCount start N M)*
                    ((gFac q x M*gFac (q*q) 1 M)*amplification x) :=
                Q'.eqv_trans _ _ _
                  (Q'.mul_eqv_congr_right _ _ _ (pairedProduct_succ q x 1 M))
                  (poly_identity_of_normal_eq
                    (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
                    (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 2)))
                    (by decide) (fun
                      | 0 => pairedProduct q x 1 M
                      | 1 => gFac q x M*gFac (q*q) 1 M
                      | 2 => amplification x
                      | _ => (amplification x)^retainedCount start N M))
              exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
                (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv (pairedProduct_succ q 1 x M)))

/-- Literal original partial products, including a cutoff inside the block. -/
theorem Ppart_partial_block_amplification {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (start N M : Nat)
    (hblock : ∀ j : Nat, j < N →
      Q'.mkPos 1 4 (by decide) ≤ geoAmp q (start+j) ∧
      geoAmp q (start+j) ≤ Q'.mkPos 3 4 (by decide)) :
    (Ppart q x M*Ppart (q*q) 1 M)*(amplification x)^retainedCount start N M ≤
      Ppart q 1 M*Ppart (q*q) x M :=
  partial_bound hq0 hq1 hxlo hxhi start N hblock M

/-- Once the actual finite cutoff includes the whole contiguous block, all N
quantitative factors survive, with both original Euler products retained. -/
theorem Ppart_block_amplification {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (start N M : Nat) (hM : start+N ≤ M)
    (hblock : ∀ j : Nat, j < N →
      Q'.mkPos 1 4 (by decide) ≤ geoAmp q (start+j) ∧
      geoAmp q (start+j) ≤ Q'.mkPos 3 4 (by decide)) :
    (Ppart q x M*Ppart (q*q) 1 M)*(amplification x)^N ≤
      Ppart q 1 M*Ppart (q*q) x M := by
  have hc : retainedCount start N M=N := by unfold retainedCount; omega
  simpa only [hc] using Ppart_partial_block_amplification hq0 hq1 hxlo hxhi start N M hblock

private theorem additive_le_power {g : Q'} (hg : (0 : Q') ≤ g) : ∀ n : Nat,
    HKConvGen.bScale g n ≤ (1+g)^n
  | 0 => Q'.le_refl' 1
  | n+1 => by
      rw [HKConvGen.bScale_succ, Q'.pow_succ]
      have hgb : g ≤ g*HKConvGen.bScale g n := Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.mul_one_eqv g))
        (Q'.mul_le_mul_of_nonneg_left _ _ g (HKConvGen.bScale_one_le hg n) hg)
      have he : HKConvGen.bScale g n+g*HKConvGen.bScale g n ≈
          (1+g)*HKConvGen.bScale g n := poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.var 1) (.var 0)))
        (.mul (.add (.const 1) (.var 1)) (.var 0))
        (by decide) (fun | 0 => HKConvGen.bScale g n | _ => g)
      exact Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hgb)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
          (Q'.mul_le_mul_of_nonneg_left _ _ (1+g) (additive_le_power hg n)
            (Q'.zero_le_add _ _ Q'.zero_le_one hg)))

private theorem power_one_le {a : Q'} (ha : (1 : Q') ≤ a) : ∀ n : Nat,
    (1 : Q') ≤ a^n
  | 0 => Q'.le_refl' 1
  | n+1 => Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv 1))
      (mul_le_mul' Q'.zero_le_one (Q'.pow_nonneg a
        (Q'.le_trans' _ _ _ Q'.zero_le_one ha) n) ha (power_one_le ha n))

/-- A computed quadratic retained multiplier. The floor half is explicit;
for N>=2 it is comparable to N, rather than an assumed binomial coefficient. -/
def quadraticAmplification (x : Q') (N : Nat) : Q' :=
  let t := (Q'.mkPos 1 512 (by decide))*(1-x)
  (Q'.ofNat (N/2)*t)*(Q'.ofNat (N/2)*t)

theorem quadraticAmplification_le_power {x : Q'} (hx : x ≤ (1 : Q')) (N : Nat) :
    quadraticAmplification x N ≤ (amplification x)^N := by
  let t := (Q'.mkPos 1 512 (by decide))*(1-x)
  let n := N/2
  have ht : (0 : Q') ≤ t := Q'.mul_nonneg _ _ (by decide) (Q'.sub_nonneg_of_le hx)
  have hn : (0 : Q') ≤ Q'.ofNat n := by
    show (0 : Int)*1 ≤ (n : Int)*1
    omega
  have hlinear : Q'.ofNat n*t ≤ (1+t)^n := Q'.le_trans' _ _ _
    (HKConvGen.ofNat_mul_le_bScale ht n) (additive_le_power ht n)
  have hsq := mul_le_mul' (Q'.mul_nonneg _ _ hn ht)
    (Q'.pow_nonneg (1+t) (Q'.zero_le_add _ _ Q'.zero_le_one ht) n) hlinear hlinear
  have htwon : n+n ≤ N := by dsimp only [n]; omega
  have hsum : n+n+(N-(n+n))=N := by omega
  have ha : (1 : Q') ≤ 1+t := Q'.add_le_self_of_nonneg 1 t ht
  have heven : quadraticAmplification x N ≤ (1+t)^(n+n) :=
    Q'.le_trans' _ _ _ hsq (Q'.ge_of_eqv (Q'.pow_add_eqv (1+t) n n))
  have hextra : (1+t)^(n+n) ≤ (1+t)^N := by
    have h := Q'.mul_le_mul_of_nonneg_left _ _ ((1+t)^(n+n))
      (power_one_le ha (N-(n+n)))
      (Q'.pow_nonneg (1+t) (Q'.zero_le_add _ _ Q'.zero_le_one ht) (n+n))
    have he := Q'.pow_add_eqv (1+t) (n+n) (N-(n+n))
    rw [hsum] at he
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.le_trans' _ _ _ h (Q'.ge_of_eqv he))
  exact Q'.le_trans' _ _ _ heven hextra

/-- Quadratic count amplification on the SAME complete finite products. -/
theorem Ppart_block_quadratic_amplification {q x : Q'} (hq0 : (0 : Q') < q)
    (hq1 : q < (1 : Q')) (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q'))
    (start N M : Nat) (hM : start+N ≤ M)
    (hblock : ∀ j : Nat, j < N →
      Q'.mkPos 1 4 (by decide) ≤ geoAmp q (start+j) ∧
      geoAmp q (start+j) ≤ Q'.mkPos 3 4 (by decide)) :
    (Ppart q x M*Ppart (q*q) 1 M)*quadraticAmplification x N ≤
      Ppart q 1 M*Ppart (q*q) x M :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (Ppart q x M*Ppart (q*q) 1 M)
      (quadraticAmplification_le_power hxhi N)
      (Q'.mul_nonneg _ _ (ThetaConv.Ppart_nonneg hq0 hq1 hxlo M)
        (ThetaConv.Ppart_nonneg (HKPos.q_mul_pos hq0 hq0)
          (squared_nome_lt_one hq0 hq1) (by decide) M)))
    (Ppart_block_amplification hq0 hq1 hxlo hxhi start N M hM hblock)

#print axioms amplification_nonnegative
#print axioms Ppart_partial_block_amplification
#print axioms Ppart_block_amplification
#print axioms quadraticAmplification_le_power
#print axioms Ppart_block_quadratic_amplification

end YMGap.Continuum.SU2HeatJacobiProductAmplification
