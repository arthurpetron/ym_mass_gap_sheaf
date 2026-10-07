/-
# Actual Jacobi product radial cost: signed finite tails

The literal logarithmic factor increments HKConv.sTerm satisfy -r <= d <= r
on the full scalar interval, where d=(1-x*x)*r*r+x*r.  Once the first omitted
amplitude is at most 1/8, every further factor has floor 1/2.  This gives the
explicit tail payment 4*w^(2*N+1)/(1-w*w), without a heat-density reciprocal.

These are finite rational comparisons of the SAME product radial cost.  No
completed ceiling, Poisson identity, Haar certificate, conditional estimate,
original-action estimate or physical scaling conclusion is asserted.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.JacobiHeatRadialMixtureCancellation
import YMGap.Constructive.CornerBound

namespace YMGap.Continuum.JacobiProductRadialSignedTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.JacobiHeatRadialMixtureCancellation

local infix:50 " ≈ " => Q'.eqv

def eighth : Q' := Q'.mkPos 1 8 (by decide)

def radialSummand (w x : Q') (i : Nat) : Q' :=
  radialA x*(HKConv.sTerm w x i*HKConv.sTerm w x i) + x*HKConv.sTerm w x i

/-- Literal geometric payment 4*c_N/(1-w*w). -/
def radialTailPayment (w : Q') (N : Nat) : Q' :=
  HKConvGen.geoTailBase (4*HKPos.geoAmp w N) (w*w) 0

private theorem add_congr {a b c d : Q'} (hab : a ≈ b) (hcd : c ≈ d) :
    a+c ≈ b+d :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right a b c hab)
    (Q'.add_eqv_congr_left b c d hcd)

private theorem nonneg_of_eqv {a b : Q'} (h : a ≈ b) (hb : (0 : Q') ≤ b) :
    (0 : Q') ≤ a :=
  Q'.le_trans' _ _ _ hb (Q'.ge_of_eqv h)

private theorem nome_square_lt_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : w*w < (1 : Q') :=
  HKPos.q_lt_of_le_of_lt (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
    (Q'.le_of_eqv (Q'.one_mul_eqv w))) hw1

private theorem sTerm_factor_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x) (i : Nat) :
    HKConv.sTerm w x i * HKPos.factor (HKPos.geoAmp w i) x ≈
      HKPos.two (HKPos.geoAmp w i) :=
  HKConv.divPos_mul_eqv (HKConv.factor_num_pos hw0 hw1 hx i)

/-- The finite signed sum is exactly the already constructed moment cost. -/
theorem radialSummand_sum_pin (w x : Q') (N : Nat) :
    finSum (radialSummand w x) N ≈ productRadialCost (HKConv.sTerm w x) N x :=
  Q'.eqv_trans _ _ _
    (finSum_add (fun i => radialA x*(HKConv.sTerm w x i*HKConv.sTerm w x i))
      (fun i => x*HKConv.sTerm w x i) N)
    (add_congr
      (Q'.eqv_symm (const_mul_finSum (fun i => HKConv.sTerm w x i*HKConv.sTerm w x i)
        (radialA x) N))
      (Q'.eqv_symm (const_mul_finSum (HKConv.sTerm w x) x N)))

/-- Full-interval signed bounds, retaining rather than discarding negative
radial increments. The factor cancellation is (1+x)*r <= 1. -/
theorem radialSummand_bounds {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (i : Nat) :
    -(HKConv.sTerm w x i) ≤ radialSummand w x i ∧
      radialSummand w x i ≤ HKConv.sTerm w x i := by
  let c := HKPos.geoAmp w i
  let r := HKConv.sTerm w x i
  let f := HKPos.factor c x
  have hc := HKPos.pow_succ_pos_lt_one hw0 hw1 (2*i)
  have hf : (0 : Q') < f := HKPos.factor_pos (Q'.le_of_lt hc.1) hc.2 hx0
  have hr : (0 : Q') ≤ r := HKConv.sTerm_nonneg hw0 hw1 hx0 i
  have hrf : r*f ≈ c+c := sTerm_factor_pin hw0 hw1 hx0 i
  have hplus : (0 : Q') ≤ 1+x :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv 1))
      (Q'.add_le_add_left 1 (-1) x hx0)
  have hminus : (0 : Q') ≤ 1 + -x := Q'.sub_nonneg_of_le hx1
  have ha : (0 : Q') ≤ radialA x := nonneg_of_eqv
    (poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.mul (.var 0) (.var 0))))
      (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.var 0)))
      (by decide) (fun _ => x)) (Q'.mul_nonneg _ _ hminus hplus)
  have hfactor : (1+x)*(c+c) ≤ f := by
    apply Q'.le_of_sub_nonneg
    exact nonneg_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.const 1) (.add (.mul (.add (.var 0) (.var 0)) (.var 1))
        (.mul (.var 0) (.var 0))))
        (.neg (.mul (.add (.const 1) (.var 1)) (.add (.var 0) (.var 0)))))
      (.mul (.add (.const 1) (.neg (.var 0))) (.add (.const 1) (.neg (.var 0))))
      (by decide) (fun | 0 => c | _ => x))
      (SumOfSquares.q_mul_self_nonneg (1 + -c))
  have hrr : (1+x)*r ≤ (1 : Q') := by
    apply HKConvGen.mul_le_mul_left_cancel hf
    have hpin : f*((1+x)*r) ≈ (1+x)*(c+c) := Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.add (.const 1) (.var 1)) (.var 2)))
        (.mul (.add (.const 1) (.var 1)) (.mul (.var 2) (.var 0)))
        (by decide) (fun | 0 => f | 1 => x | _ => r))
      (Q'.mul_eqv_congr_left (1+x) _ _ hrf)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _ hfactor (Q'.ge_of_eqv (Q'.mul_one_eqv f)))
  constructor
  · apply Q'.neg_le_of_zero_le_add
    exact nonneg_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.mul (.var 2) (.var 2))) (.mul (.var 1) (.var 2))) (.var 2))
      (.add (.mul (.var 0) (.mul (.var 2) (.var 2)))
        (.mul (.add (.const 1) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => radialA x | 1 => x | _ => r))
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ ha (SumOfSquares.q_mul_self_nonneg r))
        (Q'.mul_nonneg _ _ hplus hr))
  · apply Q'.le_of_sub_nonneg
    exact nonneg_of_eqv (poly_identity_of_normal_eq
      (.add (.var 1) (.neg (.add
        (.mul (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))) (.mul (.var 1) (.var 1)))
        (.mul (.var 0) (.var 1)))))
      (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
        (.add (.const 1) (.neg (.mul (.add (.const 1) (.var 0)) (.var 1)))))
      (by decide) (fun | 0 => x | _ => r))
      (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hminus hr) (Q'.sub_nonneg_of_le hrr))

private theorem geoAmp_shift_pin (w : Q') (N : Nat) : ∀ j,
    HKPos.geoAmp w (N+j) ≈ HKPos.geoAmp w N*(w*w)^j
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv _)
  | j+1 => by
      have he : 2*(N+(j+1))+1 = (2*(N+j)+1)+2 := by omega
      change w^(2*(N+(j+1))+1) ≈ HKPos.geoAmp w N*((w*w)*(w*w)^j)
      rw [he]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left w _ _ (Q'.mul_eqv_congr_left w _ _ (geoAmp_shift_pin w N j)))
        (poly_identity_of_normal_eq
          (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 2))))
          (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.var 2)))
          (by decide) (fun | 0 => w | 1 => HKPos.geoAmp w N | _ => (w*w)^j))

/-- Past the explicit onset, only the floor of the omitted affine factors
is used, not the global heat/product floor. -/
theorem sTerm_tail_le_four_geoAmp {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) (j : Nat) :
    HKConv.sTerm w x (N+j) ≤ 4*HKPos.geoAmp w (N+j) := by
  let c := HKPos.geoAmp w (N+j)
  let f := HKPos.factor c x
  have hc := HKPos.pow_succ_pos_lt_one hw0 hw1 (2*(N+j))
  have hce : c ≤ eighth := Q'.le_trans' _ _ _
    (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
      (m := 2*N+1) (n := 2*(N+j)+1) (by omega)) hN
  have hfloor : HalfPow.half ≤ f := Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (by decide : HalfPow.half ≤ HKPos.factorLB eighth)
      (HKConv.factorLB_antitone (Q'.le_of_lt hc.1) hce (by decide : eighth ≤ (1 : Q'))))
    (HKPos.factorLB_le_factor (Q'.le_of_lt hc.1) hx)
  have hf : (0 : Q') < f := HKPos.factor_pos (Q'.le_of_lt hc.1) hc.2 hx
  have h4c : (0 : Q') ≤ 4*c := Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt hc.1)
  apply HKConvGen.mul_le_mul_left_cancel hf
  have hleft : f*HKConv.sTerm w x (N+j) ≈ c+c := Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv _ _) (sTerm_factor_pin hw0 hw1 hx (N+j))
  have hhalf : HalfPow.half*(4*c) ≈ c+c := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half 4 c))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c
      (by decide : HalfPow.half*4 ≈ (2 : Q')))
      (poly_identity_of_normal_eq (.mul (.const 2) (.var 0))
        (.add (.var 0) (.var 0)) (by decide) (fun _ => c)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hhalf)
      (Q'.mul_le_mul_of_nonneg_right HalfPow.half f (4*c) hfloor h4c))

/-- Uniform over every finite omitted segment; no completed limit is assumed. -/
theorem sTerm_finite_tail_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hx : (-1 : Q') ≤ x)
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) (L : Nat) :
    finSum (fun j => HKConv.sTerm w x (N+j)) L ≤ radialTailPayment w N := by
  have hterm : ∀ j, 4*HKPos.geoAmp w (N+j) ≈
      HKConvGen.geoIncrBase (4*HKPos.geoAmp w N) (w*w) (0+j) := fun j =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 4 _ _ (geoAmp_shift_pin w N j))
      (by simpa only [HKConvGen.geoIncrBase, Nat.zero_add] using
        (Q'.eqv_symm (Q'.mul_assoc_eqv 4 (HKPos.geoAmp w N) ((w*w)^j))))
  exact Q'.le_trans' _ _ _
    (finSum_le_lt (fun j => HKConv.sTerm w x (N+j))
      (fun j => HKConvGen.geoIncrBase (4*HKPos.geoAmp w N) (w*w) (0+j)) L
      (fun j _ => Q'.le_trans' _ _ _
      (sTerm_tail_le_four_geoAmp hw0 hw1 hx N hN j) (Q'.le_of_eqv (hterm j))))
    (HKConvGen.geoTailBase_series_le
      (Q'.mul_nonneg 4 (HKPos.geoAmp w N) (by decide)
        (Q'.pow_nonneg w (Q'.le_of_lt hw0) (2*N+1)))
      (HKPos.q_mul_pos hw0 hw0) (nome_square_lt_one hw0 hw1) 0 L)

private theorem sum_nonneg (f : Nat → Q') : ∀ N,
    (∀ i, i < N → (0 : Q') ≤ f i) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N+1, hf => Q'.zero_le_add _ _
      (sum_nonneg f N (fun i hi => hf i (Nat.lt_succ_of_lt hi)))
      (hf N (Nat.lt_succ_self N))

private theorem finite_lower (d r : Nat → Q') (N : Nat)
    (h : ∀ i, i < N → -(r i) ≤ d i) :
    (0 : Q') ≤ finSum d N + finSum r N := by
  have hsum : (0 : Q') ≤ finSum (fun i => d i+r i) N :=
    sum_nonneg _ N (fun i hi => Q'.le_trans' _ _ _
      (Q'.sub_nonneg_of_le (h i hi))
      (Q'.le_of_eqv (Q'.add_eqv_congr_left (d i) _ _ (Q'.neg_neg_eqv (r i)))))
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (finSum_add d r N))

/-- Signed finite-to-finite comparison of the literal product cost. Negative
tail increments are paid, not silently replaced by monotonicity. -/
theorem productRadialCost_finite_tail_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) (L : Nat) :
    productRadialCost (HKConv.sTerm w x) N x ≤
      productRadialCost (HKConv.sTerm w x) (N+L) x + radialTailPayment w N := by
  let d := radialSummand w x
  let r := HKConv.sTerm w x
  have hlo : (0 : Q') ≤ finSum (fun j => d (N+j)) L + finSum (fun j => r (N+j)) L :=
    finite_lower _ _ L (fun j _ => (radialSummand_bounds hw0 hw1 hx0 hx1 (N+j)).1)
  have htail : (0 : Q') ≤ finSum (fun j => d (N+j)) L + radialTailPayment w N :=
    Q'.le_trans' _ _ _ hlo (Q'.add_le_add_left _ _ _ (sTerm_finite_tail_le hw0 hw1 hx0 N hN L))
  have hstep : finSum d N ≤ (finSum d N+finSum (fun j => d (N+j)) L)+radialTailPayment w N :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (finSum d N) _ htail)
      (Q'.ge_of_eqv (Q'.add_assoc_eqv _ _ _))
  have hfull : finSum d (N+L) ≈ finSum d N+finSum (fun j => d (N+j)) L :=
    finSum_split d N L
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (radialSummand_sum_pin w x N))
    (Q'.le_trans' _ _ _ hstep
      (Q'.le_of_eqv (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.eqv_symm hfull) (radialSummand_sum_pin w x (N+L))))))

/-- Cleared exact denominator pin: the explicit payment is 4*c_N/(1-w*w). -/
theorem radialTailPayment_denominator_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (N : Nat) :
    radialTailPayment w N*(1 + -(w*w)) ≈ 4*HKPos.geoAmp w N := by
  have hD := HKPos.one_sub_pos (nome_square_lt_one hw0 hw1)
  have hp : radialTailPayment w N ≈
      (4*HKPos.geoAmp w N)*HKConv.divPos 1 (1 + -(w*w)) :=
    Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hp)
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hD))) (Q'.mul_one_eqv _)))

/-- At the explicit onset, the payment costs at most half an inverse nome
defect; there is no global Euler/head-floor reciprocal. -/
theorem radialTailPayment_nome_defect_le_half {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hN : HKPos.geoAmp w N ≤ eighth) :
    (1 + -w)*radialTailPayment w N ≤ HalfPow.half := by
  have hp : (0 : Q') < 1+w := Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 w (Q'.le_of_lt hw0))
  apply HKConvGen.mul_le_mul_left_cancel hp
  have hfactor : (1+w)*((1 + -w)*radialTailPayment w N) ≈
      radialTailPayment w N*(1 + -(w*w)) :=
    poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.var 0)) (.mul (.add (.const 1) (.neg (.var 0))) (.var 1)))
      (.mul (.var 1) (.add (.const 1) (.neg (.mul (.var 0) (.var 0)))))
      (by decide) (fun | 0 => w | _ => radialTailPayment w N)
  have h4 : 4*HKPos.geoAmp w N ≤ HalfPow.half := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ 4 hN (by decide))
    (Q'.le_of_eqv (by decide : (4 : Q')*eighth ≈ HalfPow.half))
  have hh : HalfPow.half ≤ (1+w)*HalfPow.half := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv HalfPow.half))
    (Q'.mul_le_mul_of_nonneg_right 1 (1+w) HalfPow.half
      (Q'.add_le_self_of_nonneg 1 w (Q'.le_of_lt hw0)) HalfPow.half_nonneg)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfactor (radialTailPayment_denominator_pin hw0 hw1 N)))
    (Q'.le_trans' _ _ _ h4 hh)

end YMGap.Continuum.JacobiProductRadialSignedTail

#print axioms YMGap.Continuum.JacobiProductRadialSignedTail.radialSummand_sum_pin
#print axioms YMGap.Continuum.JacobiProductRadialSignedTail.radialSummand_bounds
#print axioms YMGap.Continuum.JacobiProductRadialSignedTail.sTerm_tail_le_four_geoAmp
#print axioms YMGap.Continuum.JacobiProductRadialSignedTail.sTerm_finite_tail_le
#print axioms YMGap.Continuum.JacobiProductRadialSignedTail.productRadialCost_finite_tail_le
#print axioms YMGap.Continuum.JacobiProductRadialSignedTail.radialTailPayment_denominator_pin
#print axioms YMGap.Continuum.JacobiProductRadialSignedTail.radialTailPayment_nome_defect_le_half
