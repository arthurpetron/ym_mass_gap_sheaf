/-
# Actual alternating square on the mixed half-diamond

The literal pair kernel is transported through the explicit square/half-
diamond bijection, including its odd-sector minus sign. The resulting
actual finite square differs from the actual mixed rectangle by the
already checked Gaussian shell budget, with its explicit nome cutoff.

This is a finite scalar identity and approximation. No infinite addition
formula, curvature ceiling, OS operator estimate or physical gap is claimed.
-/

import YMGap.Continuum.ThetaAlternatingKernel
import YMGap.Continuum.ThetaAlternatingHalfDiamond
import YMGap.Continuum.ThetaAlternatingMixedTail
import YMGap.Continuum.ThetaAlternatingMixedRectangle

namespace YMGap.Continuum.ThetaAlternatingMixedPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaAlternatingKernel
open YMGap.Continuum.ThetaAlternatingHalfDiamond
open YMGap.Continuum.ThetaAlternatingMixedTail
open YMGap.Continuum.ThetaAlternatingMixedRectangle
open YMGap.Continuum.ThetaParityConvolution
open YMGap.Continuum.ChebyshevHalfShiftProduct (natDist)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm (listQSum listQSum_congr)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem minus_one_even (h : Nat) : (-1 : Q')^(2*h) ≈ 1 := by
  induction h with
  | zero => exact Q'.eqv_refl _
  | succ h ih =>
      rw [show 2*(h+1) = (2*h+1)+1 by omega, Q'.pow_succ, Q'.pow_succ]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (-1) _ _ (Q'.mul_eqv_congr_left (-1) _ _ ih))
        (by decide : (-1 : Q')*((-1)*1) ≈ 1)

private theorem minus_one_odd (h : Nat) : (-1 : Q')^(2*h+1) ≈ -1 := by
  rw [Q'.pow_succ]
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (-1) _ _ (minus_one_even h))
    (Q'.mul_one_eqv _)

private theorem natDist_cast (n m : Nat) : natDist n m = ((n : Int)-m).natAbs := by
  unfold natDist
  by_cases hn : m ≤ n
  · have he := Int.natAbs_of_nonneg (show 0 ≤ (n : Int)-m by omega)
    omega
  · have he := Int.ofNat_natAbs_of_nonpos (show (n : Int)-m ≤ 0 by omega)
    omega

private theorem double_natAbs (k : Int) : (2*k).natAbs = 2*k.natAbs := by
  rw [Int.natAbs_mul]
  rfl

private theorem even_degree (n m h : Nat) (k : Int)
    (hn : (n : Int) = (h : Int)+k) (hm : (m : Int) = (h : Int)-k) :
    n*(n+1)+m*(m+1) = 2*(h*(h+1))+2*(k.natAbs*k.natAbs) := by
  have hc : ((n*(n+1)+m*(m+1) : Nat) : Int) =
      ((2*(h*(h+1))+2*(k.natAbs*k.natAbs) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul, Int.natAbs_mul_self']
    rw [hn, hm]
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub,
      Int.mul_one, Int.one_mul]
    rw [Int.mul_comm k (h : Int)]
    omega
  exact Int.ofNat.inj hc

private theorem odd_degree (n m h q : Nat)
    (hn : (n : Int) = (q : Int)+h) (hm : (m : Int) = (q : Int)-h-1) :
    n*(n+1)+m*(m+1) = 2*(h*(h+1))+2*(q*q) := by
  have hc : ((n*(n+1)+m*(m+1) : Nat) : Int) =
      ((2*(h*(h+1))+2*(q*q) : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_mul]
    rw [hn, hm]
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub,
      Int.mul_one, Int.one_mul]
    rw [Int.mul_comm (h : Int) (q : Int)]
    omega
  exact Int.ofNat.inj hc

private theorem even_pair_pin (w x : Q') (n m h : Nat) (k : Int)
    (hn : (n : Int) = (h : Int)+k) (hm : (m : Int) = (h : Int)-k) :
    alternatingPairCell w x (n,m) ≈ mixedCell w x (h,k) := by
  have hs : n+m = 2*h := by omega
  have hd : natDist n m = (2*k).natAbs := by
    rw [natDist_cast]
    have hc : (n : Int)-m = 2*k := by omega
    rw [hc]
  unfold alternatingPairCell mixedCell
  rw [even_degree n m h k hn hm, hs, hd]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (minus_one_even h)))
    (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv _))

private theorem odd_pair_pin (w x : Q') (n m h q : Nat)
    (hn : (n : Int) = (q : Int)+h) (hm : (m : Int) = (q : Int)-h-1) :
    alternatingPairCell w x (n,m) ≈
      w^(2*(h*(h+1))+2*(q*q))*(Cheb.T (2*h+1) x + -(Cheb.T (2*q) x)) := by
  have hq : 1 ≤ q := by omega
  have hs : n+m = 2*(q-1)+1 := by omega
  have hf : n+m+1 = 2*q := by omega
  have hd : natDist n m = 2*h+1 := by
    rw [natDist_cast]
    have hc : (n : Int)-m = (2*h+1 : Nat) := by omega
    rw [hc]
    rfl
  unfold alternatingPairCell
  rw [odd_degree n m h q hn hm, hf, hd, hs]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (minus_one_odd (q-1)))) ?_
  exact poly_identity_of_normal_eq
    (.mul (.mul (.neg (.const 1)) (.var 0)) (.add (.var 1) (.neg (.var 2))))
    (.mul (.var 0) (.add (.var 2) (.neg (.var 1)))) (by decide)
    (fun | 0 => w^(2*(h*(h+1))+2*(q*q))
         | 1 => Cheb.T (2*q) x
         | _ => Cheb.T (2*h+1) x)

private theorem pair_swap (w x : Q') (n m : Nat) :
    alternatingPairCell w x (n,m) ≈ alternatingPairCell w x (m,n) := by
  have hd : natDist n m = natDist m n := by unfold natDist; omega
  unfold alternatingPairCell
  rw [hd, Nat.add_comm n m, Nat.add_comm (n*(n+1)) (m*(m+1))]
  exact Q'.eqv_refl _

private theorem encoded_cast (p : MixedIndex) :
    (((encodeMixed p).1 : Int), ((encodeMixed p).2 : Int)) = encode (mixedParity p) := by
  rw [encodeMixed_as_parityNat]
  apply Prod.ext
  · exact Int.toNat_of_nonneg (mixedParity_encode_nonneg p).1
  · exact Int.toNat_of_nonneg (mixedParity_encode_nonneg p).2

/-- Every actual square pair becomes the stated mixed cell, with the odd
sector sign reversing the difference rather than being discarded. -/
theorem alternatingPairCell_encodeMixed_pin (w x : Q') (p : MixedIndex) :
    alternatingPairCell w x (encodeMixed p) ≈ mixedCell w x p := by
  rcases p with ⟨h,k⟩
  have hc := encoded_cast (h,k)
  by_cases he : k.natAbs ≤ h
  · simp only [mixedParity, dif_pos he, encode, encodeEven] at hc
    exact even_pair_pin w x _ _ h k (congrArg Prod.fst hc) (congrArg Prod.snd hc)
  · by_cases hk : 0 ≤ k
    · simp only [mixedParity, dif_neg he, dif_pos hk, encode, encodeOdd] at hc
      have hn : ((encodeMixed (h,k)).1 : Int) = (k.natAbs : Int)+h := by
        have ht := congrArg Prod.fst hc
        dsimp at ht
        omega
      have hm : ((encodeMixed (h,k)).2 : Int) = (k.natAbs : Int)-h-1 := by
        have ht := congrArg Prod.snd hc
        dsimp at ht
        omega
      have hp := odd_pair_pin w x _ _ h k.natAbs hn hm
      simpa only [mixedCell, double_natAbs] using hp
    · simp only [mixedParity, dif_neg he, dif_neg hk, encode, encodeOdd] at hc
      have hn : ((encodeMixed (h,k)).2 : Int) = (k.natAbs : Int)+h := by
        have ht := congrArg Prod.snd hc
        dsimp at ht
        omega
      have hm : ((encodeMixed (h,k)).1 : Int) = (k.natAbs : Int)-h-1 := by
        have ht := congrArg Prod.fst hc
        dsimp at ht
        omega
      exact Q'.eqv_trans _ _ _ (pair_swap w x _ _)
        (by simpa only [mixedCell, double_natAbs] using odd_pair_pin w x _ _ h k.natAbs hn hm)

/-- Exact finite alternating square on the actual half-diamond, including
N=0 and all rational nomes and coordinates. -/
theorem alternatingPartial_halfDiamond_square (w x : Q') (N : Nat) :
    (x + -(1 : Q'))*(alternatingPartial w x N*alternatingPartial w x N) ≈
      listQSum (mixedCell w x) (mixedDiamondIndices N) := by
  refine Q'.eqv_trans _ _ _ (alternatingPartial_square_expansion w x N) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_positiveSquare_halfDiamond (alternatingPairCell w x) N) ?_
  exact listQSum_congr (alternatingPairCell_encodeMixed_pin w x) _

/-- The actual rectangle is approximated by the actual alternating square,
not by a supplied equality or discrepancy premise. -/
theorem alternatingPartial_rectangle_error_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    Q'.abs (listQSum (mixedCell w x) (mixedRectangleIndices N) +
      -((x + -(1 : Q'))*(alternatingPartial w x N*alternatingPartial w x N))) ≤
        ThetaParityDiamondTail.omittedBudget w N := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _
      (alternatingPartial_halfDiamond_square w x N)))))
    (mixed_rectangle_error_le hw0 hw1 hx0 hx1 N)

/-- The inherited explicit nome-dependent cutoff controls the same finite
square/rectangle error uniformly on the scalar coordinate interval. -/
theorem alternatingPartial_rectangle_error_le_epsilon {w x epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : ThetaAngularShellTail.shellTailCutoff w epsilon ≤ N) :
    Q'.abs (listQSum (mixedCell w x) (mixedRectangleIndices N) +
      -((x + -(1 : Q'))*(alternatingPartial w x N*alternatingPartial w x N))) ≤ epsilon :=
  Q'.le_trans' _ _ _ (alternatingPartial_rectangle_error_le hw0 hw1 hx0 hx1 N)
    (ThetaAngularShellTail.shellTail_le_epsilon hw0 hw1 he (N+1) (N+3) (by omega))

/-- The actual endpoint determinant and alternating square are close with
the inherited shell budget; the odd prefix is explicitly one-sided. -/
theorem alternatingPartial_factored_error_le {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (N : Nat) :
    Q'.abs ((evenPartial w 1 N*oddPartial w x N +
      -(oddPartial w 1 N*evenPartial w x N)) +
      -((x + -(1 : Q'))*(alternatingPartial w x N*alternatingPartial w x N))) ≤
        ThetaParityDiamondTail.omittedBudget w N := by
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (mixed_rectangle_factored_pin w x N)))))
    (alternatingPartial_rectangle_error_le hw0 hw1 hx0 hx1 N)

/-- Same-prefix finite determinant/square approximation with an explicit
nome-dependent modulus, uniform in x on [-1,1]. This does not itself form
the limits, or differentiate their value identity. -/
theorem alternatingPartial_factored_error_le_epsilon {w x epsilon : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-(1 : Q')) ≤ x) (hx1 : x ≤ (1 : Q')) (he : (0 : Q') < epsilon)
    (N : Nat) (hN : ThetaAngularShellTail.shellTailCutoff w epsilon ≤ N) :
    Q'.abs ((evenPartial w 1 N*oddPartial w x N +
      -(oddPartial w 1 N*evenPartial w x N)) +
      -((x + -(1 : Q'))*(alternatingPartial w x N*alternatingPartial w x N))) ≤ epsilon :=
  Q'.le_trans' _ _ _ (alternatingPartial_factored_error_le hw0 hw1 hx0 hx1 N)
    (ThetaAngularShellTail.shellTail_le_epsilon hw0 hw1 he (N+1) (N+3) (by omega))

end YMGap.Continuum.ThetaAlternatingMixedPin

#print axioms YMGap.Continuum.ThetaAlternatingMixedPin.alternatingPairCell_encodeMixed_pin
#print axioms YMGap.Continuum.ThetaAlternatingMixedPin.alternatingPartial_halfDiamond_square
#print axioms YMGap.Continuum.ThetaAlternatingMixedPin.alternatingPartial_rectangle_error_le
#print axioms YMGap.Continuum.ThetaAlternatingMixedPin.alternatingPartial_rectangle_error_le_epsilon
#print axioms YMGap.Continuum.ThetaAlternatingMixedPin.alternatingPartial_factored_error_le
#print axioms YMGap.Continuum.ThetaAlternatingMixedPin.alternatingPartial_factored_error_le_epsilon
