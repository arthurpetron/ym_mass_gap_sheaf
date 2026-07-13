/-
# Output-row covariance for arbitrary-label Cayley transvectants

The raising covariance of the two-factor Cayley process becomes useful for
row norms only after diagonal restriction.  This module proves that diagonal
restriction commutes with total raising on physically supported bidegrees,
including the truncated antidiagonal boundary terms, and then transports the
identity through every admissible transvectant order.
-/

import YMGap.Continuum.SU2TransvectantRaisingCovariance

namespace YMGap.Continuum.SU2TransvectantOutputRowInvariant

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantBinaryGramInvariant
open YMGap.Continuum.SU2TransvectantRaisingCovariance

local infix:50 " ≈ " => Q'.eqv

private theorem scale_zero (q x : Q') (hx : x ≈ 0) : q * x ≈ 0 :=
  Q'.eqv_trans _ (q * 0) _ (Q'.mul_eqv_congr_left q _ _ hx)
    (Q'.mul_zero_eqv q)

private theorem first_raise_antidiagonal (p t : Nat) (c : BForm2) :
    finSum (fun i =>
      match i with
      | 0 => 0
      | u + 1 => Q'.ofNat (p - u) * c u (t + 1 - i)) (t + 2) ≈
      finSum (fun u => Q'.ofNat (p - u) * c u (t - u)) (t + 1) := by
  let g : Nat → Q' := fun i =>
    match i with
    | 0 => 0
    | u + 1 => Q'.ofNat (p - u) * c u (t + 1 - i)
  have hpeel := RationalTail.finSum_peel_left g (t + 1)
  have hshift :
      finSum (fun i => g (i + 1)) (t + 1) ≈
        finSum (fun u => Q'.ofNat (p - u) * c u (t - u)) (t + 1) := by
    refine finSum_eqv_congr_lt _ _ (t + 1) (fun i hi => ?_)
    simp only [g]
    rw [show t + 1 - (i + 1) = t - i by omega]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ (g 0 + finSum (fun i => g (i + 1)) (t + 1)) _
    (by simpa only [g] using hpeel) ?_
  refine Q'.eqv_trans _ (0 + finSum (fun i => g (i + 1)) (t + 1)) _
    (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _ (finSum (fun i => g (i + 1)) (t + 1)) _
    (Q'.eqv_of_eq (Q'.zero_add' _)) hshift

private theorem second_raise_antidiagonal (q t : Nat) (c : BForm2) :
    finSum (fun i =>
      match t + 1 - i with
      | 0 => 0
      | v + 1 => Q'.ofNat (q - v) * c i v) (t + 2) ≈
      finSum (fun i => Q'.ofNat (q - (t - i)) * c i (t - i)) (t + 1) := by
  let g : Nat → Q' := fun i =>
    match t + 1 - i with
    | 0 => 0
    | v + 1 => Q'.ofNat (q - v) * c i v
  have hprefix :
      finSum g (t + 1) ≈
        finSum (fun i => Q'.ofNat (q - (t - i)) * c i (t - i)) (t + 1) := by
    refine finSum_eqv_congr_lt _ _ (t + 1) (fun i hi => ?_)
    have hslot : t + 1 - i = (t - i) + 1 := by omega
    simp only [g, hslot]
    exact Q'.eqv_refl _
  have htop : g (t + 1) ≈ 0 := by
    simp only [g, Nat.sub_self]
    exact Q'.eqv_refl _
  change finSum g (t + 1) + g (t + 1) ≈ _
  refine Q'.eqv_trans _ (finSum g (t + 1) + 0) _
    (Q'.add_eqv_congr_left _ _ _ htop) ?_
  refine Q'.eqv_trans _ (finSum g (t + 1)) _
    (Q'.eqv_of_eq (Q'.add_zero' _)) hprefix

private theorem active_raise_coefficient (p q t i : Nat)
    (hi : i < t + 1) (hp : i ≤ p) (hq : t - i ≤ q) (x : Q') :
    Q'.ofNat (p - i) * x + Q'.ofNat (q - (t - i)) * x ≈
      Q'.ofNat (p + q - t) * x := by
  have hnat : (p - i) + (q - (t - i)) = p + q - t := by omega
  have hcoeff := Q'.ofNat_add_eqv (p - i) (q - (t - i))
  rw [hnat] at hcoeff
  refine Q'.eqv_trans _
    ((Q'.ofNat (p - i) + Q'.ofNat (q - (t - i))) * x) _
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ x (Q'.eqv_symm hcoeff)

private theorem supported_raise_term (p q t i : Nat) (c : BForm2)
    (hc : BidegreeSupported p q c) (hi : i < t + 1) :
    Q'.ofNat (p - i) * c i (t - i) +
        Q'.ofNat (q - (t - i)) * c i (t - i) ≈
      Q'.ofNat (p + q - t) * c i (t - i) := by
  by_cases hp : i ≤ p
  · by_cases hq : t - i ≤ q
    · exact active_raise_coefficient p q t i hi hp hq _
    · have hz := hc i (t - i) (Or.inr (by omega))
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (scale_zero _ _ hz) (scale_zero _ _ hz)) ?_
      refine Q'.eqv_trans _ 0 _ (Q'.eqv_of_eq (Q'.zero_add' 0)) ?_
      exact Q'.eqv_symm (scale_zero _ _ hz)
  · have hz := hc i (t - i) (Or.inl (by omega))
    refine Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr' (scale_zero _ _ hz) (scale_zero _ _ hz)) ?_
    refine Q'.eqv_trans _ 0 _ (Q'.eqv_of_eq (Q'.zero_add' 0)) ?_
    exact Q'.eqv_symm (scale_zero _ _ hz)

/-- Diagonal restriction commutes with total raising for a physical
bidegree.  Support is essential here: outside the bidegree rectangle Nat
subtraction truncates the formal coefficient identity. -/
theorem diag_E2_supported (p q s : Nat) (c : BForm2)
    (hc : BidegreeSupported p q c) :
    diag (E2 p q c) s ≈ Eop (p + q) (diag c) s := by
  cases s with
  | zero =>
      unfold diag E2 Eop
      simp only [finSum_succ, finSum_zero, Nat.zero_sub]
      exact Q'.eqv_refl _
  | succ t =>
      have hsplit := RationalTail.finSum_add
        (fun i => match i with
          | 0 => 0
          | u + 1 => Q'.ofNat (p - u) * c u (t + 1 - i))
        (fun i => match t + 1 - i with
          | 0 => 0
          | v + 1 => Q'.ofNat (q - v) * c i v) (t + 2)
      have hfirst := first_raise_antidiagonal p t c
      have hsecond := second_raise_antidiagonal q t c
      have hcombine := RationalTail.finSum_add
        (fun i => Q'.ofNat (p - i) * c i (t - i))
        (fun i => Q'.ofNat (q - (t - i)) * c i (t - i)) (t + 1)
      have hterms :
          finSum (fun i =>
            Q'.ofNat (p - i) * c i (t - i) +
              Q'.ofNat (q - (t - i)) * c i (t - i)) (t + 1) ≈
            finSum (fun i => Q'.ofNat (p + q - t) * c i (t - i))
              (t + 1) :=
        finSum_eqv_congr_lt _ _ (t + 1)
          (fun i hi => supported_raise_term p q t i c hc hi)
      unfold diag E2 Eop
      refine Q'.eqv_trans _
        (finSum (fun i => match i with
          | 0 => 0
          | u + 1 => Q'.ofNat (p - u) * c u (t + 1 - i)) (t + 2) +
         finSum (fun i => match t + 1 - i with
          | 0 => 0
          | v + 1 => Q'.ofNat (q - v) * c i v) (t + 2)) _ hsplit ?_
      refine Q'.eqv_trans _
        (finSum (fun i => Q'.ofNat (p - i) * c i (t - i)) (t + 1) +
         finSum (fun i => Q'.ofNat (q - (t - i)) * c i (t - i)) (t + 1)) _
        (Q'.add_eqv_congr' hfirst hsecond) ?_
      refine Q'.eqv_trans _
        (finSum (fun i =>
          Q'.ofNat (p - i) * c i (t - i) +
            Q'.ofNat (q - (t - i)) * c i (t - i)) (t + 1)) _
        (Q'.eqv_symm hcombine) ?_
      refine Q'.eqv_trans _
        (finSum (fun i => Q'.ofNat (p + q - t) * c i (t - i)) (t + 1)) _
        hterms ?_
      exact Q'.eqv_symm
        (const_mul_finSum (fun i => c i (t - i)) (Q'.ofNat (p + q - t))
          (t + 1))

/-- Every admissible Cayley transvectant commutes with total raising on a
physically supported input. -/
theorem transvect_E2_supported (m n k s : Nat) (c : BForm2)
    (hm : k ≤ m) (hn : k ≤ n) (hc : BidegreeSupported m n c) :
    transvect m n k (E2 m n c) s ≈
      Eop (m + n - 2 * k) (transvect m n k c) s := by
  have hpoint : BForm2Eqv
      (OmegaK m n k (E2 m n c))
      (E2 (m - k) (n - k) (OmegaK m n k c)) :=
    fun a b => omegaK_E2_comm_supported m n k a b c hm hn hc
  have hdiag := diag_congr hpoint s
  have hE := diag_E2_supported (m - k) (n - k) s (OmegaK m n k c)
    (omegaK_supported k m n c hm hn hc)
  refine Q'.eqv_trans _ _ _ hdiag ?_
  simpa only [transvect,
    show (m - k) + (n - k) = m + n - 2 * k by omega] using hE

end YMGap.Continuum.SU2TransvectantOutputRowInvariant

#print axioms YMGap.Continuum.SU2TransvectantOutputRowInvariant.diag_E2_supported
#print axioms YMGap.Continuum.SU2TransvectantOutputRowInvariant.transvect_E2_supported
