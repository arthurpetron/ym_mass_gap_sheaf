/-
# Connecting the spin-half shell inverse to the actual transvectants

On every interior shell of `V_(1/2) tensor V_(n/2)`, the order-zero and
order-one Cayley transvectants are exactly the two coordinates consumed by
`SU2SpinHalfShellHahnInverse`.  This turns the abstract determinant calculation
into a genuine all-`n` Clebsch--Gordan statement.
-/

import YMGap.Continuum.SU2SpinHalfShellHahnInverse

namespace YMGap.Continuum.SU2SpinHalfShellTransvectantBridge

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2SpinHalfShellHahnInverse

/-- The two source monomials on total-index shell `s`. -/
def shellTensor (s : Nat) (left right : Q') : BForm2 :=
  badd
    (bscale left (tprod (mono 0) (mono s)))
    (bscale right (tprod (mono 1) (mono (s - 1))))

/-- Order zero reads the sum coordinate on every interior shell. -/
theorem shellTensor_orderZero_at (n s : Nat) (hs0 : 1 ≤ s)
    (left right : Q') :
    (transvect 1 n 0 (shellTensor s left right) s).eqv (left + right) := by
  have hadd := transvect_add 1 n 0
    (bscale left (tprod (mono 0) (mono s)))
    (bscale right (tprod (mono 1) (mono (s - 1)))) s
  have hleftScale := transvect_scale 1 n 0 left
    (tprod (mono 0) (mono s)) s
  have hrightScale := transvect_scale 1 n 0 right
    (tprod (mono 1) (mono (s - 1))) s
  have hleftMono := transvect_zero_monomial 1 n 0 s s
  have hrightMono := transvect_zero_monomial 1 n 1 (s - 1) s
  have hshell : s = 1 + (s - 1) := by omega
  have hleftMono' :
      (transvect 1 n 0 (tprod (mono 0) (mono s)) s).eqv 1 := by
    simpa using hleftMono
  have hrightMono' :
      (transvect 1 n 0 (tprod (mono 1) (mono (s - 1))) s).eqv 1 := by
    simpa only [if_pos hshell] using hrightMono
  refine Q'.eqv_trans _
    (transvect 1 n 0 (bscale left (tprod (mono 0) (mono s))) s +
      transvect 1 n 0 (bscale right (tprod (mono 1) (mono (s - 1)))) s) _
    (by simpa only [shellTensor] using hadd) ?_
  refine Q'.eqv_trans _ (left * 1 + right * 1) _
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ hleftScale
        (Q'.mul_eqv_congr_left left _ _ hleftMono'))
      (Q'.eqv_trans _ _ _ hrightScale
        (Q'.mul_eqv_congr_left right _ _ hrightMono'))) ?_
  exact Q'.add_eqv_congr' (Q'.mul_one_eqv left) (Q'.mul_one_eqv right)

/-- Order one reads the signed difference coordinate on every interior shell. -/
theorem shellTensor_orderOne_at (n s : Nat) (hs0 : 1 ≤ s) (hsn : s ≤ n)
    (left right : Q') :
    (transvect 1 n 1 (shellTensor s left right) (s - 1)).eqv
      (Q'.ofNat (n + 1 - s) * right + -(Q'.ofNat s * left)) := by
  have hadd := transvect_add 1 n 1
    (bscale left (tprod (mono 0) (mono s)))
    (bscale right (tprod (mono 1) (mono (s - 1)))) (s - 1)
  have hleftScale := transvect_scale 1 n 1 left
    (tprod (mono 0) (mono s)) (s - 1)
  have hrightScale := transvect_scale 1 n 1 right
    (tprod (mono 1) (mono (s - 1))) (s - 1)
  have hleftMono := transvect_one_monomial 1 n 0 s (s - 1)
  have hrightMono := transvect_one_monomial 1 n 1 (s - 1) (s - 1)
  have hshellL : s - 1 + 1 = 0 + s := by omega
  have hshellR : s - 1 + 1 = 1 + (s - 1) := by omega
  have hnshift : n - (s - 1) = n + 1 - s := by omega
  have hleftMono' :
      (transvect 1 n 1 (tprod (mono 0) (mono s)) (s - 1)).eqv
        (-(Q'.ofNat s)) := by
    refine Q'.eqv_trans _
      (Q'.ofNat (0 * (n - s)) + -(Q'.ofNat ((1 - 0) * s))) _ ?_ ?_
    · simpa only [if_pos hshellL] using hleftMono
    · simp only [Nat.zero_mul, show 1 - 0 = 1 by omega, Nat.one_mul]
      exact Q'.eqv_trans _ ((0 : Q') + -(Q'.ofNat s)) _
        (Q'.add_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (Q'.eqv_of_eq (Q'.zero_add' (-(Q'.ofNat s))))
  have hrightMono' :
      (transvect 1 n 1 (tprod (mono 1) (mono (s - 1))) (s - 1)).eqv
        (Q'.ofNat (n + 1 - s)) := by
    refine Q'.eqv_trans _
      (Q'.ofNat (1 * (n - (s - 1))) +
        -(Q'.ofNat ((1 - 1) * (s - 1)))) _ ?_ ?_
    · simpa only [if_pos hshellR] using hrightMono
    · rw [hnshift]
      simpa only [Nat.one_mul, Nat.sub_self, Nat.zero_mul]
        using Q'.eqv_of_eq (Q'.add_zero' (Q'.ofNat (n + 1 - s)))
  refine Q'.eqv_trans _
    (transvect 1 n 1 (bscale left (tprod (mono 0) (mono s))) (s - 1) +
      transvect 1 n 1 (bscale right (tprod (mono 1) (mono (s - 1))))
        (s - 1)) _
    (by simpa only [shellTensor] using hadd) ?_
  have hscaledLeft :
      (transvect 1 n 1 (bscale left (tprod (mono 0) (mono s)))
        (s - 1)).eqv (-(Q'.ofNat s * left)) := by
    have hleftScale' :
        (transvect 1 n 1 (bscale left (tprod (mono 0) (mono s)))
          (s - 1)).eqv
          (left * transvect 1 n 1 (tprod (mono 0) (mono s)) (s - 1)) := by
      simpa using hleftScale
    refine Q'.eqv_trans _ (left * (-(Q'.ofNat s))) _
      (Q'.eqv_trans _ _ _ hleftScale'
        (Q'.mul_eqv_congr_left left _ _ hleftMono')) ?_
    refine Q'.eqv_trans _ (-(left * Q'.ofNat s)) _
      (Q'.mul_neg_eqv left (Q'.ofNat s)) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv left (Q'.ofNat s))
  have hscaledRight :
      (transvect 1 n 1 (bscale right (tprod (mono 1) (mono (s - 1))))
        (s - 1)).eqv (Q'.ofNat (n + 1 - s) * right) := by
    refine Q'.eqv_trans _ (right * Q'.ofNat (n + 1 - s)) _
      (Q'.eqv_trans _ _ _ hrightScale
        (Q'.mul_eqv_congr_left right _ _ hrightMono')) ?_
    exact Q'.mul_comm_eqv right (Q'.ofNat (n + 1 - s))
  refine Q'.eqv_trans _
    (-(Q'.ofNat s * left) + Q'.ofNat (n + 1 - s) * right) _
    (Q'.add_eqv_congr' hscaledLeft hscaledRight) ?_
  exact Q'.add_comm_eqv _ _

/-- The order-zero channel has no support away from its shell coordinate. -/
theorem shellTensor_orderZero_form (n s : Nat) (hs0 : 1 ≤ s)
    (left right : Q') :
    BFormEqv (transvect 1 n 0 (shellTensor s left right))
      (fun t => (left + right) * mono s t) := by
  intro t
  by_cases ht : t = s
  · subst t
    refine Q'.eqv_trans _ (left + right) _
      (shellTensor_orderZero_at n s hs0 left right) ?_
    simp only [mono]
    exact Q'.eqv_symm (Q'.mul_one_eqv (left + right))
  · have hadd := transvect_add 1 n 0
      (bscale left (tprod (mono 0) (mono s)))
      (bscale right (tprod (mono 1) (mono (s - 1)))) t
    have hleftScale := transvect_scale 1 n 0 left
      (tprod (mono 0) (mono s)) t
    have hrightScale := transvect_scale 1 n 0 right
      (tprod (mono 1) (mono (s - 1))) t
    have hleftMono0 := transvect_zero_monomial 1 n 0 s t
    have hrightMono0 := transvect_zero_monomial 1 n 1 (s - 1) t
    have hleftMono :
        (transvect 1 n 0 (tprod (mono 0) (mono s)) t).eqv 0 := by
      simpa only [if_neg (by omega : ¬ t = 0 + s)] using hleftMono0
    have hrightMono :
        (transvect 1 n 0 (tprod (mono 1) (mono (s - 1))) t).eqv 0 := by
      simpa only [if_neg (by omega : ¬ t = 1 + (s - 1))] using hrightMono0
    refine Q'.eqv_trans _
      (transvect 1 n 0 (bscale left (tprod (mono 0) (mono s))) t +
        transvect 1 n 0 (bscale right (tprod (mono 1) (mono (s - 1)))) t) _
      (by simpa only [shellTensor] using hadd) ?_
    refine Q'.eqv_trans _ (left * 0 + right * 0) _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (by simpa using hleftScale)
          (Q'.mul_eqv_congr_left left _ _ hleftMono))
        (Q'.eqv_trans _ _ _ (by simpa using hrightScale)
          (Q'.mul_eqv_congr_left right _ _ hrightMono))) ?_
    refine Q'.eqv_trans _ 0 _ ?_ ?_
    · exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (Q'.mul_zero_eqv left) (Q'.mul_zero_eqv right))
        (Q'.eqv_of_eq (Q'.zero_add' 0))
    · simp only [mono, if_neg ht]
      exact Q'.eqv_symm (Q'.mul_zero_eqv (left + right))

/-- The order-one channel likewise has support only at the degree-lowered
shell coordinate. -/
theorem shellTensor_orderOne_form (n s : Nat) (hs0 : 1 ≤ s) (hsn : s ≤ n)
    (left right : Q') :
    BFormEqv (transvect 1 n 1 (shellTensor s left right))
      (fun t =>
        (Q'.ofNat (n + 1 - s) * right + -(Q'.ofNat s * left)) *
          mono (s - 1) t) := by
  intro t
  by_cases ht : t = s - 1
  · subst t
    refine Q'.eqv_trans _
      (Q'.ofNat (n + 1 - s) * right + -(Q'.ofNat s * left)) _
      (shellTensor_orderOne_at n s hs0 hsn left right) ?_
    simp only [mono]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · have hadd := transvect_add 1 n 1
      (bscale left (tprod (mono 0) (mono s)))
      (bscale right (tprod (mono 1) (mono (s - 1)))) t
    have hleftScale := transvect_scale 1 n 1 left
      (tprod (mono 0) (mono s)) t
    have hrightScale := transvect_scale 1 n 1 right
      (tprod (mono 1) (mono (s - 1))) t
    have hleftMono0 := transvect_one_monomial 1 n 0 s t
    have hrightMono0 := transvect_one_monomial 1 n 1 (s - 1) t
    have hleftMono :
        (transvect 1 n 1 (tprod (mono 0) (mono s)) t).eqv 0 := by
      simpa only [if_neg (by omega : ¬ t + 1 = 0 + s)] using hleftMono0
    have hrightMono :
        (transvect 1 n 1 (tprod (mono 1) (mono (s - 1))) t).eqv 0 := by
      simpa only [if_neg (by omega : ¬ t + 1 = 1 + (s - 1))] using hrightMono0
    refine Q'.eqv_trans _
      (transvect 1 n 1 (bscale left (tprod (mono 0) (mono s))) t +
        transvect 1 n 1 (bscale right (tprod (mono 1) (mono (s - 1)))) t) _
      (by simpa only [shellTensor] using hadd) ?_
    refine Q'.eqv_trans _ (left * 0 + right * 0) _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (by simpa using hleftScale)
          (Q'.mul_eqv_congr_left left _ _ hleftMono))
        (Q'.eqv_trans _ _ _ (by simpa using hrightScale)
          (Q'.mul_eqv_congr_left right _ _ hrightMono))) ?_
    refine Q'.eqv_trans _ 0 _ ?_ ?_
    · exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (Q'.mul_zero_eqv left) (Q'.mul_zero_eqv right))
        (Q'.eqv_of_eq (Q'.zero_add' 0))
    · simp only [mono, if_neg ht]
      exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-- The actual pair of transvectant shell coordinates is exactly `shellForward`. -/
theorem shellTensor_transvectants_forward (n s : Nat)
    (hs0 : 1 ≤ s) (hsn : s ≤ n) (left right : Q') :
    ((transvect 1 n 0 (shellTensor s left right) s,
      transvect 1 n 1 (shellTensor s left right) (s - 1))).1.eqv
        (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).1 ∧
    ((transvect 1 n 0 (shellTensor s left right) s,
      transvect 1 n 1 (shellTensor s left right) (s - 1))).2.eqv
        (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).2 := by
  constructor
  · simpa only [Prod.fst, shellForward] using
      shellTensor_orderZero_at n s hs0 left right
  · simpa only [Prod.snd, shellForward] using
      shellTensor_orderOne_at n s hs0 hsn left right

/-- The two actual Cayley coordinates reconstruct the left source coefficient
up to the determinant `n+1`. -/
theorem actual_transvectants_left_scaled (n s : Nat)
    (hs0 : 1 ≤ s) (hsn : s ≤ n) (left right : Q') :
    (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
      (transvect 1 n 0 (shellTensor s left right) s)
      (transvect 1 n 1 (shellTensor s left right) (s - 1))).1.eqv
      (Q'.ofNat (n + 1) * left) := by
  have hcoords := shellTensor_transvectants_forward n s hs0 hsn left right
  have hcongr :
      (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
        (transvect 1 n 0 (shellTensor s left right) s)
        (transvect 1 n 1 (shellTensor s left right) (s - 1))).1.eqv
      (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
        (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).1
        (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).2).1 := by
    unfold shellAdjugate
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (Q'.ofNat (n + 1 - s)) _ _ hcoords.1)
      (Q'.neg_eqv_congr _ _ hcoords.2)
  exact Q'.eqv_trans _ _ _ hcongr
    (spinHalfShell_left_scaled n s (by omega) left right)

/-- The same actual Cayley coordinates reconstruct the right source coefficient
up to the determinant `n+1`. -/
theorem actual_transvectants_right_scaled (n s : Nat)
    (hs0 : 1 ≤ s) (hsn : s ≤ n) (left right : Q') :
    (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
      (transvect 1 n 0 (shellTensor s left right) s)
      (transvect 1 n 1 (shellTensor s left right) (s - 1))).2.eqv
      (Q'.ofNat (n + 1) * right) := by
  have hcoords := shellTensor_transvectants_forward n s hs0 hsn left right
  have hcongr :
      (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
        (transvect 1 n 0 (shellTensor s left right) s)
        (transvect 1 n 1 (shellTensor s left right) (s - 1))).2.eqv
      (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
        (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).1
        (shellForward (Q'.ofNat s) (Q'.ofNat (n + 1 - s)) left right).2).2 := by
    unfold shellAdjugate
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (Q'.ofNat s) _ _ hcoords.1)
      hcoords.2
  exact Q'.eqv_trans _ _ _ hcongr
    (spinHalfShell_right_scaled n s (by omega) left right)

end YMGap.Continuum.SU2SpinHalfShellTransvectantBridge

#print axioms YMGap.Continuum.SU2SpinHalfShellTransvectantBridge.shellTensor_orderZero_at
#print axioms YMGap.Continuum.SU2SpinHalfShellTransvectantBridge.shellTensor_orderOne_at
#print axioms YMGap.Continuum.SU2SpinHalfShellTransvectantBridge.shellTensor_orderZero_form
#print axioms YMGap.Continuum.SU2SpinHalfShellTransvectantBridge.shellTensor_orderOne_form
#print axioms YMGap.Continuum.SU2SpinHalfShellTransvectantBridge.shellTensor_transvectants_forward
#print axioms YMGap.Continuum.SU2SpinHalfShellTransvectantBridge.actual_transvectants_left_scaled
#print axioms YMGap.Continuum.SU2SpinHalfShellTransvectantBridge.actual_transvectants_right_scaled
