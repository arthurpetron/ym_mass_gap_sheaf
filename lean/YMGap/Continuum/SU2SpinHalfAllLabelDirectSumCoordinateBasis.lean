/-
# A simultaneous Clebsch--Gordan basis for spin one-half times every label

The shell inverse is upgraded to leakage-free vectors on every interior weight
shell of `V_(1/2) tensor V_(n/2)`.  The upper vector maps only to the order-zero
channel and the lower vector maps only to the order-one channel; both surviving
coordinates have the same exact multiplier `n+1`.  The two one-dimensional
boundary shells are handled separately.  Together with the already proved
adjugate identities, this is a division-free all-label coordinate basis.
-/

import YMGap.Continuum.SU2SpinHalfShellTransvectantBridge

namespace YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantGeneralCoefficient
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2SpinHalfShellHahnInverse
open YMGap.Continuum.SU2SpinHalfShellTransvectantBridge

/-- The upper-channel vector on the interior shell `s`. -/
def upperShell (n s : Nat) : BForm2 :=
  shellTensor s (Q'.ofNat (n + 1 - s)) (Q'.ofNat s)

/-- The lower-channel vector on the interior shell `s`. -/
def lowerShell (s : Nat) : BForm2 :=
  shellTensor s (-1) 1

/-- The constructive reciprocal of the common determinant `n+1`. -/
def shellUnit (n : Nat) : Q' :=
  Q'.recipPos (Q'.ofNat (n + 1)) (Q'.ofNat_succ_pos n)

/-- Exactly normalized upper-channel vector. -/
def normalizedUpperShell (n s : Nat) : BForm2 :=
  bscale (shellUnit n) (upperShell n s)

/-- Exactly normalized lower-channel vector. -/
def normalizedLowerShell (n s : Nat) : BForm2 :=
  bscale (shellUnit n) (lowerShell s)

/-- The lowest one-dimensional shell. -/
def upperBoundaryLow : BForm2 := tprod (mono 0) (mono 0)

/-- The highest one-dimensional shell. -/
def upperBoundaryHigh (n : Nat) : BForm2 := tprod (mono 1) (mono n)

private theorem upperCoeff_zero (n s : Nat) :
    (Q'.ofNat (n + 1 - s) * Q'.ofNat s +
      -(Q'.ofNat s * Q'.ofNat (n + 1 - s))).eqv 0 := by
  refine Q'.eqv_trans _
    (Q'.ofNat s * Q'.ofNat (n + 1 - s) +
      -(Q'.ofNat s * Q'.ofNat (n + 1 - s))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_comm_eqv (Q'.ofNat (n + 1 - s)) (Q'.ofNat s))
      (Q'.eqv_refl _)
  · exact Q'.add_neg_self_eqv _

private theorem lowerCoeff_sum (n s : Nat) (hs : s ≤ n + 1) :
    (Q'.ofNat (n + 1 - s) * 1 +
      -(Q'.ofNat s * (-1))).eqv (Q'.ofNat (n + 1)) := by
  have hneg : (-(Q'.ofNat s * (-1))).eqv (Q'.ofNat s) := by
    refine Q'.eqv_trans _ (-(-(Q'.ofNat s * 1))) _
      (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv (Q'.ofNat s) 1)) ?_
    exact Q'.eqv_trans _ (Q'.ofNat s * 1) _
      (Q'.neg_neg_eqv _) (Q'.mul_one_eqv _)
  refine Q'.eqv_trans _
    (Q'.ofNat (n + 1 - s) + Q'.ofNat s) _
    (Q'.add_eqv_congr' (Q'.mul_one_eqv _) hneg) ?_
  exact shellCoeff_sum n s hs

/-! ## Leakage-free interior channel table -/

/-- Every interior upper vector maps to `(n+1)` times its order-zero monomial. -/
theorem upperShell_orderZero (n s : Nat) (hs0 : 1 ≤ s) (hsn : s ≤ n) :
    BFormEqv (transvect 1 n 0 (upperShell n s))
      (fun t => Q'.ofNat (n + 1) * mono s t) := by
  intro t
  refine Q'.eqv_trans _
    ((Q'.ofNat (n + 1 - s) + Q'.ofNat s) * mono s t) _
    (shellTensor_orderZero_form n s hs0 _ _ t) ?_
  exact Q'.mul_eqv_congr_right _ _ (mono s t)
    (shellCoeff_sum n s (by omega))

/-- Every interior upper vector is killed by the order-one channel. -/
theorem upperShell_orderOne_kernel (n s : Nat) (hs0 : 1 ≤ s) (hsn : s ≤ n) :
    BFormEqv (transvect 1 n 1 (upperShell n s)) zeroF := by
  intro t
  refine Q'.eqv_trans _
    ((Q'.ofNat (n + 1 - s) * Q'.ofNat s +
      -(Q'.ofNat s * Q'.ofNat (n + 1 - s))) * mono (s - 1) t) _
    (shellTensor_orderOne_form n s hs0 hsn _ _ t) ?_
  refine Q'.eqv_trans _ (0 * mono (s - 1) t) _
    (Q'.mul_eqv_congr_right _ _ _ (upperCoeff_zero n s)) ?_
  exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _) (Q'.eqv_refl _)

/-- Every interior lower vector is killed by the order-zero channel. -/
theorem lowerShell_orderZero_kernel (n s : Nat) (hs0 : 1 ≤ s) :
    BFormEqv (transvect 1 n 0 (lowerShell s)) zeroF := by
  intro t
  refine Q'.eqv_trans _ (((-1 : Q') + 1) * mono s t) _
    (shellTensor_orderZero_form n s hs0 _ _ t) ?_
  refine Q'.eqv_trans _ (0 * mono s t) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.neg_add_self_eqv 1)) ?_
  exact Q'.eqv_trans _ 0 _ (Q'.zero_mul_eqv _) (Q'.eqv_refl _)

/-- Every interior lower vector maps to `(n+1)` times its order-one monomial. -/
theorem lowerShell_orderOne (n s : Nat) (hs0 : 1 ≤ s) (hsn : s ≤ n) :
    BFormEqv (transvect 1 n 1 (lowerShell s))
      (fun t => Q'.ofNat (n + 1) * mono (s - 1) t) := by
  intro t
  refine Q'.eqv_trans _
    ((Q'.ofNat (n + 1 - s) * 1 + -(Q'.ofNat s * (-1))) *
      mono (s - 1) t) _
    (shellTensor_orderOne_form n s hs0 hsn _ _ t) ?_
  exact Q'.mul_eqv_congr_right _ _ (mono (s - 1) t)
    (lowerCoeff_sum n s (by omega))

private theorem shellUnit_mul_det (n : Nat) :
    (shellUnit n * Q'.ofNat (n + 1)).eqv 1 := by
  refine Q'.eqv_trans _ (Q'.ofNat (n + 1) * shellUnit n) _
    (Q'.mul_comm_eqv _ _) ?_
  exact Q'.mul_recipPos_eqv (Q'.ofNat (n + 1)) (Q'.ofNat_succ_pos n)

/-- Reciprocal normalization removes the common determinant from the upper
channel without introducing leakage. -/
theorem normalizedUpperShell_orderZero (n s : Nat) (hs0 : 1 ≤ s) (hsn : s ≤ n) :
    BFormEqv (transvect 1 n 0 (normalizedUpperShell n s)) (mono s) := by
  intro t
  refine Q'.eqv_trans _
    (shellUnit n * transvect 1 n 0 (upperShell n s) t) _
    (transvect_scale 1 n 0 (shellUnit n) (upperShell n s) t) ?_
  refine Q'.eqv_trans _
    (shellUnit n * (Q'.ofNat (n + 1) * mono s t)) _
    (Q'.mul_eqv_congr_left _ _ _ (upperShell_orderZero n s hs0 hsn t)) ?_
  refine Q'.eqv_trans _
    ((shellUnit n * Q'.ofNat (n + 1)) * mono s t) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.eqv_trans _ (1 * mono s t) _
    (Q'.mul_eqv_congr_right _ _ _ (shellUnit_mul_det n))
    (Q'.one_mul_eqv _)

theorem normalizedUpperShell_orderOne_kernel (n s : Nat)
    (hs0 : 1 ≤ s) (hsn : s ≤ n) :
    BFormEqv (transvect 1 n 1 (normalizedUpperShell n s)) zeroF := by
  intro t
  refine Q'.eqv_trans _
    (shellUnit n * transvect 1 n 1 (upperShell n s) t) _
    (transvect_scale 1 n 1 (shellUnit n) (upperShell n s) t) ?_
  refine Q'.eqv_trans _ (shellUnit n * 0) _
    (Q'.mul_eqv_congr_left _ _ _ (upperShell_orderOne_kernel n s hs0 hsn t)) ?_
  exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _) (Q'.eqv_refl _)

theorem normalizedLowerShell_orderZero_kernel (n s : Nat) (hs0 : 1 ≤ s) :
    BFormEqv (transvect 1 n 0 (normalizedLowerShell n s)) zeroF := by
  intro t
  refine Q'.eqv_trans _
    (shellUnit n * transvect 1 n 0 (lowerShell s) t) _
    (transvect_scale 1 n 0 (shellUnit n) (lowerShell s) t) ?_
  refine Q'.eqv_trans _ (shellUnit n * 0) _
    (Q'.mul_eqv_congr_left _ _ _ (lowerShell_orderZero_kernel n s hs0 t)) ?_
  exact Q'.eqv_trans _ 0 _ (Q'.mul_zero_eqv _) (Q'.eqv_refl _)

/-- Reciprocal normalization removes the common determinant from the lower
channel without introducing leakage. -/
theorem normalizedLowerShell_orderOne (n s : Nat) (hs0 : 1 ≤ s) (hsn : s ≤ n) :
    BFormEqv (transvect 1 n 1 (normalizedLowerShell n s)) (mono (s - 1)) := by
  intro t
  refine Q'.eqv_trans _
    (shellUnit n * transvect 1 n 1 (lowerShell s) t) _
    (transvect_scale 1 n 1 (shellUnit n) (lowerShell s) t) ?_
  refine Q'.eqv_trans _
    (shellUnit n * (Q'.ofNat (n + 1) * mono (s - 1) t)) _
    (Q'.mul_eqv_congr_left _ _ _ (lowerShell_orderOne n s hs0 hsn t)) ?_
  refine Q'.eqv_trans _
    ((shellUnit n * Q'.ofNat (n + 1)) * mono (s - 1) t) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.eqv_trans _ (1 * mono (s - 1) t) _
    (Q'.mul_eqv_congr_right _ _ _ (shellUnit_mul_det n))
    (Q'.one_mul_eqv _)

/-! ## Boundary shells -/

theorem upperBoundaryLow_orderZero (n : Nat) :
    BFormEqv (transvect 1 n 0 upperBoundaryLow) (mono 0) := by
  intro t
  simpa only [upperBoundaryLow, mono, Nat.zero_add] using
    transvect_zero_monomial 1 n 0 0 t

theorem upperBoundaryLow_orderOne_kernel (n : Nat) :
    BFormEqv (transvect 1 n 1 upperBoundaryLow) zeroF := by
  intro t
  have h := transvect_one_monomial 1 n 0 0 t
  simpa only [upperBoundaryLow, zeroF, Nat.zero_add, Nat.zero_mul,
    if_neg (by omega : ¬ t + 1 = 0)] using h

theorem upperBoundaryHigh_orderZero (n : Nat) :
    BFormEqv (transvect 1 n 0 (upperBoundaryHigh n)) (mono (n + 1)) := by
  intro t
  have h := transvect_zero_monomial 1 n 1 n t
  simpa only [upperBoundaryHigh, mono, Nat.add_comm] using h

theorem upperBoundaryHigh_orderOne_kernel (n : Nat) :
    BFormEqv (transvect 1 n 1 (upperBoundaryHigh n)) zeroF := by
  intro t
  have h := transvect_one_monomial 1 n 1 n t
  by_cases ht : t + 1 = 1 + n
  · simpa only [upperBoundaryHigh, zeroF, if_pos ht, Nat.sub_self,
      Nat.mul_zero, Nat.zero_mul, Nat.sub_self, Q'.ofNat_zero_eqv] using h
  · simpa only [upperBoundaryHigh, zeroF, if_neg ht] using h

/-! ## Full all-label package -/

/-- On every interior shell the leakage-free pair supplies one coordinate in
each direct-sum channel, while the actual two transvectant coordinates recover
both source coefficients up to the common nonzero determinant `n+1`. -/
theorem interiorShell_coordinate_basis (n s : Nat) (hs0 : 1 ≤ s) (hsn : s ≤ n) :
    BFormEqv (transvect 1 n 0 (upperShell n s))
        (fun t => Q'.ofNat (n + 1) * mono s t) ∧
    BFormEqv (transvect 1 n 1 (upperShell n s)) zeroF ∧
    BFormEqv (transvect 1 n 0 (lowerShell s)) zeroF ∧
    BFormEqv (transvect 1 n 1 (lowerShell s))
        (fun t => Q'.ofNat (n + 1) * mono (s - 1) t) ∧
    (∀ left right : Q',
      (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
        (transvect 1 n 0 (shellTensor s left right) s)
        (transvect 1 n 1 (shellTensor s left right) (s - 1))).1.eqv
          (Q'.ofNat (n + 1) * left)) ∧
    (∀ left right : Q',
      (shellAdjugate (Q'.ofNat s) (Q'.ofNat (n + 1 - s))
        (transvect 1 n 0 (shellTensor s left right) s)
        (transvect 1 n 1 (shellTensor s left right) (s - 1))).2.eqv
          (Q'.ofNat (n + 1) * right)) := by
  exact ⟨upperShell_orderZero n s hs0 hsn,
    upperShell_orderOne_kernel n s hs0 hsn,
    lowerShell_orderZero_kernel n s hs0,
    lowerShell_orderOne n s hs0 hsn,
    actual_transvectants_left_scaled n s hs0 hsn,
    actual_transvectants_right_scaled n s hs0 hsn⟩

/-- Complete all-label `V_(1/2) tensor V_(n/2) = V_((n+1)/2) plus
V_((n-1)/2)` coordinate table, including both boundary shells. -/
theorem spinHalf_allLabel_directSum_coordinate_basis (n : Nat) :
    (BFormEqv (transvect 1 n 0 upperBoundaryLow) (mono 0) ∧
     BFormEqv (transvect 1 n 1 upperBoundaryLow) zeroF) ∧
    (BFormEqv (transvect 1 n 0 (upperBoundaryHigh n)) (mono (n + 1)) ∧
     BFormEqv (transvect 1 n 1 (upperBoundaryHigh n)) zeroF) ∧
    (∀ s, 1 ≤ s → s ≤ n →
      BFormEqv (transvect 1 n 0 (upperShell n s))
          (fun t => Q'.ofNat (n + 1) * mono s t) ∧
      BFormEqv (transvect 1 n 1 (upperShell n s)) zeroF ∧
      BFormEqv (transvect 1 n 0 (lowerShell s)) zeroF ∧
      BFormEqv (transvect 1 n 1 (lowerShell s))
          (fun t => Q'.ofNat (n + 1) * mono (s - 1) t)) := by
  exact ⟨⟨upperBoundaryLow_orderZero n, upperBoundaryLow_orderOne_kernel n⟩,
    ⟨upperBoundaryHigh_orderZero n, upperBoundaryHigh_orderOne_kernel n⟩,
    fun s hs0 hsn =>
      ⟨upperShell_orderZero n s hs0 hsn,
       upperShell_orderOne_kernel n s hs0 hsn,
       lowerShell_orderZero_kernel n s hs0,
       lowerShell_orderOne n s hs0 hsn⟩⟩

end YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis

#print axioms YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis.upperShell_orderZero
#print axioms YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis.upperShell_orderOne_kernel
#print axioms YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis.lowerShell_orderZero_kernel
#print axioms YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis.lowerShell_orderOne
#print axioms YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis.normalizedUpperShell_orderZero
#print axioms YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis.normalizedLowerShell_orderOne
#print axioms YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis.interiorShell_coordinate_basis
#print axioms YMGap.Continuum.SU2SpinHalfAllLabelDirectSumCoordinateBasis.spinHalf_allLabel_directSum_coordinate_basis
