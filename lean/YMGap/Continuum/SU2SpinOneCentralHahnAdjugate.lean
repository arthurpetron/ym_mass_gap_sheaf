/-
# Division-free inverse for the physical spin-one Hahn matrix

On every central shell `2 <= t <= n`, the symbolic adjugate is simultaneously
a left and right inverse up to the explicit positive determinant
`2*n*(n+1)*(n+2)` for the actual transvectant matrix `hahnEntry 2 n t`.
-/

import YMGap.Continuum.SU2ThreeByThreeAdjugate

namespace YMGap.Continuum.SU2SpinOneCentralHahnAdjugate

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2SpinOneCentralHahnDeterminant
open YMGap.Continuum.SU2SpinOneCentralHahnPhysicalBridge
open YMGap.Continuum.SU2ThreeByThreeAdjugate

/-- The actual derived central-shell matrix. -/
def physicalHahn (n t : Nat) : Nat -> Nat -> Q' :=
  fun r i => hahnEntry 2 n t r i

/-- Its symbolic comparison matrix. -/
def symbolicHahn (n t : Nat) : Nat -> Nat -> Q' :=
  centralHahn (Q'.ofNat n) (Q'.ofNat t)

private theorem add3_congr {a0 a1 a2 b0 b1 b2 : Q'}
    (h0 : a0.eqv b0) (h1 : a1.eqv b1) (h2 : a2.eqv b2) :
    (a0 + a1 + a2).eqv (b0 + b1 + b2) := by
  have h01 : (a0 + a1).eqv (b0 + b1) :=
    Q'.eqv_trans _ (b0 + a1) _
      (Q'.add_eqv_congr_right a0 b0 a1 h0)
      (Q'.add_eqv_congr_left b0 a1 b1 h1)
  exact Q'.eqv_trans _ (b0 + b1 + a2) _
    (Q'.add_eqv_congr_right (a0 + a1) (b0 + b1) a2 h01)
    (Q'.add_eqv_congr_left (b0 + b1) a2 b2 h2)

private theorem physical_to_symbolic_left (n t r c : Nat)
    (ht : 2 <= t) (htn : t <= n) (hc : c < 3) :
    (matMul3 (adj3 (symbolicHahn n t)) (physicalHahn n t) r c).eqv
      (matMul3 (adj3 (symbolicHahn n t)) (symbolicHahn n t) r c) := by
  unfold matMul3
  apply add3_congr
  · exact Q'.mul_eqv_congr_left _ _ _
      (hahnEntry_eq_central n t 0 c ht htn (by decide) hc)
  · exact Q'.mul_eqv_congr_left _ _ _
      (hahnEntry_eq_central n t 1 c ht htn (by decide) hc)
  · exact Q'.mul_eqv_congr_left _ _ _
      (hahnEntry_eq_central n t 2 c ht htn (by decide) hc)

private theorem physical_to_symbolic_right (n t r c : Nat)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) :
    (matMul3 (physicalHahn n t) (adj3 (symbolicHahn n t)) r c).eqv
      (matMul3 (symbolicHahn n t) (adj3 (symbolicHahn n t)) r c) := by
  unfold matMul3
  apply add3_congr
  · exact Q'.mul_eqv_congr_right _ _ _
      (hahnEntry_eq_central n t r 0 ht htn hr (by decide))
  · exact Q'.mul_eqv_congr_right _ _ _
      (hahnEntry_eq_central n t r 1 ht htn hr (by decide))
  · exact Q'.mul_eqv_congr_right _ _ _
      (hahnEntry_eq_central n t r 2 ht htn hr (by decide))

/-- Physical left adjugate identity. -/
theorem physical_adjugate_mul (n t r c : Nat)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) (hc : c < 3) :
    (matMul3 (adj3 (symbolicHahn n t)) (physicalHahn n t) r c).eqv
      (if r = c then det3 (symbolicHahn n t) else 0) :=
  Q'.eqv_trans _ _ _ (physical_to_symbolic_left n t r c ht htn hc)
    (adjugate_mul (symbolicHahn n t) r c hr hc)

/-- Physical right adjugate identity. -/
theorem physical_mul_adjugate (n t r c : Nat)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) (hc : c < 3) :
    (matMul3 (physicalHahn n t) (adj3 (symbolicHahn n t)) r c).eqv
      (if r = c then det3 (symbolicHahn n t) else 0) :=
  Q'.eqv_trans _ _ _ (physical_to_symbolic_right n t r c ht htn hr)
    (mul_adjugate (symbolicHahn n t) r c hr hc)

/-- Explicit determinant-scaled left inverse for the physical matrix. -/
theorem physical_adjugate_mul_explicit (n t r c : Nat)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) (hc : c < 3) :
    (matMul3 (adj3 (symbolicHahn n t)) (physicalHahn n t) r c).eqv
      (if r = c then
        ((((2 : Q') * Q'.ofNat n) * (Q'.ofNat n + 1)) *
          (Q'.ofNat n + 2))
       else 0) := by
  refine Q'.eqv_trans _ _ _ (physical_adjugate_mul n t r c ht htn hr hc) ?_
  by_cases hrc : r = c
  · simp only [if_pos hrc]
    exact centralHahn_det (Q'.ofNat n) (Q'.ofNat t)
  · simp only [if_neg hrc]
    exact Q'.eqv_refl 0

/-- Explicit determinant-scaled right inverse for the physical matrix. -/
theorem physical_mul_adjugate_explicit (n t r c : Nat)
    (ht : 2 <= t) (htn : t <= n) (hr : r < 3) (hc : c < 3) :
    (matMul3 (physicalHahn n t) (adj3 (symbolicHahn n t)) r c).eqv
      (if r = c then
        ((((2 : Q') * Q'.ofNat n) * (Q'.ofNat n + 1)) *
          (Q'.ofNat n + 2))
       else 0) := by
  refine Q'.eqv_trans _ _ _ (physical_mul_adjugate n t r c ht htn hr hc) ?_
  by_cases hrc : r = c
  · simp only [if_pos hrc]
    exact centralHahn_det (Q'.ofNat n) (Q'.ofNat t)
  · simp only [if_neg hrc]
    exact Q'.eqv_refl 0

end YMGap.Continuum.SU2SpinOneCentralHahnAdjugate

#print axioms YMGap.Continuum.SU2SpinOneCentralHahnAdjugate.physical_adjugate_mul
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnAdjugate.physical_mul_adjugate
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnAdjugate.physical_adjugate_mul_explicit
#print axioms YMGap.Continuum.SU2SpinOneCentralHahnAdjugate.physical_mul_adjugate_explicit
