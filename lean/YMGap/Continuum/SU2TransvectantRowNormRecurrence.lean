/-
# Tensor-basis recurrences for arbitrary Cayley output rows

This module computes total lowering and raising on a pure tensor basis and
combines those decompositions with the two global transvectant covariance
theorems.  The resulting identities are the exact coefficient-row
recurrences used by the binary Hilbert--Schmidt norm argument.
-/

import YMGap.Continuum.SU2TransvectantOutputRowInvariant

namespace YMGap.Continuum.SU2TransvectantRowNormRecurrence

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

open YMGap.Constructive
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantBinaryGramInvariant
open YMGap.Continuum.SU2TransvectantOutputRowInvariant

local infix:50 " ≈ " => Q'.eqv

private theorem lower_first_mono (i j a b : Nat) :
    Q'.ofNat (a + 1) * tprod (mono i) (mono j) (a + 1) b ≈
      Q'.ofNat i * tprod (mono (i - 1)) (mono j) a b := by
  cases i with
  | zero =>
      have hne : ¬ a + 1 = 0 := by omega
      simp only [tprod, mono, if_neg hne, Nat.zero_sub]
      refine Q'.eqv_trans _ 0 _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
      exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ u =>
      by_cases ha : a = u
      · subst a
        by_cases hb : b = j
        · subst b
          simp only [tprod, mono, if_pos, Nat.add_sub_cancel]
          exact Q'.eqv_refl _
        · simp only [tprod, mono, if_pos, if_neg hb, Nat.add_sub_cancel]
          refine Q'.eqv_trans _ 0 _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) ?_
          exact Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
      · have hsucc : ¬ a + 1 = u + 1 := by omega
        simp only [tprod, mono, if_neg ha, if_neg hsucc, Nat.add_sub_cancel]
        refine Q'.eqv_trans _ 0 _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
        exact Q'.eqv_symm
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))

private theorem lower_second_mono (i j a b : Nat) :
    Q'.ofNat (b + 1) * tprod (mono i) (mono j) a (b + 1) ≈
      Q'.ofNat j * tprod (mono i) (mono (j - 1)) a b := by
  cases j with
  | zero =>
      have hne : ¬ b + 1 = 0 := by omega
      simp only [tprod, mono, if_neg hne, Nat.zero_sub]
      by_cases ha : a = i
      · simp only [if_pos ha]
        refine Q'.eqv_trans _ 0 _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) ?_
        exact Q'.eqv_symm (Q'.zero_mul_eqv _)
      · simp only [if_neg ha]
        refine Q'.eqv_trans _ 0 _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
        exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | succ v =>
      by_cases hb : b = v
      · subst b
        by_cases ha : a = i
        · subst a
          simp only [tprod, mono, if_pos, Nat.add_sub_cancel]
          exact Q'.eqv_refl _
        · simp only [tprod, mono, if_neg ha, Nat.add_sub_cancel]
          refine Q'.eqv_trans _ 0 _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
          exact Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
      · have hsucc : ¬ b + 1 = v + 1 := by omega
        simp only [tprod, mono, if_neg hb, if_neg hsucc, Nat.add_sub_cancel]
        by_cases ha : a = i
        · simp only [if_pos ha]
          refine Q'.eqv_trans _ 0 _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) ?_
          exact Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
        · simp only [if_neg ha]
          refine Q'.eqv_trans _ 0 _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
          exact Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))

/-- Total lowering of a tensor monomial has its two exact predecessor
branches, including the zero-index boundaries. -/
theorem F2_tprod_mono (m n i j : Nat) :
    BForm2Eqv (F2 m n (tprod (mono i) (mono j)))
      (badd
        (bscale (Q'.ofNat i) (tprod (mono (i - 1)) (mono j)))
        (bscale (Q'.ofNat j) (tprod (mono i) (mono (j - 1))))) := by
  intro a b
  unfold F2 badd bscale
  exact Q'.add_eqv_congr'
    (lower_first_mono i j a b) (lower_second_mono i j a b)

private theorem raise_first_mono (m i j a b : Nat) :
    (match a with
      | 0 => 0
      | u + 1 => Q'.ofNat (m - u) * tprod (mono i) (mono j) u b) ≈
      Q'.ofNat (m - i) * tprod (mono (i + 1)) (mono j) a b := by
  cases a with
  | zero =>
      have hne : ¬ 0 = i + 1 := by omega
      simp only [tprod, mono, if_neg hne]
      exact Q'.eqv_symm
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
  | succ u =>
      by_cases hu : u = i
      · subst u
        by_cases hb : b = j
        · subst b
          simp only [tprod, mono, if_pos]
          exact Q'.eqv_refl _
        · simp only [tprod, mono, if_pos, if_neg hb]
          exact Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
      · have hsucc : ¬ u + 1 = i + 1 := by omega
        simp only [tprod, mono, if_neg hu, if_neg hsucc]
        refine Q'.eqv_trans _ 0 _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
        exact Q'.eqv_symm
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))

private theorem raise_second_mono (n i j a b : Nat) :
    (match b with
      | 0 => 0
      | v + 1 => Q'.ofNat (n - v) * tprod (mono i) (mono j) a v) ≈
      Q'.ofNat (n - j) * tprod (mono i) (mono (j + 1)) a b := by
  cases b with
  | zero =>
      have hne : ¬ 0 = j + 1 := by omega
      simp only [tprod, mono, if_neg hne]
      by_cases ha : a = i
      · simp only [if_pos ha]
        exact Q'.eqv_symm
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
      · simp only [if_neg ha]
        exact Q'.eqv_symm
          (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
  | succ v =>
      by_cases hv : v = j
      · subst v
        by_cases ha : a = i
        · subst a
          simp only [tprod, mono, if_pos]
          exact Q'.eqv_refl _
        · simp only [tprod, mono, if_neg ha, if_pos]
          refine Q'.eqv_trans _ 0 _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
          exact Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
      · have hsucc : ¬ v + 1 = j + 1 := by omega
        simp only [tprod, mono, if_neg hv, if_neg hsucc]
        by_cases ha : a = i
        · simp only [if_pos ha]
          refine Q'.eqv_trans _ 0 _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _)) ?_
          exact Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
        · simp only [if_neg ha]
          refine Q'.eqv_trans _ 0 _
            (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _)) ?_
          exact Q'.eqv_symm
            (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))

/-- Total raising of a tensor monomial has its two exact successor branches,
with coefficients truncated precisely at the two physical top edges. -/
theorem E2_tprod_mono (m n i j : Nat) :
    BForm2Eqv (E2 m n (tprod (mono i) (mono j)))
      (badd
        (bscale (Q'.ofNat (m - i)) (tprod (mono (i + 1)) (mono j)))
        (bscale (Q'.ofNat (n - j)) (tprod (mono i) (mono (j + 1))))) := by
  intro a b
  unfold E2 badd bscale
  exact Q'.add_eqv_congr'
    (raise_first_mono m i j a b) (raise_second_mono n i j a b)

private theorem transvect_two_scaled (m n k s : Nat)
    (A B : Q') (c d : BForm2) :
    transvect m n k (badd (bscale A c) (bscale B d)) s ≈
      A * transvect m n k c s + B * transvect m n k d s := by
  have hadd := transvect_add m n k (bscale A c) (bscale B d) s
  have hA := transvect_scale m n k A c s
  have hB := transvect_scale m n k B d s
  exact Q'.eqv_trans _ _ _ hadd (Q'.add_eqv_congr' hA hB)

/-- Lowering recurrence between adjacent output rows of the tensor-basis
coefficient matrix. -/
theorem transvect_row_lowering (m n k s i j : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hi : i ≤ m) (hj : j ≤ n) :
    Q'.ofNat i *
        transvect m n k (tprod (mono (i - 1)) (mono j)) s +
      Q'.ofNat j *
        transvect m n k (tprod (mono i) (mono (j - 1))) s ≈
      Q'.ofNat (s + 1) *
        transvect m n k (tprod (mono i) (mono j)) (s + 1) := by
  let c := tprod (mono i) (mono j)
  let d := badd
    (bscale (Q'.ofNat i) (tprod (mono (i - 1)) (mono j)))
    (bscale (Q'.ofNat j) (tprod (mono i) (mono (j - 1))))
  have hdecomp : BForm2Eqv (F2 m n c) d := by
    simpa only [c, d] using F2_tprod_mono m n i j
  have hleft := transvect_congr m n k hdecomp s
  have hexpand := transvect_two_scaled m n k s (Q'.ofNat i) (Q'.ofNat j)
    (tprod (mono (i - 1)) (mono j))
    (tprod (mono i) (mono (j - 1)))
  have hcov :=
    YMGap.Continuum.SU2TransvectantBinaryGramInvariant.transvect_F2_supported
      m n k s c hm hn (tprod_mono_supported m n i j hi hj)
  refine Q'.eqv_trans _ (transvect m n k d s) _ ?_ ?_
  · exact Q'.eqv_symm (by simpa only [d] using hexpand)
  · refine Q'.eqv_trans _ (transvect m n k (F2 m n c) s) _
      (Q'.eqv_symm hleft) ?_
    simpa only [c, Fop] using hcov

/-- Raising recurrence between adjacent output rows of the tensor-basis
coefficient matrix. -/
theorem transvect_row_raising (m n k s i j : Nat)
    (hm : k ≤ m) (hn : k ≤ n) (hi : i ≤ m) (hj : j ≤ n) :
    Q'.ofNat (m - i) *
        transvect m n k (tprod (mono (i + 1)) (mono j)) (s + 1) +
      Q'.ofNat (n - j) *
        transvect m n k (tprod (mono i) (mono (j + 1))) (s + 1) ≈
      Q'.ofNat (m + n - 2 * k - s) *
        transvect m n k (tprod (mono i) (mono j)) s := by
  let c := tprod (mono i) (mono j)
  let d := badd
    (bscale (Q'.ofNat (m - i)) (tprod (mono (i + 1)) (mono j)))
    (bscale (Q'.ofNat (n - j)) (tprod (mono i) (mono (j + 1))))
  have hdecomp : BForm2Eqv (E2 m n c) d := by
    simpa only [c, d] using E2_tprod_mono m n i j
  have hleft := transvect_congr m n k hdecomp (s + 1)
  have hexpand := transvect_two_scaled m n k (s + 1)
    (Q'.ofNat (m - i)) (Q'.ofNat (n - j))
    (tprod (mono (i + 1)) (mono j))
    (tprod (mono i) (mono (j + 1)))
  have hcov := transvect_E2_supported m n k (s + 1) c hm hn
    (tprod_mono_supported m n i j hi hj)
  refine Q'.eqv_trans _ (transvect m n k d (s + 1)) _ ?_ ?_
  · exact Q'.eqv_symm (by simpa only [d] using hexpand)
  · refine Q'.eqv_trans _ (transvect m n k (E2 m n c) (s + 1)) _
      (Q'.eqv_symm hleft) ?_
    simpa only [c, Eop] using hcov

end YMGap.Continuum.SU2TransvectantRowNormRecurrence

#print axioms YMGap.Continuum.SU2TransvectantRowNormRecurrence.F2_tprod_mono
#print axioms YMGap.Continuum.SU2TransvectantRowNormRecurrence.E2_tprod_mono
#print axioms YMGap.Continuum.SU2TransvectantRowNormRecurrence.transvect_row_lowering
#print axioms YMGap.Continuum.SU2TransvectantRowNormRecurrence.transvect_row_raising
