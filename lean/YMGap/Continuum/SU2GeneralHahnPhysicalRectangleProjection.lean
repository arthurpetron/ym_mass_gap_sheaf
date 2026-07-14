/-
# Physical rectangle projection by total-weight shells

The total `BForm2` carrier is normalized by summing its physical monomial
coefficients shell by shell.  The resulting tensor agrees with the input on
the complete `(m+1) x (n+1)` rectangle and is zero outside it.  This is the
support normalization required before raw transvectant coordinates descend
to rectangle semantics.
-/

import YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction

namespace YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection

set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnCentralShellBasis
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction

local infix:50 " ≈ " => Q'.eqv

private theorem finiteDot_right_congr (N : Nat)
    (coeff row row' : Nat → Q')
    (hrow : ∀ i, i < N → row i ≈ row' i) :
    finiteDot N coeff row ≈ finiteDot N coeff row' := by
  induction N generalizing coeff row row' with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [finiteDot]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _ (hrow 0 (by omega)))
        (ih _ _ _ (fun i hi => hrow (i + 1) (by omega)))

private theorem finiteDot_zero_right (N : Nat) (coeff row : Nat → Q')
    (hrow : ∀ i, i < N → row i ≈ 0) :
    finiteDot N coeff row ≈ 0 := by
  induction N generalizing coeff row with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [finiteDot]
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ (coeff 0 * 0) _
            (Q'.mul_eqv_congr_left _ _ _ (hrow 0 (by omega)))
            (Q'.mul_zero_eqv _))
          (ih _ _ (fun i hi => hrow (i + 1) (by omega)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem finiteDot_onehot_right : ∀ N a : Nat,
    a < N → ∀ coeff : Nat → Q',
      finiteDot N coeff (fun q => if q = a then 1 else 0) ≈ coeff a
  | 0, a, ha, coeff => absurd ha (Nat.not_lt_zero a)
  | N + 1, 0, ha, coeff => by
      simp only [finiteDot, if_pos]
      have htail : finiteDot N (fun q => coeff (q + 1))
          (fun q => if q + 1 = 0 then 1 else 0) ≈ 0 :=
        finiteDot_zero_right N _ _ (fun q hq => by
          rw [if_neg (by omega)]
          exact Q'.eqv_refl _)
      refine Q'.eqv_trans _ (coeff 0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_one_eqv _) htail
      · exact Q'.eqv_of_eq (Q'.add_zero' _)
  | N + 1, a + 1, ha, coeff => by
      simp only [finiteDot, if_neg (by omega : ¬ 0 = a + 1)]
      have hih := finiteDot_onehot_right N a (by omega)
        (fun q => coeff (q + 1))
      have htail : finiteDot N (fun q => coeff (q + 1))
          (fun q => if q + 1 = a + 1 then 1 else 0) ≈ coeff (a + 1) := by
        refine Q'.eqv_trans _
          (finiteDot N (fun q => coeff (q + 1))
            (fun q => if q = a then 1 else 0)) _ ?_ hih
        exact finiteDot_right_congr _ _ _ _ (fun q hq => by
          by_cases hqa : q = a
          · subst q
            rw [if_pos rfl, if_pos rfl]
            exact Q'.eqv_refl _
          · have hshift : ¬ q + 1 = a + 1 := by omega
            rw [if_neg hshift, if_neg hqa]
            exact Q'.eqv_refl _)
      refine Q'.eqv_trans _ (0 + coeff (a + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_zero_eqv _) htail
      · exact Q'.eqv_of_eq (Q'.zero_add' _)

/-- Pointwise evaluation of an arbitrary finite shell-source prefix. -/
theorem shellSourcePrefix_apply (t N : Nat) (col : Nat → Nat)
    (coeff : Nat → Q') (i j : Nat) :
    shellSourcePrefix t N col coeff i j ≈
      finiteDot N coeff (fun q => shellBasis t (col q) i j) := by
  induction N generalizing col coeff with
  | zero =>
      simp only [shellSourcePrefix, bscale, finiteDot]
      exact Q'.zero_mul_eqv _
  | succ N ih =>
      simp only [shellSourcePrefix, badd, bscale, finiteDot]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (ih _ _)

/-- The actual tensor containing exactly the physical columns of one source
total-weight shell. -/
def physicalSourceShell (m n t : Nat) (x : BForm2) : BForm2 :=
  shellSourcePrefix t (shellWidth m n t + 1)
    (fun a => shellLo n t + a) (sourceShellCoordinates n t x)

/-- Exact pointwise value of one physical source shell. -/
theorem physicalSourceShell_apply (m n t : Nat) (ht : t ≤ m + n)
    (x : BForm2) (i j : Nat) :
    physicalSourceShell m n t x i j ≈
      (if hi : i ≤ m then if hj : j ≤ n then
        if i + j = t then x i j else 0 else 0 else 0) := by
  have hprefix := shellSourcePrefix_apply t (shellWidth m n t + 1)
    (fun a => shellLo n t + a) (sourceShellCoordinates n t x) i j
  by_cases hi : i ≤ m
  · rw [dif_pos hi]
    by_cases hj : j ≤ n
    · rw [dif_pos hj]
      by_cases hs : i + j = t
      · rw [if_pos hs]
        have hactive : SourceActive m n t i := by
          unfold SourceActive
          exact ⟨by omega, hi, by omega⟩
        have hindex := sourceActive_index_complete m n t i hactive
        let a := i - shellLo n t
        have ha : a < shellWidth m n t + 1 :=
          Nat.lt_succ_iff.mpr hindex.1
        have hrows : ∀ q, q < shellWidth m n t + 1 →
            shellBasis t (shellLo n t + q) i j ≈
              (if q = a then 1 else 0) := by
          intro q hq
          have hsrc := sourceActive_of_index m n t q ht
            (Nat.lt_succ_iff.mp hq)
          by_cases hqa : q = a
          · subst q
            have hleft : shellLo n t + a = i := hindex.2
            have hright : t - (shellLo n t + a) = j := by omega
            have hright' : j = t - (shellLo n t + a) := hright.symm
            simp only [shellBasis, tprod, mono, hleft, hright', if_pos]
            exact Q'.one_mul_eqv _
          · have hleft : ¬ i = shellLo n t + q := by
              intro heq
              have : q = a := by unfold a; omega
              exact hqa this
            simp only [shellBasis, tprod, mono, if_neg hleft, if_neg hqa]
            exact Q'.zero_mul_eqv _
        refine Q'.eqv_trans _
          (finiteDot (shellWidth m n t + 1)
            (sourceShellCoordinates n t x)
            (fun q => shellBasis t (shellLo n t + q) i j)) _ hprefix ?_
        refine Q'.eqv_trans _
          (finiteDot (shellWidth m n t + 1)
            (sourceShellCoordinates n t x)
            (fun q => if q = a then 1 else 0)) _
          (finiteDot_right_congr _ _ _ _ hrows) ?_
        refine Q'.eqv_trans _ (sourceShellCoordinates n t x a) _
          (finiteDot_onehot_right _ a ha _) ?_
        unfold sourceShellCoordinates
        rw [hindex.2]
        have hright : t - i = j := by omega
        rw [hright]
        exact Q'.eqv_refl _
      · rw [if_neg hs]
        refine Q'.eqv_trans _ _ _ hprefix ?_
        apply finiteDot_zero_right
        intro q hq
        have hsrc := sourceActive_of_index m n t q ht
          (Nat.lt_succ_iff.mp hq)
        have hcolt : shellLo n t + q ≤ t := hsrc.1
        unfold shellBasis tprod mono
        by_cases hleft : i = shellLo n t + q
        · have hright : ¬ j = t - (shellLo n t + q) := by
            intro hjEq
            apply hs
            omega
          rw [if_pos hleft, if_neg hright]
          exact Q'.mul_zero_eqv _
        · rw [if_neg hleft]
          exact Q'.zero_mul_eqv _
    · rw [dif_neg hj]
      refine Q'.eqv_trans _ _ _ hprefix ?_
      apply finiteDot_zero_right
      intro q hq
      have hsrc := sourceActive_of_index m n t q ht
        (Nat.lt_succ_iff.mp hq)
      have hrightBound : t - (shellLo n t + q) ≤ n := hsrc.2.2
      unfold shellBasis tprod mono
      have hright : ¬ j = t - (shellLo n t + q) := by omega
      rw [if_neg hright]
      exact Q'.mul_zero_eqv _
  · rw [dif_neg hi]
    refine Q'.eqv_trans _ _ _ hprefix ?_
    apply finiteDot_zero_right
    intro q hq
    have hsrc := sourceActive_of_index m n t q ht
      (Nat.lt_succ_iff.mp hq)
    have hleftBound : shellLo n t + q ≤ m := hsrc.2.1
    unfold shellBasis tprod mono
    have hleft : ¬ i = shellLo n t + q := by omega
    rw [if_neg hleft]
    exact Q'.zero_mul_eqv _

/-- Finite sum of consecutive physical source shells. -/
def physicalShellRange (m n : Nat) (x : BForm2) (start : Nat) :
    Nat → BForm2
  | 0 => fun _ _ => 0
  | N + 1 => badd (physicalSourceShell m n start x)
      (physicalShellRange m n x (start + 1) N)

theorem physicalShellRange_apply (m n : Nat) (x : BForm2)
    (start N i j : Nat) :
    physicalShellRange m n x start N i j ≈
      finSum (fun r => physicalSourceShell m n (start + r) x i j) N := by
  induction N generalizing start with
  | zero => exact Q'.eqv_refl _
  | succ N ih =>
      simp only [physicalShellRange, badd]
      refine Q'.eqv_trans _
        (physicalSourceShell m n start x i j +
          finSum (fun r => physicalSourceShell m n (start + 1 + r) x i j) N) _
        (Q'.add_eqv_congr_left _ _ _ (ih (start + 1))) ?_
      have hpeel := RationalTail.finSum_peel_left
        (fun r => physicalSourceShell m n (start + r) x i j) N
      have hshift :
          finSum (fun r => physicalSourceShell m n (start + (r + 1)) x i j) N ≈
            finSum (fun r => physicalSourceShell m n (start + 1 + r) x i j) N := by
        apply RationalTail.finSum_eqv_congr_lt
        intro r hr
        rw [show start + (r + 1) = start + 1 + r by omega]
        exact Q'.eqv_refl _
      refine Q'.eqv_trans _
        (physicalSourceShell m n start x i j +
          finSum (fun r => physicalSourceShell m n (start + (r + 1)) x i j) N) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hshift)) ?_
      exact Q'.eqv_symm (by simpa only [Nat.add_zero] using hpeel)

/-- Zero-outside physical normalization of a total tensor. -/
def rectProject (m n : Nat) (x : BForm2) : BForm2 :=
  physicalShellRange m n x 0 (m + n + 1)

/-- Projection is the identity on every physical source coefficient. -/
theorem rectProject_apply_physical (m n : Nat) (x : BForm2)
    (i j : Nat) (hi : i ≤ m) (hj : j ≤ n) :
    rectProject m n x i j ≈ x i j := by
  have hrange := physicalShellRange_apply m n x 0 (m + n + 1) i j
  refine Q'.eqv_trans _
    (finSum (fun r => physicalSourceShell m n r x i j) (m + n + 1)) _
    (by simpa only [Nat.zero_add, rectProject] using hrange) ?_
  refine Q'.eqv_trans _
    (finSum (fun r => if r = i + j then x i j else 0) (m + n + 1)) _ ?_ ?_
  · apply RationalTail.finSum_eqv_congr_lt
    intro r hr
    have hshell := physicalSourceShell_apply m n r
      (Nat.lt_succ_iff.mp hr) x i j
    simpa only [dif_pos hi, dif_pos hj, eq_comm] using hshell
  · exact YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (x i j) (m + n + 1) (i + j) (by omega)

/-- Projection has literal zero support outside the physical rectangle. -/
theorem rectProject_zero_outside (m n : Nat) (x : BForm2) (i j : Nat)
    (hout : m < i ∨ n < j) : rectProject m n x i j ≈ 0 := by
  have hrange := physicalShellRange_apply m n x 0 (m + n + 1) i j
  refine Q'.eqv_trans _
    (finSum (fun r => physicalSourceShell m n r x i j) (m + n + 1)) _
    (by simpa only [Nat.zero_add, rectProject] using hrange) ?_
  apply YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_zero_on
  intro r hr
  have hshell := physicalSourceShell_apply m n r
    (Nat.lt_succ_iff.mp hr) x i j
  rcases hout with hi | hj
  · simpa only [dif_neg (by omega : ¬ i ≤ m)] using hshell
  · by_cases hi : i ≤ m
    · simpa only [dif_pos hi, dif_neg (by omega : ¬ j ≤ n)] using hshell
    · simpa only [dif_neg hi] using hshell

end YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection

#print axioms YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection.shellSourcePrefix_apply
#print axioms YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection.physicalSourceShell_apply
#print axioms YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection.rectProject_apply_physical
#print axioms YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection.rectProject_zero_outside
