/-
# Actual global transvectant coordinates

After zero-outside physical projection, a raw transvectant coordinate receives
exactly one total-weight shell.  Cross-shell terms vanish because a monomial
tensor of total weight `t` can contribute only to output slot `s` when
`s+k=t`.  Thus the actual dependent coordinates coincide with the global
Hahn coordinates and reconstruct the complete physical source rectangle.
-/

import YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection

namespace YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates

set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnCumulativeTransform
open YMGap.Continuum.SU2GeneralHahnCentralShellBasis
open YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination
open YMGap.Continuum.SU2GeneralHahnAllShellRecursiveSolver
open YMGap.Continuum.SU2GeneralHahnAllShellCoordinateEquivalence
open YMGap.Continuum.SU2GeneralHahnGlobalSourceReconstruction
open YMGap.Continuum.SU2GeneralHahnPhysicalRectangleProjection

local infix:50 " ≈ " => Q'.eqv

/-- A shell prefix is zero at every output coordinate whose total weight does
not match `s+k`, with no assumption `k≤t`. -/
theorem shellSourcePrefix_transvect_offshell (m n t k s : Nat) :
    ∀ N : Nat, ∀ col : Nat → Nat, ∀ x : Nat → Q',
      (∀ q, q < N → col q ≤ t) → ¬ s + k = t →
      transvect m n k (shellSourcePrefix t N col x) s ≈ 0
  | 0, col, x, hcol, hne => by
      have hscale := transvect_scale m n k 0 (shellBasis t 0) s
      exact Q'.eqv_trans _ _ _ hscale (Q'.zero_mul_eqv _)
  | N + 1, col, x, hcol, hne => by
      have hhead : col 0 ≤ t := hcol 0 (by omega)
      have htail : ∀ q, q < N → col (q + 1) ≤ t := by
        intro q hq
        exact hcol (q + 1) (by omega)
      have hadd := transvect_add m n k
        (bscale (x 0) (shellBasis t (col 0)))
        (shellSourcePrefix t N (fun q => col (q + 1))
          (fun q => x (q + 1))) s
      have hscale := transvect_scale m n k (x 0)
        (shellBasis t (col 0)) s
      have hformula := transvect_monomial_factorial_formula
        m n k (col 0) (t - col 0) s
      have htotal : col 0 + (t - col 0) = t := Nat.add_sub_of_le hhead
      have hcond : ¬ s + k = col 0 + (t - col 0) := by
        rw [htotal]
        exact hne
      have hbasis : transvect m n k (shellBasis t (col 0)) s ≈ 0 := by
        simpa only [shellBasis, if_neg hcond] using hformula
      have hrest := shellSourcePrefix_transvect_offshell m n t k s N
        (fun q => col (q + 1)) (fun q => x (q + 1)) htail hne
      simp only [shellSourcePrefix]
      refine Q'.eqv_trans _
        (transvect m n k (bscale (x 0) (shellBasis t (col 0))) s +
          transvect m n k
            (shellSourcePrefix t N (fun q => col (q + 1))
              (fun q => x (q + 1))) s) _ hadd ?_
      refine Q'.eqv_trans _ (x 0 * 0 + 0) _
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ (x 0 * transvect m n k
              (shellBasis t (col 0)) s) _ hscale
            (Q'.mul_eqv_congr_left _ _ _ hbasis)) hrest) ?_
      refine Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _)) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- One physical source shell contributes to exactly its matching dependent
channel shell. -/
theorem physicalSourceShell_transvect_channel (m n u : Nat)
    (hu : u ≤ m + n) (x : BForm2) (q : PhysicalCGChannel m n) :
    transvect m n q.k (physicalSourceShell m n u x) q.s ≈
      (if u = q.shell then globalHahnCoordinates m n x q else 0) := by
  by_cases hut : u = q.shell
  · rw [if_pos hut]
    subst u
    have hmin := Nat.le_min.mp q.k_le
    have hchannel : ChannelActive m n q.shell q.k := by
      unfold ChannelActive PhysicalCGChannel.shell
      exact ⟨hmin.1, hmin.2, by omega, by
        have h2k : 2 * q.k ≤ m + n := by omega
        have hs2k : q.s + 2 * q.k ≤ m + n :=
          Nat.add_le_of_le_sub h2k q.s_le
        omega⟩
    have hk := channelActive_index_complete m n q.shell q.k
      q.shell_le hchannel
    have hcols : ∀ a, a < shellWidth m n q.shell + 1 →
        shellLo n q.shell + a ≤ q.shell := by
      intro a ha
      exact (sourceActive_of_index m n q.shell a q.shell_le
        (Nat.lt_succ_iff.mp ha)).1
    have hform := shellSourcePrefix_transvect_form m n q.shell q.k
      (shellWidth m n q.shell + 1) (fun a => shellLo n q.shell + a)
      (sourceShellCoordinates n q.shell x) hcols hchannel.2.2.1 q.s
    have hs : q.shell - q.k = q.s := by
      unfold PhysicalCGChannel.shell
      omega
    refine Q'.eqv_trans _
      (physicalHahnAction m n q.shell
        (sourceShellCoordinates n q.shell x) q.k *
          mono (q.shell - q.k) q.s) _ ?_ ?_
    · simpa only [physicalSourceShell, physicalHahnAction,
        physicalHahnMatrix] using hform
    · rw [hs]
      simp only [mono, if_pos]
      refine Q'.eqv_trans _
        (physicalHahnAction m n q.shell
          (sourceShellCoordinates n q.shell x) q.k) _
        (Q'.mul_one_eqv _) ?_
      exact Q'.eqv_refl _
  · rw [if_neg hut]
    have hcols : ∀ a, a < shellWidth m n u + 1 →
        shellLo n u + a ≤ u := by
      intro a ha
      exact (sourceActive_of_index m n u a hu
        (Nat.lt_succ_iff.mp ha)).1
    apply shellSourcePrefix_transvect_offshell m n u q.k q.s
      (shellWidth m n u + 1) (fun a => shellLo n u + a)
      (sourceShellCoordinates n u x) hcols
    intro heq
    apply hut
    exact heq.symm

private theorem transvect_zero_tensor (m n k s : Nat) :
    transvect m n k (fun _ _ => 0) s ≈ 0 := by
  have hinput : BForm2Eqv (fun _ _ => 0) (bscale 0 (shellBasis 0 0)) := by
    intro i j
    exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  have hcongr := transvect_congr m n k hinput s
  have hscale := transvect_scale m n k 0 (shellBasis 0 0) s
  exact Q'.eqv_trans _ _ _ hcongr
    (Q'.eqv_trans _ _ _ hscale (Q'.zero_mul_eqv _))

/-- Transvecting a finite shell range is the finite sum of transvecting each
shell. -/
theorem physicalShellRange_transvect (m n : Nat) (x : BForm2)
    (start N k s : Nat) :
    transvect m n k (physicalShellRange m n x start N) s ≈
      finSum (fun r =>
        transvect m n k (physicalSourceShell m n (start + r) x) s) N := by
  induction N generalizing start with
  | zero => exact transvect_zero_tensor m n k s
  | succ N ih =>
      have hadd := transvect_add m n k
        (physicalSourceShell m n start x)
        (physicalShellRange m n x (start + 1) N) s
      simp only [physicalShellRange]
      refine Q'.eqv_trans _
        (transvect m n k (physicalSourceShell m n start x) s +
          transvect m n k (physicalShellRange m n x (start + 1) N) s) _
        hadd ?_
      refine Q'.eqv_trans _
        (transvect m n k (physicalSourceShell m n start x) s +
          finSum (fun r => transvect m n k
            (physicalSourceShell m n (start + 1 + r) x) s) N) _
        (Q'.add_eqv_congr_left _ _ _ (ih (start + 1))) ?_
      have hpeel := RationalTail.finSum_peel_left
        (fun r => transvect m n k
          (physicalSourceShell m n (start + r) x) s) N
      have hshift :
          finSum (fun r => transvect m n k
            (physicalSourceShell m n (start + (r + 1)) x) s) N ≈
          finSum (fun r => transvect m n k
            (physicalSourceShell m n (start + 1 + r) x) s) N := by
        apply RationalTail.finSum_eqv_congr_lt
        intro r hr
        rw [show start + (r + 1) = start + 1 + r by omega]
        exact Q'.eqv_refl _
      refine Q'.eqv_trans _
        (transvect m n k (physicalSourceShell m n start x) s +
          finSum (fun r => transvect m n k
            (physicalSourceShell m n (start + (r + 1)) x) s) N) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hshift)) ?_
      exact Q'.eqv_symm (by simpa only [Nat.add_zero] using hpeel)

/-- Actual dependent CG coordinates, evaluated only after physical support
projection. -/
def globalTransvectCoordinates (m n : Nat) (x : BForm2) :
    PhysicalCGChannel m n → Q' :=
  fun q => transvect m n q.k (rectProject m n x) q.s

/-- **Actual-coordinate bridge.**  Projected transvectant coordinates are
exactly the assembled physical Hahn coordinates. -/
theorem globalTransvectCoordinates_eq_hahn (m n : Nat) (x : BForm2)
    (q : PhysicalCGChannel m n) :
    globalTransvectCoordinates m n x q ≈ globalHahnCoordinates m n x q := by
  have hrange := physicalShellRange_transvect m n x 0 (m + n + 1) q.k q.s
  refine Q'.eqv_trans _
    (finSum (fun r => transvect m n q.k
      (physicalSourceShell m n r x) q.s) (m + n + 1)) _
    (by simpa only [globalTransvectCoordinates, rectProject, Nat.zero_add] using hrange) ?_
  refine Q'.eqv_trans _
    (finSum (fun r => if r = q.shell then globalHahnCoordinates m n x q else 0)
      (m + n + 1)) _ ?_ ?_
  · apply RationalTail.finSum_eqv_congr_lt
    intro r hr
    exact physicalSourceShell_transvect_channel m n r
      (Nat.lt_succ_iff.mp hr) x q
  · exact YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
      (globalHahnCoordinates m n x q) (m + n + 1) q.shell
      (Nat.lt_succ_iff.mpr q.shell_le)

/-- Global reconstruction respects pointwise equivalence of dependent channel
data on every physical source coefficient. -/
theorem globalHahnReconstruct_congr (m n : Nat)
    (c d : PhysicalCGChannel m n → Q')
    (hcd : ∀ q, c q ≈ d q) (i j : Nat)
    (hi : i ≤ m) (hj : j ≤ n) :
    globalHahnReconstruct m n c i j ≈ globalHahnReconstruct m n d i j := by
  let t := i + j
  have ht : t ≤ m + n := Nat.add_le_add hi hj
  let yc := shellDataFromGlobal m n t ht c
  let yd := shellDataFromGlobal m n t ht d
  have hy : ∀ k, k < shellWidth m n t + 1 → yc k ≈ yd k := by
    intro k hk
    unfold yc yd shellDataFromGlobal
    rw [dif_pos hk, dif_pos hk]
    exact hcd _
  have hsolve : ∀ a, a < shellWidth m n t + 1 →
      allShellHahnSolve m n t ht yc a ≈
        allShellHahnSolve m n t ht yd a := by
    apply physicalHahnAction_injective m n t ht
    intro k hk
    have hc := allShellHahnSolve_rightInverse m n t ht yc k hk
    have hd := allShellHahnSolve_rightInverse m n t ht yd k hk
    exact Q'.eqv_trans _ _ _ hc
      (Q'.eqv_trans _ _ _ (hy k hk) (Q'.eqv_symm hd))
  unfold globalHahnReconstruct
  simp only [dif_pos hi, dif_pos hj]
  change allShellHahnSolve m n t ht yc (i - shellLo n t) ≈
    allShellHahnSolve m n t ht yd (i - shellLo n t)
  exact hsolve (i - shellLo n t) (by
    have hactive : SourceActive m n t i := by
      unfold SourceActive t
      exact ⟨by omega, hi, by omega⟩
    exact Nat.lt_succ_iff.mpr
      (sourceActive_index_complete m n t i hactive).1)

/-- **Actual all-label CG reconstruction.**  The complete dependent family
`transvect m n k (rectProject x) s` reconstructs every physical source
coefficient. -/
theorem globalHahnReconstruct_transvectCoordinates (m n : Nat) (x : BForm2)
    (i j : Nat) (hi : i ≤ m) (hj : j ≤ n) :
    globalHahnReconstruct m n (globalTransvectCoordinates m n x) i j ≈ x i j := by
  exact Q'.eqv_trans _ _ _
    (globalHahnReconstruct_congr m n
      (globalTransvectCoordinates m n x) (globalHahnCoordinates m n x)
      (globalTransvectCoordinates_eq_hahn m n x) i j hi hj)
    (globalHahnReconstruct_coordinates m n x i j hi hj)

end YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates

#print axioms YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates.shellSourcePrefix_transvect_offshell
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates.physicalSourceShell_transvect_channel
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates.globalTransvectCoordinates_eq_hahn
#print axioms YMGap.Continuum.SU2GeneralHahnGlobalTransvectantCoordinates.globalHahnReconstruct_transvectCoordinates
