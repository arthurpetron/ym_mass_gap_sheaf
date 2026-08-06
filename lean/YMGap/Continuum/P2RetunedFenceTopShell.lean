/-
Track 11.7-fusion / R2o -- exact top Clebsch shell for the retuned Turan family.

At cutoff `N`, the last three two-fold fusion coefficients have only one,
two, and four contributing pairs.  This module derives those formulas from
the cutoff recurrence and the exact Clebsch support predicate.  They are the
finite-combinatorial input for discharging the canonical boundary Turan atom
`s = 2*N-2` uniformly in `N`.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFenceEdgeAllCutoffs
import YMGap.Continuum.BoxSumTailGeneral

namespace YMGap.Continuum.P2RetunedFenceTopShell

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BoxSumTailGeneral
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem fsum_collapse_bounded {g : Nat → Q'} {k n : Nat}
    (hk : k < n) (hz : ∀ i, i < n → i ≠ k → g i ≈ (0 : Q')) :
    fsum g n ≈ g k := by
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      show fsum g n + g n ≈ g k
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | hkn
      · have hlast : g n ≈ (0 : Q') :=
          hz n (Nat.lt_succ_self n) (fun h => by subst h; omega)
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (ih hkn ?_) hlast) ?_
        · intro i hi hne
          exact hz i (Nat.lt_succ_of_lt hi) hne
        · exact q_add_zero_eqv _
      · subst hkn
        have hpre : fsum g k ≈ (0 : Q') :=
          fsum_zero_below k
            (fun i hi => hz i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi))
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hpre) ?_
        exact q_zero_add_eqv _

private theorem zeroFsumTerm (x : Q') :
    (0 : Q') + 0 * x ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 (0 * x) 0 (Q'.zero_mul_eqv x)) ?_
  exact q_zero_add_eqv 0

private theorem fusionInd_top_diag (N : Nat) :
    fusionInd N N (2 * N) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_self, Nat.min_self]
  refine ⟨by omega, by omega, ?_⟩
  have he : N + N + 2 * N = 2 * (2 * N) := by omega
  rw [he, Nat.mul_comm 2 (2 * N), Nat.mul_mod_left]

private theorem fusionInd_top_odd_diag (N : Nat) (hN : 1 ≤ N) :
    fusionInd N N (2 * N - 1) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff N N (2 * N - 1)).mp hok with ⟨_, _, hp⟩
  omega

private theorem fusionInd_top_even_diag (N : Nat) (hN : 1 ≤ N) :
    fusionInd N N (2 * N - 2) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_self, Nat.min_self]
  refine ⟨by omega, by omega, ?_⟩
  have he : N + N + (2 * N - 2) = 2 * (2 * N - 1) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 1), Nat.mul_mod_left]

/-- The new-cutoff contribution to the top channel is only its diagonal. -/
theorem boxSumDelta_top (w : Q') (N : Nat) :
    boxSumDelta w N (2 * (N + 1)) ≈
      coeffW w (N + 1) * coeffW w (N + 1) := by
  unfold boxSumDelta
  have hleft :
      fsum (fun a => fusionInd a (N + 1) (2 * (N + 1)) *
        (coeffW w a * coeffW w (N + 1))) (N + 1) ≈ 0 :=
    fsum_zero_below (N + 1) (fun a ha => by
      have hz : fusionInd a (N + 1) (2 * (N + 1)) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff a (N + 1) (2 * (N + 1))).mp hok with
          ⟨_, hhi, _⟩
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _)
  have hright :
      fsum (fun b => fusionInd (N + 1) b (2 * (N + 1)) *
        (coeffW w (N + 1) * coeffW w b)) (N + 1) ≈ 0 :=
    fsum_zero_below (N + 1) (fun b hb => by
      have hz : fusionInd (N + 1) b (2 * (N + 1)) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff (N + 1) b (2 * (N + 1))).mp hok with
          ⟨_, hhi, _⟩
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _)
  rw [fusionInd_top_diag (N + 1)]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft
      (Q'.add_eqv_congr' hright (Q'.one_mul_eqv _))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 0 (0 + _) _ (q_zero_add_eqv _)) ?_
  exact q_zero_add_eqv _

/-- The top box coefficient has exactly one Clebsch pair. -/
theorem boxSum_top (w : Q') (N : Nat) :
    boxSum w N (2 * N) ≈ coeffW w N * coeffW w N := by
  cases N with
  | zero =>
      unfold boxSum
      simp only [fsum]
      rw [fusionInd_top_diag 0]
      have hinner :
          (0 : Q') + 1 * (coeffW w 0 * coeffW w 0) ≈
            coeffW w 0 * coeffW w 0 := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left 0 _ _ (Q'.one_mul_eqv _)) ?_
        exact q_zero_add_eqv _
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left 0 _ _ hinner) ?_
      exact q_zero_add_eqv _
  | succ K =>
      refine Q'.eqv_trans _ _ _ (boxSum_succ_decomp w K (2 * (K + 1))) ?_
      have hold : boxSum w K (2 * (K + 1)) ≈ 0 :=
        boxSum_tail w K (2 * (K + 1)) (by omega)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hold (boxSumDelta_top w K)) ?_
      exact q_zero_add_eqv _

/-- The penultimate channel receives the two orientations of `(N-1,N)`. -/
theorem boxSumDelta_top_odd (w : Q') (N : Nat) (hN : 1 ≤ N) :
    boxSumDelta w (N - 1) (2 * N - 1) ≈
      (coeffW w (N - 1) * coeffW w N) +
        (coeffW w (N - 1) * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft :
      fsum (fun a => fusionInd a N (2 * N - 1) *
        (coeffW w a * coeffW w N)) N ≈
        coeffW w (N - 1) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 1) (n := N) (by omega)
        (fun a ha hne => ?_)) ?_
    · have hz : fusionInd a N (2 * N - 1) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff a N (2 * N - 1)).mp hok with ⟨_, hhi, _⟩
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd (N - 1) N (2 * N - 1) = (1 : Q') := by
        unfold fusionInd
        rw [if_pos]
        rw [fusionOK_eq_true_iff]
        have hmax : Nat.max (N - 1) N = N := Nat.max_eq_right (by omega)
        have hmin : Nat.min (N - 1) N = N - 1 := Nat.min_eq_left (by omega)
        rw [hmax, hmin]
        refine ⟨by omega, by omega, ?_⟩
        have he : N - 1 + N + (2 * N - 1) = 2 * (2 * N - 1) := by omega
        rw [he, Nat.mul_comm 2 (2 * N - 1), Nat.mul_mod_left]
      rw [hone]
      exact Q'.one_mul_eqv _
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 1) *
        (coeffW w N * coeffW w b)) N ≈
        coeffW w (N - 1) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 1) (n := N) (by omega)
        (fun b hb hne => ?_)) ?_
    · have hz : fusionInd N b (2 * N - 1) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff N b (2 * N - 1)).mp hok with ⟨_, hhi, _⟩
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd N (N - 1) (2 * N - 1) = (1 : Q') := by
        unfold fusionInd
        rw [if_pos]
        rw [fusionOK_eq_true_iff]
        have hmax : Nat.max N (N - 1) = N := Nat.max_eq_left (by omega)
        have hmin : Nat.min N (N - 1) = N - 1 := Nat.min_eq_right (by omega)
        rw [hmax, hmin]
        refine ⟨by omega, by omega, ?_⟩
        have he : N + (N - 1) + (2 * N - 1) = 2 * (2 * N - 1) := by omega
        rw [he, Nat.mul_comm 2 (2 * N - 1), Nat.mul_mod_left]
      rw [hone]
      refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
      exact Q'.mul_comm_eqv _ _
  rw [fusionInd_top_odd_diag N hN]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft
      (Q'.add_eqv_congr' hright (Q'.zero_mul_eqv _))) ?_
  exact Q'.add_eqv_congr_left _ _ _ (q_add_zero_eqv _)

/-- The penultimate box coefficient has exactly two ordered pairs. -/
theorem boxSum_top_odd (w : Q') (N : Nat) (hN : 1 ≤ N) :
    boxSum w N (2 * N - 1) ≈
      (coeffW w (N - 1) * coeffW w N) +
        (coeffW w (N - 1) * coeffW w N) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 1)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold : boxSum w (N - 1) (2 * N - 1) ≈ 0 :=
    boxSum_tail w (N - 1) (2 * N - 1) (by omega)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hold (boxSumDelta_top_odd w N hN)) ?_
  exact q_zero_add_eqv _

/-- The last even-shell increment contains the two orientations of
`(N-2,N)` and the new diagonal `(N,N)`. -/
theorem boxSumDelta_top_even (w : Q') (N : Nat) (hN : 2 ≤ N) :
    boxSumDelta w (N - 1) (2 * N - 2) ≈
      (coeffW w (N - 2) * coeffW w N) +
        ((coeffW w (N - 2) * coeffW w N) +
          coeffW w N * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft :
      fsum (fun a => fusionInd a N (2 * N - 2) *
        (coeffW w a * coeffW w N)) N ≈
        coeffW w (N - 2) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 2) (n := N) (by omega)
        (fun a ha hne => ?_)) ?_
    · have hz : fusionInd a N (2 * N - 2) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff a N (2 * N - 2)).mp hok with
          ⟨_, hhi, hp⟩
        have haeq : a = N - 1 := by omega
        subst a
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd (N - 2) N (2 * N - 2) = (1 : Q') := by
        unfold fusionInd
        rw [if_pos]
        rw [fusionOK_eq_true_iff]
        have hmax : Nat.max (N - 2) N = N := Nat.max_eq_right (by omega)
        have hmin : Nat.min (N - 2) N = N - 2 := Nat.min_eq_left (by omega)
        rw [hmax, hmin]
        refine ⟨by omega, by omega, ?_⟩
        have he : N - 2 + N + (2 * N - 2) = 2 * (2 * N - 2) := by omega
        rw [he, Nat.mul_comm 2 (2 * N - 2), Nat.mul_mod_left]
      rw [hone]
      exact Q'.one_mul_eqv _
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 2) *
        (coeffW w N * coeffW w b)) N ≈
        coeffW w (N - 2) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 2) (n := N) (by omega)
        (fun b hb hne => ?_)) ?_
    · have hz : fusionInd N b (2 * N - 2) = (0 : Q') := by
        unfold fusionInd
        rw [if_neg]
        intro hok
        rcases (fusionOK_eq_true_iff N b (2 * N - 2)).mp hok with
          ⟨_, hhi, hp⟩
        have hbeq : b = N - 1 := by omega
        subst b
        omega
      rw [hz]
      exact Q'.zero_mul_eqv _
    · have hone : fusionInd N (N - 2) (2 * N - 2) = (1 : Q') := by
        unfold fusionInd
        rw [if_pos]
        rw [fusionOK_eq_true_iff]
        have hmax : Nat.max N (N - 2) = N := Nat.max_eq_left (by omega)
        have hmin : Nat.min N (N - 2) = N - 2 := Nat.min_eq_right (by omega)
        rw [hmax, hmin]
        refine ⟨by omega, by omega, ?_⟩
        have he : N + (N - 2) + (2 * N - 2) = 2 * (2 * N - 2) := by omega
        rw [he, Nat.mul_comm 2 (2 * N - 2), Nat.mul_mod_left]
      rw [hone]
      refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
      exact Q'.mul_comm_eqv _ _
  rw [fusionInd_top_even_diag N (by omega)]
  exact Q'.add_eqv_congr' hleft
    (Q'.add_eqv_congr' hright (Q'.one_mul_eqv _))

/-- The last even box coefficient has exactly four contributing pairs. -/
theorem boxSum_top_even (w : Q') (N : Nat) (hN : 2 ≤ N) :
    boxSum w N (2 * N - 2) ≈
      (coeffW w (N - 1) * coeffW w (N - 1)) +
        ((coeffW w (N - 2) * coeffW w N) +
          ((coeffW w (N - 2) * coeffW w N) +
            coeffW w N * coeffW w N)) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 2)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top w (N - 1)
  rw [show 2 * (N - 1) = 2 * N - 2 by omega] at hold
  exact Q'.add_eqv_congr' hold (boxSumDelta_top_even w N hN)

end YMGap.Continuum.P2RetunedFenceTopShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSumDelta_top
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSum_top
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSumDelta_top_odd
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSum_top_odd
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSumDelta_top_even
#print axioms YMGap.Continuum.P2RetunedFenceTopShell.boxSum_top_even
