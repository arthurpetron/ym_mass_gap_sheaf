/-
# Monotonicity of the finite-cutoff fused correlation quotient

For `A_N = adjCorr w N` and `D_N = coordNormSq w N`, this module proves the
division-free quotient monotonicity

    A_N D_{N+1} <= A_{N+1} D_N

for `0 < w <= 1`.  The mechanism is the shifted PF2 injection

    c_a c_{N+1} <= c_{a+1} c_N       (a < N),

obtained from the spread log-concavity theorem `coeffW_step`.  After multiplying
by `c_{a+1}` and summing, every numerator term injects into the next diagonal
square; the vacuum square remains unused.

Iteration gives a concrete finite-tail comparison between any two cutoffs
`N` and `N+k`.  This is the finite statement needed before any constructive
passage to an infinite theta quotient; no infinite-limit hypothesis or carrier
is introduced here.
-/

import YMGap.Continuum.AllWindowCorrDirichlet
import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.CutoffCorrelationMonotone

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.FusionCoreStepRoundE

local infix:50 " ≈ " => Q'.eqv

/-- Bottom peel for `fsum`, kept local to avoid importing unrelated analytic
machinery. -/
theorem fsum_peel_local (f : Nat → Q') : ∀ n,
    (fsum f (n + 1)).eqv (f 0 + fsum (fun i => f (i + 1)) n)
  | 0 => by
      show ((0 : Q') + f 0).eqv (f 0 + 0)
      exact Q'.eqv_trans _ _ _ (QPoly.q_zero_add_eqv _) (Q'.eqv_symm (QPoly.q_add_zero_eqv _))
  | n + 1 => by
      show (fsum f (n + 1) + f (n + 1)).eqv
        (f 0 + (fsum (fun i => f (i + 1)) n + f (n + 1)))
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (f (n + 1)) (fsum_peel_local f n)) ?_
      exact Q'.add_assoc_eqv (f 0) (fsum (fun i => f (i + 1)) n) (f (n + 1))

/-- The diagonal norm is strictly positive because it contains `c_0^2=1`. -/
theorem coordNormSq_pos {w : Q'} (hw0 : (0 : Q') ≤ w) (N : Nat) :
    (0 : Q') < coordNormSq w N := by
  let S := fsum (fun i => coeffW w (i + 1) * coeffW w (i + 1)) N
  have hS : (0 : Q') ≤ S := fsum_nonneg (fun i =>
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) (coeffW_nonneg hw0 _)) N
  have hpeel : (coordNormSq w N).eqv
      (coeffW w 0 * coeffW w 0 + S) := by
    unfold coordNormSq S
    exact fsum_peel_local (fun i => coeffW w i * coeffW w i) N
  have h1 : (1 : Q') ≤ coeffW w 0 * coeffW w 0 + S := by
    rw [coeffW_zero]
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv 1))) ?_
    exact Q'.add_le_self_of_nonneg 1 S hS
  exact q_lt_of_lt_of_le (by decide : (0 : Q') < (1 : Q'))
    (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.eqv_symm hpeel)))

/-- Shifted PF2 injection from spread log-concavity. -/
theorem shifted_ratio_injection {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) {a N : Nat} (ha : a < N) :
    coeffW w a * coeffW w (N + 1) ≤
      coeffW w (a + 1) * coeffW w N := by
  have hs := coeffW_step hw0 hw1 hwp a (N - a - 1)
  have hi1 : a + (N - a - 1) + 2 = N + 1 := by omega
  have hi2 : a + (N - a - 1) + 1 = N := by omega
  rw [hi1, hi2] at hs
  exact hs

/-- Termwise shifted-square injection after multiplying PF2 by `c_{a+1}`. -/
theorem adjacent_tail_term_injection {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) {a N : Nat} (ha : a < N) :
    (coeffW w a * coeffW w (a + 1)) * coeffW w (N + 1) ≤
      coeffW w N * (coeffW w (a + 1) * coeffW w (a + 1)) := by
  have hs := shifted_ratio_injection hw0 hw1 hwp ha
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ hs
    (coeffW_nonneg hw0 (a + 1))
  have hL : (coeffW w a * coeffW w (a + 1)) * coeffW w (N + 1) ≈
      (coeffW w a * coeffW w (N + 1)) * coeffW w (a + 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (coeffW w a) (coeffW w (a + 1)) (coeffW w (N + 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w a) _ _
        (Q'.mul_comm_eqv (coeffW w (a + 1)) (coeffW w (N + 1)))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (coeffW w a) (coeffW w (N + 1)) (coeffW w (a + 1)))
  have hR : (coeffW w (a + 1) * coeffW w N) * coeffW w (a + 1) ≈
      coeffW w N * (coeffW w (a + 1) * coeffW w (a + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (coeffW w (a + 1))
        (Q'.mul_comm_eqv (coeffW w (a + 1)) (coeffW w N))) ?_
    exact Q'.mul_assoc_eqv (coeffW w N) (coeffW w (a + 1)) (coeffW w (a + 1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hR))

/-- Summed injection `A_N c_{N+1} <= c_N D_N`. -/
theorem adjCorr_mul_terminal_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) (N : Nat) :
    adjCorr w N * coeffW w (N + 1) ≤
      coeffW w N * coordNormSq w N := by
  let T := fsum (fun a => coeffW w (a + 1) * coeffW w (a + 1)) N
  have hsum : fsum (fun a =>
        (coeffW w a * coeffW w (a + 1)) * coeffW w (N + 1)) N ≤
      fsum (fun a => coeffW w N *
        (coeffW w (a + 1) * coeffW w (a + 1))) N :=
    fsum_mono_lt N (fun a ha => adjacent_tail_term_injection hw0 hw1 hwp ha)
  have hL : (adjCorr w N * coeffW w (N + 1)).eqv
      (fsum (fun a => (coeffW w a * coeffW w (a + 1)) * coeffW w (N + 1)) N) :=
    fsum_mul_const (fun a => coeffW w a * coeffW w (a + 1)) (coeffW w (N + 1)) N
  have hR : (coeffW w N * T).eqv
      (fsum (fun a => coeffW w N *
        (coeffW w (a + 1) * coeffW w (a + 1))) N) :=
    fsum_const_mul (coeffW w N)
      (fun a => coeffW w (a + 1) * coeffW w (a + 1)) N
  have hAT : adjCorr w N * coeffW w (N + 1) ≤ coeffW w N * T :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm hR)))
  have hpeel : (coordNormSq w N).eqv
      (coeffW w 0 * coeffW w 0 + T) := by
    unfold coordNormSq T
    exact fsum_peel_local (fun i => coeffW w i * coeffW w i) N
  have h0 : (0 : Q') ≤ coeffW w 0 * coeffW w 0 :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 0) (coeffW_nonneg hw0 0)
  have hTD : T ≤ coordNormSq w N := by
    have h := Q'.add_le_self_of_nonneg T (coeffW w 0 * coeffW w 0) h0
    refine Q'.le_trans' _ _ _ h ?_
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv T (coeffW w 0 * coeffW w 0))
        (Q'.eqv_symm hpeel))
  have hx : (0 : Q') ≤ coeffW w N := coeffW_nonneg hw0 N
  exact Q'.le_trans' _ _ _ hAT
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hTD hx)

/-- **Exact one-step cutoff quotient monotonicity, division-free.** -/
theorem cutoff_quotient_mono_step {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) (N : Nat) :
    adjCorr w N * coordNormSq w (N + 1) ≤
      adjCorr w (N + 1) * coordNormSq w N := by
  let A := adjCorr w N
  let D := coordNormSq w N
  let x := coeffW w N
  let y := coeffW w (N + 1)
  have hAy : A * y ≤ x * D := adjCorr_mul_terminal_le hw0 hw1 hwp N
  have hy : (0 : Q') ≤ y := coeffW_nonneg hw0 (N + 1)
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ hAy hy
  have hquad : A * (y * y) ≤ (x * y) * D := by
    have hL : A * (y * y) ≈ (A * y) * y := Q'.eqv_symm (Q'.mul_assoc_eqv A y y)
    have hR : (x * D) * y ≈ (x * y) * D := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv x D y) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left x _ _ (Q'.mul_comm_eqv D y)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv x y D)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
      (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hR))
  have hadd := Q'.add_le_add_left (A * D) _ _ hquad
  have hDs := coordNormSq_succ w N
  have hAs := adjCorr_succ w N
  have hL : adjCorr w N * coordNormSq w (N + 1) ≈
      A * D + A * (y * y) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left A _ _ hDs) ?_
    exact Q'.mul_add_eqv A D (y * y)
  have hR : adjCorr w (N + 1) * coordNormSq w N ≈
      A * D + (x * y) * D := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ D hAs) ?_
    exact Q'.add_mul_eqv A (x * y) D
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.eqv_symm hR)))

/-- **Finite theta-tail comparison.** Every later cutoff has quotient at least
that of the starting cutoff, expressed without division. -/
theorem finite_cutoff_tail_compare {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) (N : Nat) : ∀ k : Nat,
    adjCorr w N * coordNormSq w (N + k) ≤
      adjCorr w (N + k) * coordNormSq w N
  | 0 => Q'.le_refl' _
  | k + 1 => by
      let M := N + k
      have ih := finite_cutoff_tail_compare hw0 hw1 hwp N k
      have hs := cutoff_quotient_mono_step hw0 hw1 hwp M
      have hDM : (0 : Q') < coordNormSq w M := coordNormSq_pos hw0 M
      have hnext : (0 : Q') ≤ coordNormSq w (M + 1) :=
        coordNormSq_nonneg hw0 (M + 1)
      have hDN : (0 : Q') ≤ coordNormSq w N := coordNormSq_nonneg hw0 N
      have h1 := Q'.mul_le_mul_of_nonneg_right _ _ _ ih hnext
      have h2 := Q'.mul_le_mul_of_nonneg_left _ _ (coordNormSq w N) hs hDN
      have he1 : coordNormSq w M *
          (adjCorr w N * coordNormSq w (M + 1)) ≈
        (adjCorr w N * coordNormSq w M) * coordNormSq w (M + 1) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (coordNormSq w M) (adjCorr w N)
            (coordNormSq w (M + 1)))) ?_
        exact Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv (coordNormSq w M) (adjCorr w N))
      have he2 : (adjCorr w M * coordNormSq w N) * coordNormSq w (M + 1) ≈
          coordNormSq w N * (adjCorr w M * coordNormSq w (M + 1)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (coordNormSq w (M + 1))
            (Q'.mul_comm_eqv (adjCorr w M) (coordNormSq w N))) ?_
        exact Q'.mul_assoc_eqv (coordNormSq w N) (adjCorr w M)
          (coordNormSq w (M + 1))
      have he3 : coordNormSq w N *
          (adjCorr w (M + 1) * coordNormSq w M) ≈
        coordNormSq w M *
          (adjCorr w (M + 1) * coordNormSq w N) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (coordNormSq w N)
            (adjCorr w (M + 1)) (coordNormSq w M))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) ?_
        exact Q'.mul_eqv_congr_left (coordNormSq w M) _ _
          (Q'.mul_comm_eqv (coordNormSq w N) (adjCorr w (M + 1)))
      have hchain : coordNormSq w M *
          (adjCorr w N * coordNormSq w (M + 1)) ≤
        coordNormSq w M *
          (adjCorr w (M + 1) * coordNormSq w N) := by
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he1) ?_
        refine Q'.le_trans' _ _ _ h1 ?_
        refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he2) ?_
        refine Q'.le_trans' _ _ _ h2 ?_
        exact Q'.le_of_eqv he3
      have hc := Q'.le_of_mul_le_mul_left hchain hDM
      simpa [M, Nat.add_assoc] using hc

end YMGap.Continuum.CutoffCorrelationMonotone

#print axioms YMGap.Continuum.CutoffCorrelationMonotone.shifted_ratio_injection
#print axioms YMGap.Continuum.CutoffCorrelationMonotone.adjCorr_mul_terminal_le
#print axioms YMGap.Continuum.CutoffCorrelationMonotone.cutoff_quotient_mono_step
#print axioms YMGap.Continuum.CutoffCorrelationMonotone.finite_cutoff_tail_compare
