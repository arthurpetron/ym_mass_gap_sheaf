/-
Track 11.7-fusion / R2p -- the next exact boundary shell.

At channel `2*N-3`, the old cutoff contributes its two top-odd pairs and
the newly appended row/column contributes exactly four more pairs.  This
file derives the resulting six-pair formula from the cutoff recurrence.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFenceTopShell

namespace YMGap.Continuum.P2RetunedFenceSecondShell

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.P2RetunedFenceTopShell
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

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

private theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd
  rw [fusionOK_symm_ab]

private theorem fusionInd_top_three_low (N : Nat) (hN : 3 ≤ N) :
    fusionInd (N - 3) N (2 * N - 3) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 3) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 3) N = N - 3 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 3 + N + (2 * N - 3) = 2 * (2 * N - 3) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 3), Nat.mul_mod_left]

private theorem fusionInd_top_three_high (N : Nat) (hN : 3 ≤ N) :
    fusionInd (N - 1) N (2 * N - 3) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 1) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 1) N = N - 1 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 1 + N + (2 * N - 3) = 2 * (2 * N - 2) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 2), Nat.mul_mod_left]

private theorem fusionInd_top_three_diag_zero (N : Nat) (hN : 3 ≤ N) :
    fusionInd N N (2 * N - 3) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff N N (2 * N - 3)).mp hok with ⟨_, _, hp⟩
  omega

private theorem fusionInd_top_three_zero_below
    (N a : Nat) (hN : 3 ≤ N) (ha : a < N - 1) (hne : a ≠ N - 3) :
    fusionInd a N (2 * N - 3) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff a N (2 * N - 3)).mp hok with ⟨_, hhi, hp⟩
  have halow : N - 3 ≤ a := by omega
  have haeq : a = N - 2 := by omega
  subst a
  omega

private theorem topThreeRow (w : Q') (N : Nat) (hN : 3 ≤ N) :
    fsum (fun a => fusionInd a N (2 * N - 3) *
      (coeffW w a * coeffW w N)) N ≈
      coeffW w (N - 3) * coeffW w N +
        coeffW w (N - 1) * coeffW w N := by
  have hsplit :
      fsum (fun a => fusionInd a N (2 * N - 3) *
        (coeffW w a * coeffW w N)) N =
      fsum (fun a => fusionInd a N (2 * N - 3) *
        (coeffW w a * coeffW w N)) (N - 1) +
      fusionInd (N - 1) N (2 * N - 3) *
        (coeffW w (N - 1) * coeffW w N) := by
    rw [show N = (N - 1) + 1 by omega]
    rfl
  rw [hsplit]
  have hpre :
      fsum (fun a => fusionInd a N (2 * N - 3) *
        (coeffW w a * coeffW w N)) (N - 1) ≈
        coeffW w (N - 3) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded
        (k := N - 3) (n := N - 1) (by omega) (fun a ha hne => ?_)) ?_
    · rw [fusionInd_top_three_zero_below N a hN ha hne]
      exact Q'.zero_mul_eqv _
    · rw [fusionInd_top_three_low N hN]
      exact Q'.one_mul_eqv _
  refine Q'.add_eqv_congr' hpre ?_
  rw [fusionInd_top_three_high N hN]
  exact Q'.one_mul_eqv _

/-- The appended cutoff contributes the four orientations with deficits
one and three; the new diagonal is parity-forbidden. -/
theorem boxSumDelta_top_three (w : Q') (N : Nat) (hN : 3 ≤ N) :
    boxSumDelta w (N - 1) (2 * N - 3) ≈
      (coeffW w (N - 3) * coeffW w N +
        coeffW w (N - 1) * coeffW w N) +
      (coeffW w (N - 3) * coeffW w N +
        coeffW w (N - 1) * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft := topThreeRow w N hN
  have hright0 := topThreeRow w N hN
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 3) *
        (coeffW w N * coeffW w b)) N ≈
        coeffW w (N - 3) * coeffW w N +
          coeffW w (N - 1) * coeffW w N := by
    refine Q'.eqv_trans _ _ _ ?_ hright0
    apply CubeRatioBounds.fsum_eqv_congr
    intro b
    rw [fusionInd_comm N b (2 * N - 3)]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  rw [fusionInd_top_three_diag_zero N hN]
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft
      (Q'.add_eqv_congr' hright (Q'.zero_mul_eqv _))) ?_
  exact Q'.add_eqv_congr_left _ _ _ (q_add_zero_eqv _)

/-- Channel `2*N-3` has exactly six Clebsch pairs: the two old top-odd
pairs plus four new row/column pairs. -/
theorem boxSum_top_three (w : Q') (N : Nat) (hN : 3 ≤ N) :
    boxSum w N (2 * N - 3) ≈
      ((coeffW w (N - 2) * coeffW w (N - 1)) +
        (coeffW w (N - 2) * coeffW w (N - 1))) +
      ((coeffW w (N - 3) * coeffW w N +
        coeffW w (N - 1) * coeffW w N) +
       (coeffW w (N - 3) * coeffW w N +
        coeffW w (N - 1) * coeffW w N)) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 3)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top_odd w (N - 1) (by omega)
  rw [show 2 * (N - 1) - 1 = 2 * N - 3 by omega] at hold
  exact Q'.add_eqv_congr' hold (boxSumDelta_top_three w N hN)

/-! ## The next physical strong-Turan atom in scalar coordinates -/

def secondShellLow (A X B C : Q') : Q' :=
  ((X * B) + (X * B)) +
    ((A * C + B * C) + (A * C + B * C))

def secondShellMid (X B C : Q') : Q' :=
  B * B + (X * C + (X * C + C * C))

def secondShellHigh (B C : Q') : Q' := (B * C) + (B * C)

/-- Sum-free statement of the `s=2*N-3` atom.  The remaining proof is now a
four-coefficient heat-ratio inequality; no Clebsch enumeration remains. -/
def SecondShellScalarFence (N : Nat) : Prop :=
  let A := coeffW fenceW (N - 3)
  let X := coeffW fenceW (N - 2)
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  (dimQ (2 * N - 2) * secondShellLow A X B C) *
      (dimQ (2 * N - 2) * secondShellHigh B C) ≤
    (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
        (dimQ (2 * N - 1) * secondShellMid X B C)) *
      (dimQ (2 * N - 3) * secondShellMid X B C)

/-- Exact shell formulas compile the four-coefficient scalar fence back to
the physical weighted-box atom. -/
theorem fenceSecondShellTuran_of_scalar (N : Nat) (hN : 3 ≤ N)
    (hscalar : SecondShellScalarFence N) :
    (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 3)) *
        (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 1)) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (2 * N - 1) * boxSum fenceW N (2 * N - 2))) *
        (dimQ (2 * N - 3) * boxSum fenceW N (2 * N - 2)) := by
  let A := coeffW fenceW (N - 3)
  let X := coeffW fenceW (N - 2)
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  have hlow : boxSum fenceW N (2 * N - 3) ≈ secondShellLow A X B C := by
    simpa only [A, X, B, C, secondShellLow] using
      (boxSum_top_three fenceW N hN)
  have hmid : boxSum fenceW N (2 * N - 2) ≈ secondShellMid X B C := by
    simpa only [X, B, C, secondShellMid] using
      (boxSum_top_even fenceW N (by omega))
  have hhigh : boxSum fenceW N (2 * N - 1) ≈ secondShellHigh B C := by
    simpa only [B, C, secondShellHigh] using
      (boxSum_top_odd fenceW N (by omega))
  have hleft :
      (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 3)) *
          (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 1)) ≈
        (dimQ (2 * N - 2) * secondShellLow A X B C) *
          (dimQ (2 * N - 2) * secondShellHigh B C) :=
    mul_eqv_both
      (Q'.mul_eqv_congr_left _ _ _ hlow)
      (Q'.mul_eqv_congr_left _ _ _ hhigh)
  have hright :
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (2 * N - 1) * boxSum fenceW N (2 * N - 2))) *
        (dimQ (2 * N - 3) * boxSum fenceW N (2 * N - 2)) ≈
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (2 * N - 1) * secondShellMid X B C)) *
        (dimQ (2 * N - 3) * secondShellMid X B C) :=
    mul_eqv_both
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hmid))
      (Q'.mul_eqv_congr_left _ _ _ hmid)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (by simpa only [SecondShellScalarFence, A, X, B, C] using hscalar)
      (Q'.ge_of_eqv hright))

/-- Exact nontrivial anchor for the new scalar family. -/
theorem secondShellScalarFence_three : SecondShellScalarFence 3 := by
  unfold SecondShellScalarFence secondShellLow secondShellMid secondShellHigh
  decide

end YMGap.Continuum.P2RetunedFenceSecondShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.boxSumDelta_top_three
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.boxSum_top_three
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.fenceSecondShellTuran_of_scalar
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellScalarFence_three
