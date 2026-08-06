/-
Track 11.7-fusion / R2p -- the third exact boundary shell.

At channel `2*N-4`, the old cutoff contributes its four top-even pairs.
The appended row and column contribute deficits two and four, and the new
diagonal is admissible.  Hence the physical box coefficient has exactly nine
Clebsch pairs.  This file extracts that finite support constructively and
reduces the next strong-Turan atom to five terminal heat coefficients.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFenceSecondShell

namespace YMGap.Continuum.P2RetunedFenceThirdShell

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.P2RetunedFenceTopShell
open YMGap.Continuum.P2RetunedFenceSecondShell
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.RGTransport
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

private theorem fusionInd_comm (a b s : Nat) :
    fusionInd a b s = fusionInd b a s := by
  unfold fusionInd
  rw [fusionOK_symm_ab]

private theorem fusionInd_top_four_low (N : Nat) (hN : 4 ≤ N) :
    fusionInd (N - 4) N (2 * N - 4) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 4) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 4) N = N - 4 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 4 + N + (2 * N - 4) = 2 * (2 * N - 4) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 4), Nat.mul_mod_left]

private theorem fusionInd_top_four_mid (N : Nat) (hN : 4 ≤ N) :
    fusionInd (N - 2) N (2 * N - 4) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  have hmax : Nat.max (N - 2) N = N := Nat.max_eq_right (by omega)
  have hmin : Nat.min (N - 2) N = N - 2 := Nat.min_eq_left (by omega)
  rw [hmax, hmin]
  refine ⟨by omega, by omega, ?_⟩
  have he : N - 2 + N + (2 * N - 4) = 2 * (2 * N - 3) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 3), Nat.mul_mod_left]

private theorem fusionInd_top_four_last_zero (N : Nat) (hN : 4 ≤ N) :
    fusionInd (N - 1) N (2 * N - 4) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff (N - 1) N (2 * N - 4)).mp hok with
    ⟨_, _, hp⟩
  omega

private theorem fusionInd_top_four_diag (N : Nat) (hN : 4 ≤ N) :
    fusionInd N N (2 * N - 4) = (1 : Q') := by
  unfold fusionInd
  rw [if_pos]
  rw [fusionOK_eq_true_iff]
  simp only [Nat.max_self, Nat.min_self]
  refine ⟨by omega, by omega, ?_⟩
  have he : N + N + (2 * N - 4) = 2 * (2 * N - 2) := by omega
  rw [he, Nat.mul_comm 2 (2 * N - 2), Nat.mul_mod_left]

private theorem fusionInd_top_four_zero_below
    (N a : Nat) (hN : 4 ≤ N) (ha : a < N - 2) (hne : a ≠ N - 4) :
    fusionInd a N (2 * N - 4) = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro hok
  rcases (fusionOK_eq_true_iff a N (2 * N - 4)).mp hok with
    ⟨_, hhi, hp⟩
  have halow : N - 4 ≤ a := by omega
  have haeq : a = N - 3 := by omega
  subst a
  omega

private theorem topFourRow (w : Q') (N : Nat) (hN : 4 ≤ N) :
    fsum (fun a => fusionInd a N (2 * N - 4) *
      (coeffW w a * coeffW w N)) N ≈
      coeffW w (N - 4) * coeffW w N +
        coeffW w (N - 2) * coeffW w N := by
  let g := fun a => fusionInd a N (2 * N - 4) *
    (coeffW w a * coeffW w N)
  have hsplit : fsum g N =
      (fsum g (N - 2) + g (N - 2)) + g (N - 1) := by
    rw [show N = (N - 2) + 2 by omega]
    rfl
  rw [hsplit]
  have hpre : fsum g (N - 2) ≈
      coeffW w (N - 4) * coeffW w N := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N - 4) (n := N - 2) (by omega)
        (fun a ha hne => ?_)) ?_
    · dsimp only [g]
      rw [fusionInd_top_four_zero_below N a hN ha hne]
      exact Q'.zero_mul_eqv _
    · dsimp only [g]
      rw [fusionInd_top_four_low N hN]
      exact Q'.one_mul_eqv _
  have hmid : g (N - 2) ≈ coeffW w (N - 2) * coeffW w N := by
    dsimp only [g]
    rw [fusionInd_top_four_mid N hN]
    exact Q'.one_mul_eqv _
  have hlast : g (N - 1) ≈ (0 : Q') := by
    dsimp only [g]
    rw [fusionInd_top_four_last_zero N hN]
    exact Q'.zero_mul_eqv _
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hpre hmid) hlast)
    (q_add_zero_eqv _)

/-- The new cutoff contributes four off-diagonal orientations and its
diagonal: five new pairs in total. -/
theorem boxSumDelta_top_four (w : Q') (N : Nat) (hN : 4 ≤ N) :
    boxSumDelta w (N - 1) (2 * N - 4) ≈
      (coeffW w (N - 4) * coeffW w N +
        coeffW w (N - 2) * coeffW w N) +
      ((coeffW w (N - 4) * coeffW w N +
        coeffW w (N - 2) * coeffW w N) +
        coeffW w N * coeffW w N) := by
  have hNm : N - 1 + 1 = N := by omega
  unfold boxSumDelta
  rw [hNm]
  have hleft := topFourRow w N hN
  have hright0 := topFourRow w N hN
  have hright :
      fsum (fun b => fusionInd N b (2 * N - 4) *
        (coeffW w N * coeffW w b)) N ≈
        coeffW w (N - 4) * coeffW w N +
          coeffW w (N - 2) * coeffW w N := by
    refine Q'.eqv_trans _ _ _ ?_ hright0
    apply CubeRatioBounds.fsum_eqv_congr
    intro b
    rw [fusionInd_comm N b (2 * N - 4)]
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  rw [fusionInd_top_four_diag N hN]
  exact Q'.add_eqv_congr' hleft
    (Q'.add_eqv_congr' hright (Q'.one_mul_eqv _))

/-- Channel `2*N-4` has exactly nine Clebsch pairs: four inherited top-even
pairs and five new cutoff pairs. -/
theorem boxSum_top_four (w : Q') (N : Nat) (hN : 4 ≤ N) :
    boxSum w N (2 * N - 4) ≈
      ((coeffW w (N - 2) * coeffW w (N - 2)) +
        ((coeffW w (N - 3) * coeffW w (N - 1)) +
          ((coeffW w (N - 3) * coeffW w (N - 1)) +
            coeffW w (N - 1) * coeffW w (N - 1)))) +
      ((coeffW w (N - 4) * coeffW w N +
        coeffW w (N - 2) * coeffW w N) +
       ((coeffW w (N - 4) * coeffW w N +
        coeffW w (N - 2) * coeffW w N) +
        coeffW w N * coeffW w N)) := by
  have hdec := boxSum_succ_decomp w (N - 1) (2 * N - 4)
  rw [show N - 1 + 1 = N by omega] at hdec
  refine Q'.eqv_trans _ _ _ hdec ?_
  have hold := boxSum_top_even w (N - 1) (by omega)
  rw [show 2 * (N - 1) - 2 = 2 * N - 4 by omega] at hold
  exact Q'.add_eqv_congr' hold (boxSumDelta_top_four w N hN)

/-! ## The five-coefficient scalar boundary -/

def thirdShellLow (E A X B C : Q') : Q' :=
  (X * X + (A * B + (A * B + B * B))) +
    ((E * C + X * C) + ((E * C + X * C) + C * C))

def thirdShellMid (A X B C : Q') : Q' := secondShellLow A X B C

def thirdShellHigh (X B C : Q') : Q' := secondShellMid X B C

/-- Sum-free statement of the `s=2*N-4` physical atom. -/
def ThirdShellScalarFence (N : Nat) : Prop :=
  let E := coeffW fenceW (N - 4)
  let A := coeffW fenceW (N - 3)
  let X := coeffW fenceW (N - 2)
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  (dimQ (2 * N - 3) * thirdShellLow E A X B C) *
      (dimQ (2 * N - 3) * thirdShellHigh X B C) ≤
    (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
        (dimQ (2 * N - 2) * thirdShellMid A X B C)) *
      (dimQ (2 * N - 4) * thirdShellMid A X B C)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- The nine/six/four-pair formulas compile the five-coefficient scalar
fence back to the actual weighted-box atom. -/
theorem fenceThirdShellTuran_of_scalar (N : Nat) (hN : 4 ≤ N)
    (hscalar : ThirdShellScalarFence N) :
    (dimQ (2 * N - 3) * boxSum fenceW N (2 * N - 4)) *
        (dimQ (2 * N - 3) * boxSum fenceW N (2 * N - 2)) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 3))) *
        (dimQ (2 * N - 4) * boxSum fenceW N (2 * N - 3)) := by
  let E := coeffW fenceW (N - 4)
  let A := coeffW fenceW (N - 3)
  let X := coeffW fenceW (N - 2)
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  have hlow : boxSum fenceW N (2 * N - 4) ≈ thirdShellLow E A X B C := by
    simpa only [E, A, X, B, C, thirdShellLow] using
      (boxSum_top_four fenceW N hN)
  have hmid : boxSum fenceW N (2 * N - 3) ≈ thirdShellMid A X B C := by
    simpa only [A, X, B, C, thirdShellMid, secondShellLow] using
      (boxSum_top_three fenceW N (by omega))
  have hhigh : boxSum fenceW N (2 * N - 2) ≈ thirdShellHigh X B C := by
    simpa only [X, B, C, thirdShellHigh, secondShellMid] using
      (boxSum_top_even fenceW N (by omega))
  have hleft := mul_eqv_both
    (Q'.mul_eqv_congr_left (dimQ (2 * N - 3)) _ _ hlow)
    (Q'.mul_eqv_congr_left (dimQ (2 * N - 3)) _ _ hhigh)
  have hright := mul_eqv_both
    (Q'.mul_eqv_congr_left
      (RGTransport.qpow (p2RetunedWeight fenceW) 2) _ _
      (Q'.mul_eqv_congr_left (dimQ (2 * N - 2)) _ _ hmid))
    (Q'.mul_eqv_congr_left (dimQ (2 * N - 4)) _ _ hmid)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ (by simpa only [ThirdShellScalarFence, E, A, X, B, C]
      using hscalar) (Q'.le_of_eqv (Q'.eqv_symm hright)))

/-- First exact nontrivial cell of the five-coefficient boundary. -/
theorem thirdShellScalarFence_four : ThirdShellScalarFence 4 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

theorem thirdShellScalarFence_five : ThirdShellScalarFence 5 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

theorem thirdShellScalarFence_six : ThirdShellScalarFence 6 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

theorem thirdShellScalarFence_seven : ThirdShellScalarFence 7 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

theorem thirdShellScalarFence_eight : ThirdShellScalarFence 8 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_nine : ThirdShellScalarFence 9 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_ten : ThirdShellScalarFence 10 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_twenty : ThirdShellScalarFence 20 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

end YMGap.Continuum.P2RetunedFenceThirdShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.boxSumDelta_top_four
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.boxSum_top_four
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.fenceThirdShellTuran_of_scalar
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_four
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_five
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_six
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_seven
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_eight
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_nine
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_ten
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_twenty
