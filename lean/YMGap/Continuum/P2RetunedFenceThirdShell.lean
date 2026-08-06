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
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.LaplaceMarginDeep
open YMGap.Continuum.P2RetunedFenceTopShell
open YMGap.Continuum.P2RetunedFenceSecondShell
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RebasedBulkLocalizationBridge
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.two_mul, Int.reduceMul, Int.reduceAdd]; ac_rfl))

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

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_eleven : ThirdShellScalarFence 11 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_twelve : ThirdShellScalarFence 12 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_thirteen : ThirdShellScalarFence 13 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_fourteen : ThirdShellScalarFence 14 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_fifteen : ThirdShellScalarFence 15 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_sixteen : ThirdShellScalarFence 16 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_seventeen : ThirdShellScalarFence 17 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_eighteen : ThirdShellScalarFence 18 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

set_option maxRecDepth 10000 in
theorem thirdShellScalarFence_nineteen : ThirdShellScalarFence 19 := by
  unfold ThirdShellScalarFence thirdShellLow thirdShellMid thirdShellHigh
    secondShellLow secondShellMid
  decide

/-! ## A computation-theoretic all-cutoff envelope -/

/-- The eighth heat power used by the two-step graded rectangle. -/
def thirdShellW8 : Q' := Q'.mkPos 214358881 429981696 (by decide)

theorem thirdShellW8_eqv :
    thirdShellW8 ≈ RGTransport.qpow fenceW 8 := by decide

private theorem thirdShellTerminal_rearrange_left (C c18 : Q') :
    c18 * (Q'.ofNat 20 * C) ≈ Q'.ofNat 20 * (C * c18) := by
  ring_qeqv

private theorem thirdShellTerminal_rearrange_right (B c18 : Q') :
    Q'.ofNat 20 *
        (Q'.mkPos 1 20 (by decide) * (B * c18)) ≈ c18 * B := by
  ring_qeqv

private theorem thirdShellTerminal_fraction_rearrange (B c18 : Q') :
    B * (Q'.mkPos 1 20 (by decide) * c18) ≈
      Q'.mkPos 1 20 (by decide) * (B * c18) := by
  ring_qeqv

set_option maxRecDepth 10000 in
/-- From cutoff nineteen onward, one terminal coefficient costs at most one
twentieth of its predecessor.  Only the closed `18 -> 19` anchor is
evaluated; shifted log-concavity transports it to every later cutoff. -/
theorem thirdShellTerminalRatio (N : Nat) (hN : 19 ≤ N) :
    Q'.ofNat 20 * coeffW fenceW N ≤ coeffW fenceW (N - 1) := by
  by_cases h19 : N = 19
  · subst N
    decide
  have hN20 : 20 ≤ N := by omega
  have hwp : (0 : Q') < fenceW := by decide
  have hcross0 := coeffW_step fenceW_nonneg fenceW_le_one hwp 18 (N - 20)
  have eN : 18 + (N - 20) + 2 = N := by omega
  have ePrev : 18 + (N - 20) + 1 = N - 1 := by omega
  rw [eN, ePrev] at hcross0
  have hcross :
      coeffW fenceW N * coeffW fenceW 18 ≤
        coeffW fenceW (N - 1) * coeffW fenceW 19 := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
      (Q'.le_trans' _ _ _ hcross0
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  have hfraction :
      coeffW fenceW 19 ≤
        Q'.mkPos 1 20 (by decide) * coeffW fenceW 18 := by
    apply coeffW_succ_le_of_cross 18 fenceW_nonneg
    decide
  have hB0 : (0 : Q') ≤ coeffW fenceW (N - 1) :=
    coeffW_nonneg fenceW_nonneg _
  have hfractionScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (coeffW fenceW (N - 1)) hfraction hB0
  have hcrossFraction :
      coeffW fenceW N * coeffW fenceW 18 ≤
        Q'.mkPos 1 20 (by decide) *
          (coeffW fenceW (N - 1) * coeffW fenceW 18) := by
    exact Q'.le_trans' _ _ _ hcross
      (Q'.le_trans' _ _ _ hfractionScaled
        (Q'.le_of_eqv
          (thirdShellTerminal_fraction_rearrange
            (coeffW fenceW (N - 1)) (coeffW fenceW 18))))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 20)
    hcrossFraction (by decide)
  have hchain :
      coeffW fenceW 18 * (Q'.ofNat 20 * coeffW fenceW N) ≤
        coeffW fenceW 18 * coeffW fenceW (N - 1) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (thirdShellTerminal_rearrange_left
          (coeffW fenceW N) (coeffW fenceW 18)))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (thirdShellTerminal_rearrange_right
            (coeffW fenceW (N - 1)) (coeffW fenceW 18))))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    (FusionResidualBound.coeffW_pos hwp 18) hchain

private theorem thirdShellSuccMulPredSquare (m : Nat) (hm : 1 ≤ m) :
    (m + 1) * (m - 1) = m * m - 1 := by
  cases m with
  | zero => omega
  | succ k =>
      simp only [Nat.succ_sub_one, Nat.add_mul, Nat.mul_add]
      omega

/-- At the symbolic threshold the adjacent dimension product is within
`1443/1444` of the central square. -/
theorem thirdShellDimFloor (N : Nat) (hN : 20 ≤ N) :
    Q'.ofNat 1443 *
        (dimQ (2 * N - 3) * dimQ (2 * N - 3)) ≤
      Q'.ofNat 1444 *
        (dimQ (2 * N - 2) * dimQ (2 * N - 4)) := by
  let d := (2 * N - 3) + 1
  let hi := (2 * N - 2) + 1
  let lo := (2 * N - 4) + 1
  have hd : d = 2 * N - 2 := by dsimp only [d]; omega
  have hhi : hi = (2 * N - 2) + 1 := rfl
  have hlo : lo = (2 * N - 2) - 1 := by dsimp only [lo]; omega
  have hd38 : 38 ≤ 2 * N - 2 := by omega
  have hsq1444 : 1444 ≤ (2 * N - 2) * (2 * N - 2) := by
    have hmul : 38 * 38 ≤ (2 * N - 2) * (2 * N - 2) :=
      Nat.mul_le_mul hd38 hd38
    exact hmul
  have hnat : 1443 * (d * d) ≤ 1444 * (hi * lo) := by
    rw [hd, hhi, hlo, thirdShellSuccMulPredSquare (2 * N - 2) (by omega)]
    omega
  have hq := Q'.ofNat_le_ofNat hnat
  have hdd : Q'.ofNat d * Q'.ofNat d ≈ Q'.ofNat (d * d) :=
    FusionRDFactor.ofNat_mul_eqv d d
  have hleft :
      Q'.ofNat 1443 * (Q'.ofNat d * Q'.ofNat d) ≈
        Q'.ofNat (1443 * (d * d)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 1443) _ _ hdd)
      (FusionRDFactor.ofNat_mul_eqv 1443 (d * d))
  have hhl : Q'.ofNat hi * Q'.ofNat lo ≈ Q'.ofNat (hi * lo) :=
    FusionRDFactor.ofNat_mul_eqv hi lo
  have hright :
      Q'.ofNat 1444 * (Q'.ofNat hi * Q'.ofNat lo) ≈
        Q'.ofNat (1444 * (hi * lo)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 1444) _ _ hhl)
      (FusionRDFactor.ofNat_mul_eqv 1444 (hi * lo))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by simpa only [dimQ, d, hi, lo] using hleft))
    (Q'.le_trans' _ _ _ hq
      (Q'.le_of_eqv (Q'.eqv_symm
        (by simpa only [dimQ, d, hi, lo] using hright))))

private theorem thirdShellScale_left (d p : Q') :
    Q'.ofNat 99 * (secondShellW4 * (d * p)) ≈
      (Q'.ofNat 99 * d) *
        (RGTransport.qpow fenceW 4 * p) := by
  have hw : secondShellW4 ≈ RGTransport.qpow fenceW 4 :=
    secondShellW4_eqv
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 99) _ _
      (Q'.mul_eqv_congr_right _ _ (d * p) hw)) (by ring_qeqv)

private theorem thirdShellScale_right (d p : Q') :
    Q'.ofNat 100 *
        (d * (RGTransport.qpow fenceW 4 * p)) ≈
      (Q'.ofNat 100 * d) *
        (RGTransport.qpow fenceW 4 * p) := by
  ring_qeqv

private theorem thirdShellCrossNat (N : Nat) (hN : 20 ≤ N) :
    99 * ((N - 1) * N) ≤ 100 * ((N - 2) * (N + 1)) := by
  let m := N - 2
  have h0 : N - 2 = m := by rfl
  have h1 : N - 1 = m + 1 := by dsimp only [m]; omega
  have h2 : N = m + 2 := by dsimp only [m]; omega
  rw [h0, h1, h2]
  simp only [Nat.add_mul, Nat.mul_add]
  have hm : 18 ≤ m := by dsimp only [m]; omega
  have hsq : 18 * 18 ≤ m * m := Nat.mul_le_mul hm hm
  omega

/-- Exact symbolic lower cross-ratio for the middle shell.  The heat
exponents differ by precisely four, so after cancellation the claim is the
integer inequality `99(N-1)N ≤ 100(N-2)(N+1)`. -/
theorem thirdShellMidCrossLower (N : Nat) (hN : 20 ≤ N) :
    Q'.ofNat 99 *
        (secondShellW4 *
          (coeffW fenceW (N - 2) * coeffW fenceW (N - 1))) ≤
      Q'.ofNat 100 *
        (coeffW fenceW (N - 3) * coeffW fenceW N) := by
  let innerExp := c4 (N - 2) + c4 (N - 1)
  let p := RGTransport.qpow fenceW innerExp
  let dInner := Q'.ofNat ((N - 1) * N)
  let dOuter := Q'.ofNat ((N - 2) * (N + 1))
  have hExp : c4 (N - 3) + c4 N = 4 + innerExp := by
    dsimp only [innerExp]
    let m := N - 3
    have h0 : N - 3 = m := by rfl
    have h1 : N - 2 = m + 1 := by dsimp only [m]; omega
    have h2 : N - 1 = m + 2 := by dsimp only [m]; omega
    have h3 : N = m + 3 := by dsimp only [m]; omega
    rw [h0, h1, h2, h3]
    unfold c4
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  have hInner :
      coeffW fenceW (N - 2) * coeffW fenceW (N - 1) ≈
        dInner * p := by
    have h := coeffW_mul_ofNat fenceW (N - 2) (N - 1)
    simpa only [show N - 2 + 1 = N - 1 by omega,
      show N - 1 + 1 = N by omega, innerExp, p, dInner] using h
  have hOuter0 :
      coeffW fenceW (N - 3) * coeffW fenceW N ≈
        dOuter * RGTransport.qpow fenceW (4 + innerExp) := by
    have h := coeffW_mul_ofNat fenceW (N - 3) N
    rw [hExp] at h
    simpa only [show N - 3 + 1 = N - 2 by omega,
      dOuter, innerExp] using h
  have hOuter :
      coeffW fenceW (N - 3) * coeffW fenceW N ≈
        dOuter * (RGTransport.qpow fenceW 4 * p) :=
    Q'.eqv_trans _ _ _ hOuter0
      (Q'.mul_eqv_congr_left dOuter _ _
        (by simpa only [p] using
          (HeatKernelRGStep.qpow_add fenceW 4 innerExp)))
  have hNat := thirdShellCrossNat N hN
  have hqNat := Q'.ofNat_le_ofNat hNat
  have hDim : Q'.ofNat 99 * dInner ≤ Q'.ofNat 100 * dOuter := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by
        dsimp only [dInner]
        exact FusionRDFactor.ofNat_mul_eqv 99 ((N - 1) * N)))
      (Q'.le_trans' _ _ _ hqNat
        (Q'.le_of_eqv (Q'.eqv_symm (by
          dsimp only [dOuter]
          exact FusionRDFactor.ofNat_mul_eqv 100 ((N - 2) * (N + 1))))))
  have hCommon0 : (0 : Q') ≤ RGTransport.qpow fenceW 4 * p :=
    Q'.mul_nonneg _ _
      (RGTransport.qpow_nonneg fenceW fenceW_nonneg 4)
      (by dsimp only [p]; exact RGTransport.qpow_nonneg fenceW fenceW_nonneg _)
  have hScaled := Q'.mul_le_mul_of_nonneg_right _ _
    (RGTransport.qpow fenceW 4 * p) hDim hCommon0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 99) _ _
        (Q'.mul_eqv_congr_left secondShellW4 _ _ hInner))
      (thirdShellScale_left dInner p)))
    (Q'.le_trans' _ _ _ hScaled
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 100) _ _ hOuter)
        (thirdShellScale_right dOuter p)))))

/-- Two-step rectangle cap for the far new pair. -/
theorem thirdShellFarCrossUpper (N : Nat) (hN : 4 ≤ N) :
    coeffW fenceW (N - 4) * coeffW fenceW N ≤
      thirdShellW8 *
        (coeffW fenceW (N - 2) * coeffW fenceW (N - 2)) := by
  have h := coeffW_rect_graded_wsq (w := fenceW) (by decide) 2 2 (N - 4)
  have e0 : N - 4 + 2 = N - 2 := by omega
  have e1 : N - 2 + 2 = N := by omega
  rw [e0, e1] at h
  have hp : RGTransport.qpow (RGTransport.qpow fenceW 2) (2 * 2) ≈
      thirdShellW8 := by decide
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hp))

/-- Adjacent outer-pair cap at the third shell. -/
theorem thirdShellLeftCrossUpper (N : Nat) (hN : 4 ≤ N) :
    coeffW fenceW (N - 3) * coeffW fenceW (N - 1) ≤
      secondShellW2 *
        (coeffW fenceW (N - 2) * coeffW fenceW (N - 2)) := by
  have h := coeffW_superLogConcave_wsq fenceW_nonneg (N - 3)
  have e1 : N - 3 + 1 = N - 2 := by omega
  have e2 : N - 3 + 2 = N - 1 := by omega
  rw [e1, e2] at h
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm secondShellW2_eqv)))

/-- Adjacent right-pair cap at the third shell. -/
theorem thirdShellRightCrossUpper (N : Nat) (hN : 4 ≤ N) :
    coeffW fenceW (N - 2) * coeffW fenceW N ≤
      secondShellW2 *
        (coeffW fenceW (N - 1) * coeffW fenceW (N - 1)) := by
  have h := coeffW_superLogConcave_wsq fenceW_nonneg (N - 2)
  have e1 : N - 2 + 1 = N - 1 := by omega
  have e2 : N - 2 + 2 = N := by omega
  rw [e1, e2] at h
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm secondShellW2_eqv)))

/-! ## Division-free compiler -/

def thirdShellLowCap160000 : Q' :=
  Q'.ofNat 160000 +
    (Q'.ofNat 320000 * secondShellW2 +
      (Q'.ofNat 400 +
        (Q'.ofNat 320000 * thirdShellW8 +
          (Q'.ofNat 800 * secondShellW2 + Q'.ofNat 1))))

def thirdShellHighCap400 : Q' :=
  Q'.ofNat 401 + Q'.ofNat 800 * secondShellW2

def thirdShellInv400 : Q' := Q'.mkPos 1 400 (by decide)
def thirdShellInv160000 : Q' := Q'.mkPos 1 160000 (by decide)

def thirdShellLowCapFrac : Q' :=
  (1 : Q') +
    (secondShellW2 + (secondShellW2 + thirdShellInv400)) +
    ((thirdShellW8 + secondShellW2 * thirdShellInv400) +
      ((thirdShellW8 + secondShellW2 * thirdShellInv400) +
        thirdShellInv160000))

def thirdShellHighCapFrac : Q' :=
  (1 : Q') +
    (secondShellW2 + (secondShellW2 + thirdShellInv400))

theorem thirdShellLowCap_clear :
    Q'.ofNat 160000 * thirdShellLowCapFrac ≈
      thirdShellLowCap160000 := by decide

theorem thirdShellHighCap_clear :
    Q'.ofNat 400 * thirdShellHighCapFrac ≈
      thirdShellHighCap400 := by decide

def thirdShellProductCap : Q' :=
  thirdShellLowCap160000 * thirdShellHighCap400

def thirdShellMidGain100 : Q' :=
  Q'.ofNat 200 + Q'.ofNat 198 * secondShellW4

def thirdShellCompileScale : Q' :=
  Q'.ofNat 64000000 *
    ((thirdShellMidGain100 * thirdShellMidGain100) * Q'.ofNat 1443)

/-- The only closed arithmetic fact in the third-shell compiler. -/
theorem thirdShellClosedBalance :
    (Q'.ofNat 1444 * thirdShellProductCap) * Q'.ofNat 10000 ≤
      thirdShellCompileScale *
        RGTransport.qpow (p2RetunedWeight fenceW) 2 := by
  decide

/-- Three denominator-cleared envelopes imply the entire scalar boundary. -/
structure ThirdShellEnvelope (N : Nat) : Type where
  productCap :
    let E := coeffW fenceW (N - 4)
    let A := coeffW fenceW (N - 3)
    let X := coeffW fenceW (N - 2)
    let B := coeffW fenceW (N - 1)
    let C := coeffW fenceW N
    Q'.ofNat 64000000 *
        (thirdShellLow E A X B C * thirdShellHigh X B C) ≤
      thirdShellProductCap * ((X * B) * (X * B))
  midFloor :
    let A := coeffW fenceW (N - 3)
    let X := coeffW fenceW (N - 2)
    let B := coeffW fenceW (N - 1)
    let C := coeffW fenceW N
    (thirdShellMidGain100 * thirdShellMidGain100) *
        ((X * B) * (X * B)) ≤
      Q'.ofNat 10000 *
        (thirdShellMid A X B C * thirdShellMid A X B C)
  dimFloor :
    Q'.ofNat 1443 *
        (dimQ (2 * N - 3) * dimQ (2 * N - 3)) ≤
      Q'.ofNat 1444 *
        (dimQ (2 * N - 2) * dimQ (2 * N - 4))

private theorem thirdShellMid_nonneg (A X B C : Q')
    (hA : (0 : Q') ≤ A) (hX : (0 : Q') ≤ X)
    (hB : (0 : Q') ≤ B) (hC : (0 : Q') ≤ C) :
    (0 : Q') ≤ thirdShellMid A X B C := by
  unfold thirdShellMid secondShellLow
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hX hB)
      (Q'.mul_nonneg _ _ hX hB))
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hA hC)
        (Q'.mul_nonneg _ _ hB hC))
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hA hC)
        (Q'.mul_nonneg _ _ hB hC)))

private theorem thirdShellCompile_step1 (D LH : Q') :
    thirdShellCompileScale * ((D * D) * LH) ≈
      (((thirdShellMidGain100 * thirdShellMidGain100) * Q'.ofNat 1443) *
          (D * D)) *
        (Q'.ofNat 64000000 * LH) := by
  unfold thirdShellCompileScale
  ring_qeqv

private theorem thirdShellCompile_step2 (D cap Z2 : Q') :
    (((thirdShellMidGain100 * thirdShellMidGain100) * Q'.ofNat 1443) *
        (D * D)) * (cap * Z2) ≈
      (Q'.ofNat 1443 * (D * D)) *
        (((thirdShellMidGain100 * thirdShellMidGain100) * cap) * Z2) := by
  ring_qeqv

private theorem thirdShellCompile_step3 (H L cap Z2 : Q') :
    (Q'.ofNat 1444 * (H * L)) *
        (((thirdShellMidGain100 * thirdShellMidGain100) * cap) * Z2) ≈
      ((Q'.ofNat 1444 * cap) * (H * L)) *
        ((thirdShellMidGain100 * thirdShellMidGain100) * Z2) := by
  ring_qeqv

private theorem thirdShellCompile_step4 (H L cap mid : Q') :
    ((Q'.ofNat 1444 * cap) * (H * L)) *
        (Q'.ofNat 10000 * (mid * mid)) ≈
      ((H * L) * (mid * mid)) *
        ((Q'.ofNat 1444 * cap) * Q'.ofNat 10000) := by
  ring_qeqv

private theorem thirdShellCompile_step5 (H L mid q : Q') :
    ((H * L) * (mid * mid)) * (thirdShellCompileScale * q) ≈
      thirdShellCompileScale * (q * ((H * L) * (mid * mid))) := by
  ring_qeqv

private theorem thirdShellActual_left (D low high : Q') :
    (D * low) * (D * high) ≈ (D * D) * (low * high) := by
  ring_qeqv

private theorem thirdShellActual_right (q H L mid : Q') :
    q * (H * mid) * (L * mid) ≈ q * ((H * L) * (mid * mid)) := by
  ring_qeqv

/-- Proof-about-computation assembly from the three symbolic envelopes. -/
theorem thirdShellScalarFence_of_envelope (N : Nat)
    (E : ThirdShellEnvelope N) : ThirdShellScalarFence N := by
  let cE := coeffW fenceW (N - 4)
  let A := coeffW fenceW (N - 3)
  let X := coeffW fenceW (N - 2)
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  let low := thirdShellLow cE A X B C
  let mid := thirdShellMid A X B C
  let high := thirdShellHigh X B C
  let D := dimQ (2 * N - 3)
  let H := dimQ (2 * N - 2)
  let L := dimQ (2 * N - 4)
  let q := RGTransport.qpow (p2RetunedWeight fenceW) 2
  let Z2 := (X * B) * (X * B)
  let LH := low * high
  have hX0 : (0 : Q') ≤ X := coeffW_nonneg fenceW_nonneg _
  have hB0 : (0 : Q') ≤ B := coeffW_nonneg fenceW_nonneg _
  have hXB0 : (0 : Q') ≤ X * B := Q'.mul_nonneg _ _ hX0 hB0
  have hZ20 : (0 : Q') ≤ Z2 := Q'.mul_nonneg _ _ hXB0 hXB0
  have hD0 : (0 : Q') ≤ D := dimQ_nonneg _
  have hD20 : (0 : Q') ≤ D * D := Q'.mul_nonneg _ _ hD0 hD0
  have hHL0 : (0 : Q') ≤ H * L :=
    Q'.mul_nonneg _ _ (dimQ_nonneg _) (dimQ_nonneg _)
  have hmid0 : (0 : Q') ≤ mid :=
    thirdShellMid_nonneg A X B C
      (coeffW_nonneg fenceW_nonneg _) hX0 hB0
      (coeffW_nonneg fenceW_nonneg _)
  have hmid20 : (0 : Q') ≤ mid * mid := Q'.mul_nonneg _ _ hmid0 hmid0
  have hcap0 : (0 : Q') ≤ thirdShellProductCap := by decide
  have hgain20 : (0 : Q') ≤
      thirdShellMidGain100 * thirdShellMidGain100 := by decide
  have h1factor0 : (0 : Q') ≤
      ((thirdShellMidGain100 * thirdShellMidGain100) * Q'.ofNat 1443) *
        (D * D) := Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hgain20 (by decide)) hD20
  have h1raw := Q'.mul_le_mul_of_nonneg_left _ _
    (((thirdShellMidGain100 * thirdShellMidGain100) * Q'.ofNat 1443) *
      (D * D))
    (by simpa only [cE, A, X, B, C, low, high, Z2, LH] using E.productCap)
    h1factor0
  have h1 :
      thirdShellCompileScale * ((D * D) * LH) ≤
        (((thirdShellMidGain100 * thirdShellMidGain100) * Q'.ofNat 1443) *
          (D * D)) * (thirdShellProductCap * Z2) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (thirdShellCompile_step1 D LH)) h1raw
  have h2factor0 : (0 : Q') ≤
      (((thirdShellMidGain100 * thirdShellMidGain100) *
          thirdShellProductCap) * Z2) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ hgain20 hcap0) hZ20
  have h2raw := Q'.mul_le_mul_of_nonneg_right _ _ _
    (by simpa only [D, H, L] using E.dimFloor) h2factor0
  have h2 :
      (((thirdShellMidGain100 * thirdShellMidGain100) * Q'.ofNat 1443) *
          (D * D)) * (thirdShellProductCap * Z2) ≤
        (Q'.ofNat 1444 * (H * L)) *
          (((thirdShellMidGain100 * thirdShellMidGain100) *
            thirdShellProductCap) * Z2) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (thirdShellCompile_step2 D thirdShellProductCap Z2)) h2raw
  have h3factor0 : (0 : Q') ≤
      (Q'.ofNat 1444 * thirdShellProductCap) * (H * L) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hcap0) hHL0
  have h3raw := Q'.mul_le_mul_of_nonneg_left _ _ _
    (by simpa only [A, X, B, C, mid, Z2] using E.midFloor) h3factor0
  have h3 :
      (Q'.ofNat 1444 * (H * L)) *
          (((thirdShellMidGain100 * thirdShellMidGain100) *
            thirdShellProductCap) * Z2) ≤
        ((Q'.ofNat 1444 * thirdShellProductCap) * (H * L)) *
          (Q'.ofNat 10000 * (mid * mid)) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (thirdShellCompile_step3 H L thirdShellProductCap Z2)) h3raw
  have h4factor0 : (0 : Q') ≤ (H * L) * (mid * mid) :=
    Q'.mul_nonneg _ _ hHL0 hmid20
  have h4raw := Q'.mul_le_mul_of_nonneg_left _ _ _
    (by simpa only [q] using thirdShellClosedBalance) h4factor0
  have h4 :
      ((Q'.ofNat 1444 * thirdShellProductCap) * (H * L)) *
          (Q'.ofNat 10000 * (mid * mid)) ≤
        thirdShellCompileScale * (q * ((H * L) * (mid * mid))) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (thirdShellCompile_step4 H L thirdShellProductCap mid))
      (Q'.le_trans' _ _ _ h4raw
        (Q'.le_of_eqv (thirdShellCompile_step5 H L mid q)))
  have hscaled :
      thirdShellCompileScale * ((D * D) * LH) ≤
        thirdShellCompileScale * (q * ((H * L) * (mid * mid))) :=
    Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2
      (Q'.le_trans' _ _ _ h3 h4))
  have hscalePos : (0 : Q') < thirdShellCompileScale := by decide
  have hcore : (D * D) * LH ≤ q * ((H * L) * (mid * mid)) :=
    FusionQuotientCollapse.le_of_mul_le_mul_left_pos hscalePos hscaled
  change (D * low) * (D * high) ≤ (q * (H * mid)) * (L * mid)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (thirdShellActual_left D low high))
    (Q'.le_trans' _ _ _ hcore
      (Q'.le_of_eqv (Q'.eqv_symm (thirdShellActual_right q H L mid))))

/-! ## Physical realization of the envelopes -/

private theorem thirdShellMulLeMulNonneg {a b c d : Q'}
    (hab : a ≤ b) (hcd : c ≤ d) (hc : (0 : Q') ≤ c)
    (hb : (0 : Q') ≤ b) : a * c ≤ b * d :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

private theorem thirdShellTerminalSquare (U V : Q')
    (hU : (0 : Q') ≤ U) (hV : (0 : Q') ≤ V)
    (h : Q'.ofNat 20 * V ≤ U) :
    Q'.ofNat 400 * (V * V) ≤ U * U := by
  have h20V0 : (0 : Q') ≤ Q'.ofNat 20 * V :=
    Q'.mul_nonneg _ _ (by decide) hV
  have hsq := thirdShellMulLeMulNonneg h h h20V0 hU
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv)) hsq

private theorem thirdShellFractionCancel (r k z : Q')
    (h : r * k ≈ (1 : Q')) : r * (k * z) ≈ z :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv r k z))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z h)
      (Q'.one_mul_eqv z))

private theorem thirdShellInv400Cancel (z : Q') :
    thirdShellInv400 * (Q'.ofNat 400 * z) ≈ z :=
  thirdShellFractionCancel _ _ z (by decide)

private theorem thirdShellLowFrac_expand (X2 : Q') :
    thirdShellLowCapFrac * X2 ≈
      X2 +
        (secondShellW2 * X2 +
          (secondShellW2 * X2 + thirdShellInv400 * X2)) +
        ((thirdShellW8 * X2 +
            (secondShellW2 * thirdShellInv400) * X2) +
          ((thirdShellW8 * X2 +
              (secondShellW2 * thirdShellInv400) * X2) +
            thirdShellInv160000 * X2)) := by
  unfold thirdShellLowCapFrac
  ring_qeqv

private theorem thirdShellLowClear_right (X2 : Q') :
    Q'.ofNat 160000 * (thirdShellLowCapFrac * X2) ≈
      thirdShellLowCap160000 * X2 := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ X2))
    (Q'.mul_eqv_congr_right _ _ X2 thirdShellLowCap_clear)

private theorem thirdShellLowCap_of_atoms (E A X B C : Q')
    (hE : (0 : Q') ≤ E) (hA : (0 : Q') ≤ A)
    (hX : (0 : Q') ≤ X) (hB : (0 : Q') ≤ B)
    (hC : (0 : Q') ≤ C)
    (hAB : A * B ≤ secondShellW2 * (X * X))
    (hEC : E * C ≤ thirdShellW8 * (X * X))
    (hXC : X * C ≤ secondShellW2 * (B * B))
    (hBX : Q'.ofNat 20 * B ≤ X)
    (hCB : Q'.ofNat 20 * C ≤ B) :
    Q'.ofNat 160000 * thirdShellLow E A X B C ≤
      thirdShellLowCap160000 * (X * X) := by
  let X2 := X * X
  let B2 := B * B
  let C2 := C * C
  have hB20 : (0 : Q') ≤ B2 := Q'.mul_nonneg _ _ hB hB
  have hBX2 : Q'.ofNat 400 * B2 ≤ X2 := by
    simpa only [B2, X2] using thirdShellTerminalSquare X B hX hB hBX
  have hCB2 : Q'.ofNat 400 * C2 ≤ B2 := by
    simpa only [C2, B2] using thirdShellTerminalSquare B C hB hC hCB
  have hInv0 : (0 : Q') ≤ thirdShellInv400 := by decide
  have hBscaled := Q'.mul_le_mul_of_nonneg_left _ _ thirdShellInv400
    hBX2 hInv0
  have hBfrac : B2 ≤ thirdShellInv400 * X2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (Q'.eqv_symm (thirdShellInv400Cancel B2))) hBscaled
  have hCscaled := Q'.mul_le_mul_of_nonneg_left _ _ thirdShellInv400
    hCB2 hInv0
  have hCtoB : C2 ≤ thirdShellInv400 * B2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (Q'.eqv_symm (thirdShellInv400Cancel C2))) hCscaled
  have hCnext := Q'.mul_le_mul_of_nonneg_left _ _ thirdShellInv400
    hBfrac hInv0
  have hCfrac : C2 ≤ thirdShellInv160000 * X2 :=
    Q'.le_trans' _ _ _ hCtoB
      (Q'.le_trans' _ _ _ hCnext (Q'.le_of_eqv (by
        have hh : thirdShellInv400 * thirdShellInv400 ≈
            thirdShellInv160000 := by decide
        exact Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ X2))
          (Q'.mul_eqv_congr_right _ _ X2 hh))))
  have hW20 : (0 : Q') ≤ secondShellW2 := by decide
  have hXCnext := Q'.mul_le_mul_of_nonneg_left _ _ secondShellW2
    hBfrac hW20
  have hXCfrac : X * C ≤
      (secondShellW2 * thirdShellInv400) * X2 :=
    Q'.le_trans' _ _ _ hXC
      (Q'.le_trans' _ _ _ hXCnext
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ X2))))
  have hsum : thirdShellLow E A X B C ≤
      X2 +
        (secondShellW2 * X2 +
          (secondShellW2 * X2 + thirdShellInv400 * X2)) +
        ((thirdShellW8 * X2 +
            (secondShellW2 * thirdShellInv400) * X2) +
          ((thirdShellW8 * X2 +
              (secondShellW2 * thirdShellInv400) * X2) +
            thirdShellInv160000 * X2)) := by
    unfold thirdShellLow
    exact Q'.add_le_add
      (Q'.add_le_add (Q'.le_refl' X2)
        (Q'.add_le_add hAB (Q'.add_le_add hAB hBfrac)))
      (Q'.add_le_add (Q'.add_le_add hEC hXCfrac)
        (Q'.add_le_add (Q'.add_le_add hEC hXCfrac) hCfrac))
  have hlow : thirdShellLow E A X B C ≤ thirdShellLowCapFrac * X2 :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (thirdShellLowFrac_expand X2)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 160000)
    hlow (by decide)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (thirdShellLowClear_right X2))

private theorem thirdShellHighFrac_expand (B2 : Q') :
    thirdShellHighCapFrac * B2 ≈
      B2 + (secondShellW2 * B2 +
        (secondShellW2 * B2 + thirdShellInv400 * B2)) := by
  unfold thirdShellHighCapFrac
  ring_qeqv

private theorem thirdShellHighClear_right (B2 : Q') :
    Q'.ofNat 400 * (thirdShellHighCapFrac * B2) ≈
      thirdShellHighCap400 * B2 := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ B2))
    (Q'.mul_eqv_congr_right _ _ B2 thirdShellHighCap_clear)

private theorem thirdShellHighCap_of_atoms (X B C : Q')
    (hB : (0 : Q') ≤ B) (hC : (0 : Q') ≤ C)
    (hXC : X * C ≤ secondShellW2 * (B * B))
    (hCB : Q'.ofNat 20 * C ≤ B) :
    Q'.ofNat 400 * thirdShellHigh X B C ≤
      thirdShellHighCap400 * (B * B) := by
  let B2 := B * B
  let C2 := C * C
  have hCB2 : Q'.ofNat 400 * C2 ≤ B2 := by
    simpa only [C2, B2] using thirdShellTerminalSquare B C hB hC hCB
  have hInv0 : (0 : Q') ≤ thirdShellInv400 := by decide
  have hCscaled := Q'.mul_le_mul_of_nonneg_left _ _ thirdShellInv400
    hCB2 hInv0
  have hCfrac : C2 ≤ thirdShellInv400 * B2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv
      (Q'.eqv_symm (thirdShellInv400Cancel C2))) hCscaled
  have hsum : thirdShellHigh X B C ≤
      B2 + (secondShellW2 * B2 +
        (secondShellW2 * B2 + thirdShellInv400 * B2)) := by
    unfold thirdShellHigh secondShellMid
    exact Q'.add_le_add (Q'.le_refl' B2)
      (Q'.add_le_add hXC (Q'.add_le_add hXC hCfrac))
  have hhigh : thirdShellHigh X B C ≤ thirdShellHighCapFrac * B2 :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (thirdShellHighFrac_expand B2)))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 400)
    hhigh (by decide)
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv (thirdShellHighClear_right B2))

private theorem thirdShellProduct_left (low high : Q') :
    (Q'.ofNat 160000 * low) * (Q'.ofNat 400 * high) ≈
      Q'.ofNat 64000000 * (low * high) := by
  ring_qeqv

private theorem thirdShellProduct_right (X B : Q') :
    (thirdShellLowCap160000 * (X * X)) *
        (thirdShellHighCap400 * (B * B)) ≈
      thirdShellProductCap * ((X * B) * (X * B)) := by
  unfold thirdShellProductCap
  ring_qeqv

private theorem thirdShellProductCap_of_atoms (E A X B C : Q')
    (hE : (0 : Q') ≤ E) (hA : (0 : Q') ≤ A)
    (hX : (0 : Q') ≤ X) (hB : (0 : Q') ≤ B)
    (hC : (0 : Q') ≤ C)
    (hAB : A * B ≤ secondShellW2 * (X * X))
    (hEC : E * C ≤ thirdShellW8 * (X * X))
    (hXC : X * C ≤ secondShellW2 * (B * B))
    (hBX : Q'.ofNat 20 * B ≤ X)
    (hCB : Q'.ofNat 20 * C ≤ B) :
    Q'.ofNat 64000000 *
        (thirdShellLow E A X B C * thirdShellHigh X B C) ≤
      thirdShellProductCap * ((X * B) * (X * B)) := by
  have hlow := thirdShellLowCap_of_atoms E A X B C hE hA hX hB hC
    hAB hEC hXC hBX hCB
  have hhigh := thirdShellHighCap_of_atoms X B C hB hC hXC hCB
  have h400high0 : (0 : Q') ≤ Q'.ofNat 400 * thirdShellHigh X B C := by
    unfold thirdShellHigh secondShellMid
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hB hB)
        (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hX hC)
          (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hX hC)
            (Q'.mul_nonneg _ _ hC hC))))
  have hlowCap0 : (0 : Q') ≤ thirdShellLowCap160000 * (X * X) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hX hX)
  have hprod := thirdShellMulLeMulNonneg hlow hhigh h400high0 hlowCap0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (thirdShellProduct_left (thirdShellLow E A X B C)
        (thirdShellHigh X B C))))
    (Q'.le_trans' _ _ _ hprod
      (Q'.le_of_eqv (thirdShellProduct_right X B)))

private theorem thirdShellMid_linear_left (Z : Q') :
    thirdShellMidGain100 * Z ≈
      Q'.ofNat 200 * Z +
        Q'.ofNat 198 * (secondShellW4 * Z) := by
  unfold thirdShellMidGain100
  ring_qeqv

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
private theorem thirdShellScaleDouble100 (z : Q') :
    Q'.ofNat 100 * (z + z) ≈ Q'.ofNat 200 * z := by
  have hc : Q'.ofNat 100 + Q'.ofNat 100 ≈ Q'.ofNat 200 := by decide
  exact Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ z z)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ z))
      (Q'.mul_eqv_congr_right _ _ z hc))

private theorem thirdShellMid_linear_right (A X B C : Q') :
    Q'.ofNat 100 * thirdShellMid A X B C ≈
      (Q'.ofNat 200 * (X * B) + Q'.ofNat 200 * (A * C)) +
        Q'.ofNat 200 * (B * C) := by
  unfold thirdShellMid secondShellLow
  let Z := X * B
  let G := A * C + B * C
  have hdist := Q'.mul_add_eqv (Q'.ofNat 100) (Z + Z) (G + G)
  have hZ := thirdShellScaleDouble100 Z
  have hG0 := thirdShellScaleDouble100 G
  have hG : Q'.ofNat 100 * (G + G) ≈
      Q'.ofNat 200 * (A * C) + Q'.ofNat 200 * (B * C) :=
    Q'.eqv_trans _ _ _ hG0
      (by simpa only [G] using
        (Q'.mul_add_eqv (Q'.ofNat 200) (A * C) (B * C)))
  exact Q'.eqv_trans _ _ _
    (by simpa only [Z, G] using hdist)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hZ hG)
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))

private theorem thirdShellMidFloor_of_cross (A X B C : Q')
    (hA : (0 : Q') ≤ A) (hX : (0 : Q') ≤ X)
    (hB : (0 : Q') ≤ B) (hC : (0 : Q') ≤ C)
    (hcross : Q'.ofNat 99 * (secondShellW4 * (X * B)) ≤
      Q'.ofNat 100 * (A * C)) :
    (thirdShellMidGain100 * thirdShellMidGain100) *
        ((X * B) * (X * B)) ≤
      Q'.ofNat 10000 *
        (thirdShellMid A X B C * thirdShellMid A X B C) := by
  let Z := X * B
  let mid := thirdShellMid A X B C
  have hcross2 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    hcross (by decide)
  have hcross' : Q'.ofNat 198 * (secondShellW4 * Z) ≤
      Q'.ofNat 200 * (A * C) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by dsimp only [Z]; ring_qeqv))
      (Q'.le_trans' _ _ _ hcross2 (Q'.le_of_eqv (by ring_qeqv)))
  have hbase := Q'.add_le_add (Q'.le_refl' (Q'.ofNat 200 * Z)) hcross'
  have hBC0 : (0 : Q') ≤ Q'.ofNat 200 * (B * C) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hB hC)
  have htail := Q'.add_le_self_of_nonneg
    (Q'.ofNat 200 * Z + Q'.ofNat 200 * (A * C))
    (Q'.ofNat 200 * (B * C)) hBC0
  have hlinear : thirdShellMidGain100 * Z ≤ Q'.ofNat 100 * mid :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (thirdShellMid_linear_left Z))
      (Q'.le_trans' _ _ _ hbase
        (Q'.le_trans' _ _ _ htail
          (Q'.le_of_eqv (Q'.eqv_symm (by
            simpa only [Z, mid] using thirdShellMid_linear_right A X B C)))))
  have hZ0 : (0 : Q') ≤ Z := Q'.mul_nonneg _ _ hX hB
  have hleft0 : (0 : Q') ≤ thirdShellMidGain100 * Z :=
    Q'.mul_nonneg _ _ (by decide) hZ0
  have hmid0 : (0 : Q') ≤ mid :=
    thirdShellMid_nonneg A X B C hA hX hB hC
  have hright0 : (0 : Q') ≤ Q'.ofNat 100 * mid :=
    Q'.mul_nonneg _ _ (by decide) hmid0
  have hsq := thirdShellMulLeMulNonneg hlinear hlinear hleft0 hright0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by dsimp only [Z]; ring_qeqv))
    (Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv (by dsimp only [mid]; ring_qeqv)))

/-- The physical third-shell envelope for every symbolic cutoff `N≥20`. -/
def thirdShellEnvelope (N : Nat) (hN : 20 ≤ N) : ThirdShellEnvelope N where
  productCap := by
    exact thirdShellProductCap_of_atoms _ _ _ _ _
      (coeffW_nonneg fenceW_nonneg _)
      (coeffW_nonneg fenceW_nonneg _)
      (coeffW_nonneg fenceW_nonneg _)
      (coeffW_nonneg fenceW_nonneg _)
      (coeffW_nonneg fenceW_nonneg _)
      (thirdShellLeftCrossUpper N (by omega))
      (thirdShellFarCrossUpper N (by omega))
      (thirdShellRightCrossUpper N (by omega))
      (thirdShellTerminalRatio (N - 1) (by omega))
      (thirdShellTerminalRatio N (by omega))
  midFloor := by
    exact thirdShellMidFloor_of_cross _ _ _ _
      (coeffW_nonneg fenceW_nonneg _)
      (coeffW_nonneg fenceW_nonneg _)
      (coeffW_nonneg fenceW_nonneg _)
      (coeffW_nonneg fenceW_nonneg _)
      (thirdShellMidCrossLower N hN)
  dimFloor := thirdShellDimFloor N hN

/-- Every physical cutoff satisfies the third-shell scalar fence.  The
finite prefix stops at nineteen; all later cutoffs use the symbolic
envelope compiler. -/
theorem thirdShellScalarFence_all (N : Nat) (hN : 4 ≤ N) :
    ThirdShellScalarFence N := by
  by_cases h20 : 20 ≤ N
  · exact thirdShellScalarFence_of_envelope N (thirdShellEnvelope N h20)
  · have hcases :
        N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 ∨ N = 9 ∨
        N = 10 ∨ N = 11 ∨ N = 12 ∨ N = 13 ∨ N = 14 ∨
        N = 15 ∨ N = 16 ∨ N = 17 ∨ N = 18 ∨ N = 19 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact thirdShellScalarFence_four
    · exact thirdShellScalarFence_five
    · exact thirdShellScalarFence_six
    · exact thirdShellScalarFence_seven
    · exact thirdShellScalarFence_eight
    · exact thirdShellScalarFence_nine
    · exact thirdShellScalarFence_ten
    · exact thirdShellScalarFence_eleven
    · exact thirdShellScalarFence_twelve
    · exact thirdShellScalarFence_thirteen
    · exact thirdShellScalarFence_fourteen
    · exact thirdShellScalarFence_fifteen
    · exact thirdShellScalarFence_sixteen
    · exact thirdShellScalarFence_seventeen
    · exact thirdShellScalarFence_eighteen
    · exact thirdShellScalarFence_nineteen

/-- The actual nine/six/four-pair Turan atom at `s=2N-4`, uniformly in the
physical cutoff. -/
theorem fenceThirdShellTuran (N : Nat) (hN : 4 ≤ N) :
    (dimQ (2 * N - 3) * boxSum fenceW N (2 * N - 4)) *
        (dimQ (2 * N - 3) * boxSum fenceW N (2 * N - 2)) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 3))) *
        (dimQ (2 * N - 4) * boxSum fenceW N (2 * N - 3)) :=
  fenceThirdShellTuran_of_scalar N hN (thirdShellScalarFence_all N hN)

/-- Residual family after the top three boundary shells. -/
def FenceBoxDeeperInteriorTuranTail (N : Nat) : Prop :=
  forall s, 1 ≤ s -> s + 5 ≤ 2 * N ->
    (dimQ (s + 1) * boxSum fenceW N s) *
        (dimQ (s + 1) * boxSum fenceW N (s + 2)) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (s + 2) * boxSum fenceW N (s + 1))) *
        (dimQ s * boxSum fenceW N (s + 1))

/-- Fill `s=2N-4` and leave only `s+5≤2N` to the caller. -/
def fenceBoxDeepInteriorTuranTailOfDeeper (N : Nat) (hN : 4 ≤ N)
    (deeper : FenceBoxDeeperInteriorTuranTail N) :
    FenceBoxDeepInteriorTuranTail N := by
  intro s hs hsupport
  by_cases hthird : s = 2 * N - 4
  · subst s
    simpa only [show 2 * N - 4 + 1 = 2 * N - 3 by omega,
      show 2 * N - 4 + 2 = 2 * N - 2 by omega] using
      (fenceThirdShellTuran N hN)
  · exact deeper s hs (by omega)

/-- Reviewed `CanonicalBulkControl` repoint after closing the third physical
boundary shell. -/
def fenceCanonicalBulkControlOfDeeperInterior (N : Nat) (hN : 4 ≤ N)
    (deeper : FenceBoxDeeperInteriorTuranTail N) :
    CanonicalBulkControl N fenceW 2 :=
  fenceCanonicalBulkControlOfDeepInterior N (by omega)
    (fenceBoxDeepInteriorTuranTailOfDeeper N hN deeper)

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
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_eleven
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_twelve
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_thirteen
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_fourteen
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_fifteen
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_sixteen
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_seventeen
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_eighteen
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_nineteen
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellW8_eqv
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellTerminalRatio
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellDimFloor
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellMidCrossLower
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellFarCrossUpper
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellLeftCrossUpper
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellRightCrossUpper
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellClosedBalance
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_of_envelope
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellEnvelope
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.thirdShellScalarFence_all
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.fenceThirdShellTuran
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.fenceBoxDeepInteriorTuranTailOfDeeper
#print axioms YMGap.Continuum.P2RetunedFenceThirdShell.fenceCanonicalBulkControlOfDeeperInterior
