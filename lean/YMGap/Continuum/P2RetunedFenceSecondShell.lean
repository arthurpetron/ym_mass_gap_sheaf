/-
Track 11.7-fusion / R2p -- the next exact boundary shell.

At channel `2*N-3`, the old cutoff contributes its two top-odd pairs and
the newly appended row/column contributes exactly four more pairs.  This
file derives the resulting six-pair formula from the cutoff recurrence.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFenceTopShell
import YMGap.Continuum.LaplaceMarginDeep
import YMGap.Continuum.HarmonicSymbolicAnchorRatio

namespace YMGap.Continuum.P2RetunedFenceSecondShell

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundE
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.LaplaceMarginDeep
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.P2RetunedFenceTopShell
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

/-! ## A computation-theoretic all-N envelope compiler -/

def secondShellW2 : Q' := Q'.mkPos 121 144 (by decide)
def secondShellW4 : Q' := Q'.mkPos 14641 20736 (by decide)

theorem secondShellW2_eqv :
    secondShellW2 ≈ RGTransport.qpow fenceW 2 := by decide

theorem secondShellW4_eqv :
    secondShellW4 ≈ RGTransport.qpow fenceW 4 := by decide

/-- Nine times the uniform coefficient cap.  The factor nine clears the
terminal estimate `C^2≤B^2/9`. -/
def secondShellLowCap9 : Q' :=
  Q'.ofNat 4 *
    (Q'.ofNat 9 * (((1 : Q') + secondShellW4) * secondShellW2) + 1)

def secondShellCompileScale : Q' :=
  Q'.ofNat 9 * (Q'.ofNat 1764 * Q'.ofNat 168)

/-- The sole closed arithmetic balance in the all-N compiler. -/
theorem secondShellClosedBalance :
    (Q'.ofNat 169 * secondShellLowCap9) * Q'.ofNat 256 ≤
      secondShellCompileScale *
        RGTransport.qpow (p2RetunedWeight fenceW) 2 := by
  decide

/-- Three division-free envelopes suffice for the complete scalar shell.
The constants encode

* `9·low·high ≤ lowCap9·B⁴`,
* `1764·B⁴ ≤ 256·mid²` (equivalently `mid≥21B²/8`), and
* `168·D² ≤ 169·H·L`.
-/
structure SecondShellEnvelope (N : Nat) : Type where
  lowCap :
    let A := coeffW fenceW (N - 3)
    let X := coeffW fenceW (N - 2)
    let B := coeffW fenceW (N - 1)
    let C := coeffW fenceW N
    Q'.ofNat 9 *
        (secondShellLow A X B C * secondShellHigh B C) ≤
      secondShellLowCap9 * ((B * B) * (B * B))
  midFloor :
    let X := coeffW fenceW (N - 2)
    let B := coeffW fenceW (N - 1)
    let C := coeffW fenceW N
    Q'.ofNat 1764 * ((B * B) * (B * B)) ≤
      Q'.ofNat 256 *
        (secondShellMid X B C * secondShellMid X B C)
  dimFloor :
    Q'.ofNat 168 *
        (dimQ (2 * N - 2) * dimQ (2 * N - 2)) ≤
      Q'.ofNat 169 *
        (dimQ (2 * N - 1) * dimQ (2 * N - 3))

private theorem secondShellMid_nonneg (X B C : Q')
    (hX : (0 : Q') ≤ X) (hB : (0 : Q') ≤ B) (hC : (0 : Q') ≤ C) :
    (0 : Q') ≤ secondShellMid X B C := by
  unfold secondShellMid
  exact Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hB hB)
    (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hX hC)
      (Q'.zero_le_add _ _ (Q'.mul_nonneg _ _ hX hC)
        (Q'.mul_nonneg _ _ hC hC)))

private theorem secondShellCompile_step1 (D LH : Q') :
    secondShellCompileScale * ((D * D) * LH) ≈
      ((Q'.ofNat 1764 * Q'.ofNat 168) * (D * D)) *
        (Q'.ofNat 9 * LH) := by
  unfold secondShellCompileScale
  ring_qeqv

private theorem secondShellCompile_step2
    (D cap B4 : Q') :
    ((Q'.ofNat 1764 * Q'.ofNat 168) * (D * D)) * (cap * B4) ≈
      (Q'.ofNat 168 * (D * D)) *
        ((Q'.ofNat 1764 * cap) * B4) := by
  ring_qeqv

private theorem secondShellCompile_step3
    (H L cap B4 : Q') :
    (Q'.ofNat 169 * (H * L)) *
        ((Q'.ofNat 1764 * cap) * B4) ≈
      ((Q'.ofNat 169 * cap) * (H * L)) *
        (Q'.ofNat 1764 * B4) := by
  ring_qeqv

private theorem secondShellCompile_step4
    (H L cap mid : Q') :
    ((Q'.ofNat 169 * cap) * (H * L)) *
        (Q'.ofNat 256 * (mid * mid)) ≈
      ((H * L) * (mid * mid)) *
        ((Q'.ofNat 169 * cap) * Q'.ofNat 256) := by
  ring_qeqv

private theorem secondShellCompile_step5
    (H L mid q : Q') :
    ((H * L) * (mid * mid)) * (secondShellCompileScale * q) ≈
      secondShellCompileScale * (q * ((H * L) * (mid * mid))) := by
  ring_qeqv

private theorem secondShellActual_left (D low high : Q') :
    (D * low) * (D * high) ≈ (D * D) * (low * high) := by
  ring_qeqv

private theorem secondShellActual_right (q H L mid : Q') :
    q * (H * mid) * (L * mid) ≈ q * ((H * L) * (mid * mid)) := by
  ring_qeqv

/-- Proof-about-computation assembly: the three envelopes and one closed
rational atom imply the full second-shell scalar fence. -/
theorem secondShellScalarFence_of_envelope (N : Nat)
    (E : SecondShellEnvelope N) : SecondShellScalarFence N := by
  let A := coeffW fenceW (N - 3)
  let X := coeffW fenceW (N - 2)
  let B := coeffW fenceW (N - 1)
  let C := coeffW fenceW N
  let low := secondShellLow A X B C
  let mid := secondShellMid X B C
  let high := secondShellHigh B C
  let D := dimQ (2 * N - 2)
  let H := dimQ (2 * N - 1)
  let L := dimQ (2 * N - 3)
  let q := RGTransport.qpow (p2RetunedWeight fenceW) 2
  let B4 := (B * B) * (B * B)
  let LH := low * high
  have hB0 : (0 : Q') ≤ B := coeffW_nonneg fenceW_nonneg (N - 1)
  have hB20 : (0 : Q') ≤ B * B := Q'.mul_nonneg _ _ hB0 hB0
  have hB40 : (0 : Q') ≤ B4 := Q'.mul_nonneg _ _ hB20 hB20
  have hD0 : (0 : Q') ≤ D := dimQ_nonneg _
  have hD20 : (0 : Q') ≤ D * D := Q'.mul_nonneg _ _ hD0 hD0
  have hHL0 : (0 : Q') ≤ H * L :=
    Q'.mul_nonneg _ _ (dimQ_nonneg _) (dimQ_nonneg _)
  have hmid0 : (0 : Q') ≤ mid :=
    secondShellMid_nonneg X B C
      (coeffW_nonneg fenceW_nonneg (N - 2)) hB0
      (coeffW_nonneg fenceW_nonneg N)
  have hmid20 : (0 : Q') ≤ mid * mid := Q'.mul_nonneg _ _ hmid0 hmid0
  have hcap0 : (0 : Q') ≤ secondShellLowCap9 := by decide
  have h1factor0 : (0 : Q') ≤
      (Q'.ofNat 1764 * Q'.ofNat 168) * (D * D) :=
    Q'.mul_nonneg _ _ (by decide) hD20
  have h1raw := Q'.mul_le_mul_of_nonneg_left _ _
    ((Q'.ofNat 1764 * Q'.ofNat 168) * (D * D))
    (by simpa only [A, X, B, C, low, high, B4, LH] using E.lowCap)
    h1factor0
  have h1 :
      secondShellCompileScale * ((D * D) * LH) ≤
        ((Q'.ofNat 1764 * Q'.ofNat 168) * (D * D)) *
          (secondShellLowCap9 * B4) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (secondShellCompile_step1 D LH)) h1raw
  have h2factor0 : (0 : Q') ≤
      (Q'.ofNat 1764 * secondShellLowCap9) * B4 :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hcap0) hB40
  have h2raw := Q'.mul_le_mul_of_nonneg_right _ _
    ((Q'.ofNat 1764 * secondShellLowCap9) * B4)
    (by simpa only [D, H, L] using E.dimFloor) h2factor0
  have h2 :
      ((Q'.ofNat 1764 * Q'.ofNat 168) * (D * D)) *
          (secondShellLowCap9 * B4) ≤
        (Q'.ofNat 169 * (H * L)) *
          ((Q'.ofNat 1764 * secondShellLowCap9) * B4) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (secondShellCompile_step2 D secondShellLowCap9 B4)) h2raw
  have h3factor0 : (0 : Q') ≤
      (Q'.ofNat 169 * secondShellLowCap9) * (H * L) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hcap0) hHL0
  have h3raw := Q'.mul_le_mul_of_nonneg_left _ _
    ((Q'.ofNat 169 * secondShellLowCap9) * (H * L))
    (by simpa only [X, B, C, mid, B4] using E.midFloor) h3factor0
  have h3 :
      (Q'.ofNat 169 * (H * L)) *
          ((Q'.ofNat 1764 * secondShellLowCap9) * B4) ≤
        ((Q'.ofNat 169 * secondShellLowCap9) * (H * L)) *
          (Q'.ofNat 256 * (mid * mid)) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (secondShellCompile_step3 H L secondShellLowCap9 B4)) h3raw
  have h4factor0 : (0 : Q') ≤ (H * L) * (mid * mid) :=
    Q'.mul_nonneg _ _ hHL0 hmid20
  have h4raw := Q'.mul_le_mul_of_nonneg_left _ _ ((H * L) * (mid * mid))
    (by simpa only [q] using secondShellClosedBalance) h4factor0
  have h4 :
      ((Q'.ofNat 169 * secondShellLowCap9) * (H * L)) *
          (Q'.ofNat 256 * (mid * mid)) ≤
        secondShellCompileScale * (q * ((H * L) * (mid * mid))) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (secondShellCompile_step4 H L secondShellLowCap9 mid))
      (Q'.le_trans' _ _ _ h4raw
        (Q'.le_of_eqv (secondShellCompile_step5 H L mid q)))
  have hscaled :
      secondShellCompileScale * ((D * D) * LH) ≤
        secondShellCompileScale * (q * ((H * L) * (mid * mid))) :=
    Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2
      (Q'.le_trans' _ _ _ h3 h4))
  have hscalePos : (0 : Q') < secondShellCompileScale := by decide
  have hcore : (D * D) * LH ≤ q * ((H * L) * (mid * mid)) :=
    FusionQuotientCollapse.le_of_mul_le_mul_left_pos hscalePos hscaled
  change (D * low) * (D * high) ≤ (q * (H * mid)) * (L * mid)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (secondShellActual_left D low high))
    (Q'.le_trans' _ _ _ hcore
      (Q'.le_of_eqv (Q'.eqv_symm (secondShellActual_right q H L mid))))

/-! ## The three physical envelopes -/

private theorem succ_mul_pred_square (m : Nat) (hm : 1 ≤ m) :
    (m + 1) * (m - 1) = m * m - 1 := by
  cases m with
  | zero => omega
  | succ k =>
      simp only [Nat.succ_sub_one, Nat.add_mul, Nat.mul_add]
      omega

/-- The dimension ratio is already within `168/169` of one from `N=7`
onward. -/
theorem secondShellDimFloor (N : Nat) (hN : 7 ≤ N) :
    Q'.ofNat 168 *
        (dimQ (2 * N - 2) * dimQ (2 * N - 2)) ≤
      Q'.ofNat 169 *
        (dimQ (2 * N - 1) * dimQ (2 * N - 3)) := by
  let d := (2 * N - 2) + 1
  let hi := (2 * N - 1) + 1
  let lo := (2 * N - 3) + 1
  have hd : d = 2 * N - 1 := by dsimp only [d]; omega
  have hhi : hi = (2 * N - 1) + 1 := rfl
  have hlo : lo = (2 * N - 1) - 1 := by dsimp only [lo]; omega
  have hd13 : 13 ≤ 2 * N - 1 := by omega
  have hsq169 : 169 ≤ (2 * N - 1) * (2 * N - 1) := by
    have hmul : 13 * 13 ≤ (2 * N - 1) * (2 * N - 1) :=
      Nat.mul_le_mul hd13 hd13
    exact hmul
  have hnat : 168 * (d * d) ≤ 169 * (hi * lo) := by
    rw [hd, hhi, hlo, succ_mul_pred_square (2 * N - 1) (by omega)]
    omega
  have hq := Q'.ofNat_le_ofNat hnat
  have hdd : Q'.ofNat d * Q'.ofNat d ≈ Q'.ofNat (d * d) :=
    FusionRDFactor.ofNat_mul_eqv d d
  have hleft :
      Q'.ofNat 168 * (Q'.ofNat d * Q'.ofNat d) ≈
        Q'.ofNat (168 * (d * d)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 168) _ _ hdd)
      (FusionRDFactor.ofNat_mul_eqv 168 (d * d))
  have hhl : Q'.ofNat hi * Q'.ofNat lo ≈ Q'.ofNat (hi * lo) :=
    FusionRDFactor.ofNat_mul_eqv hi lo
  have hright :
      Q'.ofNat 169 * (Q'.ofNat hi * Q'.ofNat lo) ≈
        Q'.ofNat (169 * (hi * lo)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 169) _ _ hhl)
      (FusionRDFactor.ofNat_mul_eqv 169 (hi * lo))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by simpa only [dimQ, d, hi, lo] using hleft))
    (Q'.le_trans' _ _ _ hq
      (Q'.le_of_eqv (Q'.eqv_symm
        (by simpa only [dimQ, d, hi, lo] using hright))))

private theorem secondShellTerminal_rearrange_left (C c6 : Q') :
    c6 * (Q'.ofNat 3 * C) ≈ Q'.ofNat 3 * (C * c6) := by
  ring_qeqv

private theorem secondShellTerminal_rearrange_right (B c6 : Q') :
    Q'.ofNat 3 *
        (Q'.mkPos 1 3 (by decide) * (B * c6)) ≈ c6 * B := by
  ring_qeqv

private theorem secondShellTerminal_third_rearrange (B c6 : Q') :
    B * (Q'.mkPos 1 3 (by decide) * c6) ≈
      Q'.mkPos 1 3 (by decide) * (B * c6) := by
  ring_qeqv

/-- The terminal heat ratio is at most one third from `N=7` onward.  A
single shifted Hankel ratio is combined with the exact closed cell
`3*c_7≤c_6`; no later coefficients are evaluated. -/
theorem secondShellTerminalRatio (N : Nat) (hN : 7 ≤ N) :
    Q'.ofNat 3 * coeffW fenceW N ≤ coeffW fenceW (N - 1) := by
  have hwp : (0 : Q') < fenceW := by decide
  have hcross :
      coeffW fenceW N * coeffW fenceW 6 ≤
        coeffW fenceW (N - 1) * coeffW fenceW 7 := by
    rcases Nat.eq_or_lt_of_le hN with rfl | h8
    · exact Q'.le_of_eqv (Q'.mul_comm_eqv _ _)
    · have h := coeffW_step fenceW_nonneg fenceW_le_one hwp 6 (N - 8)
      have eN : 6 + (N - 8) + 2 = N := by omega
      have ePrev : 6 + (N - 8) + 1 = N - 1 := by omega
      rw [eN, ePrev] at h
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  have hthird :
      coeffW fenceW 7 ≤
        Q'.mkPos 1 3 (by decide) * coeffW fenceW 6 := by
    apply coeffW_succ_le_of_cross 6 fenceW_nonneg
    decide
  have hB0 : (0 : Q') ≤ coeffW fenceW (N - 1) :=
    coeffW_nonneg fenceW_nonneg _
  have hthirdScaled := Q'.mul_le_mul_of_nonneg_left _ _
    (coeffW fenceW (N - 1)) hthird hB0
  have hcrossThird :
      coeffW fenceW N * coeffW fenceW 6 ≤
        Q'.mkPos 1 3 (by decide) *
          (coeffW fenceW (N - 1) * coeffW fenceW 6) := by
    exact Q'.le_trans' _ _ _ hcross
      (Q'.le_trans' _ _ _ hthirdScaled
        (Q'.le_of_eqv
          (secondShellTerminal_third_rearrange
            (coeffW fenceW (N - 1)) (coeffW fenceW 6))))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 3)
    hcrossThird (by decide)
  have hchain :
      coeffW fenceW 6 * (Q'.ofNat 3 * coeffW fenceW N) ≤
        coeffW fenceW 6 * coeffW fenceW (N - 1) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (secondShellTerminal_rearrange_left
          (coeffW fenceW N) (coeffW fenceW 6)))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv
          (secondShellTerminal_rearrange_right
            (coeffW fenceW (N - 1)) (coeffW fenceW 6))))
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    (FusionResidualBound.coeffW_pos hwp 6) hchain

private theorem secondShellMidScalar_left (T : Nat) :
    Q'.ofNat 9 * (Q'.ofNat 13 * Q'.ofNat T) ≈
      Q'.ofNat (117 * T) := by
  refine Q'.eqv_trans _ _ _ ?_ (FusionRDFactor.ofNat_mul_eqv 117 T)
  ring_qeqv

private theorem secondShellMidWeight :
    Q'.ofNat 9 * (Q'.ofNat 16 * secondShellW2) ≈ Q'.ofNat 121 := by
  decide

private theorem secondShellMidScalar_right (T : Nat) :
    Q'.ofNat 9 *
        (Q'.ofNat 16 * (Q'.ofNat T * secondShellW2)) ≈
      Q'.ofNat (121 * T) := by
  refine Q'.eqv_trans _
    ((Q'.ofNat 9 * (Q'.ofNat 16 * secondShellW2)) * Q'.ofNat T) _
    (by ring_qeqv) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.ofNat T) secondShellMidWeight)
    (FusionRDFactor.ofNat_mul_eqv 121 T)

private theorem secondShellMidCross_left (Nq B : Q') :
    (Q'.ofNat 13 * Nq) * (B * B) ≈
      Nq * (Q'.ofNat 13 * (B * B)) := by
  ring_qeqv

private theorem secondShellMidCross_right_start (Uq B : Q') :
    (Q'.ofNat 16 * (Uq * secondShellW2)) * (B * B) ≈
      Q'.ofNat 16 * (Uq * (secondShellW2 * (B * B))) := by
  ring_qeqv

private theorem secondShellMidCross_right_finish (Nq XC : Q') :
    Q'.ofNat 16 * (Nq * XC) ≈
      Nq * (Q'.ofNat 16 * XC) := by
  ring_qeqv

/-- Uniform lower Hankel ratio needed by the middle-shell square:
`13 B²≤16 X C`.  The exact Hankel identity reduces it to
`117N²≤121(N²-1)`, hence to `121≤4N²`. -/
theorem secondShellMidCrossLower (N : Nat) (hN : 7 ≤ N) :
    Q'.ofNat 13 *
        (coeffW fenceW (N - 1) * coeffW fenceW (N - 1)) ≤
      Q'.ofNat 16 *
        (coeffW fenceW (N - 2) * coeffW fenceW N) := by
  let T := N * N
  let U := N * N - 1
  have hNN : 7 * 7 ≤ N * N := Nat.mul_le_mul hN hN
  have hnat : 117 * T ≤ 121 * U := by
    dsimp only [T, U]
    omega
  have hqNat := Q'.ofNat_le_ofNat hnat
  have hscaledFactor :
      Q'.ofNat 9 * (Q'.ofNat 13 * Q'.ofNat T) ≤
        Q'.ofNat 9 *
          (Q'.ofNat 16 * (Q'.ofNat U * secondShellW2)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (secondShellMidScalar_left T))
      (Q'.le_trans' _ _ _ hqNat
        (Q'.le_of_eqv (Q'.eqv_symm (secondShellMidScalar_right U))))
  have hfactor :
      Q'.ofNat 13 * Q'.ofNat T ≤
        Q'.ofNat 16 * (Q'.ofNat U * secondShellW2) :=
    FusionQuotientCollapse.le_of_mul_le_mul_left_pos
      (by decide : (0 : Q') < Q'.ofNat 9) hscaledFactor
  let B := coeffW fenceW (N - 1)
  let XC := coeffW fenceW (N - 2) * coeffW fenceW N
  have hB0 : (0 : Q') ≤ B := coeffW_nonneg fenceW_nonneg _
  have hB20 : (0 : Q') ≤ B * B := Q'.mul_nonneg _ _ hB0 hB0
  have hfactorScaled := Q'.mul_le_mul_of_nonneg_right _ _ (B * B)
    hfactor hB20
  have hhankel0 := coeffW_hankel_exact (w := fenceW) (N - 2)
  have hdim : (N - 1) * (N + 1) = U := by
    unfold U
    rw [Nat.mul_comm]
    exact succ_mul_pred_square N (by omega)
  have e0 : N - 2 + 2 = N := by omega
  have e1 : N - 2 + 1 = N - 1 := by omega
  have e3 : N - 2 + 3 = N + 1 := by omega
  rw [e0, e1, e3, hdim] at hhankel0
  have hhankel : Q'.ofNat T * XC ≈
      Q'.ofNat U * (secondShellW2 * (B * B)) := by
    refine Q'.eqv_trans _ _ _ (by simpa only [T, U, B, XC] using hhankel0) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat U) _ _
      (Q'.mul_eqv_congr_right _ _ (B * B)
        (Q'.eqv_symm secondShellW2_eqv))
  have hchain :
      Q'.ofNat T * (Q'.ofNat 13 * (B * B)) ≤
        Q'.ofNat T * (Q'.ofNat 16 * XC) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (secondShellMidCross_left (Q'.ofNat T) B))) ?_
    refine Q'.le_trans' _ _ _ hfactorScaled ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (secondShellMidCross_right_start (Q'.ofNat U) B)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat 16) _ _
        (Q'.eqv_symm hhankel))) ?_
    exact Q'.le_of_eqv (secondShellMidCross_right_finish (Q'.ofNat T) XC)
  have hTpos : (0 : Q') < Q'.ofNat T := by
    simpa only [T, show N * N - 1 + 1 = N * N by omega] using
      (Q'.ofNat_succ_pos (N * N - 1))
  simpa only [B, XC] using
    (FusionQuotientCollapse.le_of_mul_le_mul_left_pos hTpos hchain)

private theorem mul_le_mul_nonneg {a b c d : Q'}
    (hab : a ≤ b) (hcd : c ≤ d) (hc : (0 : Q') ≤ c)
    (hb : (0 : Q') ≤ b) : a * c ≤ b * d :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

private theorem secondShellFarCrossUpper (N : Nat) (hN : 3 ≤ N) :
    coeffW fenceW (N - 3) * coeffW fenceW N ≤
      secondShellW4 *
        (coeffW fenceW (N - 2) * coeffW fenceW (N - 1)) := by
  have h := coeffW_rect_graded_wsq (w := fenceW) (by decide) 1 2 (N - 3)
  have e0 : N - 3 + 1 = N - 2 := by omega
  have e1 : N - 3 + 2 = N - 1 := by omega
  have e2 : N - 2 + 2 = N := by omega
  rw [e0, e1, e2] at h
  have hp : RGTransport.qpow (RGTransport.qpow fenceW 2) (1 * 2) ≈
      secondShellW4 := by decide
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hp))

private theorem secondShellNearCrossUpper (N : Nat) (hN : 3 ≤ N) :
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

private theorem two_mul_eqv_local (z : Q') :
    Q'.ofNat 2 * z ≈ z + z := by
  have h : Q'.ofNat 2 ≈ (1 : Q') + 1 := by decide
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ z h)
    (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 z)
      (Q'.add_eqv_congr' (Q'.one_mul_eqv z) (Q'.one_mul_eqv z)))

private theorem secondShellLow_expand (P Q R : Q') :
    Q'.ofNat 9 *
        ((((P + P) + ((Q + R) + (Q + R))) * (R + R))) ≈
      Q'.ofNat 4 *
        ((Q'.ofNat 9 * (P * R) + Q'.ofNat 9 * (Q * R)) +
          Q'.ofNat 9 * (R * R)) := by
  let S := P + (Q + R)
  have hlow0 : (P + P) + ((Q + R) + (Q + R)) ≈ S + S := by
    dsimp only [S]
    ring_qeqv
  have hlow : (P + P) + ((Q + R) + (Q + R)) ≈ Q'.ofNat 2 * S :=
    Q'.eqv_trans _ _ _ hlow0 (Q'.eqv_symm (two_mul_eqv_local S))
  have hhigh : R + R ≈ Q'.ofNat 2 * R :=
    Q'.eqv_symm (two_mul_eqv_local R)
  have hprod :
      Q'.ofNat 9 *
          (((P + P) + ((Q + R) + (Q + R))) * (R + R)) ≈
        Q'.ofNat 9 * ((Q'.ofNat 2 * S) * (Q'.ofNat 2 * R)) :=
    Q'.mul_eqv_congr_left _ _ _ (mul_eqv_both hlow hhigh)
  have hregroup :
      Q'.ofNat 9 * ((Q'.ofNat 2 * S) * (Q'.ofNat 2 * R)) ≈
        (Q'.ofNat 2 * Q'.ofNat 2) * (Q'.ofNat 9 * (S * R)) := by
    ring_qeqv
  have hfour : Q'.ofNat 2 * Q'.ofNat 2 ≈ Q'.ofNat 4 := by decide
  have hfourScaled :
      (Q'.ofNat 2 * Q'.ofNat 2) * (Q'.ofNat 9 * (S * R)) ≈
        Q'.ofNat 4 * (Q'.ofNat 9 * (S * R)) :=
    Q'.mul_eqv_congr_right _ _ _ hfour
  have hdist :
      Q'.ofNat 9 * (S * R) ≈
        (Q'.ofNat 9 * (P * R) + Q'.ofNat 9 * (Q * R)) +
          Q'.ofNat 9 * (R * R) := by
    dsimp only [S]
    ring_qeqv
  exact Q'.eqv_trans _ _ _ hprod
    (Q'.eqv_trans _ _ _ hregroup
      (Q'.eqv_trans _ _ _ hfourScaled
        (Q'.mul_eqv_congr_left _ _ _ hdist)))

private theorem secondShellCap_expand (B4 : Q') :
    Q'.ofNat 4 *
        ((Q'.ofNat 9 * (secondShellW2 * B4) +
          Q'.ofNat 9 * ((secondShellW4 * secondShellW2) * B4)) + B4) ≈
      secondShellLowCap9 * B4 := by
  unfold secondShellLowCap9
  ring_qeqv

/-- Cancellation-free algebraic compiler for the low/high shell product. -/
private theorem secondShellLowCap_of_atoms (A X B C : Q')
    (hA : (0 : Q') ≤ A) (hX : (0 : Q') ≤ X)
    (hB : (0 : Q') ≤ B) (hC : (0 : Q') ≤ C)
    (hAC : A * C ≤ secondShellW4 * (X * B))
    (hXC : X * C ≤ secondShellW2 * (B * B))
    (hterm : Q'.ofNat 3 * C ≤ B) :
    Q'.ofNat 9 *
        (secondShellLow A X B C * secondShellHigh B C) ≤
      secondShellLowCap9 * ((B * B) * (B * B)) := by
  let P := X * B
  let Q := A * C
  let R := B * C
  let B2 := B * B
  let B4 := B2 * B2
  have hP0 : (0 : Q') ≤ P := Q'.mul_nonneg _ _ hX hB
  have hQ0 : (0 : Q') ≤ Q := Q'.mul_nonneg _ _ hA hC
  have hR0 : (0 : Q') ≤ R := Q'.mul_nonneg _ _ hB hC
  have hB20 : (0 : Q') ≤ B2 := Q'.mul_nonneg _ _ hB hB
  have hW40 : (0 : Q') ≤ secondShellW4 := by decide
  have hPRraw := Q'.mul_le_mul_of_nonneg_right _ _ B2 hXC hB20
  have hPR : P * R ≤ secondShellW2 * B4 := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      dsimp only [P, R, B2]
      ring_qeqv))
      (Q'.le_trans' _ _ _ hPRraw (Q'.le_of_eqv (by
        dsimp only [B2, B4]
        ring_qeqv)))
  have hQR0 := Q'.mul_le_mul_of_nonneg_right _ _ R hAC hR0
  have hWPR := Q'.mul_le_mul_of_nonneg_left _ _ secondShellW4 hPR hW40
  have hQR : Q * R ≤ (secondShellW4 * secondShellW2) * B4 := by
    exact Q'.le_trans' _ _ _ hQR0
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
        dsimp only [P]
        ring_qeqv))
        (Q'.le_trans' _ _ _ hWPR (Q'.le_of_eqv (by ring_qeqv))))
  have h3C0 : (0 : Q') ≤ Q'.ofNat 3 * C :=
    Q'.mul_nonneg _ _ (by decide) hC
  have htermSq := mul_le_mul_nonneg hterm hterm h3C0 hB
  have hR9raw := Q'.mul_le_mul_of_nonneg_left _ _ B2 htermSq hB20
  have hR9 : Q'.ofNat 9 * (R * R) ≤ B4 := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by
      dsimp only [R, B2]
      ring_qeqv))
      (Q'.le_trans' _ _ _ hR9raw (Q'.le_of_eqv (Q'.eqv_refl _)))
  have h9PR := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 9) hPR (by decide)
  have h9QR := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 9) hQR (by decide)
  have hsum := Q'.add_le_add (Q'.add_le_add h9PR h9QR) hR9
  have hsum4 := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hsum (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by
      simpa only [secondShellLow, secondShellHigh, P, Q, R] using
        secondShellLow_expand P Q R))
    (Q'.le_trans' _ _ _ hsum4
      (Q'.le_of_eqv (secondShellCap_expand B4)))

/-- The low/high envelope, valid uniformly once the terminal ratio starts. -/
theorem secondShellLowCap (N : Nat) (hN : 7 ≤ N) :
    let A := coeffW fenceW (N - 3)
    let X := coeffW fenceW (N - 2)
    let B := coeffW fenceW (N - 1)
    let C := coeffW fenceW N
    Q'.ofNat 9 *
        (secondShellLow A X B C * secondShellHigh B C) ≤
      secondShellLowCap9 * ((B * B) * (B * B)) := by
  dsimp only
  exact secondShellLowCap_of_atoms _ _ _ _
    (coeffW_nonneg fenceW_nonneg _)
    (coeffW_nonneg fenceW_nonneg _)
    (coeffW_nonneg fenceW_nonneg _)
    (coeffW_nonneg fenceW_nonneg _)
    (secondShellFarCrossUpper N (by omega))
    (secondShellNearCrossUpper N (by omega))
    (secondShellTerminalRatio N hN)

private theorem secondShellLinearLeft (B2 : Q') :
    Q'.ofNat 42 * B2 ≈
      Q'.ofNat 16 * B2 + Q'.ofNat 2 * (Q'.ofNat 13 * B2) := by
  have hc : Q'.ofNat 42 ≈
      Q'.ofNat 16 + Q'.ofNat 2 * Q'.ofNat 13 := by decide
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ B2 hc) (by ring_qeqv)

private theorem secondShellLinearRight (B2 XC : Q') :
    Q'.ofNat 16 * B2 + Q'.ofNat 2 * (Q'.ofNat 16 * XC) ≈
      Q'.ofNat 16 * (B2 + (XC + XC)) := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (two_mul_eqv_local (Q'.ofNat 16 * XC)))
    (by ring_qeqv)

private theorem secondShellMidSquareLeft (B2 : Q') :
    Q'.ofNat 1764 * (B2 * B2) ≈
      (Q'.ofNat 42 * B2) * (Q'.ofNat 42 * B2) := by
  have hc : Q'.ofNat 1764 ≈ Q'.ofNat 42 * Q'.ofNat 42 := by decide
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (B2 * B2) hc) (by ring_qeqv)

private theorem secondShellMidSquareRight (mid : Q') :
    (Q'.ofNat 16 * mid) * (Q'.ofNat 16 * mid) ≈
      Q'.ofNat 256 * (mid * mid) := by
  have hc : Q'.ofNat 16 * Q'.ofNat 16 ≈ Q'.ofNat 256 := by decide
  exact Q'.eqv_trans _ _ _ (by ring_qeqv)
    (Q'.mul_eqv_congr_right _ _ (mid * mid) hc)

/-- Algebraic compiler for the middle-shell square. -/
private theorem secondShellMidFloor_of_cross (X B C : Q')
    (hX : (0 : Q') ≤ X) (hB : (0 : Q') ≤ B)
    (hC : (0 : Q') ≤ C)
    (hcross : Q'.ofNat 13 * (B * B) ≤
      Q'.ofNat 16 * (X * C)) :
    Q'.ofNat 1764 * ((B * B) * (B * B)) ≤
      Q'.ofNat 256 *
        (secondShellMid X B C * secondShellMid X B C) := by
  let B2 := B * B
  let XC := X * C
  let mid := secondShellMid X B C
  have hB20 : (0 : Q') ≤ B2 := Q'.mul_nonneg _ _ hB hB
  have hmid0 : (0 : Q') ≤ mid := secondShellMid_nonneg X B C hX hB hC
  have hcross' : Q'.ofNat 13 * B2 ≤ Q'.ofNat 16 * XC := by
    simpa only [B2, XC] using hcross
  have h2cross := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hcross' (by decide)
  have hbase := Q'.add_le_add (Q'.le_refl' (Q'.ofNat 16 * B2)) h2cross
  have hlinear0 :
      Q'.ofNat 42 * B2 ≤
        Q'.ofNat 16 * (B2 + (XC + XC)) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (secondShellLinearLeft B2))
      (Q'.le_trans' _ _ _ hbase
        (Q'.le_of_eqv (secondShellLinearRight B2 XC)))
  have hXCtail : XC ≤ XC + C * C :=
    Q'.add_le_self_of_nonneg _ _ (Q'.mul_nonneg _ _ hC hC)
  have htail0 : B2 + (XC + XC) ≤ B2 + (XC + (XC + C * C)) :=
    Q'.add_le_add_left _ _ _ (Q'.add_le_add_left _ _ _ hXCtail)
  have htail : B2 + (XC + XC) ≤ mid := by
    simpa only [B2, XC, mid, secondShellMid] using htail0
  have hlinear : Q'.ofNat 42 * B2 ≤ Q'.ofNat 16 * mid :=
    Q'.le_trans' _ _ _ hlinear0
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 16) htail (by decide))
  have hleft0 : (0 : Q') ≤ Q'.ofNat 42 * B2 :=
    Q'.mul_nonneg _ _ (by decide) hB20
  have hright0 : (0 : Q') ≤ Q'.ofNat 16 * mid :=
    Q'.mul_nonneg _ _ (by decide) hmid0
  have hsq := mul_le_mul_nonneg hlinear hlinear hleft0 hright0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (secondShellMidSquareLeft B2))
    (Q'.le_trans' _ _ _ hsq
      (Q'.le_of_eqv (secondShellMidSquareRight mid)))

/-- The middle-square envelope from the exact uniform lower Hankel ratio. -/
theorem secondShellMidFloor (N : Nat) (hN : 7 ≤ N) :
    let X := coeffW fenceW (N - 2)
    let B := coeffW fenceW (N - 1)
    let C := coeffW fenceW N
    Q'.ofNat 1764 * ((B * B) * (B * B)) ≤
      Q'.ofNat 256 *
        (secondShellMid X B C * secondShellMid X B C) := by
  dsimp only
  exact secondShellMidFloor_of_cross _ _ _
    (coeffW_nonneg fenceW_nonneg _)
    (coeffW_nonneg fenceW_nonneg _)
    (coeffW_nonneg fenceW_nonneg _)
    (secondShellMidCrossLower N hN)

/-- All three physical envelopes for every cutoff `N≥7`. -/
def secondShellEnvelope (N : Nat) (hN : 7 ≤ N) : SecondShellEnvelope N where
  lowCap := secondShellLowCap N hN
  midFloor := secondShellMidFloor N hN
  dimFloor := secondShellDimFloor N hN

theorem secondShellScalarFence_four : SecondShellScalarFence 4 := by
  unfold SecondShellScalarFence secondShellLow secondShellMid secondShellHigh
  decide

theorem secondShellScalarFence_five : SecondShellScalarFence 5 := by
  unfold SecondShellScalarFence secondShellLow secondShellMid secondShellHigh
  decide

theorem secondShellScalarFence_six : SecondShellScalarFence 6 := by
  unfold SecondShellScalarFence secondShellLow secondShellMid secondShellHigh
  decide

/-- The second-shell scalar fence for every physical cutoff.  Only the four
closed cells `N=3,4,5,6` are evaluated; all later cutoffs use the symbolic
three-envelope compiler. -/
theorem secondShellScalarFence_all (N : Nat) (hN : 3 ≤ N) :
    SecondShellScalarFence N := by
  by_cases h7 : 7 ≤ N
  · exact secondShellScalarFence_of_envelope N (secondShellEnvelope N h7)
  · have hcases : N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact secondShellScalarFence_three
    · exact secondShellScalarFence_four
    · exact secondShellScalarFence_five
    · exact secondShellScalarFence_six

/-- The actual physical `s=2N-3` strong-Turan atom, uniformly in `N`. -/
theorem fenceSecondShellTuran (N : Nat) (hN : 3 ≤ N) :
    (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 3)) *
        (dimQ (2 * N - 2) * boxSum fenceW N (2 * N - 1)) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (2 * N - 1) * boxSum fenceW N (2 * N - 2))) *
        (dimQ (2 * N - 3) * boxSum fenceW N (2 * N - 2)) :=
  fenceSecondShellTuran_of_scalar N hN (secondShellScalarFence_all N hN)

/-- Residual strong-Turan family after the top two physical boundary shells
have both been discharged.  Its support is now `s+4≤2N`. -/
def FenceBoxDeepInteriorTuranTail (N : Nat) : Prop :=
  forall s, 1 ≤ s -> s + 4 ≤ 2 * N ->
    (dimQ (s + 1) * boxSum fenceW N s) *
        (dimQ (s + 1) * boxSum fenceW N (s + 2)) ≤
      (RGTransport.qpow (p2RetunedWeight fenceW) 2 *
          (dimQ (s + 2) * boxSum fenceW N (s + 1))) *
        (dimQ s * boxSum fenceW N (s + 1))

/-- Fill `s=2N-3` by the all-cutoff physical theorem and leave only the
deep-interior family to the caller. -/
def fenceBoxInteriorTuranTailOfDeep (N : Nat) (hN : 3 ≤ N)
    (deep : FenceBoxDeepInteriorTuranTail N) : FenceBoxInteriorTuranTail N := by
  intro s hs hsupport
  by_cases hsecond : s = 2 * N - 3
  · subst s
    simpa only [show 2 * N - 3 + 1 = 2 * N - 2 by omega,
      show 2 * N - 3 + 2 = 2 * N - 1 by omega] using
      (fenceSecondShellTuran N hN)
  · exact deep s hs (by omega)

/-- Reviewed `CanonicalBulkControl` repoint after the second-shell close.
The only remaining consumer premise is the physical deep interior. -/
def fenceCanonicalBulkControlOfDeepInterior (N : Nat) (hN : 3 ≤ N)
    (deep : FenceBoxDeepInteriorTuranTail N) : CanonicalBulkControl N fenceW 2 :=
  fenceCanonicalBulkControlOfInterior N (by omega)
    (fenceBoxInteriorTuranTailOfDeep N hN deep)

end YMGap.Continuum.P2RetunedFenceSecondShell

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.boxSumDelta_top_three
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.boxSum_top_three
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.fenceSecondShellTuran_of_scalar
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellScalarFence_three
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellClosedBalance
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellW2_eqv
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellW4_eqv
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellScalarFence_of_envelope
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellDimFloor
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellTerminalRatio
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellMidCrossLower
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellLowCap
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellMidFloor
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellEnvelope
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellScalarFence_four
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellScalarFence_five
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellScalarFence_six
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.secondShellScalarFence_all
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.fenceSecondShellTuran
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.fenceBoxInteriorTuranTailOfDeep
#print axioms YMGap.Continuum.P2RetunedFenceSecondShell.fenceCanonicalBulkControlOfDeepInterior
