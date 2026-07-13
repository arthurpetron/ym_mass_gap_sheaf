/-
Exact structural fence for the failure of uniform terminal-carrier dominance
at harmonic scale 17.  The proof avoids reduction of the full 361-coordinate
rational by using an exact eight-coordinate head and PF2 tail transport.
-/

import YMGap.Continuum.HarmonicWeightedAbelReserve
import YMGap.Continuum.HarmonicFixedSixFloorK17
import YMGap.Continuum.HarmonicThetaRatioExtension
import YMGap.Continuum.HarmonicGrowingAnchorPF2
import YMGap.Continuum.AbelianFusionCLT
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.HarmonicCarrierGapK17Fence

set_option maxHeartbeats 1200000
set_option maxRecDepth 5000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFixedSixFloorK17
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicHalfEdgeDominance
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv
private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

def rate17 : Q' := Q'.mkPos 221 240 (by decide)

private def c17 (i : Nat) : Q' := coeffW (harmW 17) i

/-- The exact eight-coordinate head already has the required ratio. -/
theorem head_ratio17 :
    adjCorr (harmW 17) 9 ≤ rate17 * coordNormSq (harmW 17) 8 := by
  unfold rate17 harmW harmU ReciprocalBernoulliUpper.oneSub unit
    adjCorr coordNormSq coeffW dimQ c4 qpow fsum
  decide

/-- The first omitted coefficient ratio is below the same rational rate. -/
theorem tail_ratio17 : c17 9 ≤ rate17 * c17 8 := by
  unfold rate17 c17 harmW harmU ReciprocalBernoulliUpper.oneSub unit
    coeffW dimQ c4 qpow
  decide

theorem tail_step17 {a : Nat} (ha : 8 ≤ a) :
    c17 (a + 1) ≤ rate17 * c17 a := by
  by_cases heq : a = 8
  · subst a
    exact tail_ratio17
  · have hlt : 8 < a := Nat.lt_of_le_of_ne ha (Ne.symm heq)
    have hinj := CutoffCorrelationMonotone.shifted_ratio_injection
      (harmW_nonneg 17) (harmW_le_one 17) (harmW_pos 17)
      (a := 8) (N := a) hlt
    have hca0 := coeffW_nonneg (harmW_nonneg 17) a
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ (c17 a) tail_ratio17 hca0
    have hchain : c17 8 * c17 (a + 1) ≤
        c17 8 * (rate17 * c17 a) := by
      exact Q'.le_trans' _ _ _ hinj
        (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv (by
          exact Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
            (Q'.mul_assoc_eqv _ _ _))))
    exact Q'.le_of_mul_le_mul_left hchain
      (FusionResidualBound.coeffW_pos (harmW_pos 17) 8)

private def edgeTail17 (j : Nat) : Q' := c17 (9 + j) * c17 (9 + j + 1)
private def squareTail17 (j : Nat) : Q' := c17 (9 + j) * c17 (9 + j)

private theorem tail_sum17 (M : Nat) :
    fsum edgeTail17 M ≤ rate17 * fsum squareTail17 M := by
  have ht : ∀ j, edgeTail17 j ≤ rate17 * squareTail17 j := by
    intro j
    unfold edgeTail17 squareTail17
    have hs := tail_step17 (a := 9 + j) (by omega)
    have hc0 := coeffW_nonneg (harmW_nonneg 17) (9 + j)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hs hc0)
      (Q'.le_of_eqv (by
        unfold c17
        ring_qeqv))
  have hsum := CubeRatioBounds.fsum_mono_lt M (fun j _ => ht j)
  have hpull := CubeRatioBounds.fsum_const_mul rate17 squareTail17 M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hpull)

theorem global_ratio17 (M : Nat) :
    adjCorr (harmW 17) (9 + M) ≤
      rate17 * coordNormSq (harmW 17) (9 + M) := by
  have hA : adjCorr (harmW 17) (9 + M) ≈
      adjCorr (harmW 17) 9 + fsum edgeTail17 M := by
    unfold adjCorr edgeTail17 c17
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW (harmW 17) a * coeffW (harmW 17) (a + 1)) 9 M
  have hD : coordNormSq (harmW 17) (9 + M) ≈
      coordNormSq (harmW 17) 8 + fsum squareTail17 (M + 1) := by
    unfold coordNormSq squareTail17 c17
    rw [show 9 + M + 1 = 9 + (M + 1) by omega]
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW (harmW 17) a * coeffW (harmW 17) a) 9 (M + 1)
  have hs0 : ∀ j, (0 : Q') ≤ squareTail17 j := by
    intro j
    unfold squareTail17 c17
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg 17) (9 + j))
      (coeffW_nonneg (harmW_nonneg 17) (9 + j))
  have htail : fsum squareTail17 M ≤ fsum squareTail17 (M + 1) :=
    AFRateCalibration.fsum_le_of_le hs0 (by omega)
  have hprefix : coordNormSq (harmW 17) 8 + fsum squareTail17 M ≤
      coordNormSq (harmW 17) (9 + M) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left (coordNormSq (harmW 17) 8) _ _ htail)
      (Q'.ge_of_eqv hD)
  have hpaid := Q'.add_le_add head_ratio17 (tail_sum17 M)
  have hcollect : rate17 * coordNormSq (harmW 17) 8 +
      rate17 * fsum squareTail17 M ≈
      rate17 * (coordNormSq (harmW 17) 8 + fsum squareTail17 M) :=
    Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
    (Q'.le_trans' _ _ _ hpaid
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
        (Q'.mul_le_mul_of_nonneg_left _ _ rate17 hprefix (by decide))))

theorem harmonicA_le_rate17_D :
    harmonicA 17 ≤ rate17 * harmonicD 17 := by
  have h9 : 9 ≤ Ncut 17 := by
    unfold Ncut
    omega
  have h := global_ratio17 (Ncut 17 - 9)
  have heq : 9 + (Ncut 17 - 9) = Ncut 17 := Nat.add_sub_of_le h9
  rw [heq] at h
  simpa [harmonicA, harmonicD] using h

theorem D17_lower : Q'.mkPos 277 20 (by decide) ≤ harmonicD 17 := by
  have hp : Q'.mkPos 277 20 (by decide) ≤ coordNormSq (harmW 17) 7 := by
    unfold coordNormSq harmW harmU ReciprocalBernoulliUpper.oneSub unit
      coeffW dimQ c4 qpow fsum
    decide
  have hmono : coordNormSq (harmW 17) 7 ≤ harmonicD 17 := by
    unfold coordNormSq harmonicD
    apply AFRateCalibration.fsum_le_of_le
    · intro i
      exact Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 17) i)
        (coeffW_nonneg (harmW_nonneg 17) i)
    · unfold Ncut
      omega
  exact Q'.le_trans' _ _ _ hp hmono

private theorem c17_succ_le {a : Nat} (ha : 8 ≤ a) : c17 (a + 1) ≤ c17 a := by
  have hs := tail_step17 ha
  have hc0 := coeffW_nonneg (harmW_nonneg 17) a
  have hr : rate17 ≤ (1 : Q') := by unfold rate17; decide
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (c17 a) hr hc0
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv _)))

private theorem c17_antitone_from {a : Nat} (ha : 8 ≤ a) :
    ∀ b, a ≤ b → c17 b ≤ c17 a
  | 0, hab => by omega
  | b + 1, hab => by
      by_cases heq : a = b + 1
      · subst a
        exact Q'.le_refl' _
      · have hab' : a ≤ b := by omega
        exact Q'.le_trans' _ _ _ (c17_succ_le (a := b) (by omega))
          (c17_antitone_from ha b hab')

theorem terminalCoeff17_le :
    c17 (Ncut 17) ≤ Q'.mkPos 1 50 (by decide) := by
  let w := harmW 17
  let half := Q'.mkPos 1 2 (by decide)
  have hpow0 : (0 : Q') ≤ qpow w 19 := qpow_nonneg _ (harmW_nonneg 17) 19
  have hblock : qpow w 19 ≤ half := by
    simpa [w, half] using harmonic_block_power_le_half 17
  have hiter : qpow w (19 * 10) ≈ qpow (qpow w 19) 10 :=
    AbelianFusionCLT.qpowR_exp_mul w 19 10
  have hshort : qpow w (c4 14) ≤ qpow w (19 * 10) := by
    apply HeatKernelRGStep.qpow_antitone (harmW_nonneg 17) (harmW_le_one 17)
    unfold c4
    omega
  have hbase : qpow (qpow w 19) 10 ≤ qpow half 10 :=
    HeatKernelGap.qpow_mono hpow0 hblock 10
  have hp : qpow w (c4 14) ≤ qpow half 10 :=
    Q'.le_trans' _ _ _ hshort
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hiter) hbase)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 15) hp (by decide)
  have ha : c17 14 ≤ Q'.mkPos 1 50 (by decide) := by
    unfold c17 coeffW dimQ
    have hs : Q'.ofNat 15 * qpow (harmW 17) (c4 14) ≤
        Q'.ofNat 15 * qpow half 10 := by
      simpa [w] using hscale
    exact Q'.le_trans' _ _ _ hs (by unfold half qpow; decide)
  have ht := c17_antitone_from (a := 14) (by decide) (Ncut 17) (by
    unfold Ncut
    omega)
  exact Q'.le_trans' _ _ _ ht ha

private theorem add_sub_cancel_right (a b : Q') : (a + b) + (-b) ≈ a := by
  refine Q'.eqv_trans _ (a + (b + (-b))) _ (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv b)) ?_
  exact QPoly.q_add_zero_eqv a

private def gapAlgL : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let D := RingNormaliser.PolyExpr.var 1
  let l := RingNormaliser.PolyExpr.var 2
  let e0 := RingNormaliser.PolyExpr.var 3
  let eL := RingNormaliser.PolyExpr.var 4
  let d0 := RingNormaliser.PolyExpr.var 5
  let dN := RingNormaliser.PolyExpr.var 6
  let B := .add (.add A (.mul l D)) (.add A (.mul l D))
  .add
    (.add
      (.mul D (.add (.add (.add A (.neg eL)) (.add A (.neg eL))) eL))
      (.neg (.mul B (.add D (.neg dN)))))
    (.neg (.add (.mul D e0) (.neg (.mul B d0))))

private def gapAlgR : RingNormaliser.PolyExpr :=
  let A := RingNormaliser.PolyExpr.var 0
  let D := RingNormaliser.PolyExpr.var 1
  let l := RingNormaliser.PolyExpr.var 2
  let e0 := RingNormaliser.PolyExpr.var 3
  let eL := RingNormaliser.PolyExpr.var 4
  let d0 := RingNormaliser.PolyExpr.var 5
  let dN := RingNormaliser.PolyExpr.var 6
  let B := .add (.add A (.mul l D)) (.add A (.mul l D))
  .add
    (.add (.add (.mul B d0) (.mul B dN))
      (.neg (.mul D (.add e0 eL))))
    (.neg (.mul (.add l l) (.mul D D)))

private theorem gapAlg_normal :
    RingNormaliser.normalize gapAlgL = RingNormaliser.normalize gapAlgR := by
  decide

private theorem total_gap_algebra (A D lam e0 eL d0 dN : Q') :
    let B := (A + lam * D) + (A + lam * D)
    D * ((A + (-eL)) + (A + (-eL)) + eL) +
        -(B * (D + (-dN))) + -(D * e0 + -(B * d0)) ≈
      (B * d0 + B * dN) + -(D * (e0 + eL)) +
        -((lam + lam) * (D * D)) := by
  dsimp only
  let ρ : Nat → Q' := fun
    | 0 => A
    | 1 => D
    | 2 => lam
    | 3 => e0
    | 4 => eL
    | 5 => d0
    | _ => dN
  have h := RingNormaliser.poly_identity_of_normal_eq
    gapAlgL gapAlgR gapAlg_normal ρ
  simpa [RingNormaliser.eval, gapAlgL, gapAlgR, ρ, qpow] using h

/-- Exact endpoint-slack identity for the total carrier change. -/
theorem carrier_total_gap_eq_slack (k : Nat) :
    let N := Ncut k
    let L := N - 1
    let D := harmonicD k
    let A := harmonicA k
    let lam := twoInvSq k
    let B := (A + lam * D) + (A + lam * D)
    trapezoidNodeCumulative k L + -(trapezoidNodeCumulative k 0) ≈
      (B * oldDiag k 0 + B * oldDiag k N) +
        -(D * (oldAdj k 0 + oldAdj k L)) +
        -((lam + lam) * (D * D)) := by
  dsimp only
  let N := Ncut k
  let L := N - 1
  let D := harmonicD k
  let A := harmonicA k
  let lam := twoInvSq k
  let B := (A + lam * D) + (A + lam * D)
  have hN : 1 ≤ N := by
    unfold N Ncut
    exact Nat.mul_pos (by omega) (by omega)
  have hLN : L + 1 = N := Nat.sub_add_cancel hN
  unfold N at hLN
  have hAraw : A ≈ adjCorr (harmW k) L + oldAdj k L := by
    unfold A harmonicA oldAdj
    rw [← hLN]
    exact AllWindowCorrDirichlet.adjCorr_succ (harmW k) L
  have hDraw : D ≈ coordNormSq (harmW k) L + oldDiag k N := by
    unfold D harmonicD oldDiag coordNormSq
    rw [← hLN]
    simp only [fsum_succ]
    exact Q'.eqv_refl _
  have hAL : adjCorr (harmW k) L ≈ A + -(oldAdj k L) := by
    refine Q'.eqv_trans _ ((adjCorr (harmW k) L + oldAdj k L) +
      -(oldAdj k L)) _ (Q'.eqv_symm (add_sub_cancel_right _ _)) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hAraw)
  have hDL : coordNormSq (harmW k) L ≈ D + -(oldDiag k N) := by
    refine Q'.eqv_trans _ ((coordNormSq (harmW k) L + oldDiag k N) +
      -(oldDiag k N)) _ (Q'.eqv_symm (add_sub_cancel_right _ _)) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hDraw)
  unfold trapezoidNodeCumulative
  have hreplace :
      D * (adjCorr (harmW k) L + adjCorr (harmW k) L + oldAdj k L) +
          -(B * coordNormSq (harmW k) L) +
          -(D * (adjCorr (harmW k) 0 + adjCorr (harmW k) 0 + oldAdj k 0) +
            -(B * coordNormSq (harmW k) 0)) ≈
        D * ((A + -(oldAdj k L)) + (A + -(oldAdj k L)) + oldAdj k L) +
          -(B * (D + -(oldDiag k N))) +
          -(D * (adjCorr (harmW k) 0 + adjCorr (harmW k) 0 + oldAdj k 0) +
            -(B * coordNormSq (harmW k) 0)) := by
    refine Q'.add_eqv_congr_right _ _ _ ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.mul_eqv_congr_left D _ _
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' hAL hAL) (Q'.eqv_refl _))
    · exact Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left B _ _ hDL)
  refine Q'.eqv_trans _ _ _ hreplace ?_
  unfold oldAdj oldDiag
  rw [hLN]
  dsimp only [A, D, lam, B, N, L]
  simp only [adjCorr, coordNormSq, fsum_succ, fsum_zero, Q'.zero_add',
    coeffW_zero]
  exact total_gap_algebra _ _ _ _ _ _ _

private def bracket17 : Q' :=
  let lam := twoInvSq 17
  ((rate17 + lam) + (rate17 + lam)) *
      ((1 : Q') + Q'.mkPos 1 50 (by decide) * Q'.mkPos 1 50 (by decide)) +
    -(oldAdj 17 0) +
    -((lam + lam) * Q'.mkPos 277 20 (by decide))

theorem bracket17_neg : bracket17 < (0 : Q') := by
  unfold bracket17 rate17 twoInvSq invSqTerm oldAdj harmW harmU
    ReciprocalBernoulliUpper.oneSub unit coeffW dimQ c4 qpow
  decide

private theorem slack_collect_eqv (D r lam z d e0 : Q') :
    (((r + lam) + (r + lam)) * D) * ((1 : Q') + z * z) +
        -(D * e0) + -((lam + lam) * (D * d)) ≈
      D * ((((r + lam) + (r + lam)) * ((1 : Q') + z * z) +
        (-e0)) + -((lam + lam) * d)) := by
  ring_qeqv

private def B17 : Q' :=
  (harmonicA 17 + twoInvSq 17 * harmonicD 17) +
    (harmonicA 17 + twoInvSq 17 * harmonicD 17)

private theorem B17_nonneg : (0 : Q') ≤ B17 := by
  have hA := adjCorr_nonneg (harmW_nonneg 17) (Ncut 17)
  have hl : (0 : Q') ≤ twoInvSq 17 := by
    unfold twoInvSq
    exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) 17)
  have hD := Q'.le_of_lt (harmonicD_pos 17)
  unfold B17 harmonicA
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ hA (Q'.mul_nonneg _ _ hl hD))
    (Q'.zero_le_add _ _ hA (Q'.mul_nonneg _ _ hl hD))

private theorem pair_upper {A D lam r : Q'} (hA : A ≤ r * D) :
    (A + lam * D) + (A + lam * D) ≤
      ((r + lam) + (r + lam)) * D := by
  have hs := Q'.add_le_add hA (Q'.le_refl' (lam * D))
  have ht := Q'.add_le_add hs hs
  exact Q'.le_trans' _ _ _ ht (Q'.le_of_eqv (by
    ring_qeqv))

private theorem diagN17_upper : oldDiag 17 (Ncut 17) ≤
    Q'.mkPos 1 50 (by decide) * Q'.mkPos 1 50 (by decide) := by
  have ht := terminalCoeff17_le
  unfold oldDiag at ht ⊢
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _
    (coeffW (harmW 17) (Ncut 17)) ht
    (coeffW_nonneg (harmW_nonneg 17) (Ncut 17))
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.mkPos 1 50 (by decide)) ht (by decide)
  exact Q'.le_trans' _ _ _ h1 h2

private theorem headpair17_upper :
    B17 * oldDiag 17 0 + B17 * oldDiag 17 (Ncut 17) ≤
      (((rate17 + twoInvSq 17) + (rate17 + twoInvSq 17)) * harmonicD 17) *
        ((1 : Q') + Q'.mkPos 1 50 (by decide) * Q'.mkPos 1 50 (by decide)) := by
  have hd0 : oldDiag 17 0 ≈ (1 : Q') := by
    unfold oldDiag
    simp only [coeffW_zero]
    exact Q'.one_mul_eqv (1 : Q')
  have hsum := Q'.add_le_add (Q'.le_of_eqv hd0) diagN17_upper
  have hsum0 : (0 : Q') ≤ oldDiag 17 0 + oldDiag 17 (Ncut 17) := by
    unfold oldDiag
    exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (coeffW_nonneg (harmW_nonneg 17) 0)
        (coeffW_nonneg (harmW_nonneg 17) 0))
      (Q'.mul_nonneg _ _ (coeffW_nonneg (harmW_nonneg 17) (Ncut 17))
        (coeffW_nonneg (harmW_nonneg 17) (Ncut 17)))
  have hBup : B17 ≤
      ((rate17 + twoInvSq 17) + (rate17 + twoInvSq 17)) * harmonicD 17 := by
    unfold B17
    exact pair_upper harmonicA_le_rate17_D
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _
    (oldDiag 17 0 + oldDiag 17 (Ncut 17)) hBup hsum0
  have hR0 : (0 : Q') ≤
      ((rate17 + twoInvSq 17) + (rate17 + twoInvSq 17)) * harmonicD 17 := by
    exact Q'.le_trans' _ _ _ B17_nonneg hBup
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _
    (((rate17 + twoInvSq 17) + (rate17 + twoInvSq 17)) * harmonicD 17)
    hsum hR0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)))
    (Q'.le_trans' _ _ _ h1 h2)

private theorem edge17_drop :
    -(harmonicD 17 * (oldAdj 17 0 + oldAdj 17 (Ncut 17 - 1))) ≤
      -(harmonicD 17 * oldAdj 17 0) := by
  have he0 : (0 : Q') ≤ oldAdj 17 (Ncut 17 - 1) := by
    unfold oldAdj
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg 17) _)
      (coeffW_nonneg (harmW_nonneg 17) _)
  have he := Q'.add_le_self_of_nonneg (oldAdj 17 0) _ he0
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 17) he
    (Q'.le_of_lt (harmonicD_pos 17))
  exact Q'.neg_le_neg hm

private theorem budget17_upper :
    -((twoInvSq 17 + twoInvSq 17) * (harmonicD 17 * harmonicD 17)) ≤
      -((twoInvSq 17 + twoInvSq 17) *
        (harmonicD 17 * Q'.mkPos 277 20 (by decide))) := by
  have hDD := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 17) D17_lower
    (Q'.le_of_lt (harmonicD_pos 17))
  have hl : (0 : Q') ≤ twoInvSq 17 + twoInvSq 17 := by
    have h : (0 : Q') ≤ twoInvSq 17 := by
      unfold twoInvSq
      exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) 17)
    exact Q'.zero_le_add _ _ h h
  exact Q'.neg_le_neg
    (Q'.mul_le_mul_of_nonneg_left _ _ (twoInvSq 17 + twoInvSq 17) hDD hl)

private theorem carrier_slack17_le :
    let N := Ncut 17
    let L := N - 1
    let D := harmonicD 17
    let A := harmonicA 17
    let lam := twoInvSq 17
    let B := (A + lam * D) + (A + lam * D)
    (B * oldDiag 17 0 + B * oldDiag 17 N) +
        -(D * (oldAdj 17 0 + oldAdj 17 L)) +
        -((lam + lam) * (D * D)) ≤ D * bracket17 := by
  dsimp only
  have hhead :
      (((harmonicA 17 + twoInvSq 17 * harmonicD 17) +
          (harmonicA 17 + twoInvSq 17 * harmonicD 17)) * oldDiag 17 0 +
        ((harmonicA 17 + twoInvSq 17 * harmonicD 17) +
          (harmonicA 17 + twoInvSq 17 * harmonicD 17)) * oldDiag 17 (Ncut 17)) ≤
      (((rate17 + twoInvSq 17) + (rate17 + twoInvSq 17)) * harmonicD 17) *
        ((1 : Q') + Q'.mkPos 1 50 (by decide) * Q'.mkPos 1 50 (by decide)) := by
    simpa only [B17] using headpair17_upper
  have hall := Q'.add_le_add (Q'.add_le_add hhead edge17_drop) budget17_upper
  unfold bracket17
  exact Q'.le_trans' _ _ _ hall (Q'.le_of_eqv
    (slack_collect_eqv (harmonicD 17) rate17 (twoInvSq 17)
      (Q'.mkPos 1 50 (by decide)) (Q'.mkPos 277 20 (by decide)) (oldAdj 17 0)))

/-- Exact kernel fence: uniform terminal-carrier dominance already fails at
the first bad scale `k=17`. -/
theorem terminal_carrier_total_gap_fails_k17 :
    ¬ ((0 : Q') ≤
      trapezoidNodeCumulative 17 (Ncut 17 - 1) +
        -(trapezoidNodeCumulative 17 0)) := by
  intro hgap
  have hid := carrier_total_gap_eq_slack 17
  have hup : trapezoidNodeCumulative 17 (Ncut 17 - 1) +
      -(trapezoidNodeCumulative 17 0) ≤ harmonicD 17 * bracket17 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hid) carrier_slack17_le
  have hneg : harmonicD 17 * bracket17 < (0 : Q') := by
    have hm := Q'.mul_lt_mul_of_pos_left (harmonicD_pos 17) bracket17_neg
    exact HeatKernelRGStep.lt_of_lt_of_le hm
      (Q'.le_of_eqv (Q'.mul_zero_eqv (harmonicD 17)))
  exact ClusteringImpliesGap.lt_irrefl' (0 : Q') (Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _ hgap hup) hneg)
end YMGap.Continuum.HarmonicCarrierGapK17Fence

#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.head_ratio17
#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.tail_ratio17
#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.tail_step17
#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.harmonicA_le_rate17_D
#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.D17_lower
#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.terminalCoeff17_le
#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.carrier_total_gap_eq_slack
#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.bracket17_neg
#print axioms YMGap.Continuum.HarmonicCarrierGapK17Fence.terminal_carrier_total_gap_fails_k17
