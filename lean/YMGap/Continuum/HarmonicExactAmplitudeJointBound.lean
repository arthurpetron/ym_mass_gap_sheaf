/-
# Joint exact-amplitude phase bound

The exact crossing gap need not dominate the next cell: at the genuine
`k=17,i=0` crossing the following node coefficient is still negative, so the
terminal gap grows once more.  This module banks that no-go and replaces the
one-cell envelope by the coefficient-sign phase selected by the PF2 sign law.
Once one successor coefficient is nonnegative, every later coefficient is
nonnegative and the exact-amplitude gaps decrease.  The resulting tail bound
retains the exact peak gap, including the previous-boundary deficit.
-/

import YMGap.Continuum.HarmonicExactAmplitudeCarrier

namespace YMGap.Continuum.HarmonicExactAmplitudeJointBound

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCarrierGapK17Fence
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicDynamicFirstCrossingCap
open YMGap.Continuum.HarmonicDynamicQuadraticCarrier
open YMGap.Continuum.HarmonicExactAmplitudeCarrier
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicQuadraticCapAll
open YMGap.Continuum.HarmonicSignedChordQuadraticCap
open YMGap.Continuum.HarmonicSignedChordQuantitative
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem neg_lt_zero_of_pos {a : Q'} (h : (0 : Q') < a) :
    -a < (0 : Q') := by
  have hn : (0 : Int) < a.num := Q'.num_pos_of_pos h
  show (-a).num * (((0 : Q').den) : Int) <
    (0 : Q').num * ((-a).den : Int)
  simp only [neg_num_cast]
  have h0d : (((0 : Q').den) : Int) = 1 := rfl
  have h0n : (0 : Q').num = 0 := rfl
  rw [h0d, h0n, Int.mul_one, Int.zero_mul]
  omega

private theorem sub_neg_of_lt {a b : Q'} (h : a < b) :
    a + -b < (0 : Q') := by
  have hp : (0 : Q') < b + -a :=
    ClusteringImpliesGap.sub_pos_of_lt h
  have hn : -(b + -a) < (0 : Q') := neg_lt_zero_of_pos hp
  have he : a + -b ≈ -(b + -a) := by ring_qeqv
  exact Q'.lt_of_le_of_lt (Q'.le_of_eqv he) hn

private def lowerPairRate17 : Q' :=
  (((1 : Q') + -(Q'.mkPos 2 25 (by decide))) + twoInvSq 17) +
    (((1 : Q') + -(Q'.mkPos 2 25 (by decide))) + twoInvSq 17)

private theorem pair_collect (r lam D : Q') :
    (r * D + lam * D) + (r * D + lam * D) ≈
      ((r + lam) + (r + lam)) * D := by
  ring_qeqv

/-- Exact lower enclosure of `B_17`, used only to certify that coefficient
two is strictly negative. -/
private theorem lowerPairRate17_mul_D_le_exactPair :
    lowerPairRate17 * harmonicD 17 ≤ exactCrossingPair 17 := by
  have hA := harmonicA17_lower
  change (((1 : Q') + -(Q'.mkPos 2 25 (by decide))) * harmonicD 17) ≤
    harmonicA 17 at hA
  have hs := Q'.add_le_add hA
    (Q'.le_refl' (twoInvSq 17 * harmonicD 17))
  have ht := Q'.add_le_add hs hs
  unfold lowerPairRate17 exactCrossingPair
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (pair_collect ((1 : Q') + -(Q'.mkPos 2 25 (by decide)))
        (twoInvSq 17) (harmonicD 17)))) ht

/-- Exact local half-edge ratio at node two. -/
private theorem edge_two_lt_lower_center17 :
    oldAdj 17 1 + oldAdj 17 2 <
      lowerPairRate17 * oldDiag 17 2 := by
  unfold lowerPairRate17 twoInvSq invSqTerm oldAdj oldDiag harmW harmU
    oneSub unit coeffW dimQ c4 qpow
  decide

/-- Generic exact-amplitude sign test.  A lower bound on `B_k` together with
one strict centered half-edge comparison makes the corresponding successor
node coefficient strictly negative. -/
theorem nodeCoeff_succ_neg_of_pair_lower
    {k p : Nat} {C : Q'}
    (hpairLower : C * harmonicD k ≤ exactCrossingPair k)
    (hedge : oldAdj k p + oldAdj k (p + 1) <
      C * oldDiag k (p + 1)) :
    trapezoidNodeCoeff k (p + 1) < (0 : Q') := by
  have hd0 : (0 : Q') ≤ oldDiag k (p + 1) := by
    unfold oldDiag
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) (p + 1))
      (coeffW_nonneg (harmW_nonneg k) (p + 1))
  have hpair := Q'.mul_le_mul_of_nonneg_right _ _ (oldDiag k (p + 1))
    hpairLower hd0
  have hn := Q'.neg_le_neg hpair
  have hupper := Q'.add_le_add_left
    (harmonicD k * (oldAdj k p + oldAdj k (p + 1))) _ _ hn
  have hdiff : (0 : Q') <
      C * oldDiag k (p + 1) +
        -(oldAdj k p + oldAdj k (p + 1)) :=
    ClusteringImpliesGap.sub_pos_of_lt hedge
  have hprod : (0 : Q') < harmonicD k *
      (C * oldDiag k (p + 1) +
        -(oldAdj k p + oldAdj k (p + 1))) :=
    Q'.mul_pos (harmonicD_pos k) hdiff
  have hnegprod := neg_lt_zero_of_pos hprod
  have heq :
      harmonicD k * (oldAdj k p + oldAdj k (p + 1)) +
          -((C * harmonicD k) * oldDiag k (p + 1)) ≈
        -(harmonicD k *
          (C * oldDiag k (p + 1) +
            -(oldAdj k p + oldAdj k (p + 1)))) := by
    ring_qeqv
  have hupperNeg :
      harmonicD k * (oldAdj k p + oldAdj k (p + 1)) +
          -((C * harmonicD k) * oldDiag k (p + 1)) < (0 : Q') :=
    Q'.lt_of_le_of_lt (Q'.le_of_eqv heq) hnegprod
  unfold trapezoidNodeCoeff
  exact Q'.lt_of_le_of_lt hupper hupperNeg

/-- Exact upper enclosure of `B_k`, retained symbolically for the PF2 phase
entry test. -/
theorem exactCrossingPair_le_dynamicPairRate_mul_D {k : Nat} (hk : 1 ≤ k) :
    exactCrossingPair k ≤ dynamicPairRate k * harmonicD k := by
  have hA : harmonicA k ≤ retuneCube (harmW k) * harmonicD k := by
    simpa only [harmonicA, harmonicD] using
      (harmonic_physical_cutoff_retune (k := k) hk)
  have hs := Q'.add_le_add hA
    (Q'.le_refl' (twoInvSq k * harmonicD k))
  have ht := Q'.add_le_add hs hs
  unfold exactCrossingPair dynamicPairRate
  exact Q'.le_trans' _ _ _ ht
    (Q'.le_of_eqv (pair_collect (retuneCube (harmW k))
      (twoInvSq k) (harmonicD k)))

/-- Exact local half-edge ratio at node three. -/
private theorem upper_center17_lt_edge_three :
    dynamicPairRate 17 * oldDiag 17 3 <
      oldAdj 17 2 + oldAdj 17 3 := by
  unfold dynamicPairRate retuneCube retuneBase twoInvSq invSqTerm
    oldAdj oldDiag harmW harmU oneSub unit coeffW dimQ c4 qpow
  decide

/-- Dual generic sign test for entry into the PF2-positive phase. -/
theorem nodeCoeff_succ_pos_of_pair_upper
    {k p : Nat} {C : Q'}
    (hpairUpper : exactCrossingPair k ≤ C * harmonicD k)
    (hedge : C * oldDiag k (p + 1) <
      oldAdj k p + oldAdj k (p + 1)) :
    (0 : Q') < trapezoidNodeCoeff k (p + 1) := by
  have hd0 : (0 : Q') ≤ oldDiag k (p + 1) := by
    unfold oldDiag
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) (p + 1))
      (coeffW_nonneg (harmW_nonneg k) (p + 1))
  have hpair := Q'.mul_le_mul_of_nonneg_right _ _ (oldDiag k (p + 1))
    hpairUpper hd0
  have hn := Q'.neg_le_neg hpair
  have hlower := Q'.add_le_add_left
    (harmonicD k * (oldAdj k p + oldAdj k (p + 1))) _ _ hn
  have hdiff : (0 : Q') <
      (oldAdj k p + oldAdj k (p + 1)) +
        -(C * oldDiag k (p + 1)) :=
    ClusteringImpliesGap.sub_pos_of_lt hedge
  have hprod : (0 : Q') < harmonicD k *
      ((oldAdj k p + oldAdj k (p + 1)) +
        -(C * oldDiag k (p + 1))) :=
    Q'.mul_pos (harmonicD_pos k) hdiff
  have heq :
      harmonicD k *
          ((oldAdj k p + oldAdj k (p + 1)) +
            -(C * oldDiag k (p + 1))) ≈
        harmonicD k * (oldAdj k p + oldAdj k (p + 1)) +
          -((C * harmonicD k) * oldDiag k (p + 1)) := by
    ring_qeqv
  have hlowerPos : (0 : Q') <
      harmonicD k * (oldAdj k p + oldAdj k (p + 1)) +
        -((C * harmonicD k) * oldDiag k (p + 1)) :=
    HeatKernelRGStep.lt_of_lt_of_le hprod (Q'.le_of_eqv heq)
  unfold trapezoidNodeCoeff
  exact HeatKernelRGStep.lt_of_lt_of_le hlowerPos hlower

/-! ## Exact sign-phase calculus -/

/-- Opaque-indexed terminal-gap sequence used to prevent eager expansion of
the exact crossing window at successor indices. -/
def terminalPhaseGap (k L s n : Nat) : Q' := terminalGap k L (s + n)

/-- Advancing the terminal phase subtracts exactly the next node
coefficient. -/
theorem terminalPhaseGap_succ_eqv (k L s n : Nat) :
    terminalPhaseGap k L s (n + 1) ≈
      terminalPhaseGap k L s n +
        -(trapezoidNodeCoeff k (s + n + 1)) := by
  unfold terminalPhaseGap
  rw [show s + (n + 1) = (s + n) + 1 by omega]
  exact terminalGap_succ_eqv k L (s + n)

/-- A nonnegative coefficient decreases the terminal phase across that
cell. -/
theorem terminalPhaseGap_succ_le_of_coeff_nonneg
    {k L s n : Nat}
    (hq : (0 : Q') ≤ trapezoidNodeCoeff k (s + n + 1)) :
    terminalPhaseGap k L s (n + 1) ≤ terminalPhaseGap k L s n := by
  have hn : -(trapezoidNodeCoeff k (s + n + 1)) ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hq)
      (Q'.le_of_eqv (by decide : (-(0 : Q')) ≈ (0 : Q')))
  have hadd := Q'.add_le_add_left (terminalPhaseGap k L s n) _ _ hn
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (terminalPhaseGap_succ_eqv k L s n))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (q_add_zero_eqv _)))

/-- PF2 phase bound for terminal gaps. -/
theorem terminalPhaseGap_antitone_after_sign
    {k L s t : Nat}
    (hturn : (0 : Q') ≤ trapezoidNodeCoeff k (s + t + 1)) :
    ∀ d : Nat,
      terminalPhaseGap k L s (t + d) ≤ terminalPhaseGap k L s t
  | 0 => by simp only [Nat.add_zero]; exact Q'.le_refl' _
  | d + 1 => by
      have hforward := trapezoidNodeCoeff_sign_forward k (s + t) d
        (by simpa only [Nat.add_assoc] using hturn)
      have hstep := terminalPhaseGap_succ_le_of_coeff_nonneg
        (k := k) (L := L) (s := s) (n := t + d) (by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hforward)
      exact Q'.le_trans' _ _ _ hstep
        (terminalPhaseGap_antitone_after_sign hturn d)

/-- PF2 phase bound transferred back to the exact-amplitude representation. -/
theorem exactAmplitudeGap_antitone_after_sign
    {k L i t : Nat}
    (hturn : (0 : Q') ≤ trapezoidNodeCoeff k (i + t + 2))
    (d : Nat) :
    exactAmplitudeGap k L i (t + d) ≤ exactAmplitudeGap k L i t := by
  have hturn' : (0 : Q') ≤
      trapezoidNodeCoeff k ((i + 1) + t + 1) := by
    rw [show (i + 1) + t + 1 = i + t + 2 by omega]
    exact hturn
  have hp := terminalPhaseGap_antitone_after_sign
    (k := k) (L := L) (s := i + 1) (t := t) hturn' d
  have hleft := exactAmplitudeGap_eqv_terminalGap k L i (t + d)
  have hright := exactAmplitudeGap_eqv_terminalGap k L i t
  unfold terminalPhaseGap at hp
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hp (Q'.ge_of_eqv hright))

/-- Tail carrier beginning at a coefficient-sign phase exit. -/
def exactAmplitudeTailCarrier (k L i t n : Nat) : Q' :=
  fsum (fun d => exactAmplitudeCell k L i (t + d)) n

/-- Abel carrier of the PF2-positive phase.  Unlike the peak-times-total-
weight envelope, this keeps the decay of every positive node coefficient
paired with only its preceding local quadratic cumulative weight. -/
def exactAmplitudePhaseAbelCarrier (k i t n : Nat) : Q' :=
  fsum (fun j =>
    trapezoidNodeCoeff k (i + t + j + 2) *
      harmonicChordQuadraticCumulative k (i + 1 + t) (j + 1)) n

/-- Exact phase-local Fubini/Abel identity.  This is the cumulative form that
survives the one-cell no-go: the positive PF2 phase is not enlarged to one
peak times the astronomically large full drift cumulative. -/
theorem exactAmplitudeTailCarrier_eqv_phaseAbel
    {k L i t : Nat} (htL : i + 1 + t ≤ L) :
    exactAmplitudeTailCarrier k L i t (L - (i + 1 + t)) ≈
      exactAmplitudePhaseAbelCarrier k i t (L - (i + 1 + t)) := by
  let s := i + 1 + t
  let n := L - s
  have hsn : s + n = L := Nat.add_sub_of_le htL
  have hcarrier : exactAmplitudeTailCarrier k L i t n ≈
      fsum (fun j => terminalGap k L (s + j) *
        harmonicChordQuadraticWeight k (s + j)) n := by
    unfold exactAmplitudeTailCarrier exactAmplitudeCell
    exact CubeRatioBounds.fsum_eqv_congr _ _ (fun j => by
      have hg := exactAmplitudeGap_eqv_terminalGap k L i (t + j)
      rw [show i + 1 + (t + j) = s + j by unfold s; omega] at hg ⊢
      exact Q'.mul_eqv_congr_right _ _ _ hg) n
  have hm := signedChordQuadraticNodeMoment_eq_carrier k s n
  rw [hsn] at hm
  have hm' : signedChordQuadraticNodeMoment k s n ≈
      fsum (fun j => terminalGap k L (s + j) *
        harmonicChordQuadraticWeight k (s + j)) n := by
    simpa only [intervalSum, terminalGap] using hm
  refine Q'.eqv_trans _ _ _ hcarrier (Q'.eqv_trans _ _ _
    (Q'.eqv_symm hm') ?_)
  unfold exactAmplitudePhaseAbelCarrier signedChordQuadraticNodeMoment s
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun j => by
    rw [show i + 1 + t + j + 1 = i + t + j + 2 by omega]
    exact Q'.eqv_refl _) n

/-- The phase Abel carrier is nonnegative from the single PF2 sign-exit
certificate.  All later signs are consequences, not extra premises. -/
theorem exactAmplitudePhaseAbelCarrier_nonnegative
    {k i t n : Nat}
    (hturn : (0 : Q') ≤ trapezoidNodeCoeff k (i + t + 2)) :
    (0 : Q') ≤ exactAmplitudePhaseAbelCarrier k i t n := by
  unfold exactAmplitudePhaseAbelCarrier
  exact BondMovingStep.fsum_nonneg (fun j => by
    have hq := trapezoidNodeCoeff_sign_forward k (i + t + 1) j
      (by simpa only [Nat.add_assoc] using hturn)
    have hq' : (0 : Q') ≤ trapezoidNodeCoeff k (i + t + j + 2) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
    have hW : (0 : Q') ≤
        harmonicChordQuadraticCumulative k (i + 1 + t) (j + 1) := by
      unfold harmonicChordQuadraticCumulative intervalSum
      exact BondMovingStep.fsum_nonneg
        (fun r => harmonicChordQuadraticWeight_nonnegative k
          (i + 1 + t + r)) (j + 1)
    exact Q'.mul_nonneg _ _ hq' hW) n

/-- Cumulative joint bound after the PF2 sign exit.  The multiplier is the
true peak terminal gap, so the exact `B_k`/previous-deficit cancellation is
retained rather than replaced by a retune coefficient. -/
theorem exactAmplitudeTailCarrier_le_peak
    {k L i t n : Nat}
    (hturn : (0 : Q') ≤ trapezoidNodeCoeff k (i + t + 2)) :
    exactAmplitudeTailCarrier k L i t n ≤
      exactAmplitudeGap k L i t *
        harmonicChordQuadraticCumulative k (i + 1 + t) n := by
  have hterm : ∀ d, d < n →
      exactAmplitudeCell k L i (t + d) ≤
        exactAmplitudeGap k L i t *
          harmonicChordQuadraticWeight k (i + 1 + t + d) := by
    intro d _hd
    have hgap := exactAmplitudeGap_antitone_after_sign
      (k := k) (L := L) (i := i) (t := t) hturn d
    have hW0 := harmonicChordQuadraticWeight_nonnegative k (i + 1 + t + d)
    unfold exactAmplitudeCell
    rw [show i + 1 + (t + d) = i + 1 + t + d by omega]
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hgap hW0
  have hsum := CubeRatioBounds.fsum_mono_lt n hterm
  have hpull := CubeRatioBounds.fsum_const_mul
    (exactAmplitudeGap k L i t)
    (fun d => harmonicChordQuadraticWeight k (i + 1 + t + d)) n
  unfold exactAmplitudeTailCarrier harmonicChordQuadraticCumulative intervalSum
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hpull)

/-! ## Genuine `k=17` local no-go and corrected phase -/

/-- The strongest one-cell envelope: the first forward exact gap does not
exceed the crossing gap.  The constructor wrapper keeps the genuine large
`k=17` expression opaque to the elaborator without changing its content. -/
inductive CrossingCellDominance (k L i : Nat) : Prop where
  | intro : exactAmplitudeGap k L i 1 ≤ exactAmplitudeGap k L i 0 →
      CrossingCellDominance k L i

/-- Any strictly negative next coefficient refutes one-cell dominance. -/
theorem crossingCellDominance_fails_of_next_coeff_neg
    {k L i : Nat} (hq : trapezoidNodeCoeff k (i + 2) < (0 : Q')) :
    ¬ CrossingCellDominance k L i := by
  intro hdom
  cases hdom with
  | intro hbad =>
    have hneg0 : (0 : Q') < -(trapezoidNodeCoeff k (i + 2)) := by
      have h := ClusteringImpliesGap.sub_pos_of_lt hq
      exact HeatKernelRGStep.lt_of_lt_of_le h
        (Q'.le_of_eqv (q_zero_add_eqv (-(trapezoidNodeCoeff k (i + 2)))))
    have hgrow := AFRateCalibration.lt_add_of_pos_right
      (terminalPhaseGap k L (i + 1) 0)
      (-(trapezoidNodeCoeff k (i + 2))) hneg0
    have hphase : terminalPhaseGap k L (i + 1) 0 <
        terminalPhaseGap k L (i + 1) 1 :=
      HeatKernelRGStep.lt_of_lt_of_le hgrow
        (Q'.ge_of_eqv (terminalPhaseGap_succ_eqv k L (i + 1) 0))
    have h0 := exactAmplitudeGap_eqv_terminalGap k L i 0
    have h1 := exactAmplitudeGap_eqv_terminalGap k L i 1
    have hexact : exactAmplitudeGap k L i 0 < exactAmplitudeGap k L i 1 := by
      unfold terminalPhaseGap at hphase
      exact Q'.lt_of_le_of_lt (Q'.le_of_eqv h0)
        (HeatKernelRGStep.lt_of_lt_of_le hphase (Q'.ge_of_eqv h1))
    exact ClusteringImpliesGap.lt_irrefl' (exactAmplitudeGap k L i 1)
      (Q'.lt_of_le_of_lt hbad hexact)

/-- Machine-checked no-go at the genuine first crossing. -/
theorem crossing_cell_dominance_fails_k17 :
    ¬ CrossingCellDominance 17 (Ncut 17 - 1) 0 := by
  exact crossingCellDominance_fails_of_next_coeff_neg
    (nodeCoeff_succ_neg_of_pair_lower
      lowerPairRate17_mul_D_le_exactPair edge_two_lt_lower_center17)

/-- Corrected sharp phase at the genuine crossing: the exact gap peaks at
node two, and every later gap is bounded by that two-cell peak. -/
theorem exactAmplitudeGap17_le_two_cell_peak (d : Nat) :
    exactAmplitudeGap 17 (Ncut 17 - 1) 0 (1 + d) ≤
      exactAmplitudeGap 17 (Ncut 17 - 1) 0 1 := by
  exact exactAmplitudeGap_antitone_after_sign
    (k := 17) (L := Ncut 17 - 1) (i := 0) (t := 1)
    (Q'.le_of_lt (nodeCoeff_succ_pos_of_pair_upper
      (exactCrossingPair_le_dynamicPairRate_mul_D (k := 17) (by decide))
      upper_center17_lt_edge_three)) d

/-- Cumulative version of the corrected genuine-crossing phase bound. -/
theorem exactAmplitudeTailCarrier17_le_two_cell_peak (n : Nat) :
    exactAmplitudeTailCarrier 17 (Ncut 17 - 1) 0 1 n ≤
      exactAmplitudeGap 17 (Ncut 17 - 1) 0 1 *
        harmonicChordQuadraticCumulative 17 2 n := by
  exact exactAmplitudeTailCarrier_le_peak
    (k := 17) (L := Ncut 17 - 1) (i := 0) (t := 1) (n := n)
    (Q'.le_of_lt (nodeCoeff_succ_pos_of_pair_upper
      (exactCrossingPair_le_dynamicPairRate_mul_D (k := 17) (by decide))
      upper_center17_lt_edge_three))

/-- The corrected `k=17` tail is exactly a positive-phase Abel carrier. -/
theorem exactAmplitudeTailCarrier17_eqv_phaseAbel :
    exactAmplitudeTailCarrier 17 (Ncut 17 - 1) 0 1
        (Ncut 17 - 1 - 2) ≈
      exactAmplitudePhaseAbelCarrier 17 0 1 (Ncut 17 - 1 - 2) := by
  exact exactAmplitudeTailCarrier_eqv_phaseAbel
    (k := 17) (L := Ncut 17 - 1) (i := 0) (t := 1)
    (by unfold Ncut; omega)

theorem exactAmplitudePhaseAbelCarrier17_nonnegative :
    (0 : Q') ≤
      exactAmplitudePhaseAbelCarrier 17 0 1 (Ncut 17 - 1 - 2) := by
  exact exactAmplitudePhaseAbelCarrier_nonnegative
    (Q'.le_of_lt (nodeCoeff_succ_pos_of_pair_upper
      (exactCrossingPair_le_dynamicPairRate_mul_D (k := 17) (by decide))
      upper_center17_lt_edge_three))

#print axioms nodeCoeff_succ_neg_of_pair_lower
#print axioms exactCrossingPair_le_dynamicPairRate_mul_D
#print axioms nodeCoeff_succ_pos_of_pair_upper
#print axioms terminalPhaseGap_succ_eqv
#print axioms terminalPhaseGap_succ_le_of_coeff_nonneg
#print axioms terminalPhaseGap_antitone_after_sign
#print axioms exactAmplitudeGap_antitone_after_sign
#print axioms exactAmplitudeTailCarrier_eqv_phaseAbel
#print axioms exactAmplitudePhaseAbelCarrier_nonnegative
#print axioms exactAmplitudeTailCarrier_le_peak
#print axioms crossingCellDominance_fails_of_next_coeff_neg
#print axioms crossing_cell_dominance_fails_k17
#print axioms exactAmplitudeGap17_le_two_cell_peak
#print axioms exactAmplitudeTailCarrier17_le_two_cell_peak
#print axioms exactAmplitudeTailCarrier17_eqv_phaseAbel
#print axioms exactAmplitudePhaseAbelCarrier17_nonnegative

end YMGap.Continuum.HarmonicExactAmplitudeJointBound
