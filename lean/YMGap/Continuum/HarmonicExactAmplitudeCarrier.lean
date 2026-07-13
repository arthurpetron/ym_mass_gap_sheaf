/-
# Exact-amplitude dynamic quadratic carrier

This module retains the exact crossing amplitude

  B_k = 2 * (A_k + lambda_k D_k)

instead of replacing `A_k / D_k` by a retune rate.  At a nonzero crossing,
the previous terminal deficit stays in the same weighted cell as the exact
centered edge/diagonal crossing term.  Thus no crossing overshoot is copied
across the whole remaining cumulative weight.
-/

import YMGap.Continuum.HarmonicDynamicQuadraticCarrier

namespace YMGap.Continuum.HarmonicExactAmplitudeCarrier

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicDynamicFirstCrossingCap
open YMGap.Continuum.HarmonicDynamicQuadraticCarrier
open YMGap.Continuum.HarmonicQuadraticCapAll
open YMGap.Continuum.HarmonicSchurRotationAll
open YMGap.Continuum.HarmonicSignedChordQuadraticCap
open YMGap.Continuum.HarmonicSignedChordQuantitative
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

/-- The exact doubled crossing amplitude `B_k`. -/
def exactCrossingPair (k : Nat) : Q' :=
  (harmonicA k + twoInvSq k * harmonicD k) +
    (harmonicA k + twoInvSq k * harmonicD k)

/-- The signed amount by which the preceding node is below the terminal
boundary.  It is nonnegative at a genuine nonzero first crossing. -/
def previousBoundaryDeficit (k L i : Nat) : Q' :=
  -(terminalGap k L i)

/-- The exact later terminal gap, written with the crossing amplitude,
centered crossing edge, preceding deficit, and forward coefficient window
kept together.  The crossing node is `i+1`; `n` is the forward cell offset. -/
def exactAmplitudeGap (k L i n : Nat) : Q' :=
  ((exactCrossingPair k * oldDiag k (i + 1) +
      -(harmonicD k * (oldAdj k i + oldAdj k (i + 1)))) +
    -(previousBoundaryDeficit k L i)) +
  -(crossingCoeffWindow k (i + 1) n)

/-- The exact cellwise carrier.  In particular the previous-boundary deficit
is multiplied only by the current drift weight, rather than by the complete
remaining cumulative weight. -/
def exactAmplitudeCell (k L i n : Nat) : Q' :=
  exactAmplitudeGap k L i n *
    harmonicChordQuadraticWeight k (i + 1 + n)

/-- Sum of the exact paired cells following a nonzero crossing. -/
def exactAmplitudeWindowCarrier (k L i n : Nat) : Q' :=
  fsum (exactAmplitudeCell k L i) n

private theorem crossing_seed_algebra (g D E B d : Q') :
    g + -(D * E + -(B * d)) ≈
      (B * d + -(D * E)) + -(-g) := by
  ring_qeqv

/-- Symbolic all-scale identity at the crossing node.  It is the exact
replacement for the lossy overshoot estimate: `B_k` is not enlarged, and
the preceding deficit is subtracted before any drift weight is applied. -/
theorem terminalGap_succ_eqv_exactAmplitudeSeed (k L i : Nat) :
    terminalGap k L (i + 1) ≈ exactAmplitudeGap k L i 0 := by
  have hstep := terminalGap_succ_eqv k L i
  refine Q'.eqv_trans _ _ _ hstep ?_
  have halg := crossing_seed_algebra (terminalGap k L i) (harmonicD k)
    (oldAdj k i + oldAdj k (i + 1)) (exactCrossingPair k)
    (oldDiag k (i + 1))
  refine Q'.eqv_trans _
    ((exactCrossingPair k * oldDiag k (i + 1) +
        -(harmonicD k * (oldAdj k i + oldAdj k (i + 1)))) +
      -(-terminalGap k L i)) _ ?_ ?_
  · unfold trapezoidNodeCoeff exactCrossingPair
    exact halg
  · let X :=
      (exactCrossingPair k * oldDiag k (i + 1) +
        -(harmonicD k * (oldAdj k i + oldAdj k (i + 1)))) +
      -(-terminalGap k L i)
    have hwin : crossingCoeffWindow k (i + 1) 0 ≈ (0 : Q') := by
      unfold crossingCoeffWindow intervalSum
      exact Q'.eqv_refl _
    have hnwin : -(crossingCoeffWindow k (i + 1) 0) ≈ (0 : Q') :=
      Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hwin) (by decide)
    unfold exactAmplitudeGap previousBoundaryDeficit
    refine Q'.eqv_trans _ (X + (0 : Q')) _
      (Q'.eqv_symm (q_add_zero_eqv X)) ?_
    exact Q'.add_eqv_congr_left X _ _ (Q'.eqv_symm hnwin)

/-- Symbolic all-scale, all-cell exact-amplitude identity. -/
theorem exactAmplitudeGap_eqv_terminalGap (k L i n : Nat) :
    exactAmplitudeGap k L i n ≈ terminalGap k L (i + 1 + n) := by
  have hlater := terminalGap_add_eqv_envelopeBase k L (i + 1) n
  have hstep := terminalGap_succ_eqv k L i
  have hseed : terminalGap k L (i + 1) ≈
      (exactCrossingPair k * oldDiag k (i + 1) +
        -(harmonicD k * (oldAdj k i + oldAdj k (i + 1)))) +
      -(previousBoundaryDeficit k L i) := by
    refine Q'.eqv_trans _ _ _ hstep ?_
    unfold exactCrossingPair previousBoundaryDeficit trapezoidNodeCoeff
    ring_qeqv
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ hlater ?_)
  unfold exactAmplitudeGap
  exact Q'.add_eqv_congr_right _ _ _ hseed

private theorem exact_cell_split_algebra (B d D E delta U W : Q') :
    (((B * d + -(D * E)) + -delta) + -U) * W ≈
      ((B * d + -(D * E)) * W + -(delta * W)) + -(U * W) := by
  ring_qeqv

/-- Exact cell identity exposing the surviving mechanism after the retune
fence: the centered `B_k` crossing payment, previous-boundary deficit, and
forward window are all paired with the same local drift weight. -/
theorem exactAmplitudeCell_eqv_centered_sub_deficit_window
    (k L i n : Nat) :
    exactAmplitudeCell k L i n ≈
      ((exactCrossingPair k * oldDiag k (i + 1) +
          -(harmonicD k * (oldAdj k i + oldAdj k (i + 1)))) *
          harmonicChordQuadraticWeight k (i + 1 + n) +
        -(previousBoundaryDeficit k L i *
          harmonicChordQuadraticWeight k (i + 1 + n))) +
      -(crossingCoeffWindow k (i + 1) n *
        harmonicChordQuadraticWeight k (i + 1 + n)) := by
  unfold exactAmplitudeCell exactAmplitudeGap
  exact exact_cell_split_algebra _ _ _ _ _ _ _

/-- At a genuine first crossing, the exact previous-boundary deficit is
nonnegative. -/
theorem previousBoundaryDeficit_nonnegative
    {k L i : Nat}
    (hfirst : ∀ p, p < i + 1 → terminalGap k L p ≤ (0 : Q')) :
    (0 : Q') ≤ previousBoundaryDeficit k L i := by
  unfold previousBoundaryDeficit
  have h := Q'.sub_nonneg_of_le (hfirst i (by omega))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (q_zero_add_eqv _))

/-- Exact carrier identity.  No overshoot inequality is summed: every cell
is definitionally tied to its actual terminal gap before summation. -/
theorem exactAmplitudeWindowCarrier_eqv_moment
    {k L i : Nat} (hiL : i + 1 ≤ L) :
    exactAmplitudeWindowCarrier k L i (L - (i + 1)) ≈
      signedChordQuadraticNodeMoment k (i + 1) (L - (i + 1)) := by
  let n := L - (i + 1)
  have hsum : exactAmplitudeWindowCarrier k L i n ≈
      fsum (fun j =>
        terminalGap k L (i + 1 + j) *
          harmonicChordQuadraticWeight k (i + 1 + j)) n := by
    unfold exactAmplitudeWindowCarrier exactAmplitudeCell
    exact CubeRatioBounds.fsum_eqv_congr _ _
      (fun j => Q'.mul_eqv_congr_right _ _ _
        (exactAmplitudeGap_eqv_terminalGap k L i j)) n
  have hendpoint : i + 1 + n = L := Nat.add_sub_of_le hiL
  have hm := signedChordQuadraticNodeMoment_eq_carrier k (i + 1) n
  rw [hendpoint] at hm
  have hm' : signedChordQuadraticNodeMoment k (i + 1) n ≈
      fsum (fun j =>
        terminalGap k L (i + 1 + j) *
          harmonicChordQuadraticWeight k (i + 1 + j)) n := by
    simpa only [intervalSum, terminalGap] using hm
  exact Q'.eqv_trans _ _ _ hsum (Q'.eqv_symm hm')

/-- Cleared normalized sufficient inequality for one nonzero dynamic
crossing, expressed entirely through the exact-amplitude cells. -/
def ExactAmplitudeBarrierCertificate (k i : Nat) : Prop :=
  let L := Ncut k - 1
  Q'.ofNat ((k + 2) * (k + 2)) *
      (exactAmplitudeWindowCarrier k L i (L - (i + 1)) +
        (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k)) ≤
    quadraticNodeBarrier k * quadraticNodeNormDen k

/-- A nonzero exact-amplitude certificate implies the existing normalized
quadratic-node certificate. -/
theorem quadraticNodeBarrierCertificate_of_exactAmplitude
    {k i : Nat} (hiL : i + 1 ≤ Ncut k - 1)
    (h : ExactAmplitudeBarrierCertificate k i) :
    QuadraticNodeBarrierCertificate k (i + 1) := by
  let L := Ncut k - 1
  have he := exactAmplitudeWindowCarrier_eqv_moment
    (k := k) (L := L) (i := i) hiL
  let C := trapezoidTerminalCorrection k + trapezoidTerminalCorrection k
  have hadd :
      exactAmplitudeWindowCarrier k L i (L - (i + 1)) + C ≈
        signedChordQuadraticNodeMoment k (i + 1) (L - (i + 1)) + C :=
    Q'.add_eqv_congr_right _ _ _ he
  have hmul :
      Q'.ofNat ((k + 2) * (k + 2)) *
          (exactAmplitudeWindowCarrier k L i (L - (i + 1)) + C) ≈
        Q'.ofNat ((k + 2) * (k + 2)) *
          (signedChordQuadraticNodeMoment k (i + 1) (L - (i + 1)) + C) :=
    Q'.mul_eqv_congr_left _ _ _ hadd
  unfold ExactAmplitudeBarrierCertificate at h
  unfold QuadraticNodeBarrierCertificate quadraticNodeTotal
  dsimp only [L, C] at hmul ⊢
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hmul) h

/-- Conversely, the exact identity transports an existing normalized
quadratic-node certificate into the exact-amplitude representation. -/
theorem exactAmplitudeBarrierCertificate_of_quadraticNode
    {k i : Nat} (hiL : i + 1 ≤ Ncut k - 1)
    (h : QuadraticNodeBarrierCertificate k (i + 1)) :
    ExactAmplitudeBarrierCertificate k i := by
  let L := Ncut k - 1
  have he := exactAmplitudeWindowCarrier_eqv_moment
    (k := k) (L := L) (i := i) hiL
  let C := trapezoidTerminalCorrection k + trapezoidTerminalCorrection k
  have hadd :
      exactAmplitudeWindowCarrier k L i (L - (i + 1)) + C ≈
        signedChordQuadraticNodeMoment k (i + 1) (L - (i + 1)) + C :=
    Q'.add_eqv_congr_right _ _ _ he
  have hmul :
      Q'.ofNat ((k + 2) * (k + 2)) *
          (exactAmplitudeWindowCarrier k L i (L - (i + 1)) + C) ≈
        Q'.ofNat ((k + 2) * (k + 2)) *
          (signedChordQuadraticNodeMoment k (i + 1) (L - (i + 1)) + C) :=
    Q'.mul_eqv_congr_left _ _ _ hadd
  unfold ExactAmplitudeBarrierCertificate
  unfold QuadraticNodeBarrierCertificate quadraticNodeTotal at h
  dsimp only [L, C] at hmul ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hmul) h

/-- Sound all-scale sufficient inequality for the frontier cap.  The zero
lane is kept separately; every nonzero lane is discharged by the exact
cellwise amplitude certificate, with no retune substitution. -/
theorem uniformQuadraticNodeCap_of_exactAmplitude
    (hzero : ∀ k : Nat, 5 ≤ k → QuadraticNodeBarrierCertificate k 0)
    (hexact : ∀ k i : Nat, 5 ≤ k → i + 1 ≤ Ncut k - 1 →
      (∀ p, p < i + 1 → terminalGap k (Ncut k - 1) p ≤ (0 : Q')) →
      (0 : Q') ≤ terminalGap k (Ncut k - 1) (i + 1) →
      ExactAmplitudeBarrierCertificate k i) :
    UniformQuadraticNodeCap := by
  intro k s hk hsL hfirst hboundary
  by_cases hs0 : s = 0
  · subst s
    exact quadraticNodeTotal_le_cap_of_barrierCertificate hk (hzero k hk)
  · obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
    have he := hexact k i hk hsL
      (by simpa only [terminalGap] using hfirst)
      (by simpa only [terminalGap] using hboundary)
    exact quadraticNodeTotal_le_cap_of_barrierCertificate hk
      (quadraticNodeBarrierCertificate_of_exactAmplitude hsL he)

/-! Exact finite-scale checks of the new representation. -/

theorem exactAmplitudeBarrierCertificate_k5_i0 :
    ExactAmplitudeBarrierCertificate 5 0 := by
  exact exactAmplitudeBarrierCertificate_of_quadraticNode
    (k := 5) (i := 0) (by unfold Ncut; omega)
    quadraticNodeBarrierCertificate_k5_s1

theorem exactAmplitudeBarrierCertificate_k6_i0 :
    ExactAmplitudeBarrierCertificate 6 0 := by
  exact exactAmplitudeBarrierCertificate_of_quadraticNode
    (k := 6) (i := 0) (by unfold Ncut; omega)
    quadraticNodeBarrierCertificate_k6_s1

#print axioms terminalGap_succ_eqv_exactAmplitudeSeed
#print axioms exactAmplitudeGap_eqv_terminalGap
#print axioms exactAmplitudeCell_eqv_centered_sub_deficit_window
#print axioms previousBoundaryDeficit_nonnegative
#print axioms exactAmplitudeWindowCarrier_eqv_moment
#print axioms quadraticNodeBarrierCertificate_of_exactAmplitude
#print axioms exactAmplitudeBarrierCertificate_of_quadraticNode
#print axioms uniformQuadraticNodeCap_of_exactAmplitude
#print axioms exactAmplitudeBarrierCertificate_k5_i0
#print axioms exactAmplitudeBarrierCertificate_k6_i0

end YMGap.Continuum.HarmonicExactAmplitudeCarrier
