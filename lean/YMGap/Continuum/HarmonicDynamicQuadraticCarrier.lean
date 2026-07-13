/-
# Dynamic first-crossing quadratic carrier

This module keeps the actual first-crossing seed.  It rewrites every later
terminal gap as the crossing overshoot minus the exact intervening node
window, then inserts the local overshoot bound into the positive-tail
quadratic carrier.  Thus the fixed seed disappears completely: the carrier
is controlled by the single crossing coefficient and its forward local
coefficient window.
-/

import YMGap.Continuum.HarmonicDynamicFirstCrossingCap
import YMGap.Continuum.HarmonicQuadraticCapAll

namespace YMGap.Continuum.HarmonicDynamicQuadraticCarrier

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicDynamicFirstCrossingCap
open YMGap.Continuum.HarmonicCarrierGapK17Fence
open YMGap.Continuum.HarmonicDABoundTransport
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicQuadraticCapAll
open YMGap.Continuum.HarmonicQuadraticBoundaryAll
open YMGap.Continuum.HarmonicSignedChordQuadraticCap
open YMGap.Continuum.HarmonicSignedChordAbsorption
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

/-- Exact node-coefficient window strictly after `s`. -/
def crossingCoeffWindow (k s n : Nat) : Q' :=
  intervalSum (fun p => trapezoidNodeCoeff k (p + 1)) s n

/-- The dynamic upper envelope obtained by paying the first-crossing
overshoot with `-q_s` and retaining the exact subsequent node window. -/
def crossingGapEnvelope (k s n : Nat) : Q' :=
  -(trapezoidNodeCoeff k s) + -(crossingCoeffWindow k s n)

private theorem cumulative_window_eqv (k s : Nat) : ∀ n : Nat,
    trapezoidNodeCumulative k (s + n) ≈
      trapezoidNodeCumulative k s + crossingCoeffWindow k s n
  | 0 => by
      unfold crossingCoeffWindow intervalSum
      simp only [Nat.add_zero, fsum_zero]
      exact Q'.eqv_symm (q_add_zero_eqv _)
  | n + 1 => by
      have ih := cumulative_window_eqv k s n
      have hstep := trapezoidNodeCumulative_succ_eq k (s + n)
      rw [show s + (n + 1) = (s + n) + 1 by omega]
      refine Q'.eqv_trans _ _ _ hstep ?_
      unfold crossingCoeffWindow intervalSum at ih ⊢
      rw [fsum_succ]
      refine Q'.eqv_trans _
        ((trapezoidNodeCumulative k s +
          fsum (fun j => trapezoidNodeCoeff k (s + j + 1)) n) +
          trapezoidNodeCoeff k (s + n + 1)) _ ?_ ?_
      · exact Q'.add_eqv_congr_right _ _ _ ih
      · simpa only [Nat.add_assoc] using
          (Q'.add_assoc_eqv (trapezoidNodeCumulative k s)
            (fsum (fun j => trapezoidNodeCoeff k (s + j + 1)) n)
            (trapezoidNodeCoeff k (s + n + 1)))

private theorem terminal_gap_window_algebra (x y w : Q') :
    x + -(y + w) ≈ (x + -y) + -w := by
  ring_qeqv

/-- Every later terminal gap is the crossing gap minus the exact intervening
node-coefficient window. -/
theorem terminalGap_add_eqv_envelopeBase (k L s n : Nat) :
    terminalGap k L (s + n) ≈
      terminalGap k L s + -(crossingCoeffWindow k s n) := by
  unfold terminalGap
  refine Q'.eqv_trans _
    (trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s + crossingCoeffWindow k s n)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (cumulative_window_eqv k s n))
  · exact terminal_gap_window_algebra _ _ _

/-- Dynamic pointwise carrier control.  No fixed seed occurs: at a nonzero
first crossing every later gap is bounded by the magnitude of the crossing
coefficient plus the exact signed forward window. -/
theorem terminalGap_le_crossingGapEnvelope
    {k L s : Nat} (hs : 0 < s)
    (hfirst : ∀ p, p < s → terminalGap k L p ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤ terminalGap k L s) (n : Nat) :
    terminalGap k L (s + n) ≤ crossingGapEnvelope k s n := by
  have hover := first_crossing_overshoot_le hs hfirst hboundary
  have hadd := Q'.add_le_add_right _ _
    (-(crossingCoeffWindow k s n)) hover
  unfold crossingGapEnvelope
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (terminalGap_add_eqv_envelopeBase k L s n)) hadd

/-- The quadratic local-window carrier attached to a dynamic crossing. -/
def crossingWindowCarrier (k s n : Nat) : Q' :=
  fsum (fun j =>
    crossingGapEnvelope k s j *
      harmonicChordQuadraticWeight k (s + j)) n

/-- Slack in replacing the actual crossing gap by the coefficient bound. -/
def crossingOvershootSlack (k L s : Nat) : Q' :=
  -(trapezoidNodeCoeff k s) + -(terminalGap k L s)

/-- The overshoot slack is nonnegative at a nonzero first crossing. -/
theorem crossingOvershootSlack_nonnegative
    {k L s : Nat} (hs : 0 < s)
    (hfirst : ∀ p, p < s → terminalGap k L p ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤ terminalGap k L s) :
    (0 : Q') ≤ crossingOvershootSlack k L s := by
  unfold crossingOvershootSlack
  exact Q'.sub_nonneg_of_le
    (first_crossing_overshoot_le hs hfirst hboundary)

private theorem envelope_slack_algebra (g q w : Q') :
    (-q) + (-w) ≈ (g + (-w)) + ((-q) + (-g)) := by
  let x := (-q) + (-w)
  have hzero : g + (-g) ≈ (0 : Q') := Q'.add_neg_self_eqv g
  have hins : x ≈ x + (g + (-g)) := by
    refine Q'.eqv_trans _ (x + (0 : Q')) _
      (Q'.eqv_symm (q_add_zero_eqv x)) ?_
    exact Q'.add_eqv_congr_left x _ _ (Q'.eqv_symm hzero)
  refine Q'.eqv_trans _ _ _ hins ?_
  unfold x
  ring_qeqv

/-- Exact accounting identity: the coefficient envelope is the actual later
gap plus one seed slack independent of the later cell. -/
theorem crossingGapEnvelope_eqv_terminalGap_add_slack
    (k L s n : Nat) :
    crossingGapEnvelope k s n ≈
      terminalGap k L (s + n) + crossingOvershootSlack k L s := by
  have hg := terminalGap_add_eqv_envelopeBase k L s n
  unfold crossingGapEnvelope crossingOvershootSlack
  refine Q'.eqv_trans _
    ((terminalGap k L s + -(crossingCoeffWindow k s n)) +
      (-(trapezoidNodeCoeff k s) + -(terminalGap k L s))) _ ?_ ?_
  · exact envelope_slack_algebra _ _ _
  · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hg)

/-- Exact global amplification formula for the overshoot substitution.  The
same seed slack is multiplied by the entire remaining quadratic cumulative
weight.  A uniform proof must control this product or retain the actual gap;
the bare inequality `gap ≤ -q_s` cannot be summed for free. -/
theorem crossingWindowCarrier_eqv_moment_add_slack
    (k L s : Nat) (hsL : s ≤ L) :
    crossingWindowCarrier k s (L - s) ≈
      signedChordQuadraticNodeMoment k s (L - s) +
        crossingOvershootSlack k L s *
          harmonicChordQuadraticCumulative k s (L - s) := by
  let W := fun j => harmonicChordQuadraticWeight k (s + j)
  let R := crossingOvershootSlack k L s
  have hSL : s + (L - s) = L := Nat.add_sub_of_le hsL
  have hterm : ∀ j,
      crossingGapEnvelope k s j * W j ≈
        terminalGap k L (s + j) * W j + R * W j := by
    intro j
    refine Q'.eqv_trans _
      ((terminalGap k L (s + j) + R) * W j) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (crossingGapEnvelope_eqv_terminalGap_add_slack k L s j)
    · exact Q'.add_mul_eqv _ _ _
  have hcongr := CubeRatioBounds.fsum_eqv_congr
    (fun j => crossingGapEnvelope k s j * W j)
    (fun j => terminalGap k L (s + j) * W j + R * W j) hterm (L - s)
  have hsplit := CubeRatioBounds.fsum_add
    (fun j => terminalGap k L (s + j) * W j)
    (fun j => R * W j) (L - s)
  have hpull := CubeRatioBounds.fsum_const_mul R W (L - s)
  have hcarrier := signedChordQuadraticNodeMoment_eq_carrier k s (L - s)
  rw [hSL] at hcarrier
  have hcarrier' :
      fsum (fun j => terminalGap k L (s + j) * W j) (L - s) ≈
        signedChordQuadraticNodeMoment k s (L - s) := by
    exact Q'.eqv_symm (by
      simpa only [intervalSum, terminalGap, W] using hcarrier)
  unfold crossingWindowCarrier harmonicChordQuadraticCumulative intervalSum
  refine Q'.eqv_trans _ _ _ hcongr (Q'.eqv_trans _ _ _ hsplit ?_)
  exact Q'.add_eqv_congr' hcarrier' (Q'.eqv_symm hpull)

/-- Residual carrier after removing the single crossing-coefficient payment.
Its cell at `j=0` is exactly zero. -/
def crossingWindowResidual (k s n : Nat) : Q' :=
  fsum (fun j =>
    (-(crossingCoeffWindow k s j)) *
      harmonicChordQuadraticWeight k (s + j)) n

private theorem envelope_mul_split (q u W : Q') :
    ((-q) + (-u)) * W ≈ (-q) * W + (-u) * W := by
  exact Q'.add_mul_eqv _ _ _

/-- Exact split of the dynamic carrier into one local crossing payment and a
forward residual which starts at zero. -/
theorem crossingWindowCarrier_eqv_seed_add_residual (k s n : Nat) :
    crossingWindowCarrier k s n ≈
      (-(trapezoidNodeCoeff k s)) *
          harmonicChordQuadraticCumulative k s n +
        crossingWindowResidual k s n := by
  let q := trapezoidNodeCoeff k s
  let W := fun j => harmonicChordQuadraticWeight k (s + j)
  let U := fun j => -(crossingCoeffWindow k s j)
  have hterm : ∀ j, crossingGapEnvelope k s j * W j ≈
      (-q) * W j + U j * W j := by
    intro j
    unfold crossingGapEnvelope q U
    exact envelope_mul_split _ _ _
  have hcongr := CubeRatioBounds.fsum_eqv_congr
    (fun j => crossingGapEnvelope k s j * W j)
    (fun j => (-q) * W j + U j * W j) hterm n
  have hsplit := CubeRatioBounds.fsum_add
    (fun j => (-q) * W j) (fun j => U j * W j) n
  have hpull := CubeRatioBounds.fsum_const_mul (-q) W n
  refine Q'.eqv_trans _ _ _ hcongr (Q'.eqv_trans _ _ _ hsplit ?_)
  unfold crossingWindowResidual
    harmonicChordQuadraticCumulative intervalSum q W U
  exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hpull)

/-- The positive-tail quadratic node moment is bounded by a carrier involving
only the single crossing coefficient and its exact forward coefficient
window.  This is the local dynamic input wanted by the normalized barrier. -/
theorem signedChordQuadraticNodeMoment_le_crossingWindowCarrier
    {k L s : Nat} (hs : 0 < s) (hsL : s ≤ L)
    (hfirst : ∀ p, p < s → terminalGap k L p ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤ terminalGap k L s) :
    signedChordQuadraticNodeMoment k s (L - s) ≤
      crossingWindowCarrier k s (L - s) := by
  have hSL : s + (L - s) = L := Nat.add_sub_of_le hsL
  have he := signedChordQuadraticNodeMoment_eq_carrier k s (L - s)
  rw [hSL] at he
  have he' : signedChordQuadraticNodeMoment k s (L - s) ≈
      fsum (fun j =>
        terminalGap k L (s + j) *
          harmonicChordQuadraticWeight k (s + j)) (L - s) := by
    simpa only [intervalSum, terminalGap] using he
  have hterm : ∀ j, j < L - s →
      terminalGap k L (s + j) * harmonicChordQuadraticWeight k (s + j) ≤
        crossingGapEnvelope k s j *
          harmonicChordQuadraticWeight k (s + j) := by
    intro j _hj
    exact Q'.mul_le_mul_of_nonneg_right _ _
      (harmonicChordQuadraticWeight k (s + j))
      (terminalGap_le_crossingGapEnvelope hs hfirst hboundary j)
      (harmonicChordQuadraticWeight_nonnegative k (s + j))
  have hsum := CubeRatioBounds.fsum_mono_lt (L - s) hterm
  unfold crossingWindowCarrier
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he') hsum

/-- The dynamic moment bound with the crossing payment and zero-start
residual exposed as separate terms. -/
theorem signedChordQuadraticNodeMoment_le_seed_add_residual
    {k L s : Nat} (hs : 0 < s) (hsL : s ≤ L)
    (hfirst : ∀ p, p < s → terminalGap k L p ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤ terminalGap k L s) :
    signedChordQuadraticNodeMoment k s (L - s) ≤
      (-(trapezoidNodeCoeff k s)) *
          harmonicChordQuadraticCumulative k s (L - s) +
        crossingWindowResidual k s (L - s) := by
  exact Q'.le_trans' _ _ _
    (signedChordQuadraticNodeMoment_le_crossingWindowCarrier
      hs hsL hfirst hboundary)
    (Q'.le_of_eqv (crossingWindowCarrier_eqv_seed_add_residual
      k s (L - s)))

private theorem local_crossing_diagonal_algebra (D E B d : Q') :
    -(D * E + -(B * d)) ≈ B * d + -(D * E) := by
  ring_qeqv

/-- The magnitude of any nonzero crossing coefficient is bounded by its
single local diagonal payment.  This keeps a useful local quantity instead
of replacing it by the whole diagonal norm. -/
theorem neg_trapezoidNodeCoeff_le_localDiag
    (k i : Nat) :
    -(trapezoidNodeCoeff k (i + 1)) ≤
      ((harmonicA k + twoInvSq k * harmonicD k) +
        (harmonicA k + twoInvSq k * harmonicD k)) *
          oldDiag k (i + 1) := by
  let D := harmonicD k
  let E := oldAdj k i + oldAdj k (i + 1)
  let B := (harmonicA k + twoInvSq k * harmonicD k) +
    (harmonicA k + twoInvSq k * harmonicD k)
  let d := oldDiag k (i + 1)
  have hDE0 : (0 : Q') ≤ D * E := by
    have hE0 : (0 : Q') ≤ E := by
      unfold E oldAdj
      exact Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg k) i)
          (coeffW_nonneg (harmW_nonneg k) (i + 1)))
        (Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg k) (i + 1))
          (coeffW_nonneg (harmW_nonneg k) (i + 1 + 1)))
    exact Q'.mul_nonneg _ _ (Q'.le_of_lt (harmonicD_pos k)) hE0
  have hdrop : B * d + -(D * E) ≤ B * d := by
    have hn : -(D * E) ≤ (0 : Q') :=
      Q'.le_trans' _ _ _ (Q'.neg_le_neg hDE0)
        (Q'.le_of_eqv (by decide : (-(0 : Q')) ≈ (0 : Q')))
    have hadd := Q'.add_le_add_left (B * d) _ _ hn
    exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (q_add_zero_eqv _))
  unfold trapezoidNodeCoeff
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (local_crossing_diagonal_algebra D E B d)) hdrop

/-- The isolated crossing payment is controlled by a genuinely local
diagonal coefficient times the exact remaining quadratic weight. -/
theorem crossing_seed_payment_le_localDiag
    {k s n : Nat} (hs : 0 < s) :
    (-(trapezoidNodeCoeff k s)) *
        harmonicChordQuadraticCumulative k s n ≤
      (((harmonicA k + twoInvSq k * harmonicD k) +
          (harmonicA k + twoInvSq k * harmonicD k)) * oldDiag k s) *
        harmonicChordQuadraticCumulative k s n := by
  obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
  have hW0 : (0 : Q') ≤
      harmonicChordQuadraticCumulative k (i + 1) n := by
    unfold harmonicChordQuadraticCumulative intervalSum
    exact BondMovingStep.fsum_nonneg
      (fun j => harmonicChordQuadraticWeight_nonnegative k (i + 1 + j)) n
  exact Q'.mul_le_mul_of_nonneg_right _ _
    (harmonicChordQuadraticCumulative k (i + 1) n)
    (neg_trapezoidNodeCoeff_le_localDiag k i) hW0

/-- Uniform retune rate for the doubled local diagonal payment. -/
def dynamicPairRate (k : Nat) : Q' :=
  (retuneCube (harmW k) + twoInvSq k) +
    (retuneCube (harmW k) + twoInvSq k)

private theorem pair_collect (r lam D : Q') :
    (r * D + lam * D) + (r * D + lam * D) ≈
      ((r + lam) + (r + lam)) * D := by
  ring_qeqv

private theorem actual_pair_le_retune_pair {k : Nat} (hk : 1 ≤ k) :
    (harmonicA k + twoInvSq k * harmonicD k) +
        (harmonicA k + twoInvSq k * harmonicD k) ≤
      dynamicPairRate k * harmonicD k := by
  have hA : harmonicA k ≤ retuneCube (harmW k) * harmonicD k := by
    simpa only [harmonicA, harmonicD] using
      (HarmonicThetaPascalClosure.harmonic_physical_cutoff_retune (k := k) hk)
  have hs := Q'.add_le_add hA
    (Q'.le_refl' (twoInvSq k * harmonicD k))
  have ht := Q'.add_le_add hs hs
  unfold dynamicPairRate
  exact Q'.le_trans' _ _ _ ht
    (Q'.le_of_eqv (pair_collect (retuneCube (harmW k))
      (twoInvSq k) (harmonicD k)))

/-- The crossing coefficient itself has a uniform local retune bound. -/
theorem neg_trapezoidNodeCoeff_le_retuneLocalDiag
    {k i : Nat} (hk : 1 ≤ k) :
    -(trapezoidNodeCoeff k (i + 1)) ≤
      (dynamicPairRate k * harmonicD k) * oldDiag k (i + 1) := by
  have hd0 : (0 : Q') ≤ oldDiag k (i + 1) := by
    unfold oldDiag
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) (i + 1))
      (coeffW_nonneg (harmW_nonneg k) (i + 1))
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (oldDiag k (i + 1))
    (actual_pair_le_retune_pair hk) hd0
  exact Q'.le_trans' _ _ _
    (neg_trapezoidNodeCoeff_le_localDiag k i) hm

/-- Fully uniform local bound on the isolated seed payment.  The only
seed-dependent quantity left is the true local diagonal times the remaining
quadratic weight; neither is replaced by a whole-norm worst case. -/
theorem crossing_seed_payment_le_retuneLocal
    {k s n : Nat} (hk : 1 ≤ k) (hs : 0 < s) :
    (-(trapezoidNodeCoeff k s)) *
        harmonicChordQuadraticCumulative k s n ≤
      ((dynamicPairRate k * harmonicD k) * oldDiag k s) *
        harmonicChordQuadraticCumulative k s n := by
  obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
  have hW0 : (0 : Q') ≤
      harmonicChordQuadraticCumulative k (i + 1) n := by
    unfold harmonicChordQuadraticCumulative intervalSum
    exact BondMovingStep.fsum_nonneg
      (fun j => harmonicChordQuadraticWeight_nonnegative k (i + 1 + j)) n
  exact Q'.mul_le_mul_of_nonneg_right _ _
    (harmonicChordQuadraticCumulative k (i + 1) n)
    (neg_trapezoidNodeCoeff_le_retuneLocalDiag hk) hW0

/-- Retune-local envelope with the seed payment and forward window kept in
the same cell.  This form preserves their large far-tail cancellation. -/
def retuneCrossingEnvelope (k s n : Nat) : Q' :=
  (dynamicPairRate k * harmonicD k) * oldDiag k s +
    -(crossingCoeffWindow k s n)

/-- Cellwise-recombined retune carrier. -/
def retuneWindowCarrier (k s n : Nat) : Q' :=
  fsum (fun j =>
    retuneCrossingEnvelope k s j *
      harmonicChordQuadraticWeight k (s + j)) n

/-- Exact recombination of the retune-local seed payment and residual. -/
theorem retuneWindowCarrier_eqv_local_add_residual (k s n : Nat) :
    retuneWindowCarrier k s n ≈
      ((dynamicPairRate k * harmonicD k) * oldDiag k s) *
          harmonicChordQuadraticCumulative k s n +
        crossingWindowResidual k s n := by
  let b := (dynamicPairRate k * harmonicD k) * oldDiag k s
  let W := fun j => harmonicChordQuadraticWeight k (s + j)
  let U := fun j => -(crossingCoeffWindow k s j)
  have hterm : ∀ j, retuneCrossingEnvelope k s j * W j ≈
      b * W j + U j * W j := by
    intro j
    unfold retuneCrossingEnvelope b U
    exact Q'.add_mul_eqv _ _ _
  have hcongr := CubeRatioBounds.fsum_eqv_congr
    (fun j => retuneCrossingEnvelope k s j * W j)
    (fun j => b * W j + U j * W j) hterm n
  have hsplit := CubeRatioBounds.fsum_add
    (fun j => b * W j) (fun j => U j * W j) n
  have hpull := CubeRatioBounds.fsum_const_mul b W n
  refine Q'.eqv_trans _ _ _ hcongr (Q'.eqv_trans _ _ _ hsplit ?_)
  unfold crossingWindowResidual
    harmonicChordQuadraticCumulative intervalSum b W U
  exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hpull)

/-- At an admissible nonzero first crossing, every recombined retune envelope
inside the terminal interval is nonnegative. -/
theorem retuneCrossingEnvelope_nonnegative
    {k L s n : Nat} (hk : 1 ≤ k) (hs : 0 < s) (hsL : s ≤ L)
    (hfirst : ∀ p, p < s → terminalGap k L p ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤ terminalGap k L s)
    (hnL : s + n ≤ L) :
    (0 : Q') ≤ retuneCrossingEnvelope k s n := by
  have hgap : (0 : Q') ≤ terminalGap k L (s + n) := by
    unfold terminalGap
    exact terminal_carrier_gap_nonneg_from_split k L s hsL
      (by simpa only [terminalGap] using hboundary) (by omega) hnL
  have henv := terminalGap_le_crossingGapEnvelope hs hfirst hboundary n
  have hseed : -(trapezoidNodeCoeff k s) ≤
      (dynamicPairRate k * harmonicD k) * oldDiag k s := by
    obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
    exact neg_trapezoidNodeCoeff_le_retuneLocalDiag hk
  have hadd := Q'.add_le_add_right _ _
    (-(crossingCoeffWindow k s n)) hseed
  exact Q'.le_trans' _ _ _ hgap
    (Q'.le_trans' _ _ _ henv (by
      unfold crossingGapEnvelope retuneCrossingEnvelope
      exact hadd))

/-- Localized upper bound for the complete terminal-corrected quadratic
carrier at a nonzero dynamic crossing. -/
def dynamicQuadraticNodeUpper (k s : Nat) : Q' :=
  (((dynamicPairRate k * harmonicD k) * oldDiag k s) *
      harmonicChordQuadraticCumulative k s (Ncut k - 1 - s) +
    crossingWindowResidual k s (Ncut k - 1 - s)) +
  (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k)

/-- The localized upper bound is exactly the recombined cellwise carrier plus
the two terminal corrections. -/
theorem dynamicQuadraticNodeUpper_eqv_retuneWindowCarrier (k s : Nat) :
    dynamicQuadraticNodeUpper k s ≈
      retuneWindowCarrier k s (Ncut k - 1 - s) +
        (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) := by
  unfold dynamicQuadraticNodeUpper
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_symm (retuneWindowCarrier_eqv_local_add_residual
      k s (Ncut k - 1 - s)))

/-- End-to-end localization of the frontier carrier.  The global quadratic
moment is reduced by proved inequalities to a true local diagonal payment
and the zero-start forward residual. -/
theorem quadraticNodeTotal_le_dynamicQuadraticNodeUpper
    {k s : Nat} (hk : 1 ≤ k) (hs : 0 < s) (hsL : s ≤ Ncut k - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k p) ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤
      trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k s)) :
    quadraticNodeTotal k s ≤ dynamicQuadraticNodeUpper k s := by
  let L := Ncut k - 1
  have hfirst' : ∀ p, p < s → terminalGap k L p ≤ (0 : Q') := by
    intro p hp
    simpa only [terminalGap, L] using hfirst p hp
  have hboundary' : (0 : Q') ≤ terminalGap k L s := by
    simpa only [terminalGap, L] using hboundary
  have hm := signedChordQuadraticNodeMoment_le_seed_add_residual
    hs hsL hfirst' hboundary'
  have hseed := crossing_seed_payment_le_retuneLocal
    (k := k) (s := s) (n := L - s) hk hs
  have hsr := Q'.add_le_add_right _ _
    (crossingWindowResidual k s (L - s)) hseed
  have hmoment := Q'.le_trans' _ _ _ hm hsr
  have hadd := Q'.add_le_add_right _ _
    (trapezoidTerminalCorrection k + trapezoidTerminalCorrection k) hmoment
  simpa only [quadraticNodeTotal, dynamicQuadraticNodeUpper, L] using hadd

/-- A normalized bound on the localized dynamic upper carrier supplies the
existing normalized barrier certificate for the genuine quadratic carrier. -/
theorem quadraticNodeBarrierCertificate_of_dynamicUpper
    {k s : Nat} (hk : 1 ≤ k) (hs : 0 < s) (hsL : s ≤ Ncut k - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k p) ≤ (0 : Q'))
    (hboundary : (0 : Q') ≤
      trapezoidNodeCumulative k (Ncut k - 1) +
        -(trapezoidNodeCumulative k s))
    (hlocal :
      Q'.ofNat ((k + 2) * (k + 2)) * dynamicQuadraticNodeUpper k s ≤
        quadraticNodeBarrier k * quadraticNodeNormDen k) :
    QuadraticNodeBarrierCertificate k s := by
  have hscale0 : (0 : Q') ≤ Q'.ofNat ((k + 2) * (k + 2)) :=
    Q'.ofNat_nonneg _
  have htot := quadraticNodeTotal_le_dynamicQuadraticNodeUpper
    hk hs hsL hfirst hboundary
  have hm := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat ((k + 2) * (k + 2))) htot hscale0
  unfold QuadraticNodeBarrierCertificate
  exact Q'.le_trans' _ _ _ hm hlocal

private def squareTail17 (j : Nat) : Q' :=
  coeffW (harmW 17) (9 + j) * coeffW (harmW 17) (9 + j)

private theorem squareTail17_step (j : Nat) :
    squareTail17 (j + 1) ≤ (rate17 * rate17) * squareTail17 j := by
  have hs := tail_step17 (a := 9 + j) (by omega)
  have hc0 := coeffW_nonneg (harmW_nonneg 17) (9 + j)
  have hc10 := coeffW_nonneg (harmW_nonneg 17) (9 + j + 1)
  have hr0 : (0 : Q') ≤ rate17 * coeffW (harmW 17) (9 + j) :=
    Q'.mul_nonneg _ _ (by unfold rate17; decide) hc0
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _
    (coeffW (harmW 17) (9 + j + 1)) hs hc10
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _
    (rate17 * coeffW (harmW 17) (9 + j)) hs hr0
  unfold squareTail17
  rw [show 9 + (j + 1) = 9 + j + 1 by omega]
  exact Q'.le_trans' _ _ _ h1
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (by ring_qeqv)))

private theorem squareTail17_zero_le :
    squareTail17 0 ≤ Q'.mkPos 1 400 (by decide) := by
  unfold squareTail17 harmW harmU oneSub unit coeffW dimQ c4 qpow
  decide

private theorem squareTail17_sum_le (M : Nat) :
    fsum squareTail17 M ≤ Q'.mkPos 1 50 (by decide) := by
  have h := CharacterTail.geom_series_le squareTail17
    (Q'.mkPos 1 400 (by decide)) (rate17 * rate17)
    (Q'.mkPos 1 50 (by decide))
    (by unfold rate17; decide) (by decide) squareTail17_zero_le
    squareTail17_step (by unfold rate17; decide) M
  rw [MovingCutoff.fsum_eq_finSum]
  exact h

private theorem prefixD17_add_tail_le :
    coordNormSq (harmW 17) 8 + Q'.mkPos 1 50 (by decide) ≤
      Q'.ofNat 14 := by
  unfold coordNormSq harmW harmU oneSub unit coeffW dimQ c4 qpow fsum
  decide

/-- Exact finite-head/geometric-tail diagonal upper bound used by the local
window fence. -/
theorem harmonicD17_upper : harmonicD 17 ≤ Q'.ofNat 14 := by
  have h9 : 9 ≤ Ncut 17 := by unfold Ncut; decide
  let M := Ncut 17 - 9
  have hD : harmonicD 17 ≈
      coordNormSq (harmW 17) 8 + fsum squareTail17 (M + 1) := by
    unfold harmonicD coordNormSq squareTail17
    rw [show Ncut 17 + 1 = 9 + (M + 1) by unfold M; omega]
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW (harmW 17) a * coeffW (harmW 17) a) 9 (M + 1)
  have hadd := Q'.add_le_add_left (coordNormSq (harmW 17) 8) _ _
    (squareTail17_sum_le (M + 1))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hD)
    (Q'.le_trans' _ _ _ hadd prefixD17_add_tail_le)

private def massUpper17 : Q' := Q'.mkPos 2 25 (by decide)

private theorem prefixMass17_upper :
    coordNormSq (harmW 17) 8 - adjCorr (harmW 17) 8 ≤
      massUpper17 * coordNormSq (harmW 17) 8 := by
  unfold massUpper17 coordNormSq adjCorr harmW harmU oneSub unit coeffW
    dimQ c4 qpow fsum
  decide

theorem harmonicMass17_le : harmonicMass 17 ≤ massUpper17 := by
  exact harmonicMass_le_of_prefix 17 8 (Ncut 17 - 8) massUpper17
    (by unfold Ncut; omega) prefixMass17_upper

private theorem harmonicMass_mul_D17 :
    harmonicMass 17 * harmonicD 17 ≈ harmonicD 17 - harmonicA 17 := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (harmonicD 17) (harmonicMass_eq_DA 17))
    (Q'.divPos_mul_eqv _ _ _)

private theorem one_sub_mul_eqv_sub_mul (U D : Q') :
    ((1 : Q') + (-U)) * D ≈ D + -(U * D) := by
  ring_qeqv

private theorem sub_add_cancel_eqv (D A : Q') :
    (D + (-A)) + A ≈ D := by
  refine Q'.eqv_trans _ (D + ((-A) + A)) _
    (Q'.add_assoc_eqv D (-A) A) ?_
  refine Q'.eqv_trans _ (D + 0) _
    (Q'.add_eqv_congr_left D _ _ (Q'.neg_add_self_eqv A)) ?_
  exact q_add_zero_eqv D

private theorem A_lower_of_DA {A D U : Q'} (hDA : D + (-A) ≤ U * D) :
    ((1 : Q') + (-U)) * D ≤ A := by
  have hadd := Q'.add_le_add_right _ _ A hDA
  have hD : D ≤ U * D + A :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (sub_add_cancel_eqv D A)) hadd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_mul_eqv_sub_mul U D))
    (Q'.sub_le_of_le_add hD)

theorem harmonicA17_lower :
    (((1 : Q') + (-massUpper17)) * harmonicD 17) ≤ harmonicA 17 := by
  have hD0 := Q'.le_of_lt (harmonicD_pos 17)
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (harmonicD 17)
    harmonicMass17_le hD0
  have hDA : harmonicD 17 - harmonicA 17 ≤
      massUpper17 * harmonicD 17 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv harmonicMass_mul_D17) hm
  exact A_lower_of_DA hDA

/-- Positive edge part of the node-coefficient window. -/
def crossingEdgeWindow (k s n : Nat) : Q' :=
  intervalSum (fun p => oldAdj k p + oldAdj k (p + 1)) s n

private theorem actualPair_nonnegative (k : Nat) :
    (0 : Q') ≤
      (harmonicA k + twoInvSq k * harmonicD k) +
        (harmonicA k + twoInvSq k * harmonicD k) := by
  have hA := adjCorr_nonneg (harmW_nonneg k) (Ncut k)
  have hlam : (0 : Q') ≤ twoInvSq k := by
    unfold twoInvSq
    exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) k)
  have hD := Q'.le_of_lt (harmonicD_pos k)
  have hpiece : (0 : Q') ≤ harmonicA k + twoInvSq k * harmonicD k := by
    unfold harmonicA
    exact Q'.zero_le_add _ _ hA (Q'.mul_nonneg _ _ hlam hD)
  exact Q'.zero_le_add _ _ hpiece hpiece

private theorem trapezoidNodeCoeff_succ_le_edge (k p : Nat) :
    trapezoidNodeCoeff k (p + 1) ≤
      harmonicD k * (oldAdj k p + oldAdj k (p + 1)) := by
  let B := (harmonicA k + twoInvSq k * harmonicD k) +
    (harmonicA k + twoInvSq k * harmonicD k)
  let d := oldDiag k (p + 1)
  have hd0 : (0 : Q') ≤ d := by
    unfold d oldDiag
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) (p + 1))
      (coeffW_nonneg (harmW_nonneg k) (p + 1))
  have hBd0 : (0 : Q') ≤ B * d :=
    Q'.mul_nonneg _ _ (actualPair_nonnegative k) hd0
  have hn : -(B * d) ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hBd0)
      (Q'.le_of_eqv (by decide : (-(0 : Q')) ≈ (0 : Q')))
  have hadd := Q'.add_le_add_left
    (harmonicD k * (oldAdj k p + oldAdj k (p + 1))) _ _ hn
  unfold trapezoidNodeCoeff
  change harmonicD k * (oldAdj k p + oldAdj k (p + 1)) + -(B * d) ≤
    harmonicD k * (oldAdj k p + oldAdj k (p + 1))
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (q_add_zero_eqv _))

theorem crossingCoeffWindow_le_edgeWindow (k s n : Nat) :
    crossingCoeffWindow k s n ≤ harmonicD k * crossingEdgeWindow k s n := by
  have hsum := CubeRatioBounds.fsum_mono_lt n
    (fun j _ => trapezoidNodeCoeff_succ_le_edge k (s + j))
  have hpull := CubeRatioBounds.fsum_const_mul (harmonicD k)
    (fun j => oldAdj k (s + j) + oldAdj k (s + j + 1)) n
  unfold crossingCoeffWindow crossingEdgeWindow intervalSum
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hpull)

private theorem retune_edge_algebra (D r d e : Q') :
    D * (r * d + (-e)) ≈ (r * D) * d + -(D * e) := by
  ring_qeqv

/-- The recombined retune envelope has a purely local centered-edge lower
bound; this is the exact object tested by the fence below. -/
theorem retuneCrossingEnvelope_edge_lower (k s n : Nat) :
    harmonicD k *
        (dynamicPairRate k * oldDiag k s + (-crossingEdgeWindow k s n)) ≤
      retuneCrossingEnvelope k s n := by
  have hw := crossingCoeffWindow_le_edgeWindow k s n
  have hn := Q'.neg_le_neg hw
  have hadd := Q'.add_le_add_left
    ((dynamicPairRate k * harmonicD k) * oldDiag k s) _ _ hn
  unfold retuneCrossingEnvelope
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (retune_edge_algebra (harmonicD k)
      (dynamicPairRate k) (oldDiag k s) (crossingEdgeWindow k s n))) hadd

/-- Centered edge-minus-diagonal window. -/
def crossingCenteredWindow (k : Nat) (C : Q') (s n : Nat) : Q' :=
  intervalSum (fun p =>
    (oldAdj k p + oldAdj k (p + 1)) + -(C * oldDiag k (p + 1))) s n

private theorem centered_node_algebra (D E C d : Q') :
    D * E + -((C * D) * d) ≈ D * (E + -(C * d)) := by
  ring_qeqv

private theorem trapezoidNodeCoeff_succ_le_centered
    {k : Nat} {C : Q'}
    (hpair : C * harmonicD k ≤
      (harmonicA k + twoInvSq k * harmonicD k) +
        (harmonicA k + twoInvSq k * harmonicD k)) (p : Nat) :
    trapezoidNodeCoeff k (p + 1) ≤
      harmonicD k *
        ((oldAdj k p + oldAdj k (p + 1)) +
          -(C * oldDiag k (p + 1))) := by
  let B := (harmonicA k + twoInvSq k * harmonicD k) +
    (harmonicA k + twoInvSq k * harmonicD k)
  let d := oldDiag k (p + 1)
  have hd0 : (0 : Q') ≤ d := by
    unfold d oldDiag
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) (p + 1))
      (coeffW_nonneg (harmW_nonneg k) (p + 1))
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ d hpair hd0
  have hn := Q'.neg_le_neg hm
  have hadd := Q'.add_le_add_left
    (harmonicD k * (oldAdj k p + oldAdj k (p + 1))) _ _ hn
  unfold trapezoidNodeCoeff
  change harmonicD k * (oldAdj k p + oldAdj k (p + 1)) + -(B * d) ≤ _
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (centered_node_algebra (harmonicD k)
      (oldAdj k p + oldAdj k (p + 1)) C d))

theorem crossingCoeffWindow_le_centeredWindow
    {k : Nat} {C : Q'}
    (hpair : C * harmonicD k ≤
      (harmonicA k + twoInvSq k * harmonicD k) +
        (harmonicA k + twoInvSq k * harmonicD k)) (s n : Nat) :
    crossingCoeffWindow k s n ≤
      harmonicD k * crossingCenteredWindow k C s n := by
  have hsum := CubeRatioBounds.fsum_mono_lt n
    (fun j _ => trapezoidNodeCoeff_succ_le_centered hpair (s + j))
  have hpull := CubeRatioBounds.fsum_const_mul (harmonicD k)
    (fun j => (oldAdj k (s + j) + oldAdj k (s + j + 1)) +
      -(C * oldDiag k (s + j + 1))) n
  unfold crossingCoeffWindow crossingCenteredWindow intervalSum
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hpull)

private theorem retune_centered_algebra (D r d e : Q') :
    D * (r * d + (-e)) ≈ (r * D) * d + -(D * e) := by
  ring_qeqv

theorem retuneCrossingEnvelope_centered_lower
    {k : Nat} {C : Q'}
    (hpair : C * harmonicD k ≤
      (harmonicA k + twoInvSq k * harmonicD k) +
        (harmonicA k + twoInvSq k * harmonicD k)) (s n : Nat) :
    harmonicD k *
        (dynamicPairRate k * oldDiag k s +
          (-crossingCenteredWindow k C s n)) ≤
      retuneCrossingEnvelope k s n := by
  have hw := crossingCoeffWindow_le_centeredWindow hpair s n
  have hn := Q'.neg_le_neg hw
  have hadd := Q'.add_le_add_left
    ((dynamicPairRate k * harmonicD k) * oldDiag k s) _ _ hn
  unfold retuneCrossingEnvelope
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (retune_centered_algebra (harmonicD k)
      (dynamicPairRate k) (oldDiag k s) (crossingCenteredWindow k C s n))) hadd

private def centerRate17 : Q' :=
  (((1 : Q') + (-massUpper17)) + twoInvSq 17) +
    (((1 : Q') + (-massUpper17)) + twoInvSq 17)

private theorem centerRate17_pair_lower :
    centerRate17 * harmonicD 17 ≤
      (harmonicA 17 + twoInvSq 17 * harmonicD 17) +
        (harmonicA 17 + twoInvSq 17 * harmonicD 17) := by
  have hs := Q'.add_le_add harmonicA17_lower
    (Q'.le_refl' (twoInvSq 17 * harmonicD 17))
  have ht := Q'.add_le_add hs hs
  unfold centerRate17
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (pair_collect ((1 : Q') + (-massUpper17))
        (twoInvSq 17) (harmonicD 17)))) ht

private def fenceCenteredCellBase17 : Q' :=
  dynamicPairRate 17 * oldDiag 17 1 +
    (-crossingCenteredWindow 17 centerRate17 1 9)

private theorem fenceCenteredCell17_beats_normalized_barrier :
    quadraticNodeBarrier 17 * Q'.ofNat 14 <
      Q'.ofNat ((17 + 2) * (17 + 2)) *
        (fenceCenteredCellBase17 * harmonicChordQuadraticWeight 17 10) := by
  unfold fenceCenteredCellBase17 dynamicPairRate crossingCenteredWindow
    centerRate17 massUpper17 quadraticNodeBarrier
    harmonicChordQuadraticWeight harmonicChordQuadraticFactor
    harmonicEndpointQuadraticCorrection intervalSum oldAdj oldDiag
    retuneCube retuneBase twoInvSq driftSqFactor driftRatio driftDen
    harmW harmU oneSub unit invSqTerm coeffW dimQ c4 Q'.divPos Q'.recipPos
    qpow fsum
  decide

private theorem coeff17_succ_le {a : Nat} (ha : 8 ≤ a) :
    coeffW (harmW 17) (a + 1) ≤ coeffW (harmW 17) a := by
  have hs := tail_step17 (a := a) ha
  have hc0 := coeffW_nonneg (harmW_nonneg 17) a
  have hr : rate17 ≤ (1 : Q') := by unfold rate17; decide
  have hm := Q'.mul_le_mul_of_nonneg_right _ _
    (coeffW (harmW 17) a) hr hc0
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.one_mul_eqv _)))

private theorem coeff17_antitone_from {a : Nat} (ha : 8 ≤ a) :
    ∀ b, a ≤ b → coeffW (harmW 17) b ≤ coeffW (harmW 17) a
  | 0, hab => by omega
  | b + 1, hab => by
      by_cases heq : a = b + 1
      · subst a
        exact Q'.le_refl' _
      · have hab' : a ≤ b := by omega
        exact Q'.le_trans' _ _ _ (coeff17_succ_le (a := b) (by omega))
          (coeff17_antitone_from ha b hab')

private theorem coeff17_nine_le :
    coeffW (harmW 17) 9 ≤ Q'.mkPos 1 20 (by decide) := by
  unfold harmW harmU oneSub unit coeffW dimQ c4 qpow
  decide

private theorem terminalLeftCoeff17_le :
    coeffW (harmW 17) (Ncut 17 - 1) ≤ Q'.mkPos 1 20 (by decide) := by
  have ht := coeff17_antitone_from (a := 9) (by decide)
    (Ncut 17 - 1) (by unfold Ncut; omega)
  exact Q'.le_trans' _ _ _ ht coeff17_nine_le

private theorem terminalEdge17_upper :
    oldAdj 17 (Ncut 17 - 1) ≤ Q'.mkPos 1 1000 (by decide) := by
  unfold oldAdj
  rw [show Ncut 17 - 1 + 1 = Ncut 17 by unfold Ncut; omega]
  have hL0 := coeffW_nonneg (harmW_nonneg 17) (Ncut 17 - 1)
  have h1 := Q'.mul_le_mul_of_nonneg_left _ _
    (coeffW (harmW 17) (Ncut 17 - 1)) terminalCoeff17_le hL0
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.mkPos 1 50 (by decide)) terminalLeftCoeff17_le (by decide)
  exact Q'.le_trans' _ _ _ h1 h2

private def gapBracket17 : Q' :=
  centerRate17 * (oldDiag 17 0 + oldDiag 17 1) +
    -(((oldAdj 17 0 + oldAdj 17 0) + oldAdj 17 1) +
      Q'.mkPos 1 1000 (by decide)) +
    -((twoInvSq 17 + twoInvSq 17) * Q'.ofNat 14)

private theorem gapBracket17_pos : (0 : Q') < gapBracket17 := by
  unfold gapBracket17 centerRate17 massUpper17 twoInvSq invSqTerm
    oldAdj oldDiag harmW harmU oneSub unit coeffW dimQ c4 qpow
  decide

private def actualPair17 : Q' :=
  (harmonicA 17 + twoInvSq 17 * harmonicD 17) +
    (harmonicA 17 + twoInvSq 17 * harmonicD 17)

private theorem headNodeOne17_lower :
    (centerRate17 * harmonicD 17) * (oldDiag 17 0 + oldDiag 17 1) ≤
      (actualPair17 * oldDiag 17 0 + actualPair17 * oldDiag 17 1) +
        actualPair17 * oldDiag 17 (Ncut 17) := by
  let S := oldDiag 17 0 + oldDiag 17 1
  have hS0 : (0 : Q') ≤ S := by
    unfold S oldDiag
    exact Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 17) 0)
        (coeffW_nonneg (harmW_nonneg 17) 0))
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 17) 1)
        (coeffW_nonneg (harmW_nonneg 17) 1))
  have hmain := Q'.mul_le_mul_of_nonneg_right _ _ S
    centerRate17_pair_lower hS0
  have hterm0 : (0 : Q') ≤ actualPair17 * oldDiag 17 (Ncut 17) := by
    have hd0 : (0 : Q') ≤ oldDiag 17 (Ncut 17) := by
      unfold oldDiag
      exact Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 17) (Ncut 17))
        (coeffW_nonneg (harmW_nonneg 17) (Ncut 17))
    unfold actualPair17
    exact Q'.mul_nonneg _ _ (actualPair_nonnegative 17) hd0
  have hfactor : actualPair17 * S ≈
      actualPair17 * oldDiag 17 0 + actualPair17 * oldDiag 17 1 := by
    unfold S
    exact Q'.mul_add_eqv _ _ _
  have htail := Q'.add_le_self_of_nonneg
    (actualPair17 * oldDiag 17 0 + actualPair17 * oldDiag 17 1)
    (actualPair17 * oldDiag 17 (Ncut 17)) hterm0
  exact Q'.le_trans' _ _ _ hmain
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) htail)

private theorem edgeNodeOne17_lower :
    -(harmonicD 17 *
        ((((oldAdj 17 0 + oldAdj 17 0) + oldAdj 17 1)) +
          Q'.mkPos 1 1000 (by decide))) ≤
      -(harmonicD 17 *
        (((oldAdj 17 0 + oldAdj 17 0) + oldAdj 17 1) +
          oldAdj 17 (Ncut 17 - 1))) := by
  have he := Q'.add_le_add_left
    ((oldAdj 17 0 + oldAdj 17 0) + oldAdj 17 1) _ _ terminalEdge17_upper
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 17) he
    (Q'.le_of_lt (harmonicD_pos 17))
  exact Q'.neg_le_neg hm

private theorem budgetNodeOne17_lower :
    -((twoInvSq 17 + twoInvSq 17) *
        (harmonicD 17 * Q'.ofNat 14)) ≤
      -((twoInvSq 17 + twoInvSq 17) *
        (harmonicD 17 * harmonicD 17)) := by
  have hDD := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 17)
    harmonicD17_upper (Q'.le_of_lt (harmonicD_pos 17))
  have hl : (0 : Q') ≤ twoInvSq 17 + twoInvSq 17 := by
    have h : (0 : Q') ≤ twoInvSq 17 := by
      unfold twoInvSq
      exact Q'.mul_nonneg _ _ (by decide) (invSqTerm_nonneg 2 (by decide) 17)
    exact Q'.zero_le_add _ _ h h
  exact Q'.neg_le_neg
    (Q'.mul_le_mul_of_nonneg_left _ _ (twoInvSq 17 + twoInvSq 17) hDD hl)

private theorem slack_collect_local
    (D C S E lam d : Q') :
    ((C * D) * S + -(D * E)) + -((lam + lam) * (D * d)) ≈
      D * ((C * S + (-E)) + -((lam + lam) * d)) := by
  ring_qeqv

private def nodeOneSlack17 : Q' :=
  ((actualPair17 * oldDiag 17 0 + actualPair17 * oldDiag 17 1) +
      actualPair17 * oldDiag 17 (Ncut 17)) +
    -(harmonicD 17 *
      (((oldAdj 17 0 + oldAdj 17 0) + oldAdj 17 1) +
        oldAdj 17 (Ncut 17 - 1))) +
    -((twoInvSq 17 + twoInvSq 17) *
      (harmonicD 17 * harmonicD 17))

private theorem carrierNodeOne17_lower :
    harmonicD 17 * gapBracket17 ≤ nodeOneSlack17 := by
  have hall := Q'.add_le_add
    (Q'.add_le_add headNodeOne17_lower edgeNodeOne17_lower)
    budgetNodeOne17_lower
  unfold gapBracket17
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
    (slack_collect_local (harmonicD 17) centerRate17
      (oldDiag 17 0 + oldDiag 17 1)
      (((oldAdj 17 0 + oldAdj 17 0) + oldAdj 17 1) +
        Q'.mkPos 1 1000 (by decide))
      (twoInvSq 17) (Q'.ofNat 14))) hall

/-- Exact crossing identification at the first bad total-gap scale: node zero
is still negative, while node one is already nonnegative. -/
theorem node_one_boundary_holds_k17 :
    (0 : Q') ≤ terminalGap 17 (Ncut 17 - 1) 1 := by
  have hid := carrier_node_one_gap_eq_slack 17
  have hpos : (0 : Q') < harmonicD 17 * gapBracket17 := by
    have hm := Q'.mul_lt_mul_of_pos_left (harmonicD_pos 17) gapBracket17_pos
    exact Q'.lt_of_le_of_lt
      (Q'.ge_of_eqv (Q'.mul_zero_eqv (harmonicD 17))) hm
  unfold terminalGap
  exact Q'.le_trans' _ _ _ (Q'.le_of_lt hpos)
    (Q'.le_trans' _ _ _ carrierNodeOne17_lower (by
      unfold nodeOneSlack17 actualPair17
      exact Q'.ge_of_eqv hid))

private theorem nonpos_of_not_nonnegative {a : Q'}
    (h : ¬ ((0 : Q') ≤ a)) : a ≤ (0 : Q') := by
  have hlt : a < (0 : Q') := by
    have hh : ¬ ((0 : Q').num * (a.den : Int) ≤
        a.num * (((0 : Q').den) : Int)) := h
    exact Int.not_le.mp hh
  exact Q'.le_of_lt hlt

private theorem first_crossing17_first :
    ∀ p, p < 1 → terminalGap 17 (Ncut 17 - 1) p ≤ (0 : Q') := by
  intro p hp
  have hp0 : p = 0 := by omega
  subst p
  exact nonpos_of_not_nonnegative terminal_carrier_total_gap_fails_k17

private theorem retuneEnvelope17_nonnegative (j : Nat)
    (hj : j < Ncut 17 - 1 - 1) :
    (0 : Q') ≤ retuneCrossingEnvelope 17 1 j := by
  apply retuneCrossingEnvelope_nonnegative
    (k := 17) (L := Ncut 17 - 1) (s := 1)
  · decide
  · decide
  · unfold Ncut; omega
  · exact first_crossing17_first
  · exact node_one_boundary_holds_k17
  · omega

private theorem retuneCell17_nonnegative (j : Nat)
    (hj : j < Ncut 17 - 1 - 1) :
    (0 : Q') ≤
      retuneCrossingEnvelope 17 1 j *
        harmonicChordQuadraticWeight 17 (1 + j) :=
  Q'.mul_nonneg _ _ (retuneEnvelope17_nonnegative j hj)
    (harmonicChordQuadraticWeight_nonnegative 17 (1 + j))

private theorem fsum_nonnegative_bounded (f : Nat → Q') : ∀ n,
    (∀ i, i < n → (0 : Q') ≤ f i) → (0 : Q') ≤ fsum f n
  | 0, _ => Q'.le_refl' 0
  | n + 1, hf => by
      rw [fsum_succ]
      exact Q'.zero_le_add _ _
        (fsum_nonnegative_bounded f n (fun i hi => hf i (by omega)))
        (hf n (by omega))

private theorem fenceCell17_le_retuneCarrier :
    retuneCrossingEnvelope 17 1 9 * harmonicChordQuadraticWeight 17 10 ≤
      retuneWindowCarrier 17 1 (Ncut 17 - 1 - 1) := by
  let f := fun j => retuneCrossingEnvelope 17 1 j *
    harmonicChordQuadraticWeight 17 (1 + j)
  have h9 : 9 < Ncut 17 - 1 - 1 := by unfold Ncut; omega
  have hprefix0 : (0 : Q') ≤ fsum f 9 :=
    fsum_nonnegative_bounded f 9
      (fun j hj => retuneCell17_nonnegative j (by unfold Ncut; omega))
  have hone : f 9 ≤ fsum f 10 := by
    rw [show (10 : Nat) = 9 + 1 by decide, fsum_succ]
    have h := Q'.add_le_self_of_nonneg (f 9) (fsum f 9) hprefix0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  have hmono : fsum f 10 ≤ fsum f (Ncut 17 - 1 - 1) := by
    let n := Ncut 17 - 1 - 1
    have h10 : 10 ≤ n := by unfold n Ncut; omega
    have hsplit := FusionCoreStepRoundH.fsum_split_at f 10 (n - 10)
    have hn : 10 + (n - 10) = n := Nat.add_sub_of_le h10
    rw [hn] at hsplit
    have hsuffix0 : (0 : Q') ≤ fsum (fun j => f (10 + j)) (n - 10) :=
      fsum_nonnegative_bounded _ _ (fun j hj => by
        unfold f
        have hj' : 10 + j < n := by omega
        exact retuneCell17_nonnegative (10 + j) (by
          simpa only [n] using hj'))
    have hadd := Q'.add_le_self_of_nonneg (fsum f 10)
      (fsum (fun j => f (10 + j)) (n - 10)) hsuffix0
    exact Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hsplit)
  unfold retuneWindowCarrier
  exact Q'.le_trans' _ _ _ hone hmono

private theorem mul_swap_reassoc (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  ring_qeqv

private theorem mul_scale_reassoc (D scale base W : Q') :
    D * (scale * (base * W)) ≈ scale * ((D * base) * W) := by
  ring_qeqv

private theorem normalizedCenteredBase17_exceeds_barrier :
    quadraticNodeBarrier 17 * quadraticNodeNormDen 17 <
      Q'.ofNat ((17 + 2) * (17 + 2)) *
        ((harmonicD 17 * fenceCenteredCellBase17) *
          harmonicChordQuadraticWeight 17 10) := by
  have hD0 : (0 : Q') ≤ harmonicD 17 := Q'.le_of_lt (harmonicD_pos 17)
  have hbar0 : (0 : Q') ≤ quadraticNodeBarrier 17 := by
    unfold quadraticNodeBarrier harmU unit
    decide
  have hDD : harmonicD 17 * harmonicD 17 ≤
      harmonicD 17 * Q'.ofNat 14 :=
    Q'.mul_le_mul_of_nonneg_left _ _ (harmonicD 17)
      harmonicD17_upper hD0
  have hbarD := Q'.mul_le_mul_of_nonneg_left _ _
    (quadraticNodeBarrier 17) hDD hbar0
  have hleft : quadraticNodeBarrier 17 * (harmonicD 17 * Q'.ofNat 14) ≈
      harmonicD 17 * (quadraticNodeBarrier 17 * Q'.ofNat 14) :=
    mul_swap_reassoc _ _ _
  have hle : quadraticNodeBarrier 17 *
      (harmonicD 17 * harmonicD 17) ≤
      harmonicD 17 * (quadraticNodeBarrier 17 * Q'.ofNat 14) :=
    Q'.le_trans' _ _ _ hbarD (Q'.le_of_eqv hleft)
  have hmul := Q'.mul_lt_mul_of_pos_left (harmonicD_pos 17)
    fenceCenteredCell17_beats_normalized_barrier
  have hstrict := Q'.lt_of_le_of_lt hle hmul
  have hright :
      harmonicD 17 *
        (Q'.ofNat ((17 + 2) * (17 + 2)) *
          (fenceCenteredCellBase17 * harmonicChordQuadraticWeight 17 10)) ≈
      Q'.ofNat ((17 + 2) * (17 + 2)) *
        ((harmonicD 17 * fenceCenteredCellBase17) *
          harmonicChordQuadraticWeight 17 10) :=
    mul_scale_reassoc _ _ _ _
  unfold quadraticNodeNormDen
  exact HeatKernelRGStep.lt_of_lt_of_le hstrict (Q'.le_of_eqv hright)

private theorem normalizedCenteredBase17_le_cell :
    Q'.ofNat ((17 + 2) * (17 + 2)) *
        ((harmonicD 17 * fenceCenteredCellBase17) *
          harmonicChordQuadraticWeight 17 10) ≤
      Q'.ofNat ((17 + 2) * (17 + 2)) *
        (retuneCrossingEnvelope 17 1 9 *
          harmonicChordQuadraticWeight 17 10) := by
  have hbase := retuneCrossingEnvelope_centered_lower
    centerRate17_pair_lower 1 9
  have hW0 := harmonicChordQuadraticWeight_nonnegative 17 10
  have hcell := Q'.mul_le_mul_of_nonneg_right _ _
    (harmonicChordQuadraticWeight 17 10) hbase hW0
  have hscale0 : (0 : Q') ≤ Q'.ofNat ((17 + 2) * (17 + 2)) := by decide
  exact Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat ((17 + 2) * (17 + 2))) hcell hscale0

private theorem fenceCell17_normalized_exceeds_barrier :
    quadraticNodeBarrier 17 * quadraticNodeNormDen 17 <
      Q'.ofNat ((17 + 2) * (17 + 2)) *
        (retuneCrossingEnvelope 17 1 9 *
          harmonicChordQuadraticWeight 17 10) :=
  HeatKernelRGStep.lt_of_lt_of_le normalizedCenteredBase17_exceeds_barrier
    normalizedCenteredBase17_le_cell

private theorem retuneCarrier17_normalized_exceeds_barrier :
    quadraticNodeBarrier 17 * quadraticNodeNormDen 17 <
      Q'.ofNat ((17 + 2) * (17 + 2)) *
        retuneWindowCarrier 17 1 (Ncut 17 - 1 - 1) := by
  have hscale0 : (0 : Q') ≤ Q'.ofNat ((17 + 2) * (17 + 2)) := by decide
  have hm := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat ((17 + 2) * (17 + 2)))
    fenceCell17_le_retuneCarrier hscale0
  exact HeatKernelRGStep.lt_of_lt_of_le
    fenceCell17_normalized_exceeds_barrier hm

private theorem terminalCorrection17_nonnegative :
    (0 : Q') ≤ trapezoidTerminalCorrection 17 := by
  unfold trapezoidTerminalCorrection oldAdj driftSqFactor
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (harmonicD_pos 17))
      (Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 17) (Ncut 17 - 1))
        (coeffW_nonneg (harmW_nonneg 17) (Ncut 17 - 1 + 1))))
    (Q'.mul_nonneg _ _
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos 17)) (c4 (Ncut 17)))
      (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos 17)) (c4 (Ncut 17))))

private theorem retuneCarrier17_le_dynamicUpper :
    retuneWindowCarrier 17 1 (Ncut 17 - 1 - 1) ≤
      dynamicQuadraticNodeUpper 17 1 := by
  have hcorr : (0 : Q') ≤
      trapezoidTerminalCorrection 17 + trapezoidTerminalCorrection 17 :=
    Q'.zero_le_add _ _ terminalCorrection17_nonnegative
      terminalCorrection17_nonnegative
  have hadd := Q'.add_le_self_of_nonneg
    (retuneWindowCarrier 17 1 (Ncut 17 - 1 - 1))
    (trapezoidTerminalCorrection 17 + trapezoidTerminalCorrection 17) hcorr
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv (dynamicQuadraticNodeUpper_eqv_retuneWindowCarrier 17 1))

/-- Machine-checked dead-route fence.  At the genuine first crossing
`k=17,s=1`, the retune-local diagonal substitution makes a single admissible
cell exceed the entire normalized barrier.  Therefore the residual is not
nonpositive or absorbable after that substitution; a successful dynamic
proof must keep the exact `A_k/D_k` centered cancellation. -/
theorem dynamicQuadraticNodeUpper_barrier_fails_k17_s1 :
    ¬ (Q'.ofNat ((17 + 2) * (17 + 2)) *
        dynamicQuadraticNodeUpper 17 1 ≤
      quadraticNodeBarrier 17 * quadraticNodeNormDen 17) := by
  intro hbad
  have hscale0 : (0 : Q') ≤ Q'.ofNat ((17 + 2) * (17 + 2)) := by decide
  have hm := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat ((17 + 2) * (17 + 2)))
    retuneCarrier17_le_dynamicUpper hscale0
  have hlt := HeatKernelRGStep.lt_of_lt_of_le
    retuneCarrier17_normalized_exceeds_barrier hm
  exact ClusteringImpliesGap.lt_irrefl'
    (quadraticNodeBarrier 17 * quadraticNodeNormDen 17)
    (HeatKernelRGStep.lt_of_lt_of_le hlt hbad)


#print axioms terminalGap_add_eqv_envelopeBase
#print axioms terminalGap_le_crossingGapEnvelope
#print axioms crossingOvershootSlack_nonnegative
#print axioms crossingGapEnvelope_eqv_terminalGap_add_slack
#print axioms crossingWindowCarrier_eqv_moment_add_slack
#print axioms signedChordQuadraticNodeMoment_le_crossingWindowCarrier
#print axioms crossingWindowCarrier_eqv_seed_add_residual
#print axioms signedChordQuadraticNodeMoment_le_seed_add_residual
#print axioms neg_trapezoidNodeCoeff_le_localDiag
#print axioms crossing_seed_payment_le_localDiag
#print axioms neg_trapezoidNodeCoeff_le_retuneLocalDiag
#print axioms crossing_seed_payment_le_retuneLocal
#print axioms retuneWindowCarrier_eqv_local_add_residual
#print axioms retuneCrossingEnvelope_nonnegative
#print axioms dynamicQuadraticNodeUpper_eqv_retuneWindowCarrier
#print axioms quadraticNodeTotal_le_dynamicQuadraticNodeUpper
#print axioms quadraticNodeBarrierCertificate_of_dynamicUpper
#print axioms harmonicD17_upper
#print axioms harmonicMass17_le
#print axioms harmonicA17_lower
#print axioms crossingCoeffWindow_le_centeredWindow
#print axioms retuneCrossingEnvelope_centered_lower
#print axioms node_one_boundary_holds_k17
#print axioms dynamicQuadraticNodeUpper_barrier_fails_k17_s1

end YMGap.Continuum.HarmonicDynamicQuadraticCarrier
