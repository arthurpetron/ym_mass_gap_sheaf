/-
# Quadratic signed-chord carrier cap

The second-order chord carrier introduced in
`HarmonicSignedChordQuantitative` is most useful in its positive-tail form.
This module makes that form public.  In particular, deleting an initial
segment after an admissible crossing can only decrease the quadratic carrier;
the statement is exact and does not require signs of the interpolated node
coefficients.
-/

import YMGap.Continuum.HarmonicSignedChordQuantitative

namespace YMGap.Continuum.HarmonicSignedChordQuadraticCap

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicSignedChordAbsorption
open YMGap.Continuum.HarmonicSignedChordQuantitative
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HarmonicWeightedAbelReserve
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem fsum_nonneg_lt (f : Nat → Q') : ∀ n,
    (∀ i, i < n → (0 : Q') ≤ f i) → (0 : Q') ≤ fsum f n
  | 0, _ => Q'.le_refl' 0
  | n + 1, hf => by
      rw [fsum_succ]
      exact Q'.zero_le_add _ _
        (fsum_nonneg_lt f n (fun i hi => hf i (by omega)))
        (hf n (by omega))

private theorem intervalSum_add (f : Nat → Q') (s a b : Nat) :
    intervalSum f s (a + b) ≈
      intervalSum f s a + intervalSum f (s + a) b := by
  induction b with
  | zero =>
      simp only [Nat.add_zero, intervalSum, fsum_zero]
      exact Q'.eqv_symm (q_add_zero_eqv _)
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      simp only [intervalSum, fsum_succ]
      refine Q'.eqv_trans _
        (intervalSum f s a +
          (intervalSum f (s + a) b + f (s + a + b))) _ ?_ ?_
      · exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ ih) (by
            have hidx : s + (a + b) = s + a + b := by omega
            rw [hidx]
            exact Q'.add_assoc_eqv _ _ _)
      · exact Q'.eqv_refl _

private theorem terminal_gap_weight_fubini
    (T q W : Nat → Q')
    (hstep : ∀ i, T (i + 1) ≈ T i + q (i + 1))
    (s : Nat) : ∀ n,
    intervalSum (fun p => (T (s + n) + -(T p)) * W p) s n ≈
      fsum (fun j => q (s + j + 1) * intervalSum W s (j + 1)) n
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      let L := s + n
      let qn := q (L + 1)
      let old := fun p => (T L + -(T p)) * W p
      let add := fun p => qn * W p
      have hterm : ∀ j,
          (T (s + (n + 1)) + -(T (s + j))) * W (s + j) ≈
            old (s + j) + add (s + j) := by
        intro j
        have hsuc : s + (n + 1) = L + 1 := by
          unfold L
          omega
        rw [hsuc]
        have hg : T (L + 1) + -(T (s + j)) ≈
            (T L + -(T (s + j))) + qn := by
          refine Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_right _ _ _ (hstep L)) ?_
          unfold qn
          ring_qeqv
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hg) ?_
        unfold old add
        exact Q'.add_mul_eqv _ _ _
      have hfirst :
          intervalSum
              (fun p => (T (s + (n + 1)) + -(T p)) * W p) s n ≈
            intervalSum (fun p => old p + add p) s n := by
        unfold intervalSum
        exact CubeRatioBounds.fsum_eqv_congr _ _ hterm n
      have hsplit : intervalSum (fun p => old p + add p) s n ≈
          intervalSum old s n + intervalSum add s n := by
        unfold intervalSum
        exact CubeRatioBounds.fsum_add
          (fun j => old (s + j)) (fun j => add (s + j)) n
      have haddsum : intervalSum add s n ≈
          qn * intervalSum W s n := by
        unfold intervalSum add
        exact Q'.eqv_symm
          (CubeRatioBounds.fsum_const_mul qn (fun j => W (s + j)) n)
      have hlastgap : T (s + (n + 1)) + -(T (s + n)) ≈ qn := by
        have hsuc : s + (n + 1) = L + 1 := by
          unfold L
          omega
        have hbase : s + n = L := rfl
        rw [hsuc, hbase]
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right _ _ _ (hstep L)) ?_
        unfold qn
        have hc : T L + -(T L) ≈ (0 : Q') := Q'.add_neg_self_eqv _
        refine Q'.eqv_trans _ ((T L + -(T L)) + q (L + 1)) _
          (by ring_qeqv) ?_
        refine Q'.eqv_trans _ ((0 : Q') + q (L + 1)) _
          (Q'.add_eqv_congr_right _ _ _ hc) ?_
        exact q_zero_add_eqv _
      have hlast :
          (T (s + (n + 1)) + -(T (s + n))) * W (s + n) ≈
            qn * W (s + n) :=
        Q'.mul_eqv_congr_right _ _ _ hlastgap
      have ih := terminal_gap_weight_fubini T q W hstep s n
      have hprefixSucc : intervalSum W s (n + 1) =
          intervalSum W s n + W (s + n) := rfl
      rw [show
        intervalSum
            (fun p => (T (s + (n + 1)) + -(T p)) * W p) s (n + 1) =
          intervalSum
              (fun p => (T (s + (n + 1)) + -(T p)) * W p) s n +
            (T (s + (n + 1)) + -(T (s + n))) * W (s + n) by rfl]
      rw [fsum_succ]
      refine Q'.eqv_trans _
        (intervalSum (fun p => old p + add p) s n +
          qn * W (s + n)) _
        (Q'.add_eqv_congr' hfirst hlast) ?_
      refine Q'.eqv_trans _
        ((intervalSum old s n + intervalSum add s n) +
          qn * W (s + n)) _
        (Q'.add_eqv_congr_right _ _ _ hsplit) ?_
      refine Q'.eqv_trans _
        ((intervalSum old s n + qn * intervalSum W s n) +
          qn * W (s + n)) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_eqv_congr_left _ _ _ haddsum)) ?_
      refine Q'.eqv_trans _
        (intervalSum old s n + qn * intervalSum W s (n + 1)) _ (by
          rw [hprefixSucc]
          exact Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
            (Q'.add_eqv_congr_left _ _ _
              (Q'.eqv_symm (Q'.mul_add_eqv _ _ _)))) ?_
      refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
      unfold old
      simpa using ih

/-- Exact positive-tail carrier identity for the quadratic node moment. -/
theorem signedChordQuadraticNodeMoment_eq_carrier
    (k s n : Nat) :
    signedChordQuadraticNodeMoment k s n ≈
      intervalSum
        (fun p =>
          (trapezoidNodeCumulative k (s + n) +
              -(trapezoidNodeCumulative k p)) *
            harmonicChordQuadraticWeight k p) s n := by
  have h := terminal_gap_weight_fubini
    (trapezoidNodeCumulative k) (trapezoidNodeCoeff k)
    (harmonicChordQuadraticWeight k)
    (fun i => trapezoidNodeCumulative_succ_eq k i) s n
  unfold signedChordQuadraticNodeMoment harmonicChordQuadraticCumulative
  exact Q'.eqv_symm h

/-- Every quadratic carrier weight is nonnegative. -/
theorem harmonicChordQuadraticWeight_nonnegative (k p : Nat) :
    (0 : Q') ≤ harmonicChordQuadraticWeight k p := by
  have hfactor : (0 : Q') ≤ harmonicChordQuadraticFactor k p := by
    unfold harmonicChordQuadraticFactor harmonicEndpointQuadraticCorrection
    exact Q'.zero_le_add _ _ (by decide)
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
          (ExpNeg.ofNat_nonneg' _))
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _ (unit_nonneg _ _) (unit_nonneg _ _))
          (qpow_nonneg _ (Q'.le_of_lt (driftRatio_pos k)) _)))
  exact Q'.mul_nonneg _ _ hfactor
    (driftSqFactor_increment_nonneg k p)

/-- Once a split has nonnegative terminal gaps, discarding any initial
segment can only lower the exact quadratic positive-tail carrier. -/
theorem signedChordQuadraticNodeMoment_suffix_le
    (k L s t : Nat) (hs : s ≤ t) (ht : t ≤ L)
    (hgap : ∀ p, s ≤ p → p < L →
      (0 : Q') ≤ trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k p)) :
    signedChordQuadraticNodeMoment k t (L - t) ≤
      signedChordQuadraticNodeMoment k s (L - s) := by
  let f := fun p =>
    (trapezoidNodeCumulative k L +
        -(trapezoidNodeCumulative k p)) *
      harmonicChordQuadraticWeight k p
  have hSL : s + (L - s) = L := by omega
  have hTL : t + (L - t) = L := by omega
  have hslen : t - s + (L - t) = L - s := by omega
  have hprefix0 : (0 : Q') ≤ intervalSum f s (t - s) := by
    unfold intervalSum
    apply fsum_nonneg_lt
    intro i hi
    unfold f
    exact Q'.mul_nonneg _ _
      (hgap (s + i) (by omega) (by omega))
      (harmonicChordQuadraticWeight_nonnegative k (s + i))
  have hsplit := intervalSum_add f s (t - s) (L - t)
  have hstart : s + (t - s) = t := by omega
  rw [hslen, hstart] at hsplit
  have hadd := Q'.add_le_self_of_nonneg
    (intervalSum f t (L - t)) (intervalSum f s (t - s)) hprefix0
  have hcarrier : intervalSum f t (L - t) ≤
      intervalSum f s (L - s) := by
    exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (by
      exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) (Q'.eqv_symm hsplit)))
  have heT := signedChordQuadraticNodeMoment_eq_carrier k t (L - t)
  have heS := signedChordQuadraticNodeMoment_eq_carrier k s (L - s)
  rw [hTL] at heT
  rw [hSL] at heS
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heT)
    (Q'.le_trans' _ _ _ hcarrier (Q'.ge_of_eqv heS))

/-- Crossing-specialized suffix monotonicity.  The single boundary sign at
the earlier split propagates to every later cell, so no node-coefficient sign
is exposed. -/
theorem signedChordQuadraticNodeMoment_suffix_le_of_boundary
    (k L s t : Nat) (hsL : s ≤ L) (hst : s ≤ t) (htL : t ≤ L)
    (hboundary : (0 : Q') ≤ trapezoidNodeCumulative k L +
      -(trapezoidNodeCumulative k s)) :
    signedChordQuadraticNodeMoment k t (L - t) ≤
      signedChordQuadraticNodeMoment k s (L - s) := by
  apply signedChordQuadraticNodeMoment_suffix_le k L s t hst htL
  intro p hsp hpL
  exact terminal_carrier_gap_nonneg_from_split
    k L s hsL hboundary hsp (Nat.le_of_lt hpL)

/-- Exact `k=5` crossing fence: every admissible first crossing is at zero. -/
theorem terminal_gap_k5_p0_not_nonpos :
    ¬ (trapezoidNodeCumulative 5 (Ncut 5 - 1) +
      -(trapezoidNodeCumulative 5 0) ≤ (0 : Q')) := by
  unfold trapezoidNodeCumulative harmonicD harmonicA twoInvSq oldAdj
    coordNormSq adjCorr harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    qpow Ncut fsum
  decide

/-- The quadratic cap at `k=5`, in the full admissible-crossing signature. -/
theorem signedChordQuadraticNodeMoment_le_cap_k5
    (s : Nat) (hsL : s ≤ Ncut 5 - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative 5 (Ncut 5 - 1) +
        -(trapezoidNodeCumulative 5 p) ≤ (0 : Q'))
    (_hboundary : (0 : Q') ≤
      trapezoidNodeCumulative 5 (Ncut 5 - 1) +
        -(trapezoidNodeCumulative 5 s)) :
    signedChordQuadraticNodeMoment 5 s (Ncut 5 - 1 - s) +
        (trapezoidTerminalCorrection 5 +
          trapezoidTerminalCorrection 5) ≤
      signedChordMomentCap 5 := by
  have hs0 : s = 0 := by
    by_cases hzero : s = 0
    · exact hzero
    · have hpos : 0 < s := Nat.pos_of_ne_zero hzero
      exact False.elim (terminal_gap_k5_p0_not_nonpos (hfirst 0 hpos))
  subst s
  simpa using quadraticNodeMoment_cap_k5

/-- Exact next-scale audit of the same quadratic carrier. -/
theorem quadraticNodeMoment_cap_k6 :
    signedChordQuadraticNodeMoment 6 0 (Ncut 6 - 1) +
        (trapezoidTerminalCorrection 6 + trapezoidTerminalCorrection 6) ≤
      signedChordMomentCap 6 := by
  unfold signedChordQuadraticNodeMoment harmonicChordQuadraticCumulative
    harmonicChordQuadraticWeight harmonicChordQuadraticFactor
    harmonicEndpointQuadraticCorrection intervalSum signedChordMomentCap
    signedChordMomentCore trapezoidTerminalCorrection trapezoidNodeCoeff
    harmonicD harmonicA twoInvSq oldAdj oldDiag coordNormSq adjCorr
    driftSqFactor driftRatio driftDen harmW harmU oneSub unit invSqTerm
    coeffW dimQ c4 Q'.divPos Q'.recipPos qpow Ncut fsum
  decide

theorem terminal_gap_k6_p0_not_nonpos :
    ¬ (trapezoidNodeCumulative 6 (Ncut 6 - 1) +
      -(trapezoidNodeCumulative 6 0) ≤ (0 : Q')) := by
  unfold trapezoidNodeCumulative harmonicD harmonicA twoInvSq oldAdj
    coordNormSq adjCorr harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    qpow Ncut fsum
  decide

/-- The quadratic cap at `k=6`, in the full admissible-crossing signature. -/
theorem signedChordQuadraticNodeMoment_le_cap_k6
    (s : Nat) (hsL : s ≤ Ncut 6 - 1)
    (hfirst : ∀ p, p < s →
      trapezoidNodeCumulative 6 (Ncut 6 - 1) +
        -(trapezoidNodeCumulative 6 p) ≤ (0 : Q'))
    (_hboundary : (0 : Q') ≤
      trapezoidNodeCumulative 6 (Ncut 6 - 1) +
        -(trapezoidNodeCumulative 6 s)) :
    signedChordQuadraticNodeMoment 6 s (Ncut 6 - 1 - s) +
        (trapezoidTerminalCorrection 6 +
          trapezoidTerminalCorrection 6) ≤
      signedChordMomentCap 6 := by
  have hs0 : s = 0 := by
    by_cases hzero : s = 0
    · exact hzero
    · have hpos : 0 < s := Nat.pos_of_ne_zero hzero
      exact False.elim (terminal_gap_k6_p0_not_nonpos (hfirst 0 hpos))
  subst s
  simpa using quadraticNodeMoment_cap_k6

#print axioms signedChordQuadraticNodeMoment_eq_carrier
#print axioms harmonicChordQuadraticWeight_nonnegative
#print axioms signedChordQuadraticNodeMoment_suffix_le
#print axioms signedChordQuadraticNodeMoment_suffix_le_of_boundary
#print axioms terminal_gap_k5_p0_not_nonpos
#print axioms signedChordQuadraticNodeMoment_le_cap_k5
#print axioms quadraticNodeMoment_cap_k6
#print axioms terminal_gap_k6_p0_not_nonpos
#print axioms signedChordQuadraticNodeMoment_le_cap_k6

end YMGap.Continuum.HarmonicSignedChordQuadraticCap
