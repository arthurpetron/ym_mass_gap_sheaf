/-
# Collapsing the output-shell sum in the guarded Hahn/Racah carrier

Physical left and right channels have the same total contraction order.
Consequently their two outer-shell guards coincide, and the output coefficient
sum in the fourfold factorial cross carrier is one-hot.  This file eliminates
that sum uniformly, leaving a strictly simpler threefold finite convolution.
-/

import YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
import YMGap.Continuum.RacahDougallWZ

namespace YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier

set_option maxHeartbeats 2000000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantMixedRecouplingGNSCompleted
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2DirectRightFixedOutputSections
open YMGap.Continuum.SU2OrderedFundamentalFRows
open YMGap.Continuum.SU2OrderedRacahMultiplicityFence
open YMGap.Continuum.SU2OrderedRacahGuardedHahnCarrier
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2OrderedFixedOutputFKernel
open YMGap.Continuum.SixJKernel

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_zero_of_right {a b : Q'} (hb : b ≈ 0) :
    a * b ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a b 0 hb)
    (Q'.mul_zero_eqv a)

/-! ## Common total contraction order and shell guards -/

/-- Any physical left and right channel with the same four external/final
labels has the same total contraction order.  This is the exact parity bridge
between the two bracketings. -/
theorem fixed_channels_total_order_eq {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    qL.k + qL.r = qR.p + qR.r := by
  have hk := Nat.le_min.mp qL.k_le
  have hlr := Nat.le_min.mp qL.r_le
  have hp := Nat.le_min.mp qR.p_le
  have hrr := Nat.le_min.mp qR.r_le
  have hL := qL.degree_eq
  have hR := qR.degree_eq
  omega

theorem left_outer_shell_guard_iff {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l s : Nat)
    (hinner : q.k ≤ i + j) :
    s + q.r = (i + j - q.k) + l ↔
      s + (q.k + q.r) = i + j + l := by
  constructor
  · intro h
    omega
  · intro h
    omega

theorem right_outer_shell_guard_iff {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l s : Nat)
    (hinner : q.p ≤ j + l) :
    s + q.r = i + (j + l - q.p) ↔
      s + (q.p + q.r) = i + j + l := by
  constructor
  · intro h
    omega
  · intro h
    omega

/-! ## A common-guard summand -/

def leftFactorialPayload {a b c d : Nat}
    (q : FixedLeftCGChannel a b c d) (i j l : Nat) : Q' :=
  hahnEntry a b (i + j) q.k i *
    transvectFactorialCoeff q.intermediate c q.r (i + j - q.k) l

def rightFactorialPayload {a b c d : Nat}
    (q : FixedRightCGChannel a b c d) (i j l : Nat) : Q' :=
  hahnEntry b c (j + l) q.p j *
    transvectFactorialCoeff a q.intermediate q.r i (j + l - q.p)

/-- The factorial cross summand with a single common output-shell guard. -/
def commonGuardFactorialCrossSummand {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (i j l s : Nat) : Q' :=
  if qL.k ≤ i + j then
    if qR.p ≤ j + l then
      if s + (qL.k + qL.r) = i + j + l then
        tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
          symMonomialNormSq d s *
            (leftFactorialPayload qL i j l * rightFactorialPayload qR i j l)
      else 0
    else 0
  else 0

/-- Both original outer guards are exactly the one common total-order guard. -/
theorem guardedFactorialCrossSummand_eq_commonGuard {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (i j l s : Nat) :
    guardedFactorialCrossSummand qL qR i j l s ≈
      commonGuardFactorialCrossSummand qL qR i j l s := by
  unfold guardedFactorialCrossSummand
    guardedLeftFactorialCoefficient guardedRightFactorialCoefficient
    commonGuardFactorialCrossSummand leftFactorialPayload rightFactorialPayload
  by_cases hL : qL.k ≤ i + j
  · rw [if_pos hL, if_pos hL]
    by_cases hR : qR.p ≤ j + l
    · rw [if_pos hR, if_pos hR]
      have htotal := fixed_channels_total_order_eq qL qR
      have hleft := left_outer_shell_guard_iff qL i j l s hL
      have hright := right_outer_shell_guard_iff qR i j l s hR
      by_cases hs : s + (qL.k + qL.r) = i + j + l
      · have hsL := hleft.mpr hs
        have hsR : s + qR.r = i + (j + l - qR.p) := by
          apply hright.mpr
          rw [← htotal]
          exact hs
        rw [if_pos hs, if_pos hsL, if_pos hsR]
        exact Q'.eqv_refl _
      · have hsL : ¬ s + qL.r = (i + j - qL.k) + l := by
          intro h
          exact hs (hleft.mp h)
        have hsR : ¬ s + qR.r = i + (j + l - qR.p) := by
          intro h
          have hc := hright.mp h
          rw [← htotal] at hc
          exact hs hc
        rw [if_neg hs, if_neg hsL, if_neg hsR]
        exact mul_eqv_zero_of_right
          (mul_eqv_zero_of_right (Q'.mul_zero_eqv _))
    · rw [if_neg hR, if_neg hR]
      exact mul_eqv_zero_of_right (Q'.mul_zero_eqv _)
  · rw [if_neg hL, if_neg hL]
    exact mul_eqv_zero_of_right (Q'.zero_mul_eqv _)

/-! ## One-hot collapse of the output sum -/

/-- The exact three-index summand after eliminating the output coefficient.
The guard says that the unique shell `s=i+j+l-totalOrder` is a natural number
inside the final degree window. -/
def collapsedFactorialCrossSummand {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (i j l : Nat) : Q' :=
  if qL.k ≤ i + j then
    if qR.p ≤ j + l then
      if qL.k + qL.r ≤ i + j + l ∧
          i + j + l - (qL.k + qL.r) ≤ d then
        tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
          symMonomialNormSq d (i + j + l - (qL.k + qL.r)) *
            (leftFactorialPayload qL i j l * rightFactorialPayload qR i j l)
      else 0
    else 0
  else 0

theorem output_finSum_commonGuard_eq_collapsed {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (i j l : Nat) :
    finSum (fun s => commonGuardFactorialCrossSummand qL qR i j l s)
        (d + 1) ≈
      collapsedFactorialCrossSummand qL qR i j l := by
  by_cases hL : qL.k ≤ i + j
  · by_cases hR : qR.p ≤ j + l
    · let K := qL.k + qL.r
      let t := i + j + l
      by_cases hsupp : K ≤ t ∧ t - K ≤ d
      · let s0 := t - K
        let C := tvBinomQ a i * tvBinomQ b j * tvBinomQ c l *
          symMonomialNormSq d s0 *
            (leftFactorialPayload qL i j l * rightFactorialPayload qR i j l)
        have hsum : finSum
            (fun s => commonGuardFactorialCrossSummand qL qR i j l s)
            (d + 1) ≈
            finSum (fun s => if s = s0 then C else 0) (d + 1) := by
          refine finSum_eqv_congr _ _ (fun s => ?_) (d + 1)
          unfold commonGuardFactorialCrossSummand
          rw [if_pos hL, if_pos hR]
          by_cases heq : s = s0
          · subst s
            rw [if_pos rfl]
            have hout : s0 + K = t := by
              unfold s0
              omega
            rw [if_pos (by simpa only [K, t] using hout)]
            exact Q'.eqv_refl _
          · rw [if_neg heq]
            have hout : ¬ s + K = t := by
              intro h
              apply heq
              unfold s0
              omega
            rw [if_neg (by simpa only [K, t] using hout)]
            exact Q'.eqv_refl 0
        have hone :=
          YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_onehot_value
            C (d + 1) s0 (by unfold s0; omega)
        unfold collapsedFactorialCrossSummand
        rw [if_pos hL, if_pos hR, if_pos (by simpa only [K, t] using hsupp)]
        exact Q'.eqv_trans _ _ _ hsum (by simpa only [C, s0, K, t] using hone)
      · have hzero : finSum
            (fun s => commonGuardFactorialCrossSummand qL qR i j l s)
            (d + 1) ≈ 0 := by
          apply YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_zero_on
          intro s hs
          unfold commonGuardFactorialCrossSummand
          rw [if_pos hL, if_pos hR]
          have hout : ¬ s + K = t := by
            intro heq
            apply hsupp
            constructor
            · omega
            · omega
          rw [if_neg (by simpa only [K, t] using hout)]
          exact Q'.eqv_refl 0
        unfold collapsedFactorialCrossSummand
        rw [if_pos hL, if_pos hR, if_neg (by simpa only [K, t] using hsupp)]
        exact hzero
    · have hzero : finSum
          (fun s => commonGuardFactorialCrossSummand qL qR i j l s)
          (d + 1) ≈ 0 := by
        apply YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_zero_on
        intro s _
        unfold commonGuardFactorialCrossSummand
        rw [if_pos hL, if_neg hR]
        exact Q'.eqv_refl 0
      unfold collapsedFactorialCrossSummand
      rw [if_pos hL, if_neg hR]
      exact hzero
  · have hzero : finSum
        (fun s => commonGuardFactorialCrossSummand qL qR i j l s)
        (d + 1) ≈ 0 := by
      apply YMGap.Continuum.SU2TransvectantGeneralCoefficient.finSum_zero_on
      intro s _
      unfold commonGuardFactorialCrossSummand
      rw [if_neg hL]
      exact Q'.eqv_refl 0
    unfold collapsedFactorialCrossSummand
    rw [if_neg hL]
    exact hzero

/-- The strictly simpler threefold finite convolution. -/
def collapsedFactorialCrossSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Q' :=
  finSum (fun i => finSum (fun j => finSum (fun l =>
    collapsedFactorialCrossSummand qL qR i j l) (c + 1))
      (b + 1)) (a + 1)

theorem guardedFactorialCrossSum_eq_collapsed {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    guardedFactorialCrossSum qL qR ≈ collapsedFactorialCrossSum qL qR := by
  unfold guardedFactorialCrossSum collapsedFactorialCrossSum
  refine finSum_eqv_congr _ _ (fun i => ?_) (a + 1)
  refine finSum_eqv_congr _ _ (fun j => ?_) (b + 1)
  refine finSum_eqv_congr _ _ (fun l => ?_) (c + 1)
  exact Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ _ (fun s =>
      guardedFactorialCrossSummand_eq_commonGuard qL qR i j l s) (d + 1))
    (output_finSum_commonGuard_eq_collapsed qL qR i j l)

/-- **Threefold arbitrary-label factorial carrier.** -/
theorem triCrossChannelWeight_eq_collapsedFactorialCrossSum {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) :
    triCrossChannelWeight qL qR ≈ collapsedFactorialCrossSum qL qR :=
  Q'.eqv_trans _ _ _
    (triCrossChannelWeight_eq_guardedFactorialCrossSum qL qR)
    (guardedFactorialCrossSum_eq_collapsed qL qR)

/-! ## Required boundary and multiplicity audits -/

theorem zero_leg_collapsed_cross_exact :
    collapsedFactorialCrossSum zeroLeft zeroRight ≈ 2 := by
  decide

theorem fundamental_collapsed_cross_entries :
    collapsedFactorialCrossSum fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ≈ -2 ∧
    collapsedFactorialCrossSum fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ≈ 6 ∧
    collapsedFactorialCrossSum fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ≈ 6 ∧
    collapsedFactorialCrossSum fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet ≈ 6 := by
  decide

/-- The remaining threefold convolution is genuinely signed; the singlet /
singlet block already has two negative unit summands. -/
theorem fundamental_collapsed_signed_witnesses :
    collapsedFactorialCrossSummand fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet 0 1 0 ≈ -1 ∧
    collapsedFactorialCrossSummand fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet 1 0 1 ≈ -1 := by
  decide

/-- Hence a termwise-nonnegative/Tonelli collapse is machine-refuted.  The
remaining convolution must preserve Hahn signs (for example by a genuine
Saalschütz/WZ cancellation). -/
theorem collapsed_cross_not_pointwise_nonnegative :
    ¬ (∀ i j l, (0 : Q') ≤
      collapsedFactorialCrossSummand fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet i j l) := by
  intro h
  have hbad := h 0 1 0
  have hnot : ¬ (0 : Q') ≤
      collapsedFactorialCrossSummand fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet 0 1 0 := by
    decide
  exact hnot hbad

/-- A second normalization fence: the cross Gram carries the LEFT channel
weight.  Replacing it by the right weight fails on the off-diagonal fundamental
entry (`6 ≠ 12·3/2`). -/
theorem right_weight_cross_normalization_refuted :
    ¬ (collapsedFactorialCrossSum fundamentalFixedLeftSinglet
          fundamentalFixedRightTriplet ≈
        triRightChannelWeight 1 1 1 1 2 *
          fixedOrderedFCoefficient fundamentalFixedLeftSinglet
            fundamentalFixedRightTriplet) := by
  decide

/-! ## Exact squared Racah target -/

/-- The algebraic source-weight normalization before squaring. -/
def CollapsedCrossFNormalizationAt {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Prop :=
  collapsedFactorialCrossSum qL qR ≈
    triLeftChannelWeight a b c d qL.intermediate *
      fixedOrderedFCoefficient qL qR

/-- The exact finite-convolution target for the corrected Racah bridge:
`cross² = W_left * W_right * P`. -/
def CollapsedRacahSquareAt {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d) : Prop :=
  collapsedFactorialCrossSum qL qR * collapsedFactorialCrossSum qL qR ≈
    triLeftChannelWeight a b c d qL.intermediate *
      (triRightChannelWeight a b c d qR.intermediate *
        racahKernel6 a b c d qL.intermediate qR.intermediate)

private theorem product_square_rearrange (w f : Q') :
    (w * f) * (w * f) ≈ w * (w * (f * f)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv w f (w * f)) ?_
  refine Q'.mul_eqv_congr_left w _ _ ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv f w f)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (f * w) (w * f) f (Q'.mul_comm_eqv f w)) ?_
  exact Q'.mul_assoc_eqv w f f

/-- The corrected Gram bridge plus the source-weight cross normalization
implies the explicit threefold squared target, without division or cancellation. -/
theorem collapsedRacahSquare_of_normalization_and_bridge {a b c d : Nat}
    (qL : FixedLeftCGChannel a b c d)
    (qR : FixedRightCGChannel a b c d)
    (hcross : CollapsedCrossFNormalizationAt qL qR)
    (hbridge : GramWeightedRacahBridgeAt qL qR) :
    CollapsedRacahSquareAt qL qR := by
  let C := collapsedFactorialCrossSum qL qR
  let WL := triLeftChannelWeight a b c d qL.intermediate
  let WR := triRightChannelWeight a b c d qR.intermediate
  let F := fixedOrderedFCoefficient qL qR
  let P := racahKernel6 a b c d qL.intermediate qR.intermediate
  have hc2 : C * C ≈ (WL * F) * (WL * F) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right C (WL * F) C hcross)
      (Q'.mul_eqv_congr_left (WL * F) C (WL * F) hcross)
  have hrearrange : (WL * F) * (WL * F) ≈ WL * (WL * (F * F)) :=
    product_square_rearrange WL F
  have hscaled : WL * (WR * P) ≈ WL * (WL * (F * F)) :=
    Q'.mul_eqv_congr_left WL _ _ hbridge
  exact Q'.eqv_trans _ _ _ hc2
    (Q'.eqv_trans _ _ _ hrearrange (Q'.eqv_symm hscaled))

theorem zero_leg_collapsed_targets :
    CollapsedCrossFNormalizationAt zeroLeft zeroRight ∧
    CollapsedRacahSquareAt zeroLeft zeroRight := by
  unfold CollapsedCrossFNormalizationAt CollapsedRacahSquareAt
  decide

theorem fundamental_collapsed_targets :
    CollapsedCrossFNormalizationAt fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ∧
    CollapsedRacahSquareAt fundamentalFixedLeftSinglet
        fundamentalFixedRightSinglet ∧
    CollapsedCrossFNormalizationAt fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ∧
    CollapsedRacahSquareAt fundamentalFixedLeftSinglet
        fundamentalFixedRightTriplet ∧
    CollapsedCrossFNormalizationAt fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ∧
    CollapsedRacahSquareAt fundamentalFixedLeftTriplet
        fundamentalFixedRightSinglet ∧
    CollapsedCrossFNormalizationAt fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet ∧
    CollapsedRacahSquareAt fundamentalFixedLeftTriplet
        fundamentalFixedRightTriplet := by
  unfold CollapsedCrossFNormalizationAt CollapsedRacahSquareAt
  decide

end YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier

#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.fixed_channels_total_order_eq
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.left_outer_shell_guard_iff
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.right_outer_shell_guard_iff
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.guardedFactorialCrossSummand_eq_commonGuard
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.output_finSum_commonGuard_eq_collapsed
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.guardedFactorialCrossSum_eq_collapsed
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.triCrossChannelWeight_eq_collapsedFactorialCrossSum
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.zero_leg_collapsed_cross_exact
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.fundamental_collapsed_cross_entries
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.fundamental_collapsed_signed_witnesses
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.collapsed_cross_not_pointwise_nonnegative
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.right_weight_cross_normalization_refuted
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.collapsedRacahSquare_of_normalization_and_bridge
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.zero_leg_collapsed_targets
#print axioms YMGap.Continuum.SU2OrderedRacahCollapsedHahnCarrier.fundamental_collapsed_targets
