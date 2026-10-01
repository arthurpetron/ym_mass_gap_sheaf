/-
# Near-quadratic fourth moments under the ORIGINAL Wilson edge law

On the explicit diagnostic subsequence h=2^(-6r), use the spin split
S=r*2^(3r). The original complete word fourth moment is bounded by
888*r^4*h^2 times its literal word-length factor and SAME odd partition.
The fundamental trace jump has sixteen times this ceiling. The original
radial energy formula consumes the improved quartic remainder, while its
mixed radial moment remains untouched.

This is not a physical coupling/spacing trajectory, a variance-relative
estimate, a completed width map, or a continuum-survival theorem.
-/

import YMGap.Continuum.SU2HeatQuarticLogDyadicBudget
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLogQuartic

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonQuarticIncrement
open YMGap.Continuum.QuaternionHaarWordQuartic (wordFourthFactor)
open YMGap.Continuum.SU2HeatQuarticDyadicSchedule (nome defect nome_pos nome_lt_one)
open YMGap.Continuum.SU2HeatQuarticLogDyadicBudget

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage oddMass

/-- Every stage satisfies BOTH original head and quartic shifted-spin guards. -/
def logCutoff (r stage : Nat) : Nat :=
  max (headCutoff (nome (2*r))) (logSplit r+3) + stage

theorem head_le_logCutoff (r stage : Nat) :
    headCutoff (nome (2*r)) ≤ logCutoff r stage :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ _)

theorem split_le_logCutoff (r stage : Nat) : logSplit r+3 ≤ logCutoff r stage :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)

/-- The word length is explicit; no width, terminal-depth or cutoff factor. -/
def wordLogRate (r : Nat) {width : Nat} (loop : SourceLoop width) : Q' :=
  wordFourthFactor loop.edges.length *
    (888*(Q'.ofNat (r^4)*(defect (2*r)*defect (2*r))))

private theorem word_factor_nonnegative (n : Nat) :
    (0 : Q') ≤ wordFourthFactor n := by
  unfold wordFourthFactor
  exact Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _))
      (Q'.mul_nonneg _ _ (Q'.ofNat_nonneg _) (Q'.ofNat_nonneg _)))

/-- A proved near-quadratic bound for the ACTUAL whole-word chordal moment.
All spatial weights, spectator heat factors and terminal messages remain. -/
theorem word_quartic_log_bound (r : Nat) (hr : logOnset ≤ r)
    (stage width depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges →
      (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity (nome (2*r)) (logCutoff r stage) width
        (terminalMessage (nome (2*r)) (logCutoff r stage) width depth))
        (polyMul (wordChordal width loop) (wordChordal width loop))) ≤
      wordLogRate r loop * oddMass (nome (2*r)) (logCutoff r stage) width depth := by
  have hm : 6 ≤ 2*r := by change 22 ≤ r at hr; omega
  have hw0 := nome_pos hm
  have hw1 := nome_lt_one (2*r)
  have hK := head_le_logCutoff r stage
  have h := word_quartic_bound hw0 hw1 (logSplit r) (logCutoff r stage)
    width depth (logSplit_ge_one r hr) (split_le_logCutoff r stage) hK
    (logHalf_guard r hr) (logTail_le_eighth r hr) loop hactive
  have hrate : wordQuarticRate (nome (2*r)) (logSplit r) loop ≤ wordLogRate r loop :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (logBudget_bound r hr)
      (word_factor_nonnegative _)
  exact Q'.le_trans' _ _ _ h
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate
      (Q'.le_of_lt (oddMass_positive hw0 hw1 _ _ hK depth)))

/-- The same bound reaches the literal fundamental-character fourth jump,
not merely an auxiliary quaternion-distance polynomial. -/
theorem jump_fourth_log_bound (r : Nat) (hr : logOnset ≤ r)
    (stage width depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges →
      (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    jumpFourthMoment (nome (2*r)) (logCutoff r stage) width depth loop ≤
      (16*wordLogRate r loop)*oddMass (nome (2*r)) (logCutoff r stage) width depth := by
  have hm : 6 ≤ 2*r := by change 22 ≤ r at hr; omega
  have h := jump_fourth_le_word_square (nome_pos hm) (nome_lt_one (2*r))
    (logCutoff r stage) width depth (head_le_logCutoff r stage) loop
  exact Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 16
        (word_quartic_log_bound r hr stage width depth loop hactive) (by decide))
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)))

/-- Normalization divides ONLY by the SAME positive odd-window partition. -/
theorem jump_fourth_log_normalized (r : Nat) (hr : logOnset ≤ r)
    (stage width depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges →
      (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    jumpFourthMoment (nome (2*r)) (logCutoff r stage) width depth loop *
      Q'.recipPos (oddMass (nome (2*r)) (logCutoff r stage) width depth)
        (oddMass_positive (nome_pos (by change 22 ≤ r at hr; omega))
          (nome_lt_one (2*r)) (logCutoff r stage) width
          (head_le_logCutoff r stage) depth) ≤
      16*wordLogRate r loop := by
  have hz := oddMass_positive (nome_pos (by change 22 ≤ r at hr; omega))
    (nome_lt_one (2*r)) (logCutoff r stage) width (head_le_logCutoff r stage) depth
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos _ hz)
    (jump_fourth_log_bound r hr stage width depth loop hactive)
    (Q'.le_of_lt (Q'.recipPos_pos _ hz))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hz))
        (Q'.mul_one_eqv _))))

/-- The original radial energy formula consumes the sharper quartic
remainder. Its COMPLETE mixed radial moment is still an unevaluated term,
not a product of expectations or a claimed SAME-variance bound. -/
theorem wilson_energy_log_quartic (r : Nat) (hr : logOnset ≤ r)
    (stage width depth : Nat) (loop : SourceLoop width)
    (hactive : ∀ e, e ∈ loop.edges →
      (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    (2 : Q')*energy (nome (2*r)) (logCutoff r stage) width
        (terminalMessage (nome (2*r)) (logCutoff r stage) width depth)
        (sourceCharacter width loop.edges 1) ≤
      2*mixedRadialMoment (nome (2*r)) (logCutoff r stage) width depth loop +
        2*(wordLogRate r loop*oddMass (nome (2*r)) (logCutoff r stage) width depth) := by
  have hm : 6 ≤ 2*r := by change 22 ≤ r at hr; omega
  have h := wilson_energy_radial_quartic_cleared (nome_pos hm) (nome_lt_one (2*r))
    (logSplit r) (logCutoff r stage) width depth (logSplit_ge_one r hr)
    (split_le_logCutoff r stage) (head_le_logCutoff r stage)
    (logHalf_guard r hr) (logTail_le_eighth r hr) loop hactive
  have hrate : wordQuarticRate (nome (2*r)) (logSplit r) loop ≤ wordLogRate r loop :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (logBudget_bound r hr)
      (word_factor_nonnegative _)
  exact Q'.le_trans' _ _ _ h (Q'.add_le_add (Q'.le_refl' _)
    (Q'.mul_le_mul_of_nonneg_left _ _ 2
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate
        (Q'.le_of_lt (oddMass_positive (nome_pos hm) (nome_lt_one (2*r))
          _ _ (head_le_logCutoff r stage) depth))) (by decide)))

#print axioms logCutoff
#print axioms head_le_logCutoff
#print axioms split_le_logCutoff
#print axioms wordLogRate
#print axioms word_quartic_log_bound
#print axioms jump_fourth_log_bound
#print axioms jump_fourth_log_normalized
#print axioms wilson_energy_log_quartic

end YMGap.Continuum.BF4ExactSlabFixedSpatialLogQuartic
