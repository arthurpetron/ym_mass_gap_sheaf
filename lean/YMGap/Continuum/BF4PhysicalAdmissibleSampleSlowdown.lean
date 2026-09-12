/-
# Additional finite requirements without changing the completed transfer

Compose an existing admissible Markov sampler with the executable slow
diagonal for any extra finite requirement. Its original payments remain
valid at the later action cutoff, so the existing uniqueness theorem still
identifies its action with the SAME completed conditional operator.

The companion diagonal lemma passes a convergent CReal sequence through
its own rational approximation stages, with an explicit paid inner rate.
No convergence modulus or cutoff is selected from a proposition.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm

namespace YMGap.Continuum.BF4PhysicalAdmissibleSampleSlowdown

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison

local infix:50 " ≈ " => Q'.eqv

theorem slowIndex_le_stage (required : Nat → Nat) (stage : Nat) :
    slowIndex required stage ≤ stage := greatestAdmissibleAux_le required stage stage

/-- Arbitrary extra finite requirements preserve admissibility, with a
computed composition of the two rates. -/
def slowSample {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half}
    {X : (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half).Cauchy}
    (sample : CentralPhysicalLinearMarkovAdmissibleSample hw0 hw1 half pointwise X)
    (required : Nat → Nat) :
    CentralPhysicalLinearMarkovAdmissibleSample hw0 hw1 half pointwise X where
  index stage := sample.index (slowIndex required stage)
  rate threshold := slowThreshold required (sample.rate threshold)
  paid := by
    intro anchor pointwiseTolerance pairTolerance hp hq stage hstage
    have hpaid := sample.paid anchor pointwiseTolerance pairTolerance hp hq
      (slowIndex required stage) (slowIndex_cofinal required _ stage hstage)
    exact ⟨hpaid.1, Nat.le_trans hpaid.2.1 (slowIndex_le_stage required stage),
      Nat.le_trans hpaid.2.2 (slowIndex_le_stage required stage)⟩

/-- A regularized inner rate included in the extra requirement is paid at
every positive tolerance, with the explicit slow-threshold rate. -/
theorem slow_regularized_rate_paid {s : Nat → CReal}
    (R : ∀ n, CReal.InnerRegularity (s n)) (required : Nat → Nat)
    (hrequired : ∀ n, (regularizedInnerRegularity (R n)).rate (Q'.invSucc n) ≤ required n)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (stage : Nat)
    (hstage : slowThreshold required (CReal.lv epsilon) ≤ stage) :
    (regularizedInnerRegularity (R (slowIndex required stage))).rate epsilon ≤ stage := by
  let selected := slowIndex required stage
  have hprecision := slowIndex_cofinal required (CReal.lv epsilon) stage hstage
  have hinv : Q'.invSucc selected ≤ epsilon :=
    Q'.le_trans' _ _ _ (ExpNeg.invSucc_le_of_le hprecision) (CReal.invSucc_lv_le hepsilon)
  have hpaid := required_slowIndex_le required stage
    (Nat.le_trans (slowThreshold_mono required (Nat.zero_le _)) hstage)
  exact Nat.le_trans (regularInnerRate_antitone (R selected) (Q'.invSucc_pos selected) hinv)
    (Nat.le_trans (hrequired selected) hpaid)

/-- Approximate a convergent real sequence at its own stage once its
provided inner regularity has been paid. The rate is supplied as data. -/
theorem diagonal_converges {s : Nat → CReal} {L : CReal}
    (h : CReal.ConvergesTo s L) (R : ∀ n, CReal.InnerRegularity (s n))
    (stageRate : Q' → Nat)
    (paid : ∀ epsilon, (0 : Q') < epsilon → ∀ stage,
      stageRate epsilon ≤ stage → (R stage).rate epsilon ≤ stage) :
    CReal.ConvergesTo (fun stage => CReal.ofQ' ((s stage).approx stage)) L := by
  intro epsilon hepsilon
  let q := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨outerStage, houterStage⟩ := h q hq
  refine ⟨max outerStage (stageRate q), fun stage hstage => ?_⟩
  have houter := Nat.le_trans (Nat.le_max_left _ _) hstage
  have hrate := paid q hq stage (Nat.le_trans (Nat.le_max_right _ _) hstage)
  obtain ⟨outerApprox, houterApprox⟩ := houterStage stage houter
  refine ⟨max outerApprox ((R stage).rate q), fun k hk => ?_⟩
  obtain ⟨hinnerForward, hinnerBackward⟩ := (R stage).regular q hq stage k hrate
    (Nat.le_trans (Nat.le_max_right _ _) hk)
  obtain ⟨houterForward, houterBackward⟩ := houterApprox k
    (Nat.le_trans (Nat.le_max_left _ _) hk)
  have htwo : (q + q) ≈ epsilon := ExpNeg.two_halves epsilon
  constructor
  · have hchain := Q'.le_trans' _ _ _ hinnerForward
      (Q'.add_le_add_right _ _ q houterForward)
    exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv _ q q) (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))
  · have hchain := Q'.le_trans' _ _ _ houterBackward
      (Q'.add_le_add_right _ _ q hinnerBackward)
    exact Q'.le_trans' _ _ _ hchain (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv _ q q) (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))

end YMGap.Continuum.BF4PhysicalAdmissibleSampleSlowdown

#print axioms YMGap.Continuum.BF4PhysicalAdmissibleSampleSlowdown.slowIndex_le_stage
#print axioms YMGap.Continuum.BF4PhysicalAdmissibleSampleSlowdown.slowSample
#print axioms YMGap.Continuum.BF4PhysicalAdmissibleSampleSlowdown.slow_regularized_rate_paid
#print axioms YMGap.Continuum.BF4PhysicalAdmissibleSampleSlowdown.diagonal_converges
