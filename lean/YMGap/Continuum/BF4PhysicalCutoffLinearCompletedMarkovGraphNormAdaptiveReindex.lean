/-
# Adaptive reindexing for the completed BF4 graph-norm diagonal

An arbitrary completion representative may carry finite-linear syntax whose
explicit inner modulus grows faster than its sequence index.  Same-index
cofinality is therefore not inferred from metric Cauchyness.

This file instead regularizes every inner modulus along the canonical
`invSucc` precision ladder and applies the repository's executable slow
diagonal.  For each completed representative it constructs a cofinal sampled
Cauchy representative, proves that it is close to the original representative,
and proves that the finite stage pays both the selected self-pair and
vacuum-pair inner rates.

This is a representative-normalization theorem.  Transporting the finite
sixteenth through its graph norms is the next step; no completion modulus or
gap certificate is inhabited here.

## Axiom gate

Only explicit running maxima, bounded natural-number search, the supplied
Cauchy modulus, and quotient soundness are used.  There is no classical
choice, noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance
import YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison

namespace YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. Antitone regularization of an arbitrary inner modulus -/

/-- Running-maximum regularization of an inner approximation rate along the
canonical positive rational precision ladder. -/
def regularInnerRate {x : CReal} (R : CReal.InnerRegularity x)
    (epsilon : Q') : Nat :=
  CReal.Gmax (fun precision => R.rate (Q'.invSucc precision))
    (CReal.lv epsilon)

/-- The regularized rate is antitone in the positive tolerance. -/
theorem regularInnerRate_antitone
    {x : CReal} (R : CReal.InnerRegularity x)
    {epsilon delta : Q'} (hdelta : (0 : Q') < delta)
    (hdeltaepsilon : delta <= epsilon) :
    regularInnerRate R epsilon <= regularInnerRate R delta := by
  exact CReal.Gmax_mono _ _ _
    (CReal.lv_antitone hdelta hdeltaepsilon)

/-- Every explicit inner modulus has an equivalent witness with an antitone
tolerance rate. -/
def regularizedInnerRegularity
    {x : CReal} (R : CReal.InnerRegularity x) :
    CReal.InnerRegularity x where
  rate := regularInnerRate R
  regular := by
    intro epsilon hepsilon first second hfirst hsecond
    let delta := Q'.invSucc (CReal.lv epsilon)
    have hdelta : (0 : Q') < delta := Q'.invSucc_pos _
    have hraw : R.rate delta <= regularInnerRate R epsilon :=
      CReal.Gmax_ge
        (fun precision => R.rate (Q'.invSucc precision))
        (CReal.lv epsilon)
    obtain ⟨hforward, hbackward⟩ := R.regular delta hdelta first second
      (Nat.le_trans hraw hfirst) (Nat.le_trans hraw hsecond)
    have hdeltaepsilon : delta <= epsilon :=
      CReal.invSucc_lv_le hepsilon
    exact
      ⟨Q'.le_trans' _ _ _ hforward
          (Q'.add_le_add_left _ _ _ hdeltaepsilon),
       Q'.le_trans' _ _ _ hbackward
          (Q'.add_le_add_left _ _ _ hdeltaepsilon)⟩

/-! ## 2. The representative-adaptive slow diagonal -/

/-- The two regularized inner rates required from the `index`-th term of a
completion representative at canonical precision `invSucc index`. -/
def centralPhysicalGraphInputRequirement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (index : Nat) : Nat :=
  max
    ((regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq index) (X.seq index))).rate (Q'.invSucc index))
    ((regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq index) centralPhysicalLinearVacuum)).rate
          (Q'.invSucc index))

/-- The cumulative threshold ladder of one cutoff-removed representative. -/
def centralPhysicalGraphSampleRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold : Nat) : Nat :=
  slowThreshold (centralPhysicalGraphInputRequirement hw0 hw1 half X)
    threshold

/-- The greatest representative index whose accumulated inner-rate
requirements fit inside the current representation cutoff. -/
def centralPhysicalGraphSampleIndex
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : Nat :=
  slowIndex (centralPhysicalGraphInputRequirement hw0 hw1 half X) stage

/-- Outer rate for an arbitrary rational tolerance. -/
def centralPhysicalGraphDiagonalRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  centralPhysicalGraphSampleRate hw0 hw1 half X (CReal.lv epsilon)

theorem centralPhysicalGraphSampleIndex_cofinal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold stage : Nat)
    (hstage : centralPhysicalGraphSampleRate
      hw0 hw1 half X threshold <= stage) :
    threshold <= centralPhysicalGraphSampleIndex
      hw0 hw1 half X stage :=
  slowIndex_cofinal
    (centralPhysicalGraphInputRequirement hw0 hw1 half X)
    threshold stage hstage

private theorem selected_requirement_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (stage : Nat)
    (hstage : centralPhysicalGraphDiagonalRate
      hw0 hw1 half X epsilon <= stage) :
    centralPhysicalGraphInputRequirement hw0 hw1 half X
        (centralPhysicalGraphSampleIndex hw0 hw1 half X stage) <= stage := by
  have hzeroRate : centralPhysicalGraphSampleRate hw0 hw1 half X 0 <=
      centralPhysicalGraphSampleRate hw0 hw1 half X (CReal.lv epsilon) :=
    slowThreshold_mono
      (centralPhysicalGraphInputRequirement hw0 hw1 half X)
      (Nat.zero_le _)
  exact required_slowIndex_le
    (centralPhysicalGraphInputRequirement hw0 hw1 half X) stage
    (Nat.le_trans hzeroRate hstage)

private theorem selected_precision
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalGraphDiagonalRate
      hw0 hw1 half X epsilon <= stage) :
    Q'.invSucc
        (centralPhysicalGraphSampleIndex hw0 hw1 half X stage) <= epsilon := by
  have hprecision : CReal.lv epsilon <=
      centralPhysicalGraphSampleIndex hw0 hw1 half X stage :=
    centralPhysicalGraphSampleIndex_cofinal hw0 hw1 half X
      (CReal.lv epsilon) stage hstage
  exact Q'.le_trans' _ _ _
    (ExpNeg.invSucc_le_of_le hprecision)
    (CReal.invSucc_lv_le hepsilon)

/-- At every sufficiently late representation cutoff, the selected input term
pays both regularized inner rates at the requested tolerance. -/
theorem centralPhysicalGraph_diagonal_admissible
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalGraphDiagonalRate
      hw0 hw1 half X epsilon <= stage) :
    let index := centralPhysicalGraphSampleIndex hw0 hw1 half X stage
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq index) (X.seq index))).rate epsilon <= stage /\
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (X.seq index) centralPhysicalLinearVacuum)).rate epsilon <= stage := by
  let index := centralPhysicalGraphSampleIndex hw0 hw1 half X stage
  have hrequired := selected_requirement_paid
    hw0 hw1 half X epsilon stage hstage
  have hprecision := selected_precision
    hw0 hw1 half X epsilon hepsilon stage hstage
  have hself := regularInnerRate_antitone
    (innerLimitInnerRegularity hw0 hw1 half
      (X.seq index) (X.seq index))
    (Q'.invSucc_pos index) hprecision
  have hvacuum := regularInnerRate_antitone
    (innerLimitInnerRegularity hw0 hw1 half
      (X.seq index) centralPhysicalLinearVacuum)
    (Q'.invSucc_pos index) hprecision
  constructor
  · exact Nat.le_trans hself
      (Nat.le_trans (Nat.le_max_left _ _) hrequired)
  · exact Nat.le_trans hvacuum
      (Nat.le_trans (Nat.le_max_right _ _) hrequired)

/-! ## 3. The normalized Cauchy representative -/

/-- Cofinally sample an arbitrary completed representative along the adaptive
inner-rate diagonal. -/
def centralPhysicalGraphAdaptiveReindexCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage := X.seq
    (centralPhysicalGraphSampleIndex hw0 hw1 half X stage)
  modulus epsilon := centralPhysicalGraphSampleRate
    hw0 hw1 half X (X.modulus epsilon)
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    exact X.isCauchy epsilon hepsilon
      (centralPhysicalGraphSampleIndex hw0 hw1 half X first)
      (centralPhysicalGraphSampleIndex hw0 hw1 half X second)
      (centralPhysicalGraphSampleIndex_cofinal
        hw0 hw1 half X (X.modulus epsilon) first hfirst)
      (centralPhysicalGraphSampleIndex_cofinal
        hw0 hw1 half X (X.modulus epsilon) second hsecond)

/-- The adaptive representative is explicitly close to the original one. -/
def centralPhysicalGraphAdaptiveReindexClose
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Close X
      (centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X) where
  modulus epsilon := max (X.modulus epsilon)
    (centralPhysicalGraphSampleRate hw0 hw1 half X (X.modulus epsilon))
  close := by
    intro epsilon hepsilon stage hstage
    have hraw : X.modulus epsilon <= stage :=
      Nat.le_trans (Nat.le_max_left _ _) hstage
    have hsampleRate :
        centralPhysicalGraphSampleRate hw0 hw1 half X
          (X.modulus epsilon) <= stage :=
      Nat.le_trans (Nat.le_max_right _ _) hstage
    exact X.isCauchy epsilon hepsilon stage
      (centralPhysicalGraphSampleIndex hw0 hw1 half X stage)
      hraw
      (centralPhysicalGraphSampleIndex_cofinal hw0 hw1 half X
        (X.modulus epsilon) stage hsampleRate)

/-- Adaptive normalization changes the representative, not the completed
physical point. -/
theorem centralPhysicalGraphAdaptiveReindex_class_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid X =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalGraphAdaptiveReindexCauchy hw0 hw1 half X) :=
  Quotient.sound ⟨centralPhysicalGraphAdaptiveReindexClose
    hw0 hw1 half X⟩

/-! ## Axiom audit -/

#print axioms regularizedInnerRegularity
#print axioms centralPhysicalGraphSampleIndex_cofinal
#print axioms centralPhysicalGraph_diagonal_admissible
#print axioms centralPhysicalGraphAdaptiveReindexCauchy
#print axioms centralPhysicalGraphAdaptiveReindexClose
#print axioms centralPhysicalGraphAdaptiveReindex_class_eq

end YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
