/-
# Exact spectrum of the cutoff-two vacuum-column refresh kernel

The normalized genuine BF4 cutoff-two vacuum column defines a finite posterior
on retained lower sources.  Independent resampling from this law is a
canonical rank-one Markov kernel.  We prove exact nonnegativity, normalization,
reversibility, stationarity, and idempotence.  Constants have algebraic
eigenvalue one, while every posterior-centered observable has eigenvalue zero.
The faithful non-vacuum indicator gives an explicit nonzero centered mode.

This refresh kernel is derived from the physical column but is not identified
with the Yang--Mills transfer operator.  Its finite algebraic gap one is not a
physical, cutoff-uniform, volume-uniform, or continuum mass gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumExcitation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumPosterior
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite Markov law -/

/-- Retained lower-source carrier of the cutoff-two vacuum column. -/
def cutoffTwoVacuumColumnCarrier : List EdgeLabelling :=
  centralPositiveHalfStates cutoffTwoHalfCoupling
    (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0

/-- Independent resampling from the exact normalized physical column. -/
def cutoffTwoVacuumColumnRefreshKernel
    (_source target : EdgeLabelling) : Q' :=
  cutoffTwoVacuumColumnPosterior target

theorem cutoffTwoVacuumColumnRefreshKernel_nonnegative
    (source target : EdgeLabelling) :
    (0 : Q') ≤ cutoffTwoVacuumColumnRefreshKernel source target := by
  unfold cutoffTwoVacuumColumnRefreshKernel
    cutoffTwoVacuumColumnPosterior Q'.divPos
  exact Q'.mul_nonneg _ _
    (centralHalfAmplitude_nonnegative
      (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
      2 0 target zeroEdgeLabelling)
    (Q'.le_of_lt
      (Q'.recipPos_pos cutoffTwoVacuumColumnDenominator
        cutoffTwoVacuumColumnDenominator_pos))

theorem cutoffTwoVacuumColumnRefreshKernel_row_normalized
    (source : EdgeLabelling) :
    listQSum
        (cutoffTwoVacuumColumnRefreshKernel source)
        cutoffTwoVacuumColumnCarrier ≈
      1 := by
  simpa [cutoffTwoVacuumColumnRefreshKernel,
    cutoffTwoVacuumColumnCarrier] using
      cutoffTwoVacuumColumnPosterior_total_one

/-- Detailed balance is the symmetry of the product of posterior masses. -/
theorem cutoffTwoVacuumColumnRefreshKernel_detailedBalance
    (source target : EdgeLabelling) :
    cutoffTwoVacuumColumnPosterior source *
        cutoffTwoVacuumColumnRefreshKernel source target ≈
      cutoffTwoVacuumColumnPosterior target *
        cutoffTwoVacuumColumnRefreshKernel target source := by
  unfold cutoffTwoVacuumColumnRefreshKernel
  exact Q'.mul_comm_eqv _ _

theorem cutoffTwoVacuumColumnRefreshKernel_stationary
    (target : EdgeLabelling) :
    listQSum
        (fun source =>
          cutoffTwoVacuumColumnPosterior source *
            cutoffTwoVacuumColumnRefreshKernel source target)
        cutoffTwoVacuumColumnCarrier ≈
      cutoffTwoVacuumColumnPosterior target := by
  unfold cutoffTwoVacuumColumnRefreshKernel
  refine Q'.eqv_trans _
    (listQSum cutoffTwoVacuumColumnPosterior
        cutoffTwoVacuumColumnCarrier *
      cutoffTwoVacuumColumnPosterior target) _ ?_ ?_
  · exact listQSum_mul_right cutoffTwoVacuumColumnPosterior
      (cutoffTwoVacuumColumnPosterior target)
      cutoffTwoVacuumColumnCarrier
  refine Q'.eqv_trans _
    (1 * cutoffTwoVacuumColumnPosterior target) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (by
        simpa [cutoffTwoVacuumColumnCarrier] using
          cutoffTwoVacuumColumnPosterior_total_one)
  exact Q'.one_mul_eqv _

/-! ## 2. Exact rank-one action -/

def cutoffTwoVacuumColumnPosteriorMean
    (observable : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun target =>
      cutoffTwoVacuumColumnPosterior target * observable target)
    cutoffTwoVacuumColumnCarrier

def cutoffTwoVacuumColumnRefreshAction
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      cutoffTwoVacuumColumnRefreshKernel source target *
        observable target)
    cutoffTwoVacuumColumnCarrier

theorem cutoffTwoVacuumColumnRefreshAction_eqv_mean
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) :
    cutoffTwoVacuumColumnRefreshAction observable source ≈
      cutoffTwoVacuumColumnPosteriorMean observable := by
  unfold cutoffTwoVacuumColumnRefreshAction
    cutoffTwoVacuumColumnPosteriorMean
    cutoffTwoVacuumColumnRefreshKernel
  exact Q'.eqv_refl _

theorem cutoffTwoVacuumColumnRefreshAction_one
    (source : EdgeLabelling) :
    cutoffTwoVacuumColumnRefreshAction (fun _ => 1) source ≈ 1 := by
  refine Q'.eqv_trans _
    (cutoffTwoVacuumColumnPosteriorMean (fun _ => 1)) _
    (cutoffTwoVacuumColumnRefreshAction_eqv_mean _ source) ?_
  unfold cutoffTwoVacuumColumnPosteriorMean
  refine Q'.eqv_trans _
    (listQSum cutoffTwoVacuumColumnPosterior
      cutoffTwoVacuumColumnCarrier) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_one_eqv _
  simpa [cutoffTwoVacuumColumnCarrier] using
    cutoffTwoVacuumColumnPosterior_total_one

theorem cutoffTwoVacuumColumnRefreshAction_centered_zero
    (observable : EdgeLabelling → Q')
    (hcentered :
      cutoffTwoVacuumColumnPosteriorMean observable ≈ 0)
    (source : EdgeLabelling) :
    cutoffTwoVacuumColumnRefreshAction observable source ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (cutoffTwoVacuumColumnRefreshAction_eqv_mean observable source)
    hcentered

def cutoffTwoVacuumColumnCenteredObservable
    (observable : EdgeLabelling → Q')
    (target : EdgeLabelling) : Q' :=
  observable target +
    (-cutoffTwoVacuumColumnPosteriorMean observable)

theorem cutoffTwoVacuumColumnCenteredObservable_mean_zero
    (observable : EdgeLabelling → Q') :
    cutoffTwoVacuumColumnPosteriorMean
        (cutoffTwoVacuumColumnCenteredObservable observable) ≈
      0 := by
  let states := cutoffTwoVacuumColumnCarrier
  let posterior := cutoffTwoVacuumColumnPosterior
  let mean := cutoffTwoVacuumColumnPosteriorMean observable
  change
    listQSum
        (fun target =>
          posterior target * (observable target + (-mean)))
        states ≈
      0
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        posterior target * observable target +
          posterior target * (-mean)) states) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_add_eqv _ _ _
  refine Q'.eqv_trans _
    (listQSum (fun target => posterior target * observable target) states +
      listQSum (fun target => posterior target * (-mean)) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (mean + listQSum (fun target => posterior target * (-mean)) states) _
    (Q'.add_eqv_congr' (Q'.eqv_refl mean) (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    (mean + listQSum posterior states * (-mean)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl mean)
      (listQSum_mul_right posterior (-mean) states)) ?_
  refine Q'.eqv_trans _ (mean + 1 * (-mean)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl mean)
      (Q'.mul_eqv_congr_right _ _ _
        (by
          simpa [states, posterior, cutoffTwoVacuumColumnCarrier] using
            cutoffTwoVacuumColumnPosterior_total_one))
  refine Q'.eqv_trans _ (mean + (-mean)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl mean)
      (Q'.one_mul_eqv (-mean))) ?_
  exact Q'.add_neg_self_eqv mean

theorem cutoffTwoVacuumColumnRefreshAction_idempotent
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) :
    cutoffTwoVacuumColumnRefreshAction
        (cutoffTwoVacuumColumnRefreshAction observable) source ≈
      cutoffTwoVacuumColumnRefreshAction observable source := by
  let states := cutoffTwoVacuumColumnCarrier
  let posterior := cutoffTwoVacuumColumnPosterior
  let mean := cutoffTwoVacuumColumnPosteriorMean observable
  refine Q'.eqv_trans _
    (cutoffTwoVacuumColumnPosteriorMean
      (cutoffTwoVacuumColumnRefreshAction observable)) _
    (cutoffTwoVacuumColumnRefreshAction_eqv_mean _ source) ?_
  change
    listQSum
        (fun target =>
          posterior target *
            cutoffTwoVacuumColumnRefreshAction observable target)
        states ≈
      cutoffTwoVacuumColumnRefreshAction observable source
  refine Q'.eqv_trans _
    (listQSum (fun target => posterior target * mean) states) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_eqv_congr_left (posterior target) _ _
      (cutoffTwoVacuumColumnRefreshAction_eqv_mean observable target)
  refine Q'.eqv_trans _ (listQSum posterior states * mean) _
    (listQSum_mul_right posterior mean states) ?_
  refine Q'.eqv_trans _ (1 * mean) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ mean
      (by
        simpa [states, posterior, cutoffTwoVacuumColumnCarrier] using
          cutoffTwoVacuumColumnPosterior_total_one)
  refine Q'.eqv_trans _ mean _ (Q'.one_mul_eqv mean) ?_
  exact Q'.eqv_symm
    (cutoffTwoVacuumColumnRefreshAction_eqv_mean observable source)

/-! ## 3. A genuine nonconstant centered excitation mode -/

def cutoffTwoVacuumColumnExcitationIndicator
    (source : EdgeLabelling) : Q' :=
  cutoffTwoNonvacuumMask source

private theorem mul_swap_last (a b c : Q') :
    (a * b) * c ≈ (a * c) * b := by
  exact Q'.eqv_trans _ (a * (b * c)) _
    (Q'.mul_assoc_eqv a b c)
    (Q'.eqv_trans _ (a * (c * b)) _
      (Q'.mul_eqv_congr_left a _ _ (Q'.mul_comm_eqv b c))
      (Q'.eqv_symm (Q'.mul_assoc_eqv a c b)))

theorem cutoffTwoVacuumColumnExcitationIndicator_mean :
    cutoffTwoVacuumColumnPosteriorMean
        cutoffTwoVacuumColumnExcitationIndicator ≈
      cutoffTwoVacuumExcitationProbability := by
  unfold cutoffTwoVacuumColumnPosteriorMean
    cutoffTwoVacuumColumnExcitationIndicator
    cutoffTwoVacuumColumnPosterior cutoffTwoVacuumColumnCarrier
    cutoffTwoVacuumExcitationProbability Q'.divPos
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
            zeroEdgeLabelling * cutoffTwoNonvacuumMask source) *
          Q'.recipPos cutoffTwoVacuumColumnDenominator
            cutoffTwoVacuumColumnDenominator_pos)
      (centralPositiveHalfStates cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact mul_swap_last _ _ _
  refine Q'.eqv_trans _
    (cutoffTwoNonvacuumVacuumColumnMass *
      Q'.recipPos cutoffTwoVacuumColumnDenominator
        cutoffTwoVacuumColumnDenominator_pos) _ ?_ ?_
  · unfold cutoffTwoNonvacuumVacuumColumnMass
    exact listQSum_mul_right
      (fun source =>
        centralHalfAmplitude cutoffTwoHalfCoupling 2 0 source
            zeroEdgeLabelling * cutoffTwoNonvacuumMask source)
      (Q'.recipPos cutoffTwoVacuumColumnDenominator
        cutoffTwoVacuumColumnDenominator_pos)
      (centralPositiveHalfStates cutoffTwoHalfCoupling
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling) 2 0)
  exact Q'.mul_eqv_congr_right _ _ _
    cutoffTwoNonvacuumVacuumColumnMass_eqv_excitedExcess

def cutoffTwoVacuumColumnCenteredExcitationMode
    (source : EdgeLabelling) : Q' :=
  cutoffTwoVacuumColumnCenteredObservable
    cutoffTwoVacuumColumnExcitationIndicator source

theorem cutoffTwoVacuumColumnCenteredExcitationMode_mean_zero :
    cutoffTwoVacuumColumnPosteriorMean
        cutoffTwoVacuumColumnCenteredExcitationMode ≈ 0 := by
  exact cutoffTwoVacuumColumnCenteredObservable_mean_zero
    cutoffTwoVacuumColumnExcitationIndicator

theorem cutoffTwoVacuumColumnExcitationIndicator_selected_eqv_one :
    cutoffTwoVacuumColumnExcitationIndicator
        cutoffTwoExcitedVacuumSource ≈ 1 := by
  unfold cutoffTwoVacuumColumnExcitationIndicator
    cutoffTwoNonvacuumMask
  rw [if_neg cutoffTwoExcitedVacuumSource_code_ne]
  exact Q'.eqv_refl 1

theorem cutoffTwoVacuumColumnCenteredExcitationMode_selected_eqv :
    cutoffTwoVacuumColumnCenteredExcitationMode
        cutoffTwoExcitedVacuumSource ≈
      (1 : Q') + (-cutoffTwoVacuumExcitationProbability) := by
  unfold cutoffTwoVacuumColumnCenteredExcitationMode
    cutoffTwoVacuumColumnCenteredObservable
  exact Q'.add_eqv_congr'
    cutoffTwoVacuumColumnExcitationIndicator_selected_eqv_one
    (Q'.neg_eqv_congr _ _
      cutoffTwoVacuumColumnExcitationIndicator_mean)

theorem cutoffTwoVacuumColumnCenteredExcitationMode_selected_pos :
    (0 : Q') <
      cutoffTwoVacuumColumnCenteredExcitationMode
        cutoffTwoExcitedVacuumSource := by
  exact Q'.pos_of_lt_of_le
    (one_sub_pos_of_lt_one cutoffTwoVacuumExcitationProbability_lt_one)
    (Q'.ge_of_eqv
      cutoffTwoVacuumColumnCenteredExcitationMode_selected_eqv)

theorem cutoffTwoVacuumColumnRefreshAction_centeredExcitationMode_zero
    (source : EdgeLabelling) :
    cutoffTwoVacuumColumnRefreshAction
        cutoffTwoVacuumColumnCenteredExcitationMode source ≈ 0 := by
  exact cutoffTwoVacuumColumnRefreshAction_centered_zero _
    cutoffTwoVacuumColumnCenteredExcitationMode_mean_zero source

/-- Algebraic centered eigenvalue of the exact rank-one refresh projection. -/
def cutoffTwoVacuumColumnRefreshCenteredEigenvalue : Q' := 0

/-- Exact algebraic gap of the refresh projection. -/
def cutoffTwoVacuumColumnRefreshAlgebraicGap : Q' := 1

theorem cutoffTwoVacuumColumnRefreshAlgebraicGap_pos :
    (0 : Q') < cutoffTwoVacuumColumnRefreshAlgebraicGap := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnRefreshKernel_row_normalized
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnRefreshKernel_detailedBalance
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnRefreshKernel_stationary
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnRefreshAction_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnCenteredObservable_mean_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnRefreshAction_idempotent
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnExcitationIndicator_mean
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnCenteredExcitationMode_selected_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnRefreshAction_centeredExcitationMode_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumRefreshSpectrum.cutoffTwoVacuumColumnRefreshAlgebraicGap_pos
