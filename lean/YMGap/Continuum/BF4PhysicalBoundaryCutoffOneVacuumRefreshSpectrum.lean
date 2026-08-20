/-
# Exact spectrum of the cutoff-one vacuum-column refresh kernel

The normalized genuine BF4 vacuum column defines a finite posterior on the
retained lower-half source carrier.  Independently resampling from that law
gives a canonical rank-one Markov kernel.  This file proves directly that the
kernel is nonnegative, normalized, reversible, and stationary.  Its action
fixes constants and annihilates every posterior-centered observable, so its
only algebraic modes are the constant eigenvalue one and the centered
eigenvalue zero.

The refresh kernel is derived from a genuine physical BF4 column, but it is
not identified here with the Yang--Mills transfer operator.  Its finite gap
one must therefore not be read as a physical, cutoff-uniform, or continuum
mass gap.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The posterior-resampling Markov kernel -/

/-- The finite retained source carrier used by the cutoff-one vacuum column. -/
def cutoffOneVacuumColumnCarrier
    (w : Q') (hw : (0 : Q') < w) : List EdgeLabelling :=
  centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0

/-- Independent resampling from the exact normalized vacuum-column law.  The
source argument is retained to expose the object as a Markov kernel. -/
def cutoffOneVacuumColumnRefreshKernel
    (w : Q') (hw : (0 : Q') < w)
    (_source target : EdgeLabelling) : Q' :=
  cutoffOneVacuumColumnPosterior w hw target

theorem cutoffOneVacuumColumnRefreshKernel_nonnegative
    {w : Q'} (hw : (0 : Q') < w)
    (source target : EdgeLabelling) :
    (0 : Q') ≤
      cutoffOneVacuumColumnRefreshKernel w hw source target := by
  unfold cutoffOneVacuumColumnRefreshKernel
    cutoffOneVacuumColumnPosterior Q'.divPos
  exact Q'.mul_nonneg _ _
    (centralHalfAmplitude_nonnegative
      (Q'.le_of_lt hw) 1 0 target zeroEdgeLabelling)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (cutoffOneVacuumColumnDenominator_pos hw)))

theorem cutoffOneVacuumColumnRefreshKernel_row_normalized
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling) :
    listQSum
        (cutoffOneVacuumColumnRefreshKernel w hw source)
        (cutoffOneVacuumColumnCarrier w hw) ≈
      1 := by
  simpa [cutoffOneVacuumColumnRefreshKernel,
    cutoffOneVacuumColumnCarrier] using
      (cutoffOneVacuumColumnPosterior_total_one hw)

/-! ## 2. Reversibility and stationarity -/

/-- Detailed balance is exact: the stationary flow in either direction is
the symmetric product of the two posterior masses. -/
theorem cutoffOneVacuumColumnRefreshKernel_detailedBalance
    {w : Q'} (hw : (0 : Q') < w)
    (source target : EdgeLabelling) :
    cutoffOneVacuumColumnPosterior w hw source *
        cutoffOneVacuumColumnRefreshKernel w hw source target ≈
      cutoffOneVacuumColumnPosterior w hw target *
        cutoffOneVacuumColumnRefreshKernel w hw target source := by
  unfold cutoffOneVacuumColumnRefreshKernel
  exact Q'.mul_comm_eqv _ _

/-- Pushing the posterior through the refresh kernel returns the same
posterior exactly. -/
theorem cutoffOneVacuumColumnRefreshKernel_stationary
    {w : Q'} (hw : (0 : Q') < w)
    (target : EdgeLabelling) :
    listQSum
        (fun source =>
          cutoffOneVacuumColumnPosterior w hw source *
            cutoffOneVacuumColumnRefreshKernel w hw source target)
        (cutoffOneVacuumColumnCarrier w hw) ≈
      cutoffOneVacuumColumnPosterior w hw target := by
  unfold cutoffOneVacuumColumnRefreshKernel
  refine Q'.eqv_trans _
    (listQSum (cutoffOneVacuumColumnPosterior w hw)
        (cutoffOneVacuumColumnCarrier w hw) *
      cutoffOneVacuumColumnPosterior w hw target) _ ?_ ?_
  · exact listQSum_mul_right
      (cutoffOneVacuumColumnPosterior w hw)
      (cutoffOneVacuumColumnPosterior w hw target)
      (cutoffOneVacuumColumnCarrier w hw)
  refine Q'.eqv_trans _
    (1 * cutoffOneVacuumColumnPosterior w hw target) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (by
        simpa [cutoffOneVacuumColumnCarrier] using
          (cutoffOneVacuumColumnPosterior_total_one hw))
  exact Q'.one_mul_eqv _

/-! ## 3. Exact rank-one spectral action -/

/-- Posterior expectation of a finite rational observable. -/
def cutoffOneVacuumColumnPosteriorMean
    (w : Q') (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun target =>
      cutoffOneVacuumColumnPosterior w hw target * observable target)
    (cutoffOneVacuumColumnCarrier w hw)

/-- Markov action of the refresh kernel on a finite observable. -/
def cutoffOneVacuumColumnRefreshAction
    (w : Q') (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      cutoffOneVacuumColumnRefreshKernel w hw source target *
        observable target)
    (cutoffOneVacuumColumnCarrier w hw)

/-- Every row action is the same posterior expectation. -/
theorem cutoffOneVacuumColumnRefreshAction_eqv_mean
    {w : Q'} (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) :
    cutoffOneVacuumColumnRefreshAction w hw observable source ≈
      cutoffOneVacuumColumnPosteriorMean w hw observable := by
  unfold cutoffOneVacuumColumnRefreshAction
    cutoffOneVacuumColumnPosteriorMean
    cutoffOneVacuumColumnRefreshKernel
  exact Q'.eqv_refl _

/-- Constants are eigenvectors with eigenvalue one. -/
theorem cutoffOneVacuumColumnRefreshAction_one
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling) :
    cutoffOneVacuumColumnRefreshAction w hw (fun _ => 1) source ≈
      1 := by
  refine Q'.eqv_trans _
    (cutoffOneVacuumColumnPosteriorMean w hw (fun _ => 1)) _
    (cutoffOneVacuumColumnRefreshAction_eqv_mean hw _ source) ?_
  unfold cutoffOneVacuumColumnPosteriorMean
  refine Q'.eqv_trans _
    (listQSum (cutoffOneVacuumColumnPosterior w hw)
      (cutoffOneVacuumColumnCarrier w hw)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_one_eqv _
  simpa [cutoffOneVacuumColumnCarrier] using
    (cutoffOneVacuumColumnPosterior_total_one hw)

/-- Every observable with exact posterior mean zero is annihilated in one
refresh step, i.e. it is an eigenvector with eigenvalue zero. -/
theorem cutoffOneVacuumColumnRefreshAction_centered_zero
    {w : Q'} (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q')
    (hcentered :
      cutoffOneVacuumColumnPosteriorMean w hw observable ≈ 0)
    (source : EdgeLabelling) :
    cutoffOneVacuumColumnRefreshAction w hw observable source ≈
      0 := by
  exact Q'.eqv_trans _ _ _
    (cutoffOneVacuumColumnRefreshAction_eqv_mean hw observable source)
    hcentered

/-- Canonical centering of an observable by its exact posterior mean. -/
def cutoffOneVacuumColumnCenteredObservable
    (w : Q') (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q')
    (target : EdgeLabelling) : Q' :=
  observable target +
    (-cutoffOneVacuumColumnPosteriorMean w hw observable)

/-- Canonical centering really has posterior mean zero. -/
theorem cutoffOneVacuumColumnCenteredObservable_mean_zero
    {w : Q'} (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q') :
    cutoffOneVacuumColumnPosteriorMean w hw
        (cutoffOneVacuumColumnCenteredObservable w hw observable) ≈
      0 := by
  let states := cutoffOneVacuumColumnCarrier w hw
  let posterior := cutoffOneVacuumColumnPosterior w hw
  let mean := cutoffOneVacuumColumnPosteriorMean w hw observable
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
            posterior target * (-mean))
        states) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_add_eqv _ _ _
  refine Q'.eqv_trans _
    (listQSum
        (fun target => posterior target * observable target) states +
      listQSum (fun target => posterior target * (-mean)) states) _
    (listQSum_add _ _ states) ?_
  refine Q'.eqv_trans _
    (mean + listQSum (fun target => posterior target * (-mean)) states) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl mean) (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    (mean + listQSum posterior states * (-mean)) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl mean)
      (listQSum_mul_right posterior (-mean) states)) ?_
  refine Q'.eqv_trans _ (mean + 1 * (-mean)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_refl mean)
      (Q'.mul_eqv_congr_right _ _ _
        (by
          simpa [states, posterior, cutoffOneVacuumColumnCarrier] using
            (cutoffOneVacuumColumnPosterior_total_one hw)))
  refine Q'.eqv_trans _ (mean + (-mean)) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl mean) (Q'.one_mul_eqv (-mean))) ?_
  exact Q'.add_neg_self_eqv mean

/-- The refresh action is an exact projection: applying it twice changes
nothing. -/
theorem cutoffOneVacuumColumnRefreshAction_idempotent
    {w : Q'} (hw : (0 : Q') < w)
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) :
    cutoffOneVacuumColumnRefreshAction w hw
        (cutoffOneVacuumColumnRefreshAction w hw observable) source ≈
      cutoffOneVacuumColumnRefreshAction w hw observable source := by
  let states := cutoffOneVacuumColumnCarrier w hw
  let posterior := cutoffOneVacuumColumnPosterior w hw
  let mean := cutoffOneVacuumColumnPosteriorMean w hw observable
  refine Q'.eqv_trans _
    (cutoffOneVacuumColumnPosteriorMean w hw
      (cutoffOneVacuumColumnRefreshAction w hw observable)) _
    (cutoffOneVacuumColumnRefreshAction_eqv_mean hw _ source) ?_
  change
    listQSum
        (fun target =>
          posterior target *
            cutoffOneVacuumColumnRefreshAction w hw observable target)
        states ≈
      cutoffOneVacuumColumnRefreshAction w hw observable source
  refine Q'.eqv_trans _
    (listQSum (fun target => posterior target * mean) states) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.mul_eqv_congr_left (posterior target) _ _
      (cutoffOneVacuumColumnRefreshAction_eqv_mean
        hw observable target)
  refine Q'.eqv_trans _ (listQSum posterior states * mean) _
    (listQSum_mul_right posterior mean states) ?_
  refine Q'.eqv_trans _ (1 * mean) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ mean
      (by
        simpa [states, posterior, cutoffOneVacuumColumnCarrier] using
          (cutoffOneVacuumColumnPosterior_total_one hw))
  refine Q'.eqv_trans _ mean _ (Q'.one_mul_eqv mean) ?_
  exact Q'.eqv_symm
    (cutoffOneVacuumColumnRefreshAction_eqv_mean
      hw observable source)

/-! ## 4. A genuine nonconstant centered mode -/

/-- Code-faithful indicator of the central lower cube on the retained
cutoff-one source carrier. -/
def cutoffOneVacuumColumnCubeIndicator
    (source : EdgeLabelling) : Q' :=
  cutoffOneSourceCodeDelta source centralLowerCubeState

/-- The exact posterior mean of the cube indicator is the already computed
cube atom. -/
theorem cutoffOneVacuumColumnCubeIndicator_mean
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumColumnPosteriorMean w hw
        cutoffOneVacuumColumnCubeIndicator ≈
      cutoffOneVacuumColumnPosterior w hw centralLowerCubeState := by
  unfold cutoffOneVacuumColumnPosteriorMean
    cutoffOneVacuumColumnCubeIndicator cutoffOneVacuumColumnCarrier
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        cutoffOneSourceCodeDelta source centralLowerCubeState *
          cutoffOneVacuumColumnPosterior w hw source)
      (centralPositiveHalfStates w (Q'.le_of_lt hw) 1 0)) _ ?_ ?_
  · apply listQSum_congr
    intro source
    exact Q'.mul_comm_eqv _ _
  exact cutoffOneSourceCodeDelta_action_eqv
    (Q'.le_of_lt hw) centralLowerCubeState
    (centralLowerCubeState_mem_centralPositiveHalfStates
      hw (by decide : 1 ≤ 1))
    (cutoffOneVacuumColumnPosterior w hw)

/-- The physical cube indicator centered by its exact vacuum-column
posterior mean. -/
def cutoffOneVacuumColumnCenteredCubeMode
    (w : Q') (hw : (0 : Q') < w)
    (source : EdgeLabelling) : Q' :=
  cutoffOneVacuumColumnCenteredObservable w hw
    cutoffOneVacuumColumnCubeIndicator source

theorem cutoffOneVacuumColumnCenteredCubeMode_mean_zero
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumColumnPosteriorMean w hw
        (cutoffOneVacuumColumnCenteredCubeMode w hw) ≈
      0 := by
  exact cutoffOneVacuumColumnCenteredObservable_mean_zero
    hw cutoffOneVacuumColumnCubeIndicator

theorem cutoffOneVacuumColumnCenteredCubeMode_at_cube_eqv
    {w : Q'} (hw : (0 : Q') < w) :
    cutoffOneVacuumColumnCenteredCubeMode
        w hw centralLowerCubeState ≈
      (1 : Q') +
        (-cutoffOneVacuumColumnPosterior
          w hw centralLowerCubeState) := by
  unfold cutoffOneVacuumColumnCenteredCubeMode
    cutoffOneVacuumColumnCenteredObservable
    cutoffOneVacuumColumnCubeIndicator cutoffOneSourceCodeDelta
  rw [if_pos rfl]
  exact Q'.add_eqv_congr'
    (Q'.eqv_refl 1)
    (Q'.neg_eqv_congr _ _
      (cutoffOneVacuumColumnCubeIndicator_mean hw))

/-- The centered cube mode is genuinely nonzero: at the cube its value is
strictly positive because the other (vacuum) atom also has positive mass. -/
theorem cutoffOneVacuumColumnCenteredCubeMode_at_cube_pos
    {w : Q'} (hw : (0 : Q') < w) :
    (0 : Q') <
      cutoffOneVacuumColumnCenteredCubeMode
        w hw centralLowerCubeState := by
  exact Q'.pos_of_lt_of_le
    (one_sub_pos_of_lt_one
      (cutoffOneVacuumColumnPosterior_cube_lt_one hw))
    (Q'.ge_of_eqv
      (cutoffOneVacuumColumnCenteredCubeMode_at_cube_eqv hw))

/-- The explicit nonconstant centered cube mode is annihilated in one
refresh step. -/
theorem cutoffOneVacuumColumnRefreshAction_centeredCubeMode_zero
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling) :
    cutoffOneVacuumColumnRefreshAction w hw
        (cutoffOneVacuumColumnCenteredCubeMode w hw) source ≈
      0 := by
  exact cutoffOneVacuumColumnRefreshAction_centered_zero hw _
    (cutoffOneVacuumColumnCenteredCubeMode_mean_zero hw) source

/-- Algebraic centered eigenvalue of the exact refresh projection. -/
def cutoffOneVacuumColumnRefreshCenteredEigenvalue : Q' := 0

/-- Exact finite algebraic gap between the constant and centered modes. -/
def cutoffOneVacuumColumnRefreshAlgebraicGap : Q' := 1

theorem cutoffOneVacuumColumnRefreshAlgebraicGap_pos :
    (0 : Q') < cutoffOneVacuumColumnRefreshAlgebraicGap := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnRefreshKernel_row_normalized
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnRefreshKernel_detailedBalance
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnRefreshKernel_stationary
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnRefreshAction_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnRefreshAction_centered_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnCenteredObservable_mean_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnRefreshAction_idempotent
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnCubeIndicator_mean
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnCenteredCubeMode_at_cube_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnRefreshAction_centeredCubeMode_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum.cutoffOneVacuumColumnRefreshAlgebraicGap_pos
