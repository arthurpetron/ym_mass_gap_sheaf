/-
# The cutoff-one canonical overlap residual is exactly zero

On every genuine cutoff-one boundary channel the central-cube half-amplitude
is the fixed six-face activity times the vacuum half-amplitude.  Together
with the exact two-state presentation and stationary-posterior bridge, this
factors the actual indexed state-boundary amplitude as

    amplitude(index,boundary)
      = stationary(index) * channelTotal(boundary).

Both Bayes directions are therefore independent: `target | boundary` is the
sector stationary law on every positive channel, and `boundary | source` is
the sector boundary prior for every canonical source.  Their exact overlaps,
both capped overlap floors, are one, so the residual scalar is zero.

This is finite `K = 1`, half-extent zero only.  It does not provide a cofinal
or continuum estimate.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
import YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCenteredGram
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorPresentation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCubeEntry
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumPosterior
open YMGap.Continuum.BF4PhysicalBoundaryVariableElimination
open YMGap.Continuum.BF4PhysicalBoundaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGram
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlap
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapFloor
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramOverlapResidualRate
open YMGap.Continuum.BF4PhysicalVacuumSectorCenteredGramPosterior
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

private theorem one_num_local : (1 : Q').num = 1 := rfl

private theorem one_den_local : (1 : Q').den = 1 := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofInt, Q'.ofNat, Q'.neg,
               one_num_local, one_den_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try simp;
             try omega;
             try ac_rfl))

private theorem qmul_congr
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Rank-one state-boundary amplitude -/

/-- On every literal boundary channel, the central-cube row is the fixed
six-face activity times the vacuum row. -/
theorem centralHalfAmplitude_cutoffOne_cube_eqv_activity_mul_vacuum_on_boundary
    (w : Q') {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels 1 0) :
    centralHalfAmplitude w 1 0 centralLowerCubeState boundary ≈
      (coeffW w 1) ^ 6 *
        centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary := by
  rw [centralBoundaryChannels_eq_map_allSeqs] at hboundary
  obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hboundary
  refine Q'.eqv_trans _
    (binaryVacuumWordWeight word * (coeffW w 1) ^ 6) _
    (centralHalfAmplitude_cutoffOne_cube_word_eqv_delta w word hword) ?_
  refine Q'.eqv_trans _
    ((coeffW w 1) ^ 6 * binaryVacuumWordWeight word) _
    (Q'.mul_comm_eqv _ _) ?_
  exact Q'.mul_eqv_congr_left ((coeffW w 1) ^ 6) _ _
    (Q'.eqv_symm
      (centralHalfAmplitude_cutoffOne_vacuum_word_eqv_delta
        w word hword))

/-- The literal canonical-sector channel total is the posterior denominator
times the vacuum-row amplitude. -/
theorem centralPhysicalFiniteVacuumSectorChannelTotal_cutoffOne_eqv
    {w : Q'} (hw : (0 : Q') < w) {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels 1 0) :
    centralPhysicalFiniteVacuumSectorChannelTotal
        w (Q'.le_of_lt hw) 1 0 boundary ≈
      cutoffOneVacuumColumnDenominator w *
        centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary := by
  let amplitudeOnState := fun state : EdgeLabelling =>
    centralHalfAmplitude w 1 0 state boundary
  let vacuumAmplitude :=
    centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary
  let activity := (coeffW w 1) ^ 6
  refine Q'.eqv_trans _
    (listQSum amplitudeOnState
      (centralPhysicalFiniteVacuumSectorStates
        w (Q'.le_of_lt hw) 1 0)) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorChannelTotal
      finiteChannelTotalAmplitude
      centralPhysicalFiniteVacuumSectorGramAmplitude
      centralPhysicalFiniteVacuumSectorStates
    exact Q'.eqv_of_eq
      (listQSum_map amplitudeOnState
        (centralPhysicalFiniteStateAt w (Q'.le_of_lt hw) 1 0)
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) 1 0)).symm
  refine Q'.eqv_trans _
    (listQSum amplitudeOnState cutoffOneVacuumCubePhysicalSources) _
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_sum_eqv
      hw amplitudeOnState) ?_
  refine Q'.eqv_trans _
    (vacuumAmplitude +
      centralHalfAmplitude w 1 0 centralLowerCubeState boundary) _ ?_ ?_
  · unfold cutoffOneVacuumCubePhysicalSources listQSum
    exact Q'.add_eqv_congr_left vacuumAmplitude _ _
      (Q'.eqv_of_eq (Q'.add_zero' _))
  refine Q'.eqv_trans _
    (vacuumAmplitude + activity * vacuumAmplitude) _
    (Q'.add_eqv_congr_left vacuumAmplitude _ _
      (centralHalfAmplitude_cutoffOne_cube_eqv_activity_mul_vacuum_on_boundary
        w hboundary)) ?_
  change vacuumAmplitude + activity * vacuumAmplitude ≈
    (1 + activity) * vacuumAmplitude
  refine Q'.eqv_trans _
    ((1 : Q') * vacuumAmplitude + activity * vacuumAmplitude) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.one_mul_eqv vacuumAmplitude))
      (Q'.eqv_refl _)
  exact Q'.eqv_symm
    (Q'.add_mul_eqv 1 activity vacuumAmplitude)

private theorem cutoffOneVacuumColumnPosterior_mul_channelTotal_eqv_amplitude
    {w : Q'} (hw : (0 : Q') < w) {state boundary : EdgeLabelling}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0)
    (hboundary : boundary ∈ centralBoundaryChannels 1 0) :
    cutoffOneVacuumColumnPosterior w hw state *
        centralPhysicalFiniteVacuumSectorChannelTotal
          w (Q'.le_of_lt hw) 1 0 boundary ≈
      centralHalfAmplitude w 1 0 state boundary := by
  have hblock :=
    (centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff
      hw state).mp hstate
  simp only [cutoffOneVacuumCubePhysicalSources,
    List.mem_cons, List.not_mem_nil, or_false] at hblock
  rcases hblock with hstateVacuum | hstateCube
  · subst state
    refine Q'.eqv_trans _
      (Q'.divPos 1 (cutoffOneVacuumColumnDenominator w)
          (cutoffOneVacuumColumnDenominator_pos hw) *
        (cutoffOneVacuumColumnDenominator w *
          centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary)) _ ?_ ?_
    · exact qmul_congr
        (cutoffOneVacuumColumnPosterior_vacuum_eqv hw)
        (centralPhysicalFiniteVacuumSectorChannelTotal_cutoffOne_eqv
          hw hboundary)
    refine Q'.eqv_trans _
      ((Q'.divPos 1 (cutoffOneVacuumColumnDenominator w)
          (cutoffOneVacuumColumnDenominator_pos hw) *
        cutoffOneVacuumColumnDenominator w) *
          centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      (1 * centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.divPos_mul_eqv 1 (cutoffOneVacuumColumnDenominator w)
          (cutoffOneVacuumColumnDenominator_pos hw)))
      (Q'.one_mul_eqv _)
  · subst state
    let activity := (coeffW w 1) ^ 6
    refine Q'.eqv_trans _
      (Q'.divPos activity (cutoffOneVacuumColumnDenominator w)
          (cutoffOneVacuumColumnDenominator_pos hw) *
        (cutoffOneVacuumColumnDenominator w *
          centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary)) _ ?_ ?_
    · exact qmul_congr
        (cutoffOneVacuumColumnPosterior_cube_eqv hw)
        (centralPhysicalFiniteVacuumSectorChannelTotal_cutoffOne_eqv
          hw hboundary)
    refine Q'.eqv_trans _
      ((Q'.divPos activity (cutoffOneVacuumColumnDenominator w)
          (cutoffOneVacuumColumnDenominator_pos hw) *
        cutoffOneVacuumColumnDenominator w) *
          centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _
      (activity *
        centralHalfAmplitude w 1 0 zeroEdgeLabelling boundary) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.divPos_mul_eqv activity
          (cutoffOneVacuumColumnDenominator w)
          (cutoffOneVacuumColumnDenominator_pos hw))) ?_
    exact Q'.eqv_symm
      (centralHalfAmplitude_cutoffOne_cube_eqv_activity_mul_vacuum_on_boundary
        w hboundary)

/-- The actual indexed state-boundary half-amplitude factors through the
component-conditioned stationary weight and channel total. -/
theorem centralPhysicalFiniteVacuumSectorGramAmplitude_cutoffOne_eqv_stationary_mul_channelTotal
    {w : Q'} (hw : (0 : Q') < w) {index : Nat}
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels 1 0) :
    centralPhysicalFiniteVacuumSectorGramAmplitude
        w (Q'.le_of_lt hw) 1 0 index boundary ≈
      centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w (Q'.le_of_lt hw) 1 0 index *
        centralPhysicalFiniteVacuumSectorChannelTotal
          w (Q'.le_of_lt hw) 1 0 boundary := by
  let state := centralPhysicalFiniteStateAt
    w (Q'.le_of_lt hw) 1 0 index
  have hstate : state ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w (Q'.le_of_lt hw) 1 0 hindex rfl
  refine Q'.eqv_symm (Q'.eqv_trans _
    (cutoffOneVacuumColumnPosterior w hw state *
      centralPhysicalFiniteVacuumSectorChannelTotal
        w (Q'.le_of_lt hw) 1 0 boundary) _ ?_ ?_)
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_cutoffOne_eqv_posterior
        hw hindex)
  unfold centralPhysicalFiniteVacuumSectorGramAmplitude state
  exact cutoffOneVacuumColumnPosterior_mul_channelTotal_eqv_amplitude
    hw hstate hboundary

/-! ## 2. Both conditional laws equal their priors -/

/-- On every positive cutoff-one channel, the target conditional law is the
component-conditioned stationary law. -/
theorem centralPhysicalFiniteVacuumSectorTargetGivenBoundary_cutoffOne_eqv_stationary
    {w : Q'} (hw : (0 : Q') < w)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels 1 0)
    (channelTotal_pos :
      (0 : Q') < centralPhysicalFiniteVacuumSectorChannelTotal
        w (Q'.le_of_lt hw) 1 0 boundary)
    {index : Nat}
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalFiniteVacuumSectorTargetGivenBoundary
        w (Q'.le_of_lt hw) 1 0 boundary channelTotal_pos index ≈
      centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w (Q'.le_of_lt hw) 1 0 index := by
  apply Q'.mul_left_cancel_of_pos channelTotal_pos
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
        w (Q'.le_of_lt hw) 1 0 boundary channelTotal_pos index *
      centralPhysicalFiniteVacuumSectorChannelTotal
        w (Q'.le_of_lt hw) 1 0 boundary) _
    (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorGramAmplitude
      w (Q'.le_of_lt hw) 1 0 index boundary) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorTargetGivenBoundary
      finiteStateGivenChannel
    exact Q'.divPos_mul_eqv _ _ _
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
        w (Q'.le_of_lt hw) 1 0 index *
      centralPhysicalFiniteVacuumSectorChannelTotal
        w (Q'.le_of_lt hw) 1 0 boundary) _
    (centralPhysicalFiniteVacuumSectorGramAmplitude_cutoffOne_eqv_stationary_mul_channelTotal
      hw hindex hboundary) (Q'.mul_comm_eqv _ _)

private theorem finiteWeightedGramChannelGivenState_eqv_prior_of_rankOne
    {State Channel : Type}
    (states : List State) (weight : Channel → Q')
    (amplitude : State → Channel → Q')
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (marginal : State → Q') (state : State)
    (marginal_pos : (0 : Q') < marginal state)
    (channel : Channel)
    (hrankOne : amplitude state channel ≈
      marginal state *
        finiteChannelTotalAmplitude states amplitude channel) :
    finiteWeightedGramChannelGivenState
        states weight amplitude mass mass_pos marginal state
        marginal_pos channel ≈
      finiteWeightedGramChannelPrior
        states weight amplitude mass mass_pos channel := by
  let total := finiteChannelTotalAmplitude states amplitude channel
  let priorNumerator := weight channel * (total * total)
  let givenNumerator := weight channel * (amplitude state channel * total)
  let rowMass := mass * marginal state
  let rowMass_pos := Q'.mul_pos mass_pos marginal_pos
  apply Q'.mul_left_cancel_of_pos rowMass_pos
  refine Q'.eqv_trans _
    (finiteWeightedGramChannelGivenState
        states weight amplitude mass mass_pos marginal state
          marginal_pos channel * rowMass) _
    (Q'.mul_comm_eqv _ _) ?_
  refine Q'.eqv_trans _ givenNumerator _ ?_ ?_
  · change Q'.divPos givenNumerator rowMass rowMass_pos * rowMass ≈
      givenNumerator
    exact Q'.divPos_mul_eqv _ _ _
  have hgiven : givenNumerator ≈ marginal state * priorNumerator := by
    unfold givenNumerator priorNumerator total
    refine Q'.eqv_trans _
      (weight channel *
        ((marginal state *
          finiteChannelTotalAmplitude states amplitude channel) *
        finiteChannelTotalAmplitude states amplitude channel)) _
      (Q'.mul_eqv_congr_left (weight channel) _ _
        (Q'.mul_eqv_congr_right _ _ _ hrankOne)) ?_
    q_ring
  refine Q'.eqv_trans _ (marginal state * priorNumerator) _ hgiven ?_
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (marginal state *
      (finiteWeightedGramChannelPrior
          states weight amplitude mass mass_pos channel * mass)) _ ?_ ?_
  · q_ring
  exact Q'.mul_eqv_congr_left (marginal state) _ _ (by
    unfold finiteWeightedGramChannelPrior priorNumerator total
    exact Q'.divPos_mul_eqv _ _ _)

/-- Every canonical cutoff-one source induces exactly the common boundary
prior. -/
theorem centralPhysicalFiniteVacuumSectorBoundaryGivenSource_cutoffOne_eqv_prior
    {w : Q'} (hw : (0 : Q') < w) {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels 1 0) :
    centralPhysicalFiniteVacuumSectorBoundaryGivenSource
        w (Q'.le_of_lt hw) 1 0 source hsource boundary ≈
      centralPhysicalFiniteVacuumSectorBoundaryPrior
        w (Q'.le_of_lt hw) 1 0 boundary := by
  unfold centralPhysicalFiniteVacuumSectorBoundaryGivenSource
    centralPhysicalFiniteVacuumSectorBoundaryPrior
  exact finiteWeightedGramChannelGivenState_eqv_prior_of_rankOne
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0)
    (centralPhysicalFiniteVacuumSectorGramWeight
      w (Q'.le_of_lt hw) 1 0)
    (centralPhysicalFiniteVacuumSectorGramAmplitude
      w (Q'.le_of_lt hw) 1 0)
    (centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) 1 0)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) 1 0)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w (Q'.le_of_lt hw) 1 0)
    source
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_pos hsource)
    boundary
    (centralPhysicalFiniteVacuumSectorGramAmplitude_cutoffOne_eqv_stationary_mul_channelTotal
      hw hsource hboundary)

/-! ## 3. Exact overlaps, floors, and residual -/

private theorem finiteProbabilityOverlap_eqv_one_of_pointwise_eqv
    {State : Type} (states : List State)
    (left right : State → Q')
    (hpoint : ∀ state, state ∈ states → left state ≈ right state)
    (hright : listQSum right states ≈ 1) :
    finiteProbabilityOverlap states left right ≈ 1 := by
  refine Q'.eqv_trans _ (listQSum right states) _ ?_ hright
  unfold finiteProbabilityOverlap
  apply listQSum_congr_on
  intro state hstate
  unfold Q'.min'
  by_cases hle : left state ≤ right state
  · rw [if_pos hle]
    exact hpoint state hstate
  · rw [if_neg hle]
    exact Q'.eqv_refl _

private theorem finiteCappedMinimum_eqv_one_of_values
    {A : Type} (value : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → value item ≈ 1) →
      finiteCappedMinimum value items ≈ 1
  | [], _ => Q'.eqv_refl 1
  | head :: tail, hvalue => by
      have hhead := hvalue head List.mem_cons_self
      have htail := finiteCappedMinimum_eqv_one_of_values value tail
        (fun item hitem =>
          hvalue item (List.mem_cons_of_mem head hitem))
      unfold finiteCappedMinimum Q'.min'
      by_cases hle : value head ≤ finiteCappedMinimum value tail
      · rw [if_pos hle]
        exact hhead
      · rw [if_neg hle]
        exact htail

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_cutoffOne_eqv_one
    {w : Q'} (hw : (0 : Q') < w)
    {boundary : EdgeLabelling}
    (hboundary : boundary ∈ centralBoundaryChannels 1 0)
    (channelTotal_pos :
      (0 : Q') < centralPhysicalFiniteVacuumSectorChannelTotal
        w (Q'.le_of_lt hw) 1 0 boundary) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
        w (Q'.le_of_lt hw) 1 0 boundary channelTotal_pos ≈ 1 := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap
  exact finiteProbabilityOverlap_eqv_one_of_pointwise_eqv
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0)
    (centralPhysicalFiniteVacuumSectorTargetGivenBoundary
      w (Q'.le_of_lt hw) 1 0 boundary channelTotal_pos)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w (Q'.le_of_lt hw) 1 0)
    (fun index hindex =>
      centralPhysicalFiniteVacuumSectorTargetGivenBoundary_cutoffOne_eqv_stationary
        hw hboundary channelTotal_pos hindex)
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
      w (Q'.le_of_lt hw) 1 0)

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_cutoffOne_eqv_one
    {w : Q'} (hw : (0 : Q') < w) {source : Nat}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
        w (Q'.le_of_lt hw) 1 0 source hsource ≈ 1 := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap
  exact finiteProbabilityOverlap_eqv_one_of_pointwise_eqv
    (centralBoundaryChannels 1 0)
    (centralPhysicalFiniteVacuumSectorBoundaryGivenSource
      w (Q'.le_of_lt hw) 1 0 source hsource)
    (centralPhysicalFiniteVacuumSectorBoundaryPrior
      w (Q'.le_of_lt hw) 1 0)
    (fun boundary hboundary =>
      centralPhysicalFiniteVacuumSectorBoundaryGivenSource_cutoffOne_eqv_prior
        hw hsource hboundary)
    (centralPhysicalFiniteVacuumSectorBoundaryPrior_total_one
      w (Q'.le_of_lt hw) 1 0)

theorem centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_cutoffOne_eqv_one
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
        w (Q'.le_of_lt hw) 1 0 ≈ 1 := by
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor
  apply finiteCappedMinimum_eqv_one_of_values
  intro boundary hboundary
  unfold centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapOrOne
  by_cases htotal :
      (0 : Q') < centralPhysicalFiniteVacuumSectorChannelTotal
        w (Q'.le_of_lt hw) 1 0 boundary
  · rw [dif_pos htotal]
    exact centralPhysicalFiniteVacuumSectorTargetPosteriorOverlap_cutoffOne_eqv_one
      hw hboundary htotal
  · rw [dif_neg htotal]
    exact Q'.eqv_refl 1

theorem centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_cutoffOne_eqv_one
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
        w (Q'.le_of_lt hw) 1 0 ≈ 1 := by
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor
  apply finiteCappedMinimum_eqv_one_of_values
  intro source hsource
  unfold centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapOrOne
  rw [dif_pos hsource]
  exact centralPhysicalFiniteVacuumSectorSourcePosteriorOverlap_cutoffOne_eqv_one
    hw hsource

/-- The exact centered-Gram posterior-overlap residual scalar vanishes at
cutoff one. -/
theorem centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_cutoffOne_eqv_zero
    {w : Q'} (hw : (0 : Q') < w) :
    centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
        w (Q'.le_of_lt hw) 1 0 ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapResidualRate
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapResidualRate
  have htarget :=
    centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_cutoffOne_eqv_one
      hw
  have hsource :=
    centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_cutoffOne_eqv_one
      hw
  apply Q'.eqv_trans _
    (((2 : Q') * (1 + (-1))) *
      ((2 : Q') * (1 + (-1)))) _
  · exact qmul_congr
      (Q'.mul_eqv_congr_left 2 _ _
        (Q'.add_eqv_congr_left 1 _ _
          (Q'.neg_eqv_congr _ _ htarget)))
      (Q'.mul_eqv_congr_left 2 _ _
        (Q'.add_eqv_congr_left 1 _ _
          (Q'.neg_eqv_congr _ _ hsource)))
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual.centralHalfAmplitude_cutoffOne_cube_eqv_activity_mul_vacuum_on_boundary
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual.centralPhysicalFiniteVacuumSectorGramAmplitude_cutoffOne_eqv_stationary_mul_channelTotal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual.centralPhysicalFiniteVacuumSectorTargetGivenBoundary_cutoffOne_eqv_stationary
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual.centralPhysicalFiniteVacuumSectorBoundaryGivenSource_cutoffOne_eqv_prior
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual.centralPhysicalFiniteVacuumSectorTargetPosteriorOverlapFloor_cutoffOne_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual.centralPhysicalFiniteVacuumSectorSourcePosteriorOverlapFloor_cutoffOne_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorOverlapResidual.centralPhysicalFiniteVacuumSectorPosteriorOverlapResidualRate_cutoffOne_eqv_zero
