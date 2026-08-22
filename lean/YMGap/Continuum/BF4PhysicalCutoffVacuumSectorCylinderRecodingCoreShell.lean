/-
# Core--shell convergence of the BF4 sector recoding

The exact sector recoding at an action cutoff and the genuine global cutoff
action agree on that cutoff's positive carrier.  At later finite GNS stages,
their discrepancy is therefore supported only on the stationary source shell.
The pointwise `l1` bounds proved in the preceding module give the fixed square
envelope `(2 l1)^2` on that shell.

This file combines those facts with the existing corrected-slab shell schedule
to prove a limiting squared-distance bound `1/(i+1)`.  The estimate is uniform
in the later approximation cutoff; it does not use moving inner regularity.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingAmplitude

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCoreTailCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingAmplitude
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.TsumDeriv.Q'
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A scaled finite core--shell inequality -/

private theorem listQSum_filter_le_nonnegative
    {A : Type} (value : A → Q') (test : A → Bool)
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A,
      listQSum value (items.filter test) ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_nonnegative value test hvalue tail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          have hmono : listQSum value tail ≤
              value head + listQSum value tail := by
            have hscaled := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail)
              (hvalue head)
            rwa [Q'.zero_add'] at hscaled
          exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_le_add_left (value head) _ _ ih

/-- A finite physical GNS distance with arbitrary pointwise envelope is
bounded by its core error plus the stationary shell mass times that envelope.
This is the scaled analogue of the unit-observable core--shell estimate. -/
theorem centralPhysicalFiniteDistSq_le_core_add_scaled_shell
    {w : Q'} (hw : (0 : Q') ≤ w)
    (cutoff half base : Nat)
    (left right : EdgeLabelling → Q')
    (coreError envelope : Q')
    (hcoreError : (0 : Q') ≤ coreError)
    (hcore : ∀ state,
      (∀ edge, edge ∉ centralLowerFaceIds half → state edge = 0) →
      labelWithinB base (centralLowerFaceIds half) state = true →
      (0 : Q') < centralPhysicalRowMarginal w hw base half state →
      let difference := left state + -(right state)
      difference * difference ≤ coreError)
    (hsquare : ∀ state,
      let difference := left state + -(right state)
      difference * difference ≤ envelope) :
    (centralPhysicalSmulGNS w hw cutoff half).toGNSData.distSqQ
        left right ≤
      coreError +
        centralPhysicalRowMarginalOutsideBase
          w hw cutoff half base * envelope := by
  let states := centralPositiveHalfStates w hw cutoff half
  let row := centralPhysicalRowMarginal w hw cutoff half
  let test := fun state =>
    labelWithinB base (centralLowerFaceIds half) state &&
      decide ((0 : Q') <
        centralPhysicalRowMarginal w hw base half state)
  let difference := fun state => left state + -(right state)
  let weightedSquare := fun state =>
    row state * (difference state * difference state)
  change listQSum weightedSquare states ≤
    coreError +
      centralPhysicalRowMarginalOutsideBase
        w hw cutoff half base * envelope
  have hsplit := listQSum_filter_partition weightedSquare test states
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
  apply Q'.add_le_add
  · have hpoint : listQSum weightedSquare (states.filter test) ≤
        listQSum (fun state => row state * coreError)
          (states.filter test) := by
      apply listQSum_mono
      intro state hstate
      have hpositive := (List.mem_filter.mp hstate).1
      have hcutoffCarrier :=
        (mem_centralPositiveHalfStates_iff.mp hpositive).1
      have hsupport :=
        (boundedEdgeLabellings_sound cutoff
          (centralLowerFaceIds half) state hcutoffCarrier).2
      have htest := (Bool.and_eq_true _ _).mp
        (List.mem_filter.mp hstate).2
      exact Q'.mul_le_mul_of_nonneg_left _ _ _
        (hcore state hsupport htest.1
          (by simpa only [decide_eq_true_eq] using htest.2))
        (centralPhysicalRowMarginal_nonnegative hw cutoff half state)
    refine Q'.le_trans' _ _ _ hpoint ?_
    refine Q'.le_trans' _
      (listQSum row (states.filter test) * coreError) _
      (Q'.le_of_eqv
        (listQSum_mul_right row coreError (states.filter test))) ?_
    have hmass : listQSum row (states.filter test) ≤ (1 : Q') :=
      Q'.le_trans' _ _ _
        (listQSum_filter_le_nonnegative row test
          (fun state =>
            centralPhysicalRowMarginal_nonnegative hw cutoff half state)
          states)
        (Q'.le_of_eqv
          (centralPositiveRowMarginal_total_one w hw cutoff half))
    exact Q'.le_trans' _ ((1 : Q') * coreError) _
      (Q'.mul_le_mul_of_nonneg_right _ _ coreError hmass hcoreError)
      (Q'.le_of_eqv (Q'.one_mul_eqv coreError))
  · change listQSum weightedSquare
        (states.filter (fun state => !(test state))) ≤
      listQSum row (states.filter (fun state => !(test state))) * envelope
    have hpoint : listQSum weightedSquare
          (states.filter (fun state => !(test state))) ≤
        listQSum (fun state => row state * envelope)
          (states.filter (fun state => !(test state))) := by
      apply listQSum_mono
      intro state _
      exact Q'.mul_le_mul_of_nonneg_left _ _ _
        (hsquare state)
        (centralPhysicalRowMarginal_nonnegative hw cutoff half state)
    exact Q'.le_trans' _ _ _ hpoint
      (Q'.le_of_eqv
        (listQSum_mul_right row envelope
          (states.filter (fun state => !(test state)))))

/-! ## 2. The recoding square envelope and exact core -/

/-- The pointwise squared discrepancy is bounded by the square of twice the
input coefficient `l1`. -/
theorem centralPhysicalVacuumSectorRecoding_sub_sq_le_envelope
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (cutoff : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (state : EdgeLabelling) :
    let left :=
      (centralPhysicalVacuumSectorPresentationMarkovAtCutoff
        cutoff presentation).toLinearObservable.value state
    let right :=
      (centralPhysicalLinearMarkovCutoffAction hw cutoff half
        presentation.toLinearObservable).value state
    let difference := left + -right
    difference * difference ≤
      centralPhysicalVacuumSectorPresentationRecodingSqEnvelope
        presentation := by
  dsimp only
  let left :=
    (centralPhysicalVacuumSectorPresentationMarkovAtCutoff
      cutoff presentation).toLinearObservable.value state
  let right :=
    (centralPhysicalLinearMarkovCutoffAction hw cutoff half
      presentation.toLinearObservable).value state
  let difference := left + -right
  let l1 := centralPhysicalVacuumSectorPresentationL1 presentation
  let doubled := l1 + l1
  have hleft : Q'.abs left ≤ l1 := by
    unfold left l1
    exact centralPhysicalVacuumSectorMarkovCylinder_abs_le_l1
      cutoff presentation state
  have hright : Q'.abs right ≤ l1 := by
    unfold right l1
    exact centralPhysicalLinearMarkovCutoffAction_vacuumSector_abs_le_l1
      cutoff presentation state
  have habs : Q'.abs difference ≤ doubled := by
    refine Q'.le_trans' _ _ _ (TsumDeriv.abs_add_le left (-right)) ?_
    exact Q'.add_le_add hleft
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (TsumDeriv.Q'.abs_neg right)) hright)
  have hsquare : difference * difference ≤
      Q'.abs difference * Q'.abs difference :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (ExpNeg.abs_mul_le difference difference)
  have hdoubled : (0 : Q') ≤ doubled := by
    unfold doubled l1 centralPhysicalVacuumSectorPresentationL1
    have hl1 := coefficientL1_nonnegative_local
      (centralPhysicalFiniteVacuumSectorIndices
        w hw presentation.base half) presentation.coefficient
    exact Q'.zero_le_add _ _ hl1 hl1
  unfold centralPhysicalVacuumSectorPresentationRecodingSqEnvelope
  exact Q'.le_trans' _ _ _ hsquare
    (Q'.mul_le_mul_of_nonneg habs habs hdoubled
      (Q'.abs_nonneg difference))

/-- On the action-cutoff core, the canonical sector recoding and genuine
global cutoff action have zero pointwise squared discrepancy. -/
theorem centralPhysicalVacuumSectorRecoding_core_sub_sq_le_zero
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hbase : presentation.base ≤ cutoff)
    (state : EdgeLabelling)
    (hsupport : ∀ edge, edge ∉ centralLowerFaceIds half → state edge = 0)
    (hwithin :
      labelWithinB cutoff (centralLowerFaceIds half) state = true)
    (hpositive :
      (0 : Q') < centralPhysicalRowMarginal w hw cutoff half state) :
    let difference :=
      (centralPhysicalVacuumSectorPresentationMarkovAtCutoff
        cutoff presentation).toLinearObservable.value state +
      -((centralPhysicalLinearMarkovCutoffAction hw cutoff half
        presentation.toLinearObservable).value state)
    difference * difference ≤ (0 : Q') := by
  dsimp only
  have hcarrier : state ∈ centralHalfStates cutoff half := by
    unfold centralHalfStates
    apply boundedEdgeLabellings_complete
    · exact (labelWithinB_true_iff
        cutoff (centralLowerFaceIds half) state).mp hwithin
    · exact hsupport
  have hstate : state ∈
      centralPositiveHalfStates w hw cutoff half :=
    mem_centralPositiveHalfStates_iff.mpr ⟨hcarrier, hpositive⟩
  obtain ⟨target, htarget, htargetState⟩ :=
    centralPhysicalFiniteStateAt_exists w hw cutoff half hstate
  have hrealization :=
    centralPhysicalVacuumSectorMarkovCylinderRealization_value
      presentation hbase htarget
  have haction :=
    centralPhysicalVacuumSectorMarkovCoefficientAtCutoff_eqv_action
      (cutoff := cutoff) (index := target) presentation
  have hagree :
      (centralPhysicalVacuumSectorPresentationMarkovAtCutoff
        cutoff presentation).toLinearObservable.value state ≈
      (centralPhysicalLinearMarkovCutoffAction hw cutoff half
        presentation.toLinearObservable).value state := by
    rw [← htargetState]
    exact Q'.eqv_trans _ _ _ hrealization haction
  let difference :=
    (centralPhysicalVacuumSectorPresentationMarkovAtCutoff
      cutoff presentation).toLinearObservable.value state +
    -((centralPhysicalLinearMarkovCutoffAction hw cutoff half
      presentation.toLinearObservable).value state)
  have hdifference : difference ≈ 0 := by
    unfold difference
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hagree)
      (Q'.add_neg_self_eqv _)
  have hsquare : difference * difference ≈ 0 :=
    Q'.eqv_trans _ (0 * difference) _
      (Q'.mul_eqv_congr_right _ _ _ hdifference)
      (Q'.zero_mul_eqv difference)
  exact Q'.le_of_eqv hsquare

/-! ## 3. The limiting shell estimate -/

private theorem leEv_of_eventual_approx_le
    {left right : CReal} (rate : Nat)
    (h : ∀ cutoff, rate ≤ cutoff →
      left.approx cutoff ≤ right.approx cutoff) :
    CReal.leEv left right := by
  intro epsilon hepsilon
  exact ⟨rate, fun cutoff hcutoff =>
    Q'.le_trans' _ _ _ (h cutoff hcutoff)
      (Q'.add_le_self_of_nonneg
        (right.approx cutoff) epsilon (Q'.le_of_lt hepsilon))⟩

/-- If the action cutoff pays the amplitude-scaled source-shell schedule, the
limiting distance from its sector recoding to the global cutoff action is at
most `1/(i+1)`. -/
theorem centralPhysicalVacuumSectorRecoding_distSq_le_invSucc
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half stage index : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (hbase : presentation.base ≤ stage)
    (hscheduled :
      centralPhysicalTargetShellCutoff w half
          (centralPhysicalVacuumSectorPresentationShellTolerance
            presentation (Q'.invSucc index)) ≤ stage) :
    CReal.leEv
      (physicalLinearDistSq hw0 hw1 half
        (centralPhysicalVacuumSectorPresentationMarkovAtCutoff
          stage presentation).toLinearObservable
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half presentation.toLinearObservable))
      (CReal.ofQ' (Q'.invSucc index)) := by
  let envelope :=
    centralPhysicalVacuumSectorPresentationRecodingSqEnvelope presentation
  let tolerance :=
    centralPhysicalVacuumSectorPresentationShellTolerance
      presentation (Q'.invSucc index)
  apply leEv_of_eventual_approx_le stage
  intro later hlater
  have hstage := physicalLinearDistSq_approx_eqv_stage
    hw0 hw1 half later
    (centralPhysicalVacuumSectorPresentationMarkovAtCutoff
      stage presentation).toLinearObservable
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half presentation.toLinearObservable)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hstage) ?_
  have hfinite := centralPhysicalFiniteDistSq_le_core_add_scaled_shell
    (Q'.le_of_lt hw0) later half stage
    (centralPhysicalVacuumSectorPresentationMarkovAtCutoff
      stage presentation).toLinearObservable.value
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) stage half presentation.toLinearObservable).value
    0 envelope (Q'.le_refl' 0)
    (centralPhysicalVacuumSectorRecoding_core_sub_sq_le_zero
      presentation hbase)
    (centralPhysicalVacuumSectorRecoding_sub_sq_le_envelope
      stage presentation)
  refine Q'.le_trans' _ _ _ hfinite ?_
  have hshell := centralPhysicalRowMarginalOutsideBase_le_increment
    (half := half) (Q'.le_of_lt hw0) hlater
  have hincrementMono := slabParametricKCutoffIncrement_antitone_base
    (extent := centralExtent half) (Q'.le_of_lt hw0)
    hscheduled hlater
  have hscheduleLater :
      centralPhysicalTargetShellCutoff w half tolerance ≤ later :=
    Nat.le_trans hscheduled hlater
  have htolerancePos : (0 : Q') < tolerance := by
    unfold tolerance
    exact CReal.InnerRegularity.scaleTolerance_pos _ _
      (Q'.invSucc_pos index)
  have hincrement :
      slabParametricKCutoffIncrement
          w (centralPhysicalTargetShellCutoff w half tolerance)
            later (centralExtent half) ≤ tolerance := by
    unfold centralPhysicalTargetShellCutoff
    exact slabPhysicalNomeCutoffIncrement_le_tolerance
      hw0 hw1 (centralExtent half) htolerancePos hscheduleLater
  have hshellTolerance :
      centralPhysicalRowMarginalOutsideBase
          w (Q'.le_of_lt hw0) later half stage ≤ tolerance :=
    Q'.le_trans' _ _ _ hshell
      (Q'.le_trans' _ _ _ hincrementMono hincrement)
  have hscaled :
      centralPhysicalRowMarginalOutsideBase
          w (Q'.le_of_lt hw0) later half stage * envelope ≤
        tolerance * envelope :=
    Q'.mul_le_mul_of_nonneg_right _ _ envelope hshellTolerance
      (centralPhysicalVacuumSectorPresentationRecodingSqEnvelope_nonnegative
        presentation)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Constructive.Q'.eqv_of_eq (Q'.zero_add' _))) ?_
  refine Q'.le_trans' _ _ _ hscaled ?_
  refine Q'.le_trans' _ (envelope * tolerance) _
    (Q'.le_of_eqv (Q'.mul_comm_eqv tolerance envelope)) ?_
  exact centralPhysicalVacuumSectorPresentationEnvelope_mul_shellTolerance_le
    presentation (Q'.invSucc index) (Q'.invSucc_pos index)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell.centralPhysicalFiniteDistSq_le_core_add_scaled_shell
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell.centralPhysicalVacuumSectorRecoding_sub_sq_le_envelope
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell.centralPhysicalVacuumSectorRecoding_core_sub_sq_le_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell.centralPhysicalVacuumSectorRecoding_distSq_le_invSucc
