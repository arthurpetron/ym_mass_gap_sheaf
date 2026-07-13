/-
# Sharp occurrence fuel for traced final states

`occurrenceChainCodes Gamma fuel` contains chains with at most `fuel`
steps, hence walks with at most `fuel + 1` vertices.  The older sufficient
constructor used the stricter bound `vertices.length ≤ fuel`.  This file
proves the exact bound and applies it to source-free traced final states.

It also records exact trace length accounting: every reversible splice frame
adds two vertices and removes one unit of residual potential.  Thus final
carrier membership is reduced to the actual enumerator capacity, without the
previous off-by-one loss.  No weighted domination is claimed here.
-/

import YMGap.Continuum.XiExceptionalTraceRightInvariant
import YMGap.Continuum.XiExceptionalUnequalEarFuelFence

namespace YMGap.Continuum.XiExceptionalTraceFuelSharp

open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictSplice
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalTracedNormalization
open YMGap.Continuum.XiExceptionalUnequalEarFuelFence
open YMGap.Continuum.XiExceptionalTraceRightInvariant
open YMGap.Continuum.XiExceptionalTracedUnsafeAdapter

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Exact completeness of the finite chain enumerator -/

theorem occurrenceChainCodeOfWalk_mem_of_steps
    (Gamma : List (Polymer L)) (background : OccBitVec Gamma.length) :
    ∀ {edge : Nat → Nat → Bool} {i j : Nat}
      (walk : CWalk edge i j) (fuel : Nat),
      chainSteps (occurrenceChainCodeOfWalk walk background) ≤ fuel →
      (∀ k, k ∈ walk.vertices → k < Gamma.length) →
      occurrenceChainCodeOfWalk walk background ∈
        occurrenceChainCodes Gamma fuel
  | _, _, _, .single _, fuel, _, _ =>
      terminal_occurrence_code_mem Gamma background fuel
  | _, _, _, .cons _ rest, 0, hsteps, _ => by
      simp only [occurrenceChainCodeOfWalk, chainSteps] at hsteps
      omega
  | _, _, _, .cons _ rest, fuel + 1, hsteps, hbounds => by
      unfold occurrenceChainCodeOfWalk occurrenceChainCodes
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      have hnext : rest.start < Gamma.length :=
        hbounds rest.start
          (List.mem_cons_of_mem _ (CWalk.start_mem_vertices rest))
      refine ⟨rest.start, occurrenceIndices_complete hnext, ?_⟩
      apply List.mem_map.mpr
      refine ⟨occurrenceChainCodeOfWalk rest background, ?_, rfl⟩
      apply occurrenceChainCodeOfWalk_mem_of_steps Gamma background rest fuel
      · simp only [occurrenceChainCodeOfWalk, chainSteps] at hsteps
        omega
      · intro k hk
        exact hbounds k (List.mem_cons_of_mem _ hk)

theorem occurrenceChainCodeOfWalk_mem_iff_steps
    (Gamma : List (Polymer L)) (background : OccBitVec Gamma.length)
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (fuel : Nat)
    (hbounds : ∀ k, k ∈ walk.vertices → k < Gamma.length) :
    occurrenceChainCodeOfWalk walk background ∈
        occurrenceChainCodes Gamma fuel ↔
      chainSteps (occurrenceChainCodeOfWalk walk background) ≤ fuel := by
  constructor
  · exact chainSteps_le_fuel_of_mem Gamma fuel _
  · intro hsteps
    exact occurrenceChainCodeOfWalk_mem_of_steps Gamma background walk fuel
      hsteps hbounds

theorem occurrenceChainCodeOfWalk_mem_sharp
    (Gamma : List (Polymer L)) (background : OccBitVec Gamma.length)
    {edge : Nat → Nat → Bool} {i j : Nat}
    (walk : CWalk edge i j) (fuel : Nat)
    (hlength : walk.vertices.length ≤ fuel + 1)
    (hbounds : ∀ k, k ∈ walk.vertices → k < Gamma.length) :
    occurrenceChainCodeOfWalk walk background ∈
      occurrenceChainCodes Gamma fuel := by
  apply occurrenceChainCodeOfWalk_mem_of_steps Gamma background walk fuel
  · have hexact := occurrenceChainCodeOfWalk_steps walk background
    omega
  · exact hbounds

/-! ## Vertex bounds are preserved by endpoint detours -/

theorem cwalk_append_vertices_property {alpha : Type}
    {edge : alpha → alpha → Bool} (P : alpha → Prop) :
    ∀ {x y z : alpha} (first : CWalk edge x y)
      (second : CWalk edge y z),
      (∀ k, k ∈ first.vertices → P k) →
      (∀ k, k ∈ second.vertices → P k) →
      ∀ k, k ∈ (first.append second).vertices → P k
  | _, _, _, .single _, second, _, hsecond, k, hk => hsecond k hk
  | _, _, _, .cons _ rest, second, hfirst, hsecond, k, hk => by
      rcases List.mem_cons.mp hk with hhead | htail
      · exact hfirst k (List.mem_cons.mpr (Or.inl hhead))
      · apply cwalk_append_vertices_property P rest second
        · intro a ha
          exact hfirst a (List.mem_cons_of_mem _ ha)
        · exact hsecond
        · exact htail

theorem cwalk_mem_vertices_append_left {alpha : Type}
    {edge : alpha → alpha → Bool} :
    ∀ {x y z : alpha} (first : CWalk edge x y)
      (second : CWalk edge y z) {k : alpha},
      k ∈ first.vertices → k ∈ (first.append second).vertices
  | _, _, _, .single _, second, k, hk => by
      have hkx : k = second.start := by
        simpa only [CWalk.vertices, List.mem_singleton, CWalk.start_eq] using hk
      rw [hkx]
      exact CWalk.start_mem_vertices second
  | _, _, _, .cons _ rest, second, k, hk => by
      rcases List.mem_cons.mp hk with hhead | htail
      · exact List.mem_cons.mpr (Or.inl hhead)
      · exact List.mem_cons_of_mem _
          (cwalk_mem_vertices_append_left rest second htail)

theorem cwalk_mem_vertices_append_right {alpha : Type}
    {edge : alpha → alpha → Bool} :
    ∀ {x y z : alpha} (first : CWalk edge x y)
      (second : CWalk edge y z) {k : alpha},
      k ∈ second.vertices → k ∈ (first.append second).vertices
  | _, _, _, .single _, _, _, hk => hk
  | _, _, _, .cons _ rest, second, _, hk =>
      List.mem_cons_of_mem _
        (cwalk_mem_vertices_append_right rest second hk)

theorem endpointDetour_vertices_property {alpha : Type}
    {edge : alpha → alpha → Bool} (P : alpha → Prop)
    {x pivot y : alpha} (pre : CWalk edge x pivot)
    (suf : CWalk edge pivot y) (detour : alpha)
    (hout : edge pivot detour = true) (hin : edge detour pivot = true)
    (hpre : ∀ k, k ∈ pre.vertices → P k)
    (hsuf : ∀ k, k ∈ suf.vertices → P k)
    (hdetour : P detour) :
    ∀ k, k ∈
      (YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk.endpointDetour
        pre suf detour hout hin).vertices → P k := by
  intro k hk
  unfold YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk.endpointDetour
    at hk
  apply cwalk_append_vertices_property P pre
    (.cons hout (.cons hin suf)) hpre _ k hk
  intro a ha
  rcases List.mem_cons.mp ha with hpivot | htail
  · rw [hpivot]
    exact hsuf pivot (CWalk.start_mem_vertices suf)
  · rcases List.mem_cons.mp htail with hselected | hsufmem
    · rw [hselected]
      exact hdetour
    · exact hsuf a hsufmem

theorem firstConflictEndpointDetour_vertices_property
    (Gamma : List (Polymer L)) {start finish : Nat}
    (walk : CWalk (incAtDistinct Gamma) start finish) (u : Nat)
    (hunsafe : pathSafe Gamma walk.vertices u = false)
    (P : Nat → Prop)
    (hwalk : ∀ k, k ∈ walk.vertices → P k) (hu : P u) :
    ∀ k, k ∈
      (YMGap.Continuum.XiExceptionalFirstConflictSplice.CWalk.firstConflictEndpointDetour
        Gamma walk u hunsafe).vertices → P k := by
  let split :=
    YMGap.Continuum.XiExceptionalFirstConflictSplice.CWalk.firstConflictFactorization
      Gamma walk u hunsafe
  let j := firstConflictIndex Gamma walk.vertices u
  let hout : incAtDistinct Gamma j u = true :=
    incAtDistinct_of_symConflict_true Gamma j u
      (firstConflictIndex_mem_and_conflict Gamma walk.vertices u hunsafe).2
  let hin : incAtDistinct Gamma u j = true := by
    rw [← incAtDistinct_symm Gamma]
    exact hout
  change ∀ k, k ∈
    (YMGap.Continuum.XiExceptionalFirstConflictDetour.CWalk.endpointDetour
      split.pre split.suf u hout hin).vertices → P k
  apply endpointDetour_vertices_property P split.pre split.suf u hout hin
  · intro k hk
    apply hwalk k
    rw [← split.rejoin]
    exact cwalk_mem_vertices_append_left split.pre split.suf hk
  · intro k hk
    apply hwalk k
    rw [← split.rejoin]
    exact cwalk_mem_vertices_append_right split.pre split.suf hk
  · exact hu

theorem spliceState_step_vertices_bound
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false)
    (hbounds : ∀ k, k ∈ state.walk.vertices → k < Gamma.length) :
    ∀ k, k ∈ (state.step hunsafe).walk.vertices → k < Gamma.length := by
  apply firstConflictEndpointDetour_vertices_property Gamma state.walk
    state.selectedUnsafe
    (state.selectedUnsafe_spec hunsafe).2.2
    (fun k => k < Gamma.length) hbounds
  exact (state.selectedUnsafe_spec hunsafe).1

theorem tracedExhaust_final_vertices_bound
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hbounds : ∀ k, k ∈ state.walk.vertices → k < Gamma.length) :
    ∀ k, k ∈ (tracedExhaust state).final.walk.vertices →
      k < Gamma.length := by
  rw [tracedExhaust]
  split
  next hunsafe =>
    exact tracedExhaust_final_vertices_bound (state.step hunsafe)
      (spliceState_step_vertices_bound state hunsafe hbounds)
  next _ => exact hbounds
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

/-! ## Exact trace length and potential accounting -/

theorem tracedExhaust_frames_add_final_potential
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (tracedExhaust state).frames.length +
        (tracedExhaust state).final.potential =
      state.potential := by
  rw [tracedExhaust]
  split
  next hunsafe =>
    have ih := tracedExhaust_frames_add_final_potential
      (state.step hunsafe)
    have hpotential := state.step_potential_add_one hunsafe
    simp only [List.length_cons]
    omega
  next _ =>
    simp only [List.length_nil, Nat.zero_add]
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

theorem tracedExhaust_final_walk_length
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (tracedExhaust state).final.walk.vertices.length =
      state.walk.vertices.length + 2 * (tracedExhaust state).frames.length := by
  rw [tracedExhaust]
  split
  next hunsafe =>
    have ih := tracedExhaust_final_walk_length (state.step hunsafe)
    have hstep := state.step_walk_length hunsafe
    simp only [List.length_cons]
    omega
  next _ =>
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

theorem tracedExhaust_size_potential_conserved
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (tracedExhaust state).final.walk.vertices.length +
        2 * (tracedExhaust state).final.potential =
      state.walk.vertices.length + 2 * state.potential := by
  have hframes := tracedExhaust_frames_add_final_potential state
  have hlength := tracedExhaust_final_walk_length state
  omega

/-! ## A source-free final-state carrier and its sharp capacity condition -/

def traceFinalCarrier
    {Gamma : List (Polymer L)} (code : EntryLeftTraceRightCode Gamma) :
    OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := code.traced.start
        chain := occurrenceChainCodeOfWalk code.traced.trace.final.walk
          code.traced.trace.final.residual }
    external := code.rightResidual }

theorem traceFinalCarrier_mem
    {Gamma : List (Polymer L)} (code : EntryLeftTraceRightCode Gamma)
    (hstart : code.traced.start < Gamma.length)
    (hbounds : ∀ k, k ∈ code.traced.trace.final.walk.vertices →
      k < Gamma.length)
    (hcapacity : code.traced.trace.final.walk.vertices.length ≤
      Gamma.length + 1) :
    traceFinalCarrier code ∈ occurrenceCarrierXiCodes Gamma := by
  unfold occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨code.rightResidual, bitVectors_complete code.rightResidual, ?_⟩
  apply List.mem_map.mpr
  refine ⟨(traceFinalCarrier code).carrier, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨code.traced.start, occurrenceIndices_complete hstart, ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk code.traced.trace.final.walk
    code.traced.trace.final.residual, ?_, rfl⟩
  exact occurrenceChainCodeOfWalk_mem_sharp Gamma
    code.traced.trace.final.residual code.traced.trace.final.walk
    Gamma.length hcapacity hbounds

theorem traceFinalCarrier_mem_of_initial_budget
    {Gamma : List (Polymer L)} (code : EntryLeftTraceRightCode Gamma)
    (hcanonical : code.traced.trace =
      tracedExhaust code.traced.trace.decodeInitial)
    (hstart : code.traced.start < Gamma.length)
    (hbounds : ∀ k, k ∈ code.traced.trace.final.walk.vertices →
      k < Gamma.length)
    (hbudget : code.traced.trace.decodeInitial.walk.vertices.length +
        2 * code.traced.trace.decodeInitial.potential ≤ Gamma.length + 1) :
    traceFinalCarrier code ∈ occurrenceCarrierXiCodes Gamma := by
  apply traceFinalCarrier_mem code hstart hbounds
  have hconserved := tracedExhaust_size_potential_conserved
    code.traced.trace.decodeInitial
  rw [← hcanonical] at hconserved
  omega

/-! ## Entry traces satisfy the structural side conditions -/

theorem entryLeftSpliceState_vertices_bound
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    ∀ k, k ∈ (entryLeftSpliceState Gamma qP b1 b2 entry).walk.vertices →
      k < Gamma.length := by
  intro k hk
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  have hseed : path.seed < Gamma.length :=
    (forwardSeed_parts Gamma.length (bitMask entry.1.1)
      (bitMask entry.1.2) (predAt Gamma b2) path.seed_true).1
  have hpath : k ∈ path.indexWalk.vertices := by
    unfold entryLeftSpliceState at hk
    simp only [id_eq] at hk
    rw [conflictWalkOfDisagreement_vertices] at hk
    exact hk
  exact walk_vertices_lt_of_seed Gamma.length (incAtDistinct Gamma)
    (bitMask entry.1.1) (bitMask entry.1.2) path.indexWalk hseed k hpath

theorem entryLeftTraceRight_trace_canonical
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryLeftTraceRightCode Gamma qP b1 b2 entry).traced.trace =
      tracedExhaust
        (entryLeftTraceRightCode Gamma qP b1 b2 entry).traced.trace.decodeInitial := by
  unfold entryLeftTraceRightCode entryLeftTraceCode
  dsimp only
  rw [tracedExhaust_decodeInitial]

theorem entryLeftTraceRight_start_lt
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryLeftTraceRightCode Gamma qP b1 b2 entry).traced.start <
      Gamma.length := by
  unfold entryLeftTraceRightCode entryLeftTraceCode
  dsimp only
  exact (exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1
    entry.2).marked_lt

theorem entryLeftTraceRight_final_vertices_bound
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    ∀ k, k ∈
      (entryLeftTraceRightCode Gamma qP b1 b2 entry).traced.trace.final.walk.vertices →
      k < Gamma.length := by
  unfold entryLeftTraceRightCode entryLeftTraceCode
  dsimp only
  exact tracedExhaust_final_vertices_bound
    (entryLeftSpliceState Gamma qP b1 b2 entry)
    (entryLeftSpliceState_vertices_bound Gamma qP b1 b2 entry)

theorem entryTraceFinalCarrier_mem_of_budget
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (hbudget :
      (entryLeftSpliceState Gamma qP b1 b2 entry).walk.vertices.length +
          2 * (entryLeftSpliceState Gamma qP b1 b2 entry).potential ≤
        Gamma.length + 1) :
    traceFinalCarrier (entryLeftTraceRightCode Gamma qP b1 b2 entry) ∈
      occurrenceCarrierXiCodes Gamma := by
  apply traceFinalCarrier_mem_of_initial_budget
    (entryLeftTraceRightCode Gamma qP b1 b2 entry)
    (entryLeftTraceRight_trace_canonical Gamma qP b1 b2 entry)
    (entryLeftTraceRight_start_lt Gamma qP b1 b2 entry)
    (entryLeftTraceRight_final_vertices_bound Gamma qP b1 b2 entry)
  unfold entryLeftTraceRightCode entryLeftTraceCode
  dsimp only
  rw [tracedExhaust_decodeInitial]
  exact hbudget

#print axioms occurrenceChainCodeOfWalk_mem_of_steps
#print axioms occurrenceChainCodeOfWalk_mem_iff_steps
#print axioms occurrenceChainCodeOfWalk_mem_sharp
#print axioms cwalk_append_vertices_property
#print axioms cwalk_mem_vertices_append_left
#print axioms cwalk_mem_vertices_append_right
#print axioms endpointDetour_vertices_property
#print axioms firstConflictEndpointDetour_vertices_property
#print axioms spliceState_step_vertices_bound
#print axioms tracedExhaust_final_vertices_bound
#print axioms tracedExhaust_frames_add_final_potential
#print axioms tracedExhaust_final_walk_length
#print axioms tracedExhaust_size_potential_conserved
#print axioms traceFinalCarrier_mem
#print axioms traceFinalCarrier_mem_of_initial_budget
#print axioms entryLeftSpliceState_vertices_bound
#print axioms entryLeftTraceRight_trace_canonical
#print axioms entryLeftTraceRight_start_lt
#print axioms entryLeftTraceRight_final_vertices_bound
#print axioms entryTraceFinalCarrier_mem_of_budget

end YMGap.Continuum.XiExceptionalTraceFuelSharp
