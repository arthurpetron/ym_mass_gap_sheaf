/-
# A concrete obstruction to one-target safe fibers

The compatibility-safe path carrier forgets off-path branches.  The three
polymer example below has two admissible exceptional sources with the same
safe carrier: the second source adds a right-side branch compatible with the
marked polymer but incompatible with the left seed.  At trivial labels every
polymer activity is one, so their common safe target has weight one while the
two source terms sum to two.
-/

import YMGap.Continuum.XiExceptionalSafeCarrierWeight

namespace YMGap.Continuum.XiExceptionalSafeFiberFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalSafeCarrierWeight

local infix:50 " ≈ " => Q'.eqv

private abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

private def p0 : TL.Plaquette := (0, 0)
private def p1 : TL.Plaquette := (1, 0)
private def A : Polymer TL := [p0]
private def B : Polymer TL := [p0, p1]
private def C : Polymer TL := [p1]
private def Gamma : List (Polymer TL) := [A, B, C]
private def qAll : Polymer TL → Bool := fun _ => true
private def markA : Polymer TL → Bool := fun X => decide (X = A)
private def badB : Polymer TL → Bool := fun X => decide (X = B)
private def label0 : TL.Plaquette → Rep := fun _ => 0

private def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))

private def pairBare : MaskPair Gamma.length :=
  (bits3 false true false, bits3 true false false)

private def pairBranch : MaskPair Gamma.length :=
  (bits3 false true false, bits3 true false true)

theorem pairBare_admissible :
    sourceAdmissible Gamma qAll markA badB pairBare = true := by
  rfl

theorem pairBranch_admissible :
    sourceAdmissible Gamma qAll markA badB pairBranch = true := by
  rfl

theorem pairBare_exceptional :
    exceptionalSourceCode Gamma markA badB pairBare = true := by
  rfl

theorem pairBranch_exceptional :
    exceptionalSourceCode Gamma markA badB pairBranch = true := by
  rfl

theorem pairBare_mem :
    pairBare ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairBare, ?_⟩
  exact (Bool.and_eq_true _ _).mpr
    ⟨pairBare_admissible, pairBare_exceptional⟩

theorem pairBranch_mem :
    pairBranch ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairBranch, ?_⟩
  exact (Bool.and_eq_true _ _).mpr
    ⟨pairBranch_admissible, pairBranch_exceptional⟩

private def entryBare : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨pairBare, pairBare_mem⟩

private def entryBranch : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨pairBranch, pairBranch_mem⟩

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem occurrenceCode_eq_direct_of_nodup
    {edge : Nat → Nat → Bool} {start finish : Nat}
    (walk : CWalk edge start finish)
    (hstart : start = 0) (hfinish : finish = 1)
    (hnodup : walk.vertices.Nodup)
    (hfirst : ∀ j, edge 0 j = true → j = 1)
    (background : OccBitVec n) :
    occurrenceChainCodeOfWalk walk background =
      OccChainCode.step 1 (OccChainCode.terminal background) := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnext : next = 1 := hfirst next hedge
      subst next
      cases rest with
      | single _ => rfl
      | @cons _ next' _ hedge' tail =>
          have hp := List.nodup_cons.mp hnodup
          have htailNodup := List.nodup_cons.mp hp.2
          exact absurd (CWalk.end_mem_vertices tail) htailNodup.1

private theorem occCarrier_ext {Gamma' : List (Polymer TL)}
    (u v : OccCarrierCodeAt Gamma')
    (hstart : u.start = v.start) (hchain : u.chain = v.chain) : u = v := by
  cases u with
  | mk us uc =>
      cases v with
      | mk vs vc =>
          dsimp only at hstart hchain
          cases hstart
          cases hchain
          rfl

private theorem occCarrierXi_ext {Gamma' : List (Polymer TL)}
    (u v : OccCarrierXiCodeAt Gamma')
    (hcarrier : u.carrier = v.carrier)
    (hexternal : u.external = v.external) : u = v := by
  cases u with
  | mk uc ue =>
      cases v with
      | mk vc ve =>
          dsimp only at hcarrier hexternal
          cases hcarrier
          cases hexternal
          rfl

private theorem badB_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : badB (XiExceptionalMaskCarrier.polyAt Gamma i) = true) :
    i = 1 := by
  have hi3 : i < 3 := by simpa [Gamma] using hi
  have hne0 : i ≠ 0 := by
    intro h
    subst i
    cases hbad
  have hne2 : i ≠ 2 := by
    intro h
    subst i
    cases hbad
  omega

private theorem bare_no_edge_00 :
    disagreementEdge Gamma.length (incAtDistinct Gamma)
      (bitMask pairBare.1) (bitMask pairBare.2) 0 0 = false := by
  rfl

private theorem bare_no_edge_02 :
    disagreementEdge Gamma.length (incAtDistinct Gamma)
      (bitMask pairBare.1) (bitMask pairBare.2) 0 2 = false := by
  rfl

private theorem branch_no_edge_00 :
    disagreementEdge Gamma.length (incAtDistinct Gamma)
      (bitMask pairBranch.1) (bitMask pairBranch.2) 0 0 = false := by
  rfl

private theorem branch_no_edge_02 :
    disagreementEdge Gamma.length (incAtDistinct Gamma)
      (bitMask pairBranch.1) (bitMask pairBranch.2) 0 2 = false := by
  rfl

set_option maxHeartbeats 1000000 in
theorem safe_start_collision :
    (exceptionalSafeCarrierCode Gamma qAll markA badB entryBare).carrier.start =
      (exceptionalSafeCarrierCode Gamma qAll markA badB entryBranch).carrier.start := by
  rfl

set_option maxHeartbeats 1000000 in
theorem safe_external_collision :
    (exceptionalSafeCarrierCode Gamma qAll markA badB entryBare).external =
      (exceptionalSafeCarrierCode Gamma qAll markA badB entryBranch).external := by
  rfl

set_option maxHeartbeats 1000000 in
theorem safe_chain_collision :
    (exceptionalSafeCarrierCode Gamma qAll markA badB entryBare).carrier.chain =
      (exceptionalSafeCarrierCode Gamma qAll markA badB entryBranch).carrier.chain := by
  let factsBare := exceptionalSourceFactsOfMem Gamma qAll markA badB
    pairBare pairBare_mem
  let factsBranch := exceptionalSourceFactsOfMem Gamma qAll markA badB
    pairBranch pairBranch_mem
  let pathBare := sourceExceptionalPath Gamma qAll markA badB
    pairBare factsBare
  let pathBranch := sourceExceptionalPath Gamma qAll markA badB
    pairBranch factsBranch
  let cutBare := forwardComponent Gamma.length (incAtDistinct Gamma)
    (bitMask pairBare.1) (bitMask pairBare.2)
    (XiExceptionalMaskCarrier.predAt Gamma badB)
  let cutBranch := forwardComponent Gamma.length (incAtDistinct Gamma)
    (bitMask pairBranch.1) (bitMask pairBranch.2)
    (XiExceptionalMaskCarrier.predAt Gamma badB)
  let bgBare := bitsFromMask Gamma.length
    (outsideMask cutBare (bitMask pairBare.1)) 0
  let bgBranch := bitsFromMask Gamma.length
    (outsideMask cutBranch (bitMask pairBranch.1)) 0
  have hmarkedBare : exceptionalMarkedIndex Gamma markA badB pairBare = 0 := by
    rfl
  have hmarkedBranch :
      exceptionalMarkedIndex Gamma markA badB pairBranch = 0 := by
    rfl
  have hseedBare : pathBare.seed = 1 := by
    have hp := forwardSeed_parts Gamma.length
      (bitMask pairBare.1) (bitMask pairBare.2)
      (XiExceptionalMaskCarrier.predAt Gamma badB) pathBare.seed_true
    exact badB_polyAt_index hp.1 hp.2.2.2
  have hseedBranch : pathBranch.seed = 1 := by
    have hp := forwardSeed_parts Gamma.length
      (bitMask pairBranch.1) (bitMask pairBranch.2)
      (XiExceptionalMaskCarrier.predAt Gamma badB) pathBranch.seed_true
    exact badB_polyAt_index hp.1 hp.2.2.2
  have hfirstBare : ∀ j,
      disagreementEdge Gamma.length (incAtDistinct Gamma)
        (bitMask pairBare.1) (bitMask pairBare.2) 0 j = true →
      j = 1 := by
    intro j hedge
    have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
      (bitMask pairBare.1) (bitMask pairBare.2) hedge).2
    have hj0 : j ≠ 0 := by
      intro h
      subst j
      rw [bare_no_edge_00] at hedge
      cases hedge
    have hj2 : j ≠ 2 := by
      intro h
      subst j
      rw [bare_no_edge_02] at hedge
      cases hedge
    have hj3 : j < 3 := by simpa [Gamma] using hj
    omega
  have hfirstBranch : ∀ j,
      disagreementEdge Gamma.length (incAtDistinct Gamma)
        (bitMask pairBranch.1) (bitMask pairBranch.2) 0 j = true →
      j = 1 := by
    intro j hedge
    have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
      (bitMask pairBranch.1) (bitMask pairBranch.2) hedge).2
    have hj0 : j ≠ 0 := by
      intro h
      subst j
      rw [branch_no_edge_00] at hedge
      cases hedge
    have hj2 : j ≠ 2 := by
      intro h
      subst j
      rw [branch_no_edge_02] at hedge
      cases hedge
    have hj3 : j < 3 := by simpa [Gamma] using hj
    omega
  have hbareDirect := occurrenceCode_eq_direct_of_nodup
    pathBare.indexWalk hmarkedBare hseedBare pathBare.index_nodup
    hfirstBare bgBare
  have hbranchDirect := occurrenceCode_eq_direct_of_nodup
    pathBranch.indexWalk hmarkedBranch hseedBranch pathBranch.index_nodup
    hfirstBranch bgBranch
  have hbackground : bgBare = bgBranch := by
    apply BitVec.ext
    intro i
    by_cases hi : i < Gamma.length
    · rw [bitsFromMask_at Gamma.length _ 0 i hi,
          bitsFromMask_at Gamma.length _ 0 i hi]
      have hi3 : i < 3 := by simpa [Gamma] using hi
      cases i with
      | zero => rfl
      | succ i =>
          cases i with
          | zero => rfl
          | succ i =>
              cases i with
              | zero => rfl
              | succ i => omega
    · have hge : Gamma.length ≤ i := by omega
      exact (bitVec_at_false_of_ge bgBare i hge).trans
        (bitVec_at_false_of_ge bgBranch i hge).symm
  have hcodes : occurrenceChainCodeOfWalk pathBare.indexWalk bgBare =
      occurrenceChainCodeOfWalk pathBranch.indexWalk bgBranch := by
    rw [hbareDirect, hbranchDirect, hbackground]
  unfold exceptionalSafeCarrierCode sourcePathCarrierXiCode
  dsimp only
  simpa only [pathBare, pathBranch, bgBare, bgBranch, factsBare,
    factsBranch, cutBare, cutBranch] using hcodes

set_option maxHeartbeats 1000000 in
theorem safe_code_collision :
    exceptionalSafeCarrierCode Gamma qAll markA badB entryBare =
      exceptionalSafeCarrierCode Gamma qAll markA badB entryBranch := by
  have hcarrier :
      (exceptionalSafeCarrierCode Gamma qAll markA badB entryBare).carrier =
        (exceptionalSafeCarrierCode Gamma qAll markA badB entryBranch).carrier := by
    exact occCarrier_ext _ _ safe_start_collision safe_chain_collision
  exact occCarrierXi_ext _ _ hcarrier safe_external_collision

private theorem activity_label0_one (X : Polymer TL) :
    activity (1 : Q') X label0 = 1 := by
  induction X with
  | nil => rfl
  | cons p X ih =>
      simp only [activity_cons, plaqWeight, label0, coeffW_zero, ih]
      rfl

private theorem familyActivity_label0_one
    (S : List (Polymer TL)) :
    familyActivity (1 : Q') S label0 = 1 := by
  induction S with
  | nil => rfl
  | cons X S ih =>
      simp only [familyActivity_cons, activity_label0_one, ih]
      rfl

private theorem walkActivity_label0_one {X Y : Polymer TL}
    (walk : CWalk (fun U V : Polymer TL => !(compatibleB U V)) X Y) :
    walk.activityWeight (1 : Q') label0 = 1 := by
  induction walk with
  | single X => exact activity_label0_one X
  | cons _ rest ih =>
      simp only [CWalk.activityWeight, activity_label0_one, ih]
      rfl

theorem pairBare_weight_one :
    occurrencePairWeight 1 qAll markA badB Gamma label0 pairBare = 1 := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    1 qAll markA badB Gamma label0 pairBare pairBare_mem]
  rw [familyActivity_label0_one, familyActivity_label0_one]
  rfl

theorem pairBranch_weight_one :
    occurrencePairWeight 1 qAll markA badB Gamma label0 pairBranch = 1 := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    1 qAll markA badB Gamma label0 pairBranch pairBranch_mem]
  rw [familyActivity_label0_one, familyActivity_label0_one]
  rfl

private def fenceSourceWeight
    (entry : ExceptionalSourceEntry Gamma qAll markA badB) : Q' :=
  occurrencePairWeight 1 qAll markA badB Gamma label0 entry.1

theorem two_source_sum_eqv_two :
    qListSum fenceSourceWeight [entryBare, entryBranch] ≈ (2 : Q') := by
  simp only [qListSum_cons, qListSum_nil, fenceSourceWeight,
    pairBare_weight_one, pairBranch_weight_one]
  rfl

theorem safe_target_weight_eqv_one :
    occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0
        (exceptionalSafeCarrierCode Gamma qAll markA badB entryBare) ≈
      (1 : Q') := by
  have h := exceptionalSafeCarrierCode_weight_eqv
    1 qAll markA badB Gamma label0 entryBare
  dsimp only at h
  refine Q'.eqv_trans _ _ _ h ?_
  rw [walkActivity_label0_one, familyActivity_label0_one,
    familyActivity_label0_one]
  exact Q'.eqv_refl _

theorem two_source_safe_bound_fails :
    ¬ (qListSum fenceSourceWeight [entryBare, entryBranch] ≤
      occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0
        (exceptionalSafeCarrierCode Gamma qAll markA badB entryBare)) := by
  intro hbound
  have htwo_le_target : (2 : Q') ≤
      occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0
        (exceptionalSafeCarrierCode Gamma qAll markA badB entryBare) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv two_source_sum_eqv_two) hbound
  have htwo_le_one : (2 : Q') ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ htwo_le_target
      (Q'.le_of_eqv safe_target_weight_eqv_one)
  exact (by decide : ¬ ((2 : Q') ≤ (1 : Q'))) htwo_le_one

theorem two_source_is_one_safe_fiber :
    [entryBare, entryBranch].filter (fun entry =>
      decide (exceptionalSafeCarrierCode Gamma qAll markA badB entry =
        exceptionalSafeCarrierCode Gamma qAll markA badB entryBare)) =
      [entryBare, entryBranch] := by
  simp only [List.filter_cons, safe_code_collision, decide_true,
    Bool.true_eq, if_true, List.filter_nil]

theorem complete_safe_fiber_bound_fails :
    ¬ (qListSum fenceSourceWeight
        ([entryBare, entryBranch].filter (fun entry =>
          decide (exceptionalSafeCarrierCode Gamma qAll markA badB entry =
            exceptionalSafeCarrierCode Gamma qAll markA badB entryBare))) ≤
      occurrenceCarrierXiCodeWeight 1 qAll markA badB Gamma label0
        (exceptionalSafeCarrierCode Gamma qAll markA badB entryBare)) := by
  rw [two_source_is_one_safe_fiber]
  exact two_source_safe_bound_fails

#print axioms pairBare_mem
#print axioms pairBranch_mem
#print axioms safe_code_collision
#print axioms pairBare_weight_one
#print axioms pairBranch_weight_one
#print axioms safe_target_weight_eqv_one
#print axioms complete_safe_fiber_bound_fails

end YMGap.Continuum.XiExceptionalSafeFiberFence
