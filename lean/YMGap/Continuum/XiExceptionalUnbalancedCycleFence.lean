/-
# Genuine unbalanced two-arm residual fence

An eight-occurrence cycle has two odd marked-to-bad arcs with one and two
interior pairs.  The canonical simple path is necessarily one of those arcs;
the complementary arc therefore remains as a genuine mixed residual in both
cases.  All three old classifiers fail.  With the reject-all fourth allocator
the entry is an actual member of the four-branch residual.

The automatically exposed two-arm fuel is unbalanced (`1 != 2`).  The long
pair-bounced arm has ten vertices while the unchanged eight-occurrence target
has sharp capacity nine, so that carrier is genuinely absent.  This banks a
source-level obstruction to extracting a balanced repair from the previous
cross-conflict invariant alone.  Moreover, at exact weight one the source has
weight `65536`, while the complete target-valid part of the natural block is
the duplicate-free short singleton of weight `4096`; deleting the overflowing
arm therefore does not rescue the payment.
-/

import YMGap.Continuum.XiExceptionalFourthMixedRepair
import YMGap.Continuum.XiExceptionalEarOccurrenceCarrier
import YMGap.Continuum.XiExceptionalFirstConflictDetour

namespace YMGap.Continuum.XiExceptionalUnbalancedCycleFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalPathSafeInjection
open YMGap.Continuum.XiExceptionalRoutedExternalSplit
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalFullSourceBound
open YMGap.Continuum.XiExceptionalThreeBranchClassificationFence
open YMGap.Continuum.XiExceptionalFourthMixedRepair
open YMGap.Continuum.XiExceptionalEarPairBounce
open YMGap.Continuum.XiExceptionalEarOccurrenceCarrier
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalBlockCutFuel

abbrev TL := toyLattice
instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

def e0 : TL.Plaquette := (0, 0)
def e1 : TL.Plaquette := (1, 0)
def e2 : TL.Plaquette := (2, 0)
def e3 : TL.Plaquette := (3, 0)
def e4 : TL.Plaquette := (4, 0)
def e5 : TL.Plaquette := (5, 0)
def e6 : TL.Plaquette := (6, 0)
def e7 : TL.Plaquette := (7, 0)

def V0 : Polymer TL := [e7, e0]
def V1 : Polymer TL := [e0, e1]
def V2 : Polymer TL := [e1, e2]
def V3 : Polymer TL := [e2, e3]
def V4 : Polymer TL := [e3, e4]
def V5 : Polymer TL := [e4, e5]
def V6 : Polymer TL := [e5, e6]
def V7 : Polymer TL := [e6, e7]

def Gamma : List (Polymer TL) := [V0, V1, V2, V3, V4, V5, V6, V7]
def qAll : Polymer TL → Bool := fun _ => true
def markV0 : Polymer TL → Bool := fun X => decide (X = V0)
def badV3 : Polymer TL → Bool := fun X => decide (X = V3)

def bits8 (x0 x1 x2 x3 x4 x5 x6 x7 : Bool) : OccBitVec 8 :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3
    (.cons x4 (.cons x5 (.cons x6 (.cons x7 .nil)))))))

def pair : MaskPair Gamma.length :=
  (bits8 false true false true false true false true,
    bits8 true false true false true false true false)

theorem pair_mem :
    pair ∈ exceptionalSourceCodes Gamma qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

def entry : ExceptionalSourceEntry Gamma qAll markV0 badV3 :=
  ⟨pair, pair_mem⟩

theorem entry_mem_full :
    entry ∈ fullExceptionalSource Gamma qAll markV0 badV3 :=
  List.mem_attach _ entry

abbrev cycleEdge := disagreementEdge Gamma.length
  (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem neighbor_zero {j : Nat}
    (h : cycleEdge 0 j = true) : j = 1 ∨ j = 7 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj8 : j < 8 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  omega

private theorem neighbor_one {j : Nat}
    (h : cycleEdge 1 j = true) : j = 0 ∨ j = 2 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj8 : j < 8 := by simpa [Gamma] using hj
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  omega

private theorem neighbor_two {j : Nat}
    (h : cycleEdge 2 j = true) : j = 1 ∨ j = 3 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj8 : j < 8 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  omega

private theorem neighbor_seven {j : Nat}
    (h : cycleEdge 7 j = true) : j = 0 ∨ j = 6 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj8 : j < 8 := by simpa [Gamma] using hj
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  omega

private theorem neighbor_six {j : Nat}
    (h : cycleEdge 6 j = true) : j = 5 ∨ j = 7 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj8 : j < 8 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  omega

private theorem neighbor_five {j : Nat}
    (h : cycleEdge 5 j = true) : j = 4 ∨ j = 6 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj8 : j < 8 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h3 : j ≠ 3 := by intro e; subst j; cases h
  have h5 : j ≠ 5 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  omega

private theorem neighbor_four {j : Nat}
    (h : cycleEdge 4 j = true) : j = 3 ∨ j = 5 := by
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pair.1) (bitMask pair.2) h).2
  have hj8 : j < 8 := by simpa [Gamma] using hj
  have h0 : j ≠ 0 := by intro e; subst j; cases h
  have h1 : j ≠ 1 := by intro e; subst j; cases h
  have h2 : j ≠ 2 := by intro e; subst j; cases h
  have h4 : j ≠ 4 := by intro e; subst j; cases h
  have h6 : j ≠ 6 := by intro e; subst j; cases h
  have h7 : j ≠ 7 := by intro e; subst j; cases h
  omega

private theorem endpoint_walk_single
    (walk : CWalk cycleEdge 3 3) (hnodup : walk.vertices.Nodup) :
    walk.vertices = [3] := by
  cases walk with
  | single _ => rfl
  | cons _ rest =>
      have hp := List.nodup_cons.mp hnodup
      exact absurd (CWalk.end_mem_vertices rest) hp.1

private theorem cycle_walk_arcs
    {start finish : Nat} (walk : CWalk cycleEdge start finish)
    (hstart : start = 0) (hfinish : finish = 3)
    (hnodup : walk.vertices.Nodup) :
    walk.vertices = [0, 1, 2, 3] ∨
      walk.vertices = [0, 7, 6, 5, 4, 3] := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnd0 := List.nodup_cons.mp hnodup
      rcases neighbor_zero hedge with hnext | hnext
      · subst next
        cases rest with
        | @cons _ next2 _ hedge2 rest2 =>
            have hnd1 := List.nodup_cons.mp hnd0.2
            rcases neighbor_one hedge2 with hnext2 | hnext2
            · subst next2
              exact absurd
                (List.mem_cons_of_mem 1 (CWalk.start_mem_vertices rest2))
                hnd0.1
            · subst next2
              cases rest2 with
              | @cons _ next3 _ hedge3 rest3 =>
                  have hnd2 := List.nodup_cons.mp hnd1.2
                  rcases neighbor_two hedge3 with hnext3 | hnext3
                  · subst next3
                    exact absurd
                      (List.mem_cons_of_mem 2
                        (CWalk.start_mem_vertices rest3)) hnd1.1
                  · subst next3
                    left
                    simp only [CWalk.vertices]
                    rw [endpoint_walk_single rest3 hnd2.2]
      · subst next
        cases rest with
        | @cons _ next2 _ hedge2 rest2 =>
            have hnd7 := List.nodup_cons.mp hnd0.2
            rcases neighbor_seven hedge2 with hnext2 | hnext2
            · subst next2
              exact absurd
                (List.mem_cons_of_mem 7 (CWalk.start_mem_vertices rest2))
                hnd0.1
            · subst next2
              cases rest2 with
              | @cons _ next3 _ hedge3 rest3 =>
                  have hnd6 := List.nodup_cons.mp hnd7.2
                  rcases neighbor_six hedge3 with hnext3 | hnext3
                  · subst next3
                    cases rest3 with
                    | @cons _ next4 _ hedge4 rest4 =>
                        have hnd5 := List.nodup_cons.mp hnd6.2
                        rcases neighbor_five hedge4 with hnext4 | hnext4
                        · subst next4
                          cases rest4 with
                          | @cons _ next5 _ hedge5 rest5 =>
                              have hnd4 := List.nodup_cons.mp hnd5.2
                              rcases neighbor_four hedge5 with
                                hnext5 | hnext5
                              · subst next5
                                right
                                simp only [CWalk.vertices]
                                rw [endpoint_walk_single rest5 hnd4.2]
                              · subst next5
                                exact absurd
                                  (List.mem_cons_of_mem 4
                                    (CWalk.start_mem_vertices rest5))
                                  hnd5.1
                        · subst next4
                          exact absurd
                            (List.mem_cons_of_mem 5
                              (CWalk.start_mem_vertices rest4)) hnd6.1
                  · subst next3
                    exact absurd
                      (List.mem_cons_of_mem 6
                        (CWalk.start_mem_vertices rest3)) hnd7.1

private theorem badV3_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : badV3 (polyAt Gamma i) = true) : i = 3 := by
  have hi8 : i < 8 := by simpa [Gamma] using hi
  have h0 : i ≠ 0 := by intro e; subst i; cases hbad
  have h1 : i ≠ 1 := by intro e; subst i; cases hbad
  have h2 : i ≠ 2 := by intro e; subst i; cases hbad
  have h4 : i ≠ 4 := by intro e; subst i; cases hbad
  have h5 : i ≠ 5 := by intro e; subst i; cases hbad
  have h6 : i ≠ 6 := by intro e; subst i; cases hbad
  have h7 : i ≠ 7 := by intro e; subst i; cases hbad
  omega

theorem source_path_is_unequal_arc :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3
      pair pair_mem
    let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
    path.indexWalk.vertices = [0, 1, 2, 3] ∨
      path.indexWalk.vertices = [0, 7, 6, 5, 4, 3] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markV0 badV3
    pair pair_mem
  let path := sourceExceptionalPath Gamma qAll markV0 badV3 pair facts
  have hstart : exceptionalMarkedIndex Gamma markV0 badV3 pair = 0 := by rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pair.1) (bitMask pair.2) (predAt Gamma badV3) path.seed_true
  have hfinish : path.seed = 3 := badV3_polyAt_index hp.1 hp.2.2.2
  exact cycle_walk_arcs path.indexWalk hstart hfinish path.index_nodup

theorem routed_path_safe_fails :
    routedExternalCompatibleB Gamma qAll markV0 badV3 entry = false := by
  unfold routedExternalCompatibleB entryRoutedExternal
    routedLeftResidual routedRightResidual exceptionalPathSafe entry
  dsimp only
  rcases source_path_is_unequal_arc with h | h
  · rw [h]
    decide
  · rw [h]
    decide

theorem component_right_safeB_fails :
    componentRightSafeB Gamma qAll markV0 badV3 entry = false := by
  unfold componentRightSafeB routedResidualPathSafeB routedRightResidual
    exceptionalPathSafe entry
  dsimp only
  rcases source_path_is_unequal_arc with h | h
  · rw [h]
    decide
  · rw [h]
    decide

theorem component_left_safeB_fails :
    componentLeftSafeB Gamma qAll markV0 badV3 entry = false := by
  unfold componentLeftSafeB routedResidualPathSafeB routedLeftResidual
    exceptionalPathSafe entry
  dsimp only
  rcases source_path_is_unequal_arc with h | h
  · rw [h]
    decide
  · rw [h]
    decide

def rejectAllAllocator
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    [DecidableEq L.Plaquette] : MixedRepairAllocator Gamma qP b1 b2 where
  test := fun _ => false
  block := fun _ => []
  block_nodup := by intro _ _; exact List.nodup_nil
  block_mem := by intro _ _ _ h; cases h
  blocks_disjoint := by intro _ h; cases h
  source_le_block := by intro _ _ _ _ h; cases h

def allocator : MixedRepairAllocator Gamma qAll markV0 badV3 :=
  rejectAllAllocator Gamma qAll markV0 badV3

theorem entry_mem_threeBranchResidual :
    entry ∈ threeBranchResidualSource Gamma qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [component_left_safeB_fails]⟩
  apply List.mem_filter.mpr
  refine ⟨?_, by simp [component_right_safeB_fails]⟩
  apply List.mem_filter.mpr
  exact ⟨entry_mem_full, by simp [routed_path_safe_fails]⟩

theorem entry_mem_fourBranchResidual :
    entry ∈ fourBranchResidualSource allocator := by
  apply List.mem_filter.mpr
  exact ⟨entry_mem_threeBranchResidual, rfl⟩

theorem residual_invariant :
    ThreeBranchResidualInvariant Gamma qAll markV0 badV3 entry :=
  threeBranchResidualSource_invariant Gamma qAll markV0 badV3 entry
    entry_mem_threeBranchResidual

/-! ## Automatically exposed unequal two-arm fuel -/

def shortArc : PairedPath (incAtDistinct Gamma) 0 3 :=
  .pair (x := 0) (y := 1) (z := 2) (t := 3)
    (by rfl) (by rfl) (.last (by rfl))

def longArc : PairedPath (incAtDistinct Gamma) 0 3 :=
  .pair (x := 0) (y := 7) (z := 6) (t := 3)
    (by rfl) (by rfl)
    (.pair (x := 6) (y := 5) (z := 4) (t := 3)
      (by rfl) (by rfl) (.last (by rfl)))

def extractedTwoArmFuel : BlockCutFuel :=
  .leaf shortArc.pairCount longArc.pairCount

theorem extracted_pair_counts :
    shortArc.pairCount = 1 ∧ longArc.pairCount = 2 := by
  decide

theorem extracted_fuel_unbalanced :
    complementaryFuelBalancedB extractedTwoArmFuel = false := by
  rfl

private theorem cycleEdge_symm (i j : Nat)
    (h : incAtDistinct Gamma i j = true) :
    incAtDistinct Gamma j i = true := by
  rw [incAtDistinct_symm Gamma]
  exact h

def emptyBits : OccBitVec Gamma.length :=
  bits8 false false false false false false false false

def shortBounceCode : OccCarrierXiCodeAt Gamma :=
  pairedBounceCarrierCode Gamma shortArc cycleEdge_symm emptyBits emptyBits

def longBounceCode : OccCarrierXiCodeAt Gamma :=
  pairedBounceCarrierCode Gamma longArc cycleEdge_symm emptyBits emptyBits

theorem shortBounceCode_mem :
    shortBounceCode ∈ occurrenceCarrierXiCodes Gamma := by
  unfold shortBounceCode
  apply pairedBounceCarrierCode_mem Gamma shortArc cycleEdge_symm
    emptyBits emptyBits
  · decide
  · decide
  · intro k hk
    simp [shortArc, PairedPath.bounceWalk, CWalk.vertices, Gamma] at hk ⊢
    omega

theorem longArc_bounce_length :
    (longArc.bounceWalk cycleEdge_symm).vertices.length = 10 := by
  rw [PairedPath.bounceWalk_length cycleEdge_symm longArc]
  decide

/-- The selected long-arm square is absent from the unchanged target by the
sharp `N+1` capacity theorem. -/
theorem longBounceCode_not_mem :
    longBounceCode ∉ occurrenceCarrierXiCodes Gamma := by
  intro hmem
  unfold longBounceCode occurrenceCarrierXiCodes at hmem
  obtain ⟨external', _, hcarrierBlock⟩ := List.mem_flatMap.mp hmem
  obtain ⟨carrier', hcarrierMem, hcodeEq⟩ := List.mem_map.mp hcarrierBlock
  have hcarrierEq := congrArg OccCarrierXiCodeAt.carrier hcodeEq
  have hchainEq := congrArg OccCarrierCodeAt.chain hcarrierEq
  unfold pairedBounceCarrierCode at hchainEq
  unfold occurrenceCarrierCodes at hcarrierMem
  obtain ⟨start, _, hchainBlock⟩ := List.mem_flatMap.mp hcarrierMem
  obtain ⟨chain, hchainMem, hcarrierCodeEq⟩ := List.mem_map.mp hchainBlock
  have hlistedChainEq := congrArg OccCarrierCodeAt.chain hcarrierCodeEq
  change carrier'.chain =
    occurrenceChainCodeOfWalk (longArc.bounceWalk cycleEdge_symm) emptyBits
      at hchainEq
  change chain = carrier'.chain at hlistedChainEq
  apply
    YMGap.Continuum.XiExceptionalUnequalEarFuelFence.occurrenceChainCodeOfWalk_not_mem_of_overflow
      Gamma (longArc.bounceWalk cycleEdge_symm) emptyBits
  · rw [longArc_bounce_length]
    simp [Gamma]
  · rw [← hchainEq, ← hlistedChainEq]
    exact hchainMem

def naturalTwoArmBlock : List (OccCarrierXiCodeAt Gamma) :=
  [shortBounceCode, longBounceCode]

theorem naturalTwoArmBlock_not_sublist_target :
    ¬ ∀ code, code ∈ naturalTwoArmBlock →
      code ∈ occurrenceCarrierXiCodes Gamma := by
  intro hall
  exact longBounceCode_not_mem
    (hall longBounceCode (by simp [naturalTwoArmBlock]))

/-! ## Exact payment failure after deleting the overflowing arm -/

def labelOne : TL.Plaquette → Rep := fun _ => 1
def unitWeight : Q' := Q'.ofNat 1

/-- The only target-valid code in the natural two-arm block is the short
square.  This is a completeness statement inside that exact proposed block,
not merely an exhibited valid subblock. -/
theorem naturalTwoArm_target_members_iff (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈ naturalTwoArmBlock) :
    code ∈ occurrenceCarrierXiCodes Gamma ↔ code = shortBounceCode := by
  simp [naturalTwoArmBlock] at hcode
  rcases hcode with hshort | hlong
  · subst code
    exact ⟨fun _ => rfl, fun _ => shortBounceCode_mem⟩
  · subst code
    constructor
    · intro hmem
      exact False.elim (longBounceCode_not_mem hmem)
    · intro heq
      have hmem : longBounceCode ∈ occurrenceCarrierXiCodes Gamma := by
        rw [heq]
        exact shortBounceCode_mem
      exact False.elim (longBounceCode_not_mem hmem)

def targetValidNaturalBlock : List (OccCarrierXiCodeAt Gamma) :=
  [shortBounceCode]

theorem targetValidNaturalBlock_nodup : targetValidNaturalBlock.Nodup := by
  simp [targetValidNaturalBlock]

theorem targetValidNaturalBlock_mem (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈ targetValidNaturalBlock) :
    code ∈ occurrenceCarrierXiCodes Gamma := by
  simp [targetValidNaturalBlock] at hcode
  subst code
  exact shortBounceCode_mem

/-- At the exact nonnegative rational weight `w = 1` with constant label
one, the exceptional source weighs `65536`. -/
theorem source_weight_at_unit :
    occurrencePairWeight unitWeight qAll markV0 badV3 Gamma labelOne pair =
      Q'.ofNat 65536 := by
  decide

/-- The complete target-valid part of the natural two-arm block weighs only
`4096` at the same exact parameters. -/
theorem targetValidNaturalBlock_weight_at_unit :
    qListSum
        (occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3 Gamma
          labelOne)
        targetValidNaturalBlock = Q'.ofNat 4096 := by
  decide

/-- Consequently, deleting the overflowing long arm does not rescue the
unchanged-target payment: the remaining exact natural block is too light. -/
theorem targetValidNaturalBlock_payment_fails :
    ¬ (occurrencePairWeight unitWeight qAll markV0 badV3 Gamma labelOne pair ≤
      qListSum
        (occurrenceCarrierXiCodeWeight unitWeight qAll markV0 badV3 Gamma
          labelOne)
        targetValidNaturalBlock) := by
  decide

#print axioms pair_mem
#print axioms source_path_is_unequal_arc
#print axioms routed_path_safe_fails
#print axioms component_right_safeB_fails
#print axioms component_left_safeB_fails
#print axioms entry_mem_fourBranchResidual
#print axioms residual_invariant
#print axioms extracted_pair_counts
#print axioms extracted_fuel_unbalanced
#print axioms shortBounceCode_mem
#print axioms longArc_bounce_length
#print axioms longBounceCode_not_mem
#print axioms naturalTwoArmBlock_not_sublist_target
#print axioms naturalTwoArm_target_members_iff
#print axioms targetValidNaturalBlock_nodup
#print axioms targetValidNaturalBlock_mem
#print axioms source_weight_at_unit
#print axioms targetValidNaturalBlock_weight_at_unit
#print axioms targetValidNaturalBlock_payment_fails

end YMGap.Continuum.XiExceptionalUnbalancedCycleFence
