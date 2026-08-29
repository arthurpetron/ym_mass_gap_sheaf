/-
# Canonical peeling contracts one complete terminal fiber

Complete paired-support peeling was previously summed over both its paid
trace mass and its terminal.  For physical repair the order of summation must
be reversed: fix one terminal, sum every reconstruction mass leading to that
terminal, and only then compare with a good receiver built from the terminal.

At the production anchor, the fixed-terminal/fixed-mass estimate contributes
`(16/25)^M`.  Connectedness forces `M` to be at least the marked-face
separation plus one.  Exact finite Fubini and the geometric tail therefore
give

```text
  weight { connected sources peeling to terminal }
    <= globalAnchorRate * terminalWeight.
```

There is no terminal count and no source-dependent prefactor.  This is the
weighted inverse-fiber estimate needed before an injective terminal-to-good-
source packing can be compiled into a physical repair.

Constructive contract: finite filters, deterministic fibers, and exact
rational geometric summation only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay

namespace YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingTerminalFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private def expandedEntryDecidableEq
    (D : SlabPhysicalData) : DecidableEq (SlabExpandedFineSourceEntry D) :=
  fun left right =>
    if hkey : left.key = right.key then
      isTrue (SlabExpandedFineSourceEntry.eq_of_key_eq hkey)
    else
      isFalse (fun heq => hkey
        (congrArg SlabExpandedFineSourceEntry.key heq))

local instance (D : SlabPhysicalData) :
    DecidableEq (SlabExpandedFineSourceEntry D) :=
  expandedEntryDecidableEq D

/-! ## 1. Terminal and paid-mass projections -/

/-- Deterministic terminal of the target-support canonical peeling. -/
def slabObservablePairTargetSupportCanonicalPeelingTerminal
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) :
    SlabAcceptedTwoReplicaState D :=
  (slabObservablePairTargetSupportCanonicalPeeling
    D rootFaceId targetFaceId htarget source.1 source.2).1

/-- Total physical multiplicity paid by the same deterministic peeling. -/
def slabObservablePairTargetSupportCanonicalPeelingMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) : Nat :=
  slabAcceptedPairedPeelTraceMass
    (slabObservablePairTargetSupportCanonicalPeeling
      D rootFaceId targetFaceId htarget source.1 source.2).2

theorem slabObservablePairTargetSupportCanonicalPeelingKey_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId) :
    slabObservablePairTargetSupportCanonicalPeelingKey
        D rootFaceId targetFaceId htarget source =
      (slabObservablePairTargetSupportCanonicalPeelingMass
          D rootFaceId targetFaceId htarget source,
        slabObservablePairTargetSupportCanonicalPeelingTerminal
          D rootFaceId targetFaceId htarget source) := by
  rfl

/-! ## 2. Exact finite summation helpers -/

private theorem range_nodup : ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count :=
              List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

private theorem listQSum_le_termwise
    {A : Type} (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_mul_right
    {A : Type} (value : A → Q') (factor : Q') : ∀ items : List A,
    listQSum (fun item => value item * factor) items ≈
      listQSum value items * factor
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv factor)
  | head :: tail => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl (value head * factor))
          (listQSum_mul_right value factor tail))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (value head) (listQSum value tail) factor))

/-! ## 3. One terminal, all reconstruction masses -/

/-- **Terminal-fiber Peierls estimate.**  The complete connected inverse
fiber of one canonical terminal is bounded by the already proved global
geometric rate times that terminal's exact accepted-state weight. -/
theorem slabObservablePairedSupportCanonicalPeeling_terminalFiberWeight_le
    (cutoff half rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈
      slabPhysicalFaceEdges (anchorSlabPhysicalData cutoff half).extent)
    (terminal : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff half)) :
    let D := anchorSlabPhysicalData cutoff half
    fiberWeight
        (slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairTargetSupportCanonicalPeelingTerminal
          D rootFaceId targetFaceId htarget)
        terminal ≤
      slabObservablePairedSupportGlobalAnchorRate
          D rootFaceId targetFaceId *
        slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
  let D := anchorSlabPhysicalData cutoff half
  let floor := linfDist
    (slabPlaquetteAt D.extent rootFaceId)
    (slabPlaquetteAt D.extent targetFaceId) + 1
  let sources :=
    slabObservablePairedSupportConnectedFourCellSourceEntries
      D rootFaceId targetFaceId
  let terminalCode :=
    slabObservablePairTargetSupportCanonicalPeelingTerminal
      D rootFaceId targetFaceId htarget
  let massCode :=
    slabObservablePairTargetSupportCanonicalPeelingMass
      D rootFaceId targetFaceId htarget
  let terminalSources :=
    sources.filter (fun source => decide (terminal = terminalCode source))
  let paidMasses := slabObservablePairedSupportPaidMasses D floor
  have hpaidNodup : paidMasses.Nodup := by
    unfold paidMasses slabObservablePairedSupportPaidMasses
    exact List.filter_sublist.nodup
      (range_nodup (2 * slabObservableRemovalMaxSize D + 1))
  have hmassMem : ∀ source, source ∈ terminalSources →
      massCode source ∈ paidMasses := by
    intro source hsource
    have hentry : source ∈ sources :=
      (List.mem_filter.mp hsource).1
    have hfloor : floor ≤ massCode source := by
      exact
        slabObservablePairTargetSupportCanonicalPeeling_traceMass_floor
          D rootFaceId targetFaceId htarget source.1 source.2
          (slabObservablePairedSupportConnectedEntry_connected
            D rootFaceId targetFaceId source hentry)
    have hkey :=
      slabObservablePairTargetSupportCanonicalPeelingKey_mem
        D rootFaceId targetFaceId floor htarget source hfloor
    have hmassPair : massCode source ∈
        slabObservablePairedSupportPaidMasses D floor := by
      have hcart :=
        (mem_cartesian_iff
          (slabObservablePairedSupportPaidMasses D floor)
          (slabAcceptedTwoReplicaStates D)
          (slabObservablePairTargetSupportCanonicalPeelingKey
            D rootFaceId targetFaceId htarget source)).mp hkey
      simpa only [slabObservablePairTargetSupportCanonicalPeelingKey_eq]
        using hcart.1
    exact hmassPair
  have hpartition :
      listQSum
          (fiberWeight terminalSources
            (fun source => slabObservableTwoReplicaPairWeight D source.1)
            massCode)
          paidMasses ≈
        listQSum
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          terminalSources := by
    exact fiberWeight_total terminalSources
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      massCode paidMasses hpaidNodup hmassMem
  have hfixed : ∀ mass, mass ∈ paidMasses →
      fiberWeight terminalSources
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          massCode mass ≤
        slabObservablePairedGlobalEntropyAnchorRatio ^ mass *
          slabAcceptedTwoReplicaStateWeight cutoff half terminal := by
    intro mass _
    unfold fiberWeight
    apply
      slabObservablePairTargetSupportCanonicalPeeling_fixedTerminalMass_weight_sum_le
        cutoff half rootFaceId targetFaceId mass htarget terminal
    · exact List.filter_sublist.nodup
        (List.filter_sublist.nodup
          (slabObservablePairedSupportConnectedFourCellSourceEntries_nodup
            D rootFaceId targetFaceId))
    · intro source hsource
      have hterminalMem :=
        (List.mem_filter.mp (List.mem_filter.mp hsource).1).2
      exact (of_decide_eq_true hterminalMem).symm
    · intro source hsource
      have hmass := (List.mem_filter.mp hsource).2
      exact (of_decide_eq_true hmass).symm
  have hfibers :
      listQSum
          (fiberWeight terminalSources
            (fun source => slabObservableTwoReplicaPairWeight D source.1)
            massCode)
          paidMasses ≤
        listQSum
          (fun mass =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ mass *
              slabAcceptedTwoReplicaStateWeight cutoff half terminal)
          paidMasses := by
    exact listQSum_le_termwise _ _ paidMasses hfixed
  have hfactor :
      listQSum
          (fun mass =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ mass *
              slabAcceptedTwoReplicaStateWeight cutoff half terminal)
          paidMasses ≈
        listQSum
            (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
            paidMasses *
          slabAcceptedTwoReplicaStateWeight cutoff half terminal :=
    listQSum_mul_right
      (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
      (slabAcceptedTwoReplicaStateWeight cutoff half terminal)
      paidMasses
  have htail := slabObservablePairedSupportPaidMasses_weight_le D floor
  have hterminalNonnegative :=
    slabAcceptedTwoReplicaStateWeight_nonnegative cutoff half terminal
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (slabAcceptedTwoReplicaStateWeight cutoff half terminal)
    htail hterminalNonnegative
  have hrate :
      Q'.mkPos 25 9 (by decide) *
            slabObservablePairedGlobalEntropyAnchorRatio ^ floor =
        slabObservablePairedSupportGlobalAnchorRate
          D rootFaceId targetFaceId := by
    rfl
  change listQSum
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      terminalSources ≤ _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition))
    (Q'.le_trans' _ _ _ hfibers
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
        (by simpa only [hrate] using hscaled)))

#print axioms slabObservablePairTargetSupportCanonicalPeelingTerminal
#print axioms slabObservablePairTargetSupportCanonicalPeelingMass
#print axioms slabObservablePairTargetSupportCanonicalPeelingKey_eq
#print axioms slabObservablePairedSupportCanonicalPeeling_terminalFiberWeight_le

end YMGap.Continuum.CompactDualSlabObservableCanonicalPeelingTerminalFiber
