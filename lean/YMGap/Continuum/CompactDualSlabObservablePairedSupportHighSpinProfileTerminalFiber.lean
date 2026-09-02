/-
# Arbitrary-coupling terminal fiber after bounded-core Fubini

For one accepted terminal, the complete connected observable source sector is
partitioned by

  (total trace mass, truncated-core mass).

The first coordinate retains the geometric separation floor and carries rate
`16/25`.  The second has at most `K + 1` values, where

  K = 2 * faceCount * anchorPaidExteriorThreshold(coupling),

and costs at most `64000000^K`.  Finite Fubini and the existing geometric tail
therefore give the explicit arbitrary-coupling terminal-fiber estimate

  ((25/9) * (16/25)^floor) * ((K+1) * 64000000^K) * terminalWeight.

This closes the complete inverse source fiber at fixed finite slab data.  Its
large volume/coupling-dependent core prefactor is deliberately exposed for the
next localized-coercivity and beta/spacing steps.

Constructive contract: finite filters, deterministic fibers, exact rational
Fubini, and the proved geometric tail only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfilePartition
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileTerminalFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalEntropyCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfilePartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
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

/-! ## 1. Bound the finite core-coordinate sum -/

private theorem qpow_le_succ_of_one_le_local {base : Q'}
    (hbase : (1 : Q') <= base) (exponent : Nat) :
    base ^ exponent <= base ^ (exponent + 1) := by
  rw [Q'.pow_succ]
  have hpow0 : (0 : Q') <= base ^ exponent :=
    Q'.pow_nonneg base
      (Q'.le_trans' _ _ _ Q'.zero_le_one hbase) exponent
  have hscaled : (1 : Q') * base ^ exponent <=
      base * base ^ exponent :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hpow0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (base ^ exponent))) hscaled

private theorem qpow_add_mono_of_one_le_local {base : Q'}
    (hbase : (1 : Q') <= base) (first : Nat) :
    forall offset : Nat, base ^ first <= base ^ (first + offset)
  | 0 => Q'.le_refl' _
  | offset + 1 => by
      have hindex : first + (offset + 1) = (first + offset) + 1 := by omega
      rw [hindex]
      exact Q'.le_trans' _ _ _
        (qpow_add_mono_of_one_le_local hbase first offset)
        (qpow_le_succ_of_one_le_local hbase (first + offset))

private theorem qpow_mono_exponent_of_one_le_local {base : Q'}
    (hbase : (1 : Q') <= base) {first second : Nat}
    (hle : first <= second) : base ^ first <= base ^ second := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact qpow_add_mono_of_one_le_local hbase first offset

/-- Coarse finite-core prefactor after extracting the total-mass rate. -/
def slabObservablePairedHighSpinProfileCorePrefactor
    (D : SlabPhysicalData) : Q' :=
  Q'.ofNat
      (slabObservablePairTargetSupportHighSpinProfileCoreBound D + 1) *
    slabObservablePairedGlobalCoreInflationBase ^
      slabObservablePairTargetSupportHighSpinProfileCoreBound D

theorem slabObservablePairedGlobalCoreInflationSum_le
    (D : SlabPhysicalData) :
    listQSum
        (fun core => slabObservablePairedGlobalCoreInflationBase ^ core)
        (List.range
          (slabObservablePairTargetSupportHighSpinProfileCoreBound D + 1)) <=
      slabObservablePairedHighSpinProfileCorePrefactor D := by
  let bound := slabObservablePairTargetSupportHighSpinProfileCoreBound D
  have hboundNonnegative : (0 : Q') <=
      slabObservablePairedGlobalCoreInflationBase ^ bound :=
    Q'.pow_nonneg slabObservablePairedGlobalCoreInflationBase
      (by decide) bound
  have hsum := listQSum_le_length_mul
    (fun core => slabObservablePairedGlobalCoreInflationBase ^ core)
    hboundNonnegative (List.range (bound + 1))
    (fun core hcore =>
      qpow_mono_exponent_of_one_le_local (by decide)
        (Nat.le_of_lt_succ (List.mem_range.mp hcore)))
  unfold slabObservablePairedHighSpinProfileCorePrefactor
  dsimp only [bound] at hsum
  simpa only [List.length_range] using hsum

/-! ## 2. A fixed terminal/key fiber -/

/-- A complete fixed terminal/key fiber is normalized to geometric total mass
and finite core inflation.  Unrealizable keys have an empty fiber. -/
theorem slabObservablePairTargetSupportHighSpinProfile_fixedTerminalKey_fiberWeight_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D)
    (sources : List (SlabObservableFourCellPairEntry
      D rootFaceId targetFaceId))
    (hsources : sources.Nodup)
    (hterminal : forall source, source ∈ sources ->
      slabObservablePairTargetSupportHighSpinProfileTerminal
        D rootFaceId targetFaceId htarget source = terminal)
    (key : Nat × Nat) :
    fiberWeight sources
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairTargetSupportHighSpinProfileKey
          D rootFaceId targetFaceId htarget)
        key <=
      (slabObservablePairedGlobalEntropyAnchorRatio ^ key.1 *
          slabObservablePairedGlobalCoreInflationBase ^ key.2) *
        slabAcceptedTwoReplicaStateWeight D terminal := by
  let selected := sources.filter fun source => decide
    (key = slabObservablePairTargetSupportHighSpinProfileKey
      D rootFaceId targetFaceId htarget source)
  have hselectedNodup : selected.Nodup :=
    List.filter_sublist.nodup hsources
  cases hselected : selected with
  | nil =>
      unfold fiberWeight
      change listQSum
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          selected <= _
      rw [hselected]
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.pow_nonneg slabObservablePairedGlobalEntropyAnchorRatio
            (by decide) key.1)
          (Q'.pow_nonneg slabObservablePairedGlobalCoreInflationBase
            (by decide) key.2))
        (slabAcceptedTwoReplicaStateWeight_nonnegative D terminal)
  | cons representative tail =>
      have hrepresentative : representative ∈ selected := by
        rw [hselected]
        exact List.mem_cons_self
      have hkey : key =
          slabObservablePairTargetSupportHighSpinProfileKey
            D rootFaceId targetFaceId htarget representative :=
        of_decide_eq_true (List.mem_filter.mp hrepresentative).2
      have hcoreMass : key.2 <= key.1 := by
        have hnatural :
            slabObservablePairTargetSupportHighSpinProfileCore
                D rootFaceId targetFaceId htarget representative <=
              slabObservablePairTargetSupportHighSpinProfileMass
                D rootFaceId targetFaceId htarget representative := by
          unfold slabObservablePairTargetSupportHighSpinProfileMass
          omega
        unfold slabObservablePairTargetSupportHighSpinProfileKey at hkey
        have hmass := congrArg Prod.fst hkey
        have hcore := congrArg Prod.snd hkey
        omega
      have hraw :=
        slabObservablePairTargetSupportHighSpinProfile_fixedTerminalMassCore_weight_sum_le
          D hw0 hw1 rootFaceId targetFaceId htarget terminal
            key.1 key.2 selected hselectedNodup
            (fun source hsource =>
              hterminal source (List.mem_filter.mp hsource).1)
            (fun source hsource => by
              have hkeySource : key =
                  slabObservablePairTargetSupportHighSpinProfileKey
                    D rootFaceId targetFaceId htarget source :=
                of_decide_eq_true (List.mem_filter.mp hsource).2
              exact (congrArg Prod.fst hkeySource).symm)
            (fun source hsource => by
              have hkeySource : key =
                  slabObservablePairTargetSupportHighSpinProfileKey
                    D rootFaceId targetFaceId htarget source :=
                of_decide_eq_true (List.mem_filter.mp hsource).2
              exact (congrArg Prod.snd hkeySource).symm)
      have hnormalize :=
        slabObservablePairedGlobalHighSpinProfileRate_eqv_totalMassCore
          key.1 key.2 hcoreMass
      unfold fiberWeight
      change listQSum
          (fun source => slabObservableTwoReplicaPairWeight D source.1)
          selected <= _
      exact Q'.le_trans' _ _ _ hraw
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_right _ _ _ hnormalize))

/-! ## 3. Sum the complete terminal fiber -/

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_mul_right_local
    {A : Type} (value : A -> Q') (factor : Q') : forall items : List A,
    listQSum (fun item => value item * factor) items ≈
      listQSum value items * factor
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv factor)
  | head :: tail => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl (value head * factor))
          (listQSum_mul_right_local value factor tail))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (value head) (listQSum value tail) factor))

/-- Explicit arbitrary-coupling decay rate for a complete accepted terminal
fiber at finite slab data. -/
def slabObservablePairedSupportHighSpinProfileTerminalRate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  (Q'.mkPos 25 9 (by decide) *
      slabObservablePairedGlobalEntropyAnchorRatio ^
        (linfDist
          (slabPlaquetteAt D.extent rootFaceId)
          (slabPlaquetteAt D.extent targetFaceId) + 1)) *
    slabObservablePairedHighSpinProfileCorePrefactor D

/-- **Complete arbitrary-coupling observable terminal-fiber estimate.** -/
theorem slabObservablePairedSupportHighSpinProfile_terminalFiberWeight_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling) (hw1 : D.coupling < (1 : Q'))
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (terminal : SlabAcceptedTwoReplicaState D) :
    fiberWeight
        (slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairTargetSupportHighSpinProfileTerminal
          D rootFaceId targetFaceId htarget)
        terminal <=
      slabObservablePairedSupportHighSpinProfileTerminalRate
          D rootFaceId targetFaceId *
        slabAcceptedTwoReplicaStateWeight D terminal := by
  let floor := linfDist
    (slabPlaquetteAt D.extent rootFaceId)
    (slabPlaquetteAt D.extent targetFaceId) + 1
  let sources := slabObservablePairedSupportConnectedFourCellSourceEntries
    D rootFaceId targetFaceId
  let terminalCode :=
    slabObservablePairTargetSupportHighSpinProfileTerminal
      D rootFaceId targetFaceId htarget
  let keyCode := slabObservablePairTargetSupportHighSpinProfileKey
    D rootFaceId targetFaceId htarget
  let terminalSources :=
    sources.filter (fun source => decide (terminal = terminalCode source))
  let keys :=
    slabObservablePairTargetSupportHighSpinProfileKeyCarrier D floor
  have hterminalSourcesNodup : terminalSources.Nodup :=
    List.filter_sublist.nodup
      (slabObservablePairedSupportConnectedFourCellSourceEntries_nodup
        D rootFaceId targetFaceId)
  have hkeyMem : forall source, source ∈ terminalSources ->
      keyCode source ∈ keys := by
    intro source hsource
    have hsourceConnected : source ∈ sources :=
      (List.mem_filter.mp hsource).1
    have hfloorTrace :=
      slabObservablePairTargetSupportCanonicalPeeling_traceMass_floor
        D rootFaceId targetFaceId htarget source.1 source.2
        (slabObservablePairedSupportConnectedEntry_connected
          D rootFaceId targetFaceId source hsourceConnected)
    have hfloorProfile : floor <=
        slabObservablePairTargetSupportHighSpinProfileMass
          D rootFaceId targetFaceId htarget source := by
      rw [slabObservablePairTargetSupportHighSpinProfileMass_eq_traceMass]
      exact hfloorTrace
    exact slabObservablePairTargetSupportHighSpinProfileKey_mem
      D rootFaceId targetFaceId floor htarget source hfloorProfile
  have hpartition := fiberWeight_total terminalSources
    (fun source => slabObservableTwoReplicaPairWeight D source.1)
    keyCode keys
    (slabObservablePairTargetSupportHighSpinProfileKeyCarrier_nodup D floor)
    hkeyMem
  have hterminal : forall source, source ∈ terminalSources ->
      terminalCode source = terminal := by
    intro source hsource
    exact (of_decide_eq_true (List.mem_filter.mp hsource).2).symm
  have hfibers :
      listQSum
          (fiberWeight terminalSources
            (fun source => slabObservableTwoReplicaPairWeight D source.1)
            keyCode)
          keys <=
        listQSum
          (fun key =>
            (slabObservablePairedGlobalEntropyAnchorRatio ^ key.1 *
                slabObservablePairedGlobalCoreInflationBase ^ key.2) *
              slabAcceptedTwoReplicaStateWeight D terminal)
          keys := by
    exact listQSum_le_termwise_local _ _ keys
      (fun key _ =>
        slabObservablePairTargetSupportHighSpinProfile_fixedTerminalKey_fiberWeight_le
          D hw0 hw1 rootFaceId targetFaceId htarget terminal
            terminalSources hterminalSourcesNodup hterminal key)
  let coefficient := fun key : Nat × Nat =>
    slabObservablePairedGlobalEntropyAnchorRatio ^ key.1 *
      slabObservablePairedGlobalCoreInflationBase ^ key.2
  have hfactorTerminal :
      listQSum
          (fun key => coefficient key *
            slabAcceptedTwoReplicaStateWeight D terminal)
          keys ≈
        listQSum coefficient keys *
          slabAcceptedTwoReplicaStateWeight D terminal :=
    listQSum_mul_right_local coefficient
      (slabAcceptedTwoReplicaStateWeight D terminal) keys
  have hcartesian :
      listQSum coefficient keys ≈
        listQSum
            (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
            (slabObservablePairedSupportPaidMasses D floor) *
          listQSum
            (fun core => slabObservablePairedGlobalCoreInflationBase ^ core)
            (List.range
              (slabObservablePairTargetSupportHighSpinProfileCoreBound D + 1)) := by
    unfold coefficient keys
    exact listQSum_cartesian_product
      (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
      (fun core => slabObservablePairedGlobalCoreInflationBase ^ core)
      (slabObservablePairedSupportPaidMasses D floor)
      (List.range
        (slabObservablePairTargetSupportHighSpinProfileCoreBound D + 1))
  have hmassTail := slabObservablePairedSupportPaidMasses_weight_le D floor
  have hcoreTail := slabObservablePairedGlobalCoreInflationSum_le D
  have hcoreSumNonnegative : (0 : Q') <=
      listQSum
        (fun core => slabObservablePairedGlobalCoreInflationBase ^ core)
        (List.range
          (slabObservablePairTargetSupportHighSpinProfileCoreBound D + 1)) :=
    listQSum_nonnegative_on _ _ (fun core _ =>
      Q'.pow_nonneg slabObservablePairedGlobalCoreInflationBase
        (by decide) core)
  have hmassEnvelopeNonnegative : (0 : Q') <=
      Q'.mkPos 25 9 (by decide) *
        slabObservablePairedGlobalEntropyAnchorRatio ^ floor :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.pow_nonneg slabObservablePairedGlobalEntropyAnchorRatio
        (by decide) floor)
  have hcoefficientBound :
      listQSum coefficient keys <=
        (Q'.mkPos 25 9 (by decide) *
            slabObservablePairedGlobalEntropyAnchorRatio ^ floor) *
          slabObservablePairedHighSpinProfileCorePrefactor D := by
    have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _
      hmassTail hcoreSumNonnegative
    have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _
      hcoreTail hmassEnvelopeNonnegative
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcartesian)
      (Q'.le_trans' _ _ _ hfirst hsecond)
  have hterminalWeightNonnegative :=
    slabAcceptedTwoReplicaStateWeight_nonnegative D terminal
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _
    hcoefficientBound hterminalWeightNonnegative
  unfold fiberWeight
  change listQSum
      (fun source => slabObservableTwoReplicaPairWeight D source.1)
      terminalSources <= _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hpartition))
    (Q'.le_trans' _ _ _ hfibers
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hfactorTerminal)
        (by
          unfold slabObservablePairedSupportHighSpinProfileTerminalRate
          exact hscaled)))

#print axioms slabObservablePairedGlobalCoreInflationSum_le
#print axioms slabObservablePairTargetSupportHighSpinProfile_fixedTerminalKey_fiberWeight_le
#print axioms slabObservablePairedSupportHighSpinProfile_terminalFiberWeight_le

end YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileTerminalFiber
