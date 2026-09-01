/-
# Necessary local domination for the canonical raw-partition repair

The canonical crossed-slab repair has one remaining weighted inverse-fiber
capacity field.  This module extracts a necessary pointwise consequence of
that field.  Every complete growing slab must be dominated by the single
growing-row completion obtained by replacing its lower restriction with the
low-spin reference, while retaining the canonical extracted/fallback
completion.

Thus the proposed many-to-one repair does not avoid the local Harnack issue:
fiber capacity implies pointwise payment before the weights of distinct
sources are summed.  More sharply, its faithful fixed-completion key lets one
sum a single positive fixed slice and cancel that fixed weight.  Any matched
scale-uniform capacity would then force the growing reference marginal times
the common ceiling to be at least one, contradicting the already proved
all-cutoff marginal tail at an explicit denominator scale.  This refutes this
specific faithful canonical repair route; it does not refute a coarser repair
that mixes fixed completions, compress the remaining spin ray, prove an
all-vector gap, take a continuum limit, or prove the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary

set_option maxRecDepth 500000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem zeroEdgeLabelling_mem_bounded_local
    (K : Nat) (ids : List Nat) :
    zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ (items : List A) {item : A},
      item ∈ items → weight item ≤ listQSum weight items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        exact Q'.add_le_self_of_nonneg
          (weight head) (listQSum weight tail)
          (listQSum_nonnegative_on weight tail
            (fun tailItem _ => hweight tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          weight hweight tail htail
        have htailLe :
            listQSum weight tail ≤
              weight head + listQSum weight tail := by
          have hle := Q'.add_le_add_right
            (0 : Q') (weight head)
            (listQSum weight tail) (hweight head)
          rwa [Q'.zero_add'] at hle
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm =>
      Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

private theorem filter_decide_code_eq_empty
    {Source Target : Type} [DecidableEq Target]
    (target : Target) (code : Source → Target) :
    ∀ source : List Source,
      (∀ item, item ∈ source → target ≠ code item) →
      source.filter (fun item => decide (target = code item)) = []
  | [], _ => rfl
  | head :: tail, houtside => by
      have hhead : target ≠ code head :=
        houtside head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → target ≠ code item :=
        fun item hitem =>
          houtside item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, decide_eq_false hhead,
        Bool.false_eq_true, if_false]
      exact filter_decide_code_eq_empty target code tail htail

private theorem filter_code_eq_singleton_of_injective_nodup
    {Source Target : Type} [DecidableEq Target]
    (code : Source → Target) (selected : Source) :
    ∀ source : List Source,
      source.Nodup →
      selected ∈ source →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        code left = code right → left = right) →
      source.filter
          (fun item => decide (code selected = code item)) =
        [selected]
  | [], _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem, hinjective => by
      have hnodupParts := List.nodup_cons.mp hnodup
      by_cases hhead : code selected = code head
      · have hselected : selected = head :=
          hinjective selected hmem head List.mem_cons_self hhead
        subst selected
        have houtside : ∀ item, item ∈ tail →
            code head ≠ code item := by
          intro item hitem hcode
          have heq : head = item :=
            hinjective head List.mem_cons_self item
              (List.mem_cons_of_mem head hitem) hcode
          subst item
          exact hnodupParts.1 hitem
        rw [List.filter_cons,
          filter_decide_code_eq_empty (code head) code tail houtside]
        simp
      · have hselectedTail : selected ∈ tail := by
          rcases List.mem_cons.mp hmem with hselectedHead | htail
          · exact False.elim
              (hhead (congrArg code hselectedHead))
          · exact htail
        have htailInjective :
            ∀ left, left ∈ tail → ∀ right, right ∈ tail →
              code left = code right → left = right := by
          intro left hleft right hright hcode
          exact hinjective left (List.mem_cons_of_mem head hleft)
            right (List.mem_cons_of_mem head hright) hcode
        simp only [List.filter_cons, decide_eq_false hhead,
          Bool.false_eq_true, if_false]
        exact filter_code_eq_singleton_of_injective_nodup
          code selected tail hnodupParts.2 hselectedTail htailInjective

private theorem fiberWeight_le_of_subset_nodup
    {Source Target : Type} [DecidableEq Target]
    (small large : List Source) (weight : Source → Q')
    (code : Source → Target) (target : Target)
    (hsmall : small.Nodup) (hlarge : large.Nodup)
    (hsubset : ∀ item, item ∈ small → item ∈ large)
    (hweight : ∀ item, (0 : Q') ≤ weight item) :
    fiberWeight small weight code target ≤
      fiberWeight large weight code target := by
  unfold fiberWeight
  apply listQSum_le_of_injective_nodup
    (small.filter (fun item => decide (target = code item)))
    (large.filter (fun item => decide (target = code item)))
    weight weight (fun item => item)
  · exact hsmall.filter _
  · exact hlarge.filter _
  · intro item hitem
    have hparts := List.mem_filter.mp hitem
    exact List.mem_filter.mpr ⟨hsubset item hparts.1, hparts.2⟩
  · intro first _ second _ heq
    exact heq
  · intro item _
    exact Q'.le_refl' (weight item)
  · intro item _
    exact hweight item

/-! ## 1. Faithful keys really carry one target-pair weight -/

theorem fixedGrowingRawPartitionTargetKeyWeight_at_pair
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {pair : (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hpair : pair ∈
      fixedGrowingRawPartitionTargetPairs w hw K volume) :
    fixedGrowingRawPartitionTargetKeyWeight w hw K volume
        (fixedGrowingRawPartitionTargetKey K volume pair) ≈
      fixedGrowingRawPartitionTargetWeight w K volume pair := by
  unfold fixedGrowingRawPartitionTargetKeyWeight fiberWeight
  have hfilter := filter_code_eq_singleton_of_injective_nodup
    (fixedGrowingRawPartitionTargetKey K volume) pair
    (fixedGrowingRawPartitionTargetPairs w hw K volume)
    (fixedGrowingRawPartitionTargetPairs_nodup w hw K volume)
    hpair
    (by
      intro left hleft right hright hkey
      exact fixedGrowingRawPartitionTargetKey_injective_on
        hleft hright hkey)
  rw [hfilter]
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## 2. Fiber capacity forces pointwise source payment -/

private theorem fixedGrowingRawPartitionSourceWeight_nonnegative_local
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat)
    (source : (EdgeLabelling × EdgeLabelling) × EdgeLabelling) :
    (0 : Q') ≤ fixedGrowingRawPartitionSourceWeight w K volume source := by
  unfold fixedGrowingRawPartitionSourceWeight
  exact Q'.mul_nonneg _ _
    (centralPositiveCompletionWeight_nonnegative hw K 0
      (centralLowerSpinCubeState 1) source.1)
    (centralPhysicalPartitionWeight_nonnegative
      hw K (volume + 1) source.2)

theorem sourceWeight_le_canonicalRepairFiber
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {source : (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hsource : source ∈
      fixedGrowingRawPartitionSourcePairs w hw K volume) :
    fixedGrowingRawPartitionSourceWeight w K volume source ≤
      fiberWeight
        (fixedGrowingRawPartitionSourcePairs w hw K volume)
        (fixedGrowingRawPartitionSourceWeight w K volume)
        (canonicalRawPartitionRepairKey w hw K volume)
        (canonicalRawPartitionRepairKey w hw K volume source) := by
  unfold fiberWeight
  apply listQSum_member_le_nonnegative_local
  · exact fixedGrowingRawPartitionSourceWeight_nonnegative_local
      hw K volume
  · exact List.mem_filter.mpr ⟨hsource, by simp⟩

/-! ## 3. The positive fixed-completion slice -/

def fixedSpinOneVacuumCompletion : EdgeLabelling × EdgeLabelling :=
  (zeroEdgeLabelling, zeroEdgeLabelling)

def fixedSpinOneVacuumPhysical : EdgeLabelling :=
  centralLowerSpinCubePhysical 1

def fixedSpinOneVacuumSourceSlice
    (K volume : Nat) :
    List ((EdgeLabelling × EdgeLabelling) × EdgeLabelling) :=
  (centralPhysicalPartitionStates K (volume + 1)).map
    (fun physical => (fixedSpinOneVacuumCompletion, physical))

def fixedSpinOneVacuumTargetKeySlice
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    List RawPartitionTargetKey :=
  (centralPositiveCompletionPairs w hw K (volume + 1)).map
    (fun completion =>
      fixedGrowingRawPartitionTargetKey K volume
        (completion, fixedSpinOneVacuumPhysical))

theorem fixedSpinOneVacuumCompletion_mem
    {w : Q'} (hw : (0 : Q') ≤ w) (K : Nat) :
    fixedSpinOneVacuumCompletion ∈
      centralPositiveCompletionPairs w hw K 0 := by
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨zeroEdgeLabelling_mem_centralPositiveHalfStates hw K 0,
    zeroEdgeLabelling_mem_bounded_local K (centralFixedFaceIds 0)⟩

theorem fixedSpinOneVacuumPhysical_mem
    {K : Nat} (hK : 1 ≤ K) :
    fixedSpinOneVacuumPhysical ∈
      centralPhysicalPartitionStates K 0 := by
  unfold fixedSpinOneVacuumPhysical centralLowerSpinCubePhysical
    centralPhysicalPartitionStates
  exact assembleReflectedSlabLabelling_mem_full
    (centralLowerSpinCubeState_mem_centralHalfStates hK)
    (zeroEdgeLabelling_mem_bounded_local K (centralFixedFaceIds 0))
    (zeroEdgeLabelling_mem_bounded_local K (centralLowerFaceIds 0))

theorem fixedSpinOneVacuumSourceSlice_nodup
    (K volume : Nat) :
    (fixedSpinOneVacuumSourceSlice K volume).Nodup := by
  unfold fixedSpinOneVacuumSourceSlice
  apply nodup_map_of_injOn
  · exact centralPhysicalPartitionStates_nodup K (volume + 1)
  · intro left _ right _ heq
    exact congrArg Prod.snd heq

theorem fixedSpinOneVacuumSourceSlice_mem_full
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    {volume : Nat}
    {source : (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hsource : source ∈ fixedSpinOneVacuumSourceSlice K volume) :
    source ∈ fixedGrowingRawPartitionSourcePairs w hw K volume := by
  obtain ⟨physical, hphysical, rfl⟩ := List.mem_map.mp hsource
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨fixedSpinOneVacuumCompletion_mem hw K, hphysical⟩

theorem fixedSpinOneVacuumTargetKeySlice_nodup
    {w : Q'} (hw : (0 : Q') ≤ w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    (fixedSpinOneVacuumTargetKeySlice w hw K volume).Nodup := by
  unfold fixedSpinOneVacuumTargetKeySlice
  apply nodup_map_of_injOn
  · exact centralPositiveCompletionPairs_nodup
      w hw K (volume + 1)
  · intro left hleft right hright hkey
    have hleftPair : (left, fixedSpinOneVacuumPhysical) ∈
        fixedGrowingRawPartitionTargetPairs w hw K volume :=
      (mem_cartesian_iff _ _ _).mpr
        ⟨hleft, fixedSpinOneVacuumPhysical_mem hK⟩
    have hrightPair : (right, fixedSpinOneVacuumPhysical) ∈
        fixedGrowingRawPartitionTargetPairs w hw K volume :=
      (mem_cartesian_iff _ _ _).mpr
        ⟨hright, fixedSpinOneVacuumPhysical_mem hK⟩
    have hpairs := fixedGrowingRawPartitionTargetKey_injective_on
      hleftPair hrightPair hkey
    exact congrArg Prod.fst hpairs

theorem fixedSpinOneVacuumTargetKeySlice_mem_full
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat} (hK : 1 ≤ K)
    {volume : Nat} {key : RawPartitionTargetKey}
    (hkey : key ∈ fixedSpinOneVacuumTargetKeySlice w hw K volume) :
    key ∈ fixedGrowingRawPartitionTargetKeys w hw K volume := by
  obtain ⟨completion, hcompletion, rfl⟩ := List.mem_map.mp hkey
  unfold fixedGrowingRawPartitionTargetKeys
  exact List.mem_map.mpr
    ⟨(completion, fixedSpinOneVacuumPhysical),
      (mem_cartesian_iff _ _ _).mpr
        ⟨hcompletion, fixedSpinOneVacuumPhysical_mem hK⟩,
      rfl⟩

theorem fixedSpinOneVacuumRepairKey_mem_slice
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    {volume : Nat}
    {source : (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hsource : source ∈ fixedSpinOneVacuumSourceSlice K volume) :
    canonicalRawPartitionRepairKey
        w (Q'.le_of_lt hw) K volume source ∈
      fixedSpinOneVacuumTargetKeySlice
        w (Q'.le_of_lt hw) K volume := by
  obtain ⟨physical, hphysical, rfl⟩ := List.mem_map.mp hsource
  unfold fixedSpinOneVacuumTargetKeySlice
  apply List.mem_map.mpr
  refine ⟨canonicalGrowingCompletion
      w (Q'.le_of_lt hw) K volume physical,
    canonicalGrowingCompletion_mem hw hK volume hphysical, ?_⟩
  rfl

theorem fixedSpinOneVacuumSourceSliceSum_eqv_partition
    (w : Q') (K volume : Nat) :
    listQSum
        (fixedGrowingRawPartitionSourceWeight w K volume)
        (fixedSpinOneVacuumSourceSlice K volume) ≈
      centralPositiveCompletionWeight w K 0
          (centralLowerSpinCubeState 1)
          fixedSpinOneVacuumCompletion *
        growingHalfPhysicalPartition w K volume := by
  unfold fixedSpinOneVacuumSourceSlice
  rw [listQSum_map]
  change listQSum
      (fun physical =>
        centralPositiveCompletionWeight w K 0
            (centralLowerSpinCubeState 1)
            fixedSpinOneVacuumCompletion *
          centralPhysicalPartitionWeight
            w K (volume + 1) physical)
      (centralPhysicalPartitionStates K (volume + 1)) ≈ _
  exact Q'.eqv_trans _ _ _
    (listQSum_mul_left
      (centralPositiveCompletionWeight w K 0
        (centralLowerSpinCubeState 1)
        fixedSpinOneVacuumCompletion)
      (centralPhysicalPartitionWeight w K (volume + 1))
      (centralPhysicalPartitionStates K (volume + 1)))
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (slabParametricKPhysicalPartition_eqv_partitionSum
          w K (volume + 1))))

theorem fixedSpinOneVacuumTargetKeySliceSum_eqv_rawRow
    {w : Q'} (hw : (0 : Q') ≤ w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) :
    listQSum
        (fixedGrowingRawPartitionTargetKeyWeight w hw K volume)
        (fixedSpinOneVacuumTargetKeySlice w hw K volume) ≈
      centralPositiveCompletionWeight w K 0
          (centralLowerSpinCubeState 1)
          fixedSpinOneVacuumCompletion *
        growingHalfSpinOneRawRow w hw K volume := by
  unfold fixedSpinOneVacuumTargetKeySlice
  rw [listQSum_map]
  let fixedWeight := centralPositiveCompletionWeight w K 0
    (centralLowerSpinCubeState 1) fixedSpinOneVacuumCompletion
  let growingWeight := centralPositiveCompletionWeight w K (volume + 1)
    (lowSpinCentralReferenceState volume)
  have hpoint : ∀ completion,
      completion ∈ centralPositiveCompletionPairs w hw K (volume + 1) →
      fixedGrowingRawPartitionTargetKeyWeight w hw K volume
          (fixedGrowingRawPartitionTargetKey K volume
            (completion, fixedSpinOneVacuumPhysical)) ≈
        fixedWeight * growingWeight completion := by
    intro completion hcompletion
    have hpair : (completion, fixedSpinOneVacuumPhysical) ∈
        fixedGrowingRawPartitionTargetPairs w hw K volume :=
      (mem_cartesian_iff _ _ _).mpr
        ⟨hcompletion, fixedSpinOneVacuumPhysical_mem hK⟩
    have hkey := fixedGrowingRawPartitionTargetKeyWeight_at_pair hpair
    exact Q'.eqv_trans _ _ _ hkey
      (Q'.eqv_trans _ _ _
        (Q'.eqv_refl _)
        (Q'.mul_comm_eqv (growingWeight completion) fixedWeight))
  have hsum :
      listQSum
          (fun completion =>
            fixedGrowingRawPartitionTargetKeyWeight w hw K volume
              (fixedGrowingRawPartitionTargetKey K volume
                (completion, fixedSpinOneVacuumPhysical)))
          (centralPositiveCompletionPairs w hw K (volume + 1)) ≈
        listQSum (fun completion => fixedWeight * growingWeight completion)
          (centralPositiveCompletionPairs w hw K (volume + 1)) := by
    apply listQSum_congr_on
    intro completion hcompletion
    exact hpoint completion hcompletion
  exact Q'.eqv_trans _ _ _ hsum
    (Q'.eqv_trans _ _ _
      (listQSum_mul_left fixedWeight growingWeight
        (centralPositiveCompletionPairs w hw K (volume + 1)))
      (Q'.mul_eqv_congr_left fixedWeight _ _
        (Q'.eqv_symm
          (centralPhysicalPositiveRawRowMass_eqv_completionSum
            hw K (volume + 1)
            (lowSpinCentralReferenceState volume)))))

namespace CanonicalRawPartitionFiberBound

theorem sourceWeight_le_repairTargetWeight
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CanonicalRawPartitionFiberBound
      w hw K hK volume ceiling)
    {source : (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hsource : source ∈
      fixedGrowingRawPartitionSourcePairs
        w (Q'.le_of_lt hw) K volume) :
    fixedGrowingRawPartitionSourceWeight w K volume source ≤
      ceiling * fixedGrowingRawPartitionTargetWeight w K volume
        (canonicalRawPartitionRepairTarget
          w (Q'.le_of_lt hw) K volume source) := by
  have hmember := sourceWeight_le_canonicalRepairFiber hsource
  have hkeyMem := canonicalRawPartitionRepairKey_mem
    hw hK volume hsource
  have hcapacity := bound.weighted_fiber_capacity
    (canonicalRawPartitionRepairKey
      w (Q'.le_of_lt hw) K volume source) hkeyMem
  have htargetMem := canonicalRawPartitionRepairTarget_mem
    hw hK volume hsource
  have hkeyWeight := fixedGrowingRawPartitionTargetKeyWeight_at_pair
    htargetMem
  have hscaledKeyWeight :
      ceiling *
          fixedGrowingRawPartitionTargetKeyWeight
            w (Q'.le_of_lt hw) K volume
            (canonicalRawPartitionRepairKey
              w (Q'.le_of_lt hw) K volume source) ≈
        ceiling * fixedGrowingRawPartitionTargetWeight w K volume
          (canonicalRawPartitionRepairTarget
            w (Q'.le_of_lt hw) K volume source) := by
    exact Q'.mul_eqv_congr_left ceiling _ _ hkeyWeight
  exact Q'.le_trans' _ _ _ hmember
    (Q'.le_trans' _ _ _ hcapacity
      (Q'.le_of_eqv hscaledKeyWeight))

/-! ## 3. Cancelling the fixed spin-one completion -/

theorem growingPhysicalWeight_le_canonicalCompletionWeight
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CanonicalRawPartitionFiberBound
      w hw K hK volume ceiling)
    {physical : EdgeLabelling}
    (hphysical : physical ∈
      centralPhysicalPartitionStates K (volume + 1)) :
    centralPhysicalPartitionWeight w K (volume + 1) physical ≤
      ceiling * centralPositiveCompletionWeight w K (volume + 1)
        (lowSpinCentralReferenceState volume)
        (canonicalGrowingCompletion
          w (Q'.le_of_lt hw) K volume physical) := by
  let zeroCompletion : EdgeLabelling × EdgeLabelling :=
    (zeroEdgeLabelling, zeroEdgeLabelling)
  let source : (EdgeLabelling × EdgeLabelling) × EdgeLabelling :=
    (zeroCompletion, physical)
  have hzeroCompletion : zeroCompletion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K 0 := by
    apply (mem_cartesian_iff _ _ _).mpr
    exact ⟨zeroEdgeLabelling_mem_centralPositiveHalfStates
        (Q'.le_of_lt hw) K 0,
      zeroEdgeLabelling_mem_bounded_local K (centralFixedFaceIds 0)⟩
  have hsource : source ∈
      fixedGrowingRawPartitionSourcePairs
        w (Q'.le_of_lt hw) K volume := by
    apply (mem_cartesian_iff _ _ _).mpr
    exact ⟨hzeroCompletion, hphysical⟩
  have hpoint := sourceWeight_le_repairTargetWeight bound hsource
  let fixedWeight := centralPositiveCompletionWeight w K 0
    (centralLowerSpinCubeState 1) zeroCompletion
  let growingWeight := centralPhysicalPartitionWeight
    w K (volume + 1) physical
  let completionWeight := centralPositiveCompletionWeight
    w K (volume + 1) (lowSpinCentralReferenceState volume)
      (canonicalGrowingCompletion
        w (Q'.le_of_lt hw) K volume physical)
  have hfixed : (0 : Q') < fixedWeight := by
    simpa only [fixedWeight, zeroCompletion,
      centralPositiveCompletionWeight,
      centralLowerSpinCubePhysical] using
      (centralLowerSpinCubePhysicalTerm_pos hw hK)
  have hpoint' :
      fixedWeight * growingWeight ≤
        ceiling * (completionWeight * fixedWeight) := by
    simpa only [source, zeroCompletion, fixedWeight, growingWeight,
      completionWeight, fixedGrowingRawPartitionSourceWeight,
      fixedGrowingRawPartitionTargetWeight,
      canonicalRawPartitionRepairTarget,
      canonicalFixedPartitionPhysical,
      centralPhysicalPartitionWeight,
      centralPositiveCompletionWeight,
      centralLowerSpinCubePhysical] using hpoint
  have hreorder :
      ceiling * (completionWeight * fixedWeight) ≈
        fixedWeight * (ceiling * completionWeight) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv ceiling completionWeight fixedWeight))
      (Q'.mul_comm_eqv (ceiling * completionWeight) fixedWeight)
  have hscaled :
      fixedWeight * growingWeight ≤
        fixedWeight * (ceiling * completionWeight) :=
    Q'.le_trans' _ _ _ hpoint' (Q'.le_of_eqv hreorder)
  have hcancel := Q'.le_of_mul_le_mul_left hscaled hfixed
  simpa only [growingWeight, completionWeight] using hcancel

/-! ## 4. The faithful fixed-completion slice forces the full local ratio -/

/-- Because the target key retains the fixed physical completion exactly, the
fiber bound can be summed over the keys with that one fixed completion.  The
positive fixed weight then cancels, leaving the entire growing partition to
be paid by the single growing low-spin raw row. -/
theorem growingPartition_le_ceiling_mul_growingRawRow
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CanonicalRawPartitionFiberBound
      w hw K hK volume ceiling) :
    growingHalfPhysicalPartition w K volume ≤
      ceiling * growingHalfSpinOneRawRow
        w (Q'.le_of_lt hw) K volume := by
  let sourceSlice := fixedSpinOneVacuumSourceSlice K volume
  let sourcePairs := fixedGrowingRawPartitionSourcePairs
    w (Q'.le_of_lt hw) K volume
  let sourceWeight := fixedGrowingRawPartitionSourceWeight w K volume
  let targetSlice := fixedSpinOneVacuumTargetKeySlice
    w (Q'.le_of_lt hw) K volume
  let targetWeight := fixedGrowingRawPartitionTargetKeyWeight
    w (Q'.le_of_lt hw) K volume
  let repair := canonicalRawPartitionRepairKey
    w (Q'.le_of_lt hw) K volume
  let pushedSliceWeight := fiberWeight sourceSlice sourceWeight repair
  have htotal :
      listQSum pushedSliceWeight targetSlice ≈
        listQSum sourceWeight sourceSlice :=
    fiberWeight_total sourceSlice sourceWeight repair targetSlice
      (fixedSpinOneVacuumTargetKeySlice_nodup
        (Q'.le_of_lt hw) hK volume)
      (by
        intro source hsource
        exact fixedSpinOneVacuumRepairKey_mem_slice hw hK hsource)
  have hcapacity :
      listQSum pushedSliceWeight targetSlice ≤
        listQSum (fun key => ceiling * targetWeight key)
          targetSlice := by
    apply listQSum_le_termwise_local
    intro key hkey
    have hsmall :
        fiberWeight sourceSlice sourceWeight repair key ≤
          fiberWeight sourcePairs sourceWeight repair key := by
      apply fiberWeight_le_of_subset_nodup
      · exact fixedSpinOneVacuumSourceSlice_nodup K volume
      · exact fixedGrowingRawPartitionSourcePairs_nodup
          w (Q'.le_of_lt hw) K volume
      · intro source hsource
        exact fixedSpinOneVacuumSourceSlice_mem_full hsource
      · exact fixedGrowingRawPartitionSourceWeight_nonnegative_local
          (Q'.le_of_lt hw) K volume
    have hfull := fixedSpinOneVacuumTargetKeySlice_mem_full hK hkey
    exact Q'.le_trans' _ _ _ hsmall
      (bound.weighted_fiber_capacity key hfull)
  let fixedWeight := centralPositiveCompletionWeight w K 0
    (centralLowerSpinCubeState 1) fixedSpinOneVacuumCompletion
  have hsource :
      listQSum sourceWeight sourceSlice ≈
        fixedWeight * growingHalfPhysicalPartition w K volume := by
    simpa only [sourceWeight, sourceSlice, fixedWeight] using
      (fixedSpinOneVacuumSourceSliceSum_eqv_partition w K volume)
  have htarget :
      listQSum targetWeight targetSlice ≈
        fixedWeight * growingHalfSpinOneRawRow
          w (Q'.le_of_lt hw) K volume := by
    simpa only [targetWeight, targetSlice, fixedWeight] using
      (fixedSpinOneVacuumTargetKeySliceSum_eqv_rawRow
        (Q'.le_of_lt hw) hK volume)
  have hfactor :
      listQSum (fun key => ceiling * targetWeight key) targetSlice ≈
        ceiling * listQSum targetWeight targetSlice :=
    listQSum_mul_left ceiling targetWeight targetSlice
  have hscaledTarget :
      listQSum (fun key => ceiling * targetWeight key) targetSlice ≈
        ceiling *
          (fixedWeight * growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) :=
    Q'.eqv_trans _ _ _ hfactor
      (Q'.mul_eqv_congr_left ceiling _ _ htarget)
  have hcross :
      fixedWeight * growingHalfPhysicalPartition w K volume ≤
        ceiling *
          (fixedWeight * growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource)
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal)
        (Q'.le_trans' _ _ _ hcapacity
          (Q'.le_of_eqv hscaledTarget)))
  have hreorder :
      ceiling *
          (fixedWeight * growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) ≈
        fixedWeight *
          (ceiling * growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv ceiling
        (fixedWeight * growingHalfSpinOneRawRow
          w (Q'.le_of_lt hw) K volume))
      (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv fixedWeight
          (growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume) ceiling)
        (Q'.mul_eqv_congr_left fixedWeight _ _
          (Q'.mul_comm_eqv
            (growingHalfSpinOneRawRow
              w (Q'.le_of_lt hw) K volume) ceiling)))
  have hfixed : (0 : Q') < fixedWeight := by
    simpa only [fixedWeight, fixedSpinOneVacuumCompletion,
      centralPositiveCompletionWeight,
      centralLowerSpinCubePhysical] using
      (centralLowerSpinCubePhysicalTerm_pos hw hK)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ hcross (Q'.le_of_eqv hreorder)) hfixed

/-- Normalized form of the faithful-slice obstruction: the scaled growing
reference marginal must be at least one. -/
theorem one_le_ceiling_mul_growingReferenceMarginal
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CanonicalRawPartitionFiberBound
      w hw K hK volume ceiling) :
    (1 : Q') ≤ ceiling *
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K (volume + 1)
        (lowSpinCentralReferenceState volume) := by
  let raw := growingHalfSpinOneRawRow
    w (Q'.le_of_lt hw) K volume
  let partition := growingHalfPhysicalPartition w K volume
  have hpartition : (0 : Q') < partition := by
    unfold partition growingHalfPhysicalPartition
    exact slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw) K (centralExtent (volume + 1))
  have hraw := growingPartition_le_ceiling_mul_growingRawRow bound
  have hcleared : (1 : Q') * partition ≤ ceiling * raw :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv partition))
      (by simpa only [partition, raw] using hraw)
  have hquotient :
      (1 : Q') ≤ Q'.divPos (ceiling * raw) partition hpartition :=
    Q'.le_divPos_of_mul_le (ceiling * raw) partition
      hpartition hcleared
  have hreferenceMem : lowSpinCentralReferenceState volume ∈
      centralHalfStates K (volume + 1) := by
    have href :=
      (lowSpinCentralKPositiveRawReplication
        w hw K hK volume).reference_mem
    exact (mem_centralPositiveHalfStates_iff.mp href).1
  have hmarginal :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (volume + 1)
          (lowSpinCentralReferenceState volume) ≈
        Q'.divPos raw partition hpartition := by
    have hrow :=
      centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
        (w := w) (hw := Q'.le_of_lt hw) (K := K)
        (half := volume + 1)
        (source := lowSpinCentralReferenceState volume)
        hreferenceMem
    simpa only [raw, partition, growingHalfSpinOneRawRow,
      growingHalfPhysicalPartition,
      centralPhysicalPositiveRawRowMass,
      centralPhysicalFiniteVacuumSectorPartitionReciprocal,
      Q'.divPos] using hrow
  have hscaled :
      ceiling *
          centralPhysicalRowMarginal
            w (Q'.le_of_lt hw) K (volume + 1)
            (lowSpinCentralReferenceState volume) ≈
        Q'.divPos (ceiling * raw) partition hpartition := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left ceiling _ _ hmarginal)
      (by
        unfold Q'.divPos
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv ceiling raw
            (Q'.recipPos partition hpartition)))
  exact Q'.le_trans' _ _ _ hquotient (Q'.ge_of_eqv hscaled)

end CanonicalRawPartitionFiberBound

/-! ## 5. No scale-uniform faithful canonical repair -/

/-- The faithful canonical target key cannot have one weighted-fiber ceiling
on the matched diagonal.  At the denominator scale of
`(1/2) / ceiling`, the exact slice lower bound is at least one while the
all-cutoff replication theorem makes it at most one half. -/
theorem no_matchedDyadicCanonicalRawPartitionFiberBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling} :
    ¬ Nonempty
      (MatchedDyadicCanonicalRawPartitionFiberBound bridge) := by
  intro hexists
  obtain ⟨bound⟩ := hexists
  have hceiling : (0 : Q') < bound.ceiling :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < (1 : Q'))
      bound.one_le_ceiling
  let epsilon := Q'.divPos HalfPow.half bound.ceiling hceiling
  let scale := epsilon.den
  let w := matchedAllSpinWeight family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  have hw : (0 : Q') < w :=
    matchedAllSpinWeight_pos family coupling scale
  have hK : 1 ≤ K := one_le_matchedAllSpinCutoff bridge scale
  have hepsilon : (0 : Q') < epsilon := by
    unfold epsilon
    exact Q'.divPos_pos HalfPow.half bound.ceiling hceiling (by decide)
  have hlower :
      (1 : Q') ≤ bound.ceiling *
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (scale + 1)
          (lowSpinCentralReferenceState scale) := by
    simpa only [w, K] using
      (CanonicalRawPartitionFiberBound.one_le_ceiling_mul_growingReferenceMarginal
          (bound.fiberBound scale))
  have hmarginal :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (scale + 1)
          (lowSpinCentralReferenceState scale) ≤ epsilon := by
    exact lowSpinCentralKReferenceMarginal_le_epsilon
      w hw K hK epsilon hepsilon scale (Nat.le_refl scale)
  have hscaled :
      bound.ceiling *
          centralPhysicalRowMarginal
            w (Q'.le_of_lt hw) K (scale + 1)
            (lowSpinCentralReferenceState scale) ≤
        bound.ceiling * epsilon :=
    Q'.mul_le_mul_of_nonneg_left _ _ bound.ceiling hmarginal
      (Q'.le_of_lt hceiling)
  have hcollapse : bound.ceiling * epsilon ≈ HalfPow.half := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv bound.ceiling epsilon)
      (by
        unfold epsilon
        exact Q'.divPos_mul_eqv HalfPow.half bound.ceiling hceiling)
  have honeHalf : (1 : Q') ≤ HalfPow.half :=
    Q'.le_trans' _ _ _ hlower
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse))
  exact (by decide : ¬ ((1 : Q') ≤ HalfPow.half)) honeHalf

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary.fixedGrowingRawPartitionTargetKeyWeight_at_pair
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary.sourceWeight_le_canonicalRepairFiber
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary.CanonicalRawPartitionFiberBound.sourceWeight_le_repairTargetWeight
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary.CanonicalRawPartitionFiberBound.growingPhysicalWeight_le_canonicalCompletionWeight
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary.CanonicalRawPartitionFiberBound.growingPartition_le_ceiling_mul_growingRawRow
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary.CanonicalRawPartitionFiberBound.one_le_ceiling_mul_growingReferenceMarginal
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary.no_matchedDyadicCanonicalRawPartitionFiberBound
