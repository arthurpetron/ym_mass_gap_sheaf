/-
# Coarse fixed-completion repair for the low-spin volume bridge

The faithful canonical target key retains the complete fixed-half physical
state.  Its weighted-fiber capacity is impossible uniformly on the matched
diagonal: a single positive fixed-completion slice must then pay the entire
growing partition with one growing raw row.

This module removes precisely that over-resolution.  Its target key keeps the
growing completion but forgets the fixed physical coordinate.  The target
key weight therefore aggregates over every fixed physical state and retains
the full `Z_0` factor required by the exact crossed-product inequality.  The
canonical growing-completion extraction gives a concrete deterministic repair
into this coarser carrier, and a weighted inverse-fiber bound for that repair
compiles to the desired normalized fixed/growing atom comparison.

The remaining capacity field is not inhabited here.  No spin-ray compression,
cofinal all-vector gap, continuum limit, or Clay theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepairNecessary

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair

set_option maxRecDepth 500000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem code_injective_on_bounded_local
    {K : Nat} {ids : List Nat} {left right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K ids)
    (hright : right ∈ boundedEdgeLabellings K ids)
    (hcode :
      edgeLabellingCode (K + 1) ids left =
        edgeLabellingCode (K + 1) ids right) :
    left = right := by
  have hleftSound := boundedEdgeLabellings_sound K ids left hleft
  have hrightSound := boundedEdgeLabellings_sound K ids right hright
  exact edgeLabellingCode_injective_on_bounded
    (Nat.zero_lt_succ K)
    hleftSound.1 hrightSound.1
    hleftSound.2 hrightSound.2 hcode

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

private theorem filter_decide_code_eq_empty_local
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
      exact filter_decide_code_eq_empty_local target code tail htail

private theorem filter_code_eq_singleton_of_injective_nodup_local
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
          filter_decide_code_eq_empty_local
            (code head) code tail houtside]
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
        exact filter_code_eq_singleton_of_injective_nodup_local
          code selected tail hnodupParts.2 hselectedTail htailInjective

/-! ## 1. A decidable key that forgets the fixed physical coordinate -/

structure GrowingCompletionKey where
  targetCode : Nat
  boundaryCode : Nat
  deriving DecidableEq

def growingCompletionKey
    (K volume : Nat)
    (completion : EdgeLabelling × EdgeLabelling) :
    GrowingCompletionKey where
  targetCode :=
    edgeLabellingCode (K + 1)
      (centralLowerFaceIds (volume + 1)) completion.1
  boundaryCode :=
    edgeLabellingCode (K + 1)
      (centralFixedFaceIds (volume + 1)) completion.2

def growingCompletionKeys
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    List GrowingCompletionKey :=
  (centralPositiveCompletionPairs w hw K (volume + 1)).map
    (growingCompletionKey K volume)

theorem growingCompletionKey_injective_on
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {left right : EdgeLabelling × EdgeLabelling}
    (hleft : left ∈
      centralPositiveCompletionPairs w hw K (volume + 1))
    (hright : right ∈
      centralPositiveCompletionPairs w hw K (volume + 1))
    (hkey :
      growingCompletionKey K volume left =
        growingCompletionKey K volume right) :
    left = right := by
  have hleftParts :=
    (mem_cartesian_iff
      (centralPositiveHalfStates w hw K (volume + 1))
      (centralBoundaryChannels K (volume + 1)) left).mp hleft
  have hrightParts :=
    (mem_cartesian_iff
      (centralPositiveHalfStates w hw K (volume + 1))
      (centralBoundaryChannels K (volume + 1)) right).mp hright
  have hcodes :
      edgeLabellingCode (K + 1)
            (centralLowerFaceIds (volume + 1)) left.1 =
          edgeLabellingCode (K + 1)
            (centralLowerFaceIds (volume + 1)) right.1 ∧
        edgeLabellingCode (K + 1)
            (centralFixedFaceIds (volume + 1)) left.2 =
          edgeLabellingCode (K + 1)
            (centralFixedFaceIds (volume + 1)) right.2 := by
    unfold growingCompletionKey at hkey
    simpa only [GrowingCompletionKey.mk.injEq] using hkey
  apply Prod.ext
  · exact code_injective_on_bounded_local
      (mem_centralPositiveHalfStates_iff.mp hleftParts.1).1
      (mem_centralPositiveHalfStates_iff.mp hrightParts.1).1
      hcodes.1
  · exact code_injective_on_bounded_local
      hleftParts.2 hrightParts.2 hcodes.2

theorem growingCompletionKeys_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    (growingCompletionKeys w hw K volume).Nodup := by
  unfold growingCompletionKeys
  apply nodup_map_of_injOn
  · exact centralPositiveCompletionPairs_nodup
      w hw K (volume + 1)
  · intro left hleft right hright hkey
    exact growingCompletionKey_injective_on hleft hright hkey

def coarseRawPartitionTargetKey
    (K volume : Nat)
    (pair : (EdgeLabelling × EdgeLabelling) × EdgeLabelling) :
    GrowingCompletionKey :=
  growingCompletionKey K volume pair.1

/-- The growing-row completion weight pushed to the decidable coarse key. -/
def growingCompletionKeyWeight
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (key : GrowingCompletionKey) : Q' :=
  fiberWeight
    (centralPositiveCompletionPairs w hw K (volume + 1))
    (centralPositiveCompletionWeight w K (volume + 1)
      (lowSpinCentralReferenceState volume))
    (growingCompletionKey K volume)
    key

theorem growingCompletionKeyWeight_at_completion
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs w hw K (volume + 1)) :
    growingCompletionKeyWeight w hw K volume
        (growingCompletionKey K volume completion) ≈
      centralPositiveCompletionWeight w K (volume + 1)
        (lowSpinCentralReferenceState volume) completion := by
  unfold growingCompletionKeyWeight fiberWeight
  have hfilter :=
    filter_code_eq_singleton_of_injective_nodup_local
      (growingCompletionKey K volume) completion
      (centralPositiveCompletionPairs w hw K (volume + 1))
      (centralPositiveCompletionPairs_nodup
        w hw K (volume + 1))
      hcompletion
      (by
        intro left hleft right hright hkey
        exact growingCompletionKey_injective_on
          hleft hright hkey)
  rw [hfilter]
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- The coarse target weight aggregates the forgotten fixed physical
coordinate by multiplying the pushed growing-completion weight by the full
fixed partition `Z_0`. -/
def coarseRawPartitionTargetKeyWeight
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (key : GrowingCompletionKey) : Q' :=
  growingCompletionKeyWeight w hw K volume key *
    fixedHalfPhysicalPartition w K

theorem coarseRawPartitionTargetKeyWeight_at_completion
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs w hw K (volume + 1)) :
    coarseRawPartitionTargetKeyWeight w hw K volume
        (growingCompletionKey K volume completion) ≈
      centralPositiveCompletionWeight w K (volume + 1)
          (lowSpinCentralReferenceState volume) completion *
        fixedHalfPhysicalPartition w K := by
  unfold coarseRawPartitionTargetKeyWeight
  exact Q'.mul_eqv_congr_right _ _ _
    (growingCompletionKeyWeight_at_completion hcompletion)

theorem coarseRawPartitionTargetKeySum_eqv_cross
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat) :
    listQSum
        (coarseRawPartitionTargetKeyWeight w hw K volume)
        (growingCompletionKeys w hw K volume) ≈
      growingHalfSpinOneRawRow w hw K volume *
        fixedHalfPhysicalPartition w K := by
  let completions :=
    centralPositiveCompletionPairs w hw K (volume + 1)
  let completionWeight :=
    centralPositiveCompletionWeight w K (volume + 1)
      (lowSpinCentralReferenceState volume)
  let pushedWeight := growingCompletionKeyWeight w hw K volume
  have htotal := fiberWeight_total
    completions completionWeight
    (growingCompletionKey K volume)
    (growingCompletionKeys w hw K volume)
    (growingCompletionKeys_nodup w hw K volume)
    (by
      intro completion hcompletion
      unfold growingCompletionKeys
      exact List.mem_map.mpr ⟨completion, hcompletion, rfl⟩)
  have hfactor :
      listQSum
          (coarseRawPartitionTargetKeyWeight w hw K volume)
          (growingCompletionKeys w hw K volume) ≈
        listQSum pushedWeight
            (growingCompletionKeys w hw K volume) *
          fixedHalfPhysicalPartition w K := by
    unfold coarseRawPartitionTargetKeyWeight
    exact listQSum_mul_right pushedWeight
      (fixedHalfPhysicalPartition w K)
      (growingCompletionKeys w hw K volume)
  have hrow := centralPhysicalPositiveRawRowMass_eqv_completionSum
    hw K (volume + 1) (lowSpinCentralReferenceState volume)
  exact Q'.eqv_trans _ _ _ hfactor
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ htotal)
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm hrow)))

/-! ## 2. The canonical repair into the coarser key carrier -/

def coarseGrowingPhysicalRepairKey
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (physical : EdgeLabelling) : GrowingCompletionKey :=
  growingCompletionKey K volume
    (canonicalGrowingCompletion w hw K volume physical)

def coarseGrowingPhysicalRepairFiberWeight
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (key : GrowingCompletionKey) : Q' :=
  fiberWeight
    (centralPhysicalPartitionStates K (volume + 1))
    (centralPhysicalPartitionWeight w K (volume + 1))
    (coarseGrowingPhysicalRepairKey w hw K volume)
    key

def coarseCanonicalRawPartitionRepairKey
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (source :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling) :
    GrowingCompletionKey :=
  coarseGrowingPhysicalRepairKey w hw K volume source.2

theorem coarseCanonicalRawPartitionRepairKey_mem
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat)
    {source :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hsource : source ∈
      fixedGrowingRawPartitionSourcePairs
        w (Q'.le_of_lt hw) K volume) :
    coarseCanonicalRawPartitionRepairKey
        w (Q'.le_of_lt hw) K volume source ∈
      growingCompletionKeys
        w (Q'.le_of_lt hw) K volume := by
  have hparts :=
    (mem_cartesian_iff
      (centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalPartitionStates K (volume + 1))
      source).mp hsource
  unfold coarseCanonicalRawPartitionRepairKey growingCompletionKeys
  exact List.mem_map.mpr
    ⟨canonicalGrowingCompletion
        w (Q'.le_of_lt hw) K volume source.2,
      canonicalGrowingCompletion_mem hw hK volume hparts.2,
      rfl⟩

/-- Forgetting the fixed physical coordinate factors every crossed source
inverse fiber into the complete fixed spin-one raw row times the corresponding
growing-physical repair fiber. -/
theorem coarseCanonicalRawPartitionSourceFiber_eqv_fixedRaw_mul_growingFiber
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat)
    (key : GrowingCompletionKey) :
    fiberWeight
        (fixedGrowingRawPartitionSourcePairs w hw K volume)
        (fixedGrowingRawPartitionSourceWeight w K volume)
        (coarseCanonicalRawPartitionRepairKey w hw K volume)
        key ≈
      fixedHalfSpinOneRawRow w hw K *
        coarseGrowingPhysicalRepairFiberWeight
          w hw K volume key := by
  let completions := centralPositiveCompletionPairs w hw K 0
  let physicals := centralPhysicalPartitionStates K (volume + 1)
  let completionWeight := centralPositiveCompletionWeight w K 0
    (centralLowerSpinCubeState 1)
  let physicalWeight := centralPhysicalPartitionWeight
    w K (volume + 1)
  let physicalRepair := coarseGrowingPhysicalRepairKey
    w hw K volume
  let sourcePairs := fixedGrowingRawPartitionSourcePairs w hw K volume
  let sourceWeight := fixedGrowingRawPartitionSourceWeight w K volume
  let sourceRepair := coarseCanonicalRawPartitionRepairKey w hw K volume
  have hkernel :
      kernelPushforwardWeight sourcePairs sourceWeight
          sourceRepair key ≈
        listQSum
          (fun pair =>
            completionWeight pair.1 *
              (physicalWeight pair.2 *
                deterministicKernel physicalRepair pair.2 key))
          (cartesian completions physicals) := by
    unfold kernelPushforwardWeight sourcePairs sourceWeight sourceRepair
      physicalRepair completionWeight physicalWeight
      fixedGrowingRawPartitionSourcePairs
      fixedGrowingRawPartitionSourceWeight
      coarseCanonicalRawPartitionRepairKey
    apply listQSum_congr
    intro pair
    exact Q'.mul_assoc_eqv _ _ _
  have hproduct :
      listQSum
          (fun pair =>
            completionWeight pair.1 *
              (physicalWeight pair.2 *
                deterministicKernel physicalRepair pair.2 key))
          (cartesian completions physicals) ≈
        listQSum completionWeight completions *
          listQSum
            (fun physical =>
              physicalWeight physical *
                deterministicKernel physicalRepair physical key)
            physicals :=
    listQSum_cartesian_product completionWeight
      (fun physical =>
        physicalWeight physical *
          deterministicKernel physicalRepair physical key)
      completions physicals
  have hrow := centralPhysicalPositiveRawRowMass_eqv_completionSum
    hw K 0 (centralLowerSpinCubeState 1)
  have hphysicalFiber :
      listQSum
          (fun physical =>
            physicalWeight physical *
              deterministicKernel physicalRepair physical key)
          physicals ≈
        coarseGrowingPhysicalRepairFiberWeight
          w hw K volume key := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_refl _)
      (kernelPushforwardWeight_eqv_fiberWeight
        physicalWeight physicalRepair key physicals)
  have hscaled :
      listQSum completionWeight completions *
          listQSum
            (fun physical =>
              physicalWeight physical *
                deterministicKernel physicalRepair physical key)
            physicals ≈
        fixedHalfSpinOneRawRow w hw K *
          coarseGrowingPhysicalRepairFiberWeight
            w hw K volume key := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hrow))
      (Q'.mul_eqv_congr_left _ _ _ hphysicalFiber)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (kernelPushforwardWeight_eqv_fiberWeight
        sourceWeight sourceRepair key sourcePairs))
    (Q'.eqv_trans _ _ _ hkernel
      (Q'.eqv_trans _ _ _ hproduct hscaled))

/-! ## 3. The reduced growing-physical fiber producer -/

/-- After exact fixed-completion aggregation, the remaining estimate is only
on the pushforward of full growing physical slabs to their extracted growing
completion.  Both the fixed raw row and the fixed partition remain visible,
so this condition does not repeat the faithful-slice overpayment. -/
structure CoarseGrowingPhysicalFiberCrossBound
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (ceiling : Q') : Type where
  weighted_fiber_cross : ∀ key,
    key ∈ growingCompletionKeys
        w (Q'.le_of_lt hw) K volume →
      fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
          coarseGrowingPhysicalRepairFiberWeight
            w (Q'.le_of_lt hw) K volume key ≤
        ceiling *
          (growingCompletionKeyWeight
              w (Q'.le_of_lt hw) K volume key *
            fixedHalfPhysicalPartition w K)

/-! ## 4. Equivalence with the coarse crossed-fiber estimate -/

/-- The exact remaining producer after removing the faithful fixed-completion
obstruction.  Each inverse fiber of the concrete coarse repair must be paid by
the corresponding growing-completion target weight, already aggregated over
the full fixed partition. -/
structure CoarseCanonicalRawPartitionFiberBound
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (ceiling : Q') : Type where
  weighted_fiber_capacity : ∀ key,
    key ∈ growingCompletionKeys
        w (Q'.le_of_lt hw) K volume →
      fiberWeight
          (fixedGrowingRawPartitionSourcePairs
            w (Q'.le_of_lt hw) K volume)
          (fixedGrowingRawPartitionSourceWeight w K volume)
          (coarseCanonicalRawPartitionRepairKey
            w (Q'.le_of_lt hw) K volume)
          key ≤
        ceiling *
          coarseRawPartitionTargetKeyWeight
            w (Q'.le_of_lt hw) K volume key

def CoarseGrowingPhysicalFiberCrossBound.toRawPartitionFiberBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingPhysicalFiberCrossBound
      w hw K hK volume ceiling) :
    CoarseCanonicalRawPartitionFiberBound
      w hw K hK volume ceiling where
  weighted_fiber_capacity := by
    intro key hkey
    have hsource :=
      coarseCanonicalRawPartitionSourceFiber_eqv_fixedRaw_mul_growingFiber
        (Q'.le_of_lt hw) K volume key
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource)
      (by
        simpa only [coarseRawPartitionTargetKeyWeight] using
          bound.weighted_fiber_cross key hkey)

def CoarseCanonicalRawPartitionFiberBound.toGrowingPhysicalFiberCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseCanonicalRawPartitionFiberBound
      w hw K hK volume ceiling) :
    CoarseGrowingPhysicalFiberCrossBound
      w hw K hK volume ceiling where
  weighted_fiber_cross := by
    intro key hkey
    have hsource :=
      coarseCanonicalRawPartitionSourceFiber_eqv_fixedRaw_mul_growingFiber
        (Q'.le_of_lt hw) K volume key
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource)
      (by
        simpa only [coarseRawPartitionTargetKeyWeight] using
          bound.weighted_fiber_capacity key hkey)

namespace CoarseCanonicalRawPartitionFiberBound

/-- The coarse weighted-fiber estimate still compiles to the exact crossed
raw-row/partition inequality. -/
theorem rawCross
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseCanonicalRawPartitionFiberBound
      w hw K hK volume ceiling) :
    fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
        growingHalfPhysicalPartition w K volume ≤
      (ceiling * growingHalfSpinOneRawRow
          w (Q'.le_of_lt hw) K volume) *
        fixedHalfPhysicalPartition w K := by
  let sourcePairs := fixedGrowingRawPartitionSourcePairs
    w (Q'.le_of_lt hw) K volume
  let sourceWeight := fixedGrowingRawPartitionSourceWeight w K volume
  let targetKeys := growingCompletionKeys
    w (Q'.le_of_lt hw) K volume
  let targetWeight := coarseRawPartitionTargetKeyWeight
    w (Q'.le_of_lt hw) K volume
  let repair := coarseCanonicalRawPartitionRepairKey
    w (Q'.le_of_lt hw) K volume
  let pushedWeight := fiberWeight sourcePairs sourceWeight repair
  have htotal :
      listQSum pushedWeight targetKeys ≈
        listQSum sourceWeight sourcePairs :=
    fiberWeight_total sourcePairs sourceWeight repair targetKeys
      (growingCompletionKeys_nodup
        w (Q'.le_of_lt hw) K volume)
      (by
        intro source hsource
        exact coarseCanonicalRawPartitionRepairKey_mem
          hw hK volume hsource)
  have hcapacity :
      listQSum pushedWeight targetKeys ≤
        listQSum (fun key => ceiling * targetWeight key)
          targetKeys := by
    apply listQSum_le_termwise_local
    intro key hkey
    exact bound.weighted_fiber_capacity key hkey
  have hsource := fixedGrowingRawPartitionSourceSum_eqv_cross
    (Q'.le_of_lt hw) K volume
  have htarget := coarseRawPartitionTargetKeySum_eqv_cross
    (Q'.le_of_lt hw) K volume
  have hfactor :
      listQSum (fun key => ceiling * targetWeight key) targetKeys ≈
        ceiling * listQSum targetWeight targetKeys :=
    listQSum_mul_left ceiling targetWeight targetKeys
  have hscaledTarget :
      listQSum (fun key => ceiling * targetWeight key) targetKeys ≈
        (ceiling * growingHalfSpinOneRawRow
          w (Q'.le_of_lt hw) K volume) *
            fixedHalfPhysicalPartition w K := by
    exact Q'.eqv_trans _ _ _ hfactor
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left ceiling _ _ htarget)
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv ceiling
            (growingHalfSpinOneRawRow
              w (Q'.le_of_lt hw) K volume)
            (fixedHalfPhysicalPartition w K))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal)
      (Q'.le_trans' _ _ _ hcapacity
        (Q'.le_of_eqv hscaledTarget)))

theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseCanonicalRawPartitionFiberBound
      w hw K hK volume ceiling) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≤
      ceiling *
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (volume + 1)
          (lowSpinCentralReferenceState volume) := by
  apply (fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference_iff_cross
    hw hK ceiling volume).mpr
  exact bound.rawCross

end CoarseCanonicalRawPartitionFiberBound

/-! ## 4. One coarse ceiling on the matched diagonal -/

structure MatchedDyadicCoarseCanonicalRawPartitionFiberBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  fiberBound : ∀ scale,
    CoarseCanonicalRawPartitionFiberBound
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale ceiling

namespace MatchedDyadicCoarseCanonicalRawPartitionFiberBound

theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicCoarseCanonicalRawPartitionFiberBound bridge)
    (scale : Nat) :
    centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (Q'.le_of_lt
          (matchedAllSpinWeight_pos family coupling scale))
        (matchedAllSpinCutoff family coupling scale) 0
        (centralLowerSpinCubeState 1) ≤
      bound.ceiling *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale)
          (scale + 1)
          (lowSpinCentralReferenceState scale) :=
  CoarseCanonicalRawPartitionFiberBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
      (bound.fiberBound scale)

end MatchedDyadicCoarseCanonicalRawPartitionFiberBound

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.growingCompletionKey_injective_on
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.growingCompletionKeyWeight_at_completion
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.coarseRawPartitionTargetKeyWeight_at_completion
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.coarseRawPartitionTargetKeySum_eqv_cross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.coarseCanonicalRawPartitionRepairKey_mem
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.coarseCanonicalRawPartitionSourceFiber_eqv_fixedRaw_mul_growingFiber
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.CoarseGrowingPhysicalFiberCrossBound.toRawPartitionFiberBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.CoarseCanonicalRawPartitionFiberBound.toGrowingPhysicalFiberCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.CoarseCanonicalRawPartitionFiberBound.rawCross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.CoarseCanonicalRawPartitionFiberBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair.MatchedDyadicCoarseCanonicalRawPartitionFiberBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
