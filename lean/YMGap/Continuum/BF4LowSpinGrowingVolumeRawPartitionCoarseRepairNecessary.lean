/-
# Necessary multiplicity for the coarse growing-physical repair

The coarse repair correctly retains the fixed normalization factor, but its
growing-physical inverse fibers are not small.  For every retained growing
completion, the fiber contains all `volume + 1` literal low-spin lower states.
The all-cutoff completion factorization makes each of those complete physical
terms exactly equal to the reference completion term.

This module compiles that observation into a necessary raw inequality for any
coarse fiber bound.  It is a diagnostic reduction, not an inhabitant or a
no-go for the coarse bound: the fixed spin-one marginal may itself vary along
the matched cutoff trajectory.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary

set_option maxRecDepth 500000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _first :: rest => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat rest.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant rest)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat rest.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv rest.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat rest.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat rest.length * constant) constant)

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum => hnot (CReal.pos_of_num_pos hnum))

private theorem exists_mem_pos_of_listQSum_pos_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (0 : Q') < listQSum value items →
        Exists fun item => item ∈ items ∧ (0 : Q') < value item
  | [], hsum => by
      have hnum := Q'.num_pos_of_pos hsum
      simp only [listQSum] at hnum
      exact False.elim (Int.lt_irrefl 0 hnum)
  | head :: tail, hsum => by
      by_cases hhead : (0 : Q') < value head
      · exact Exists.intro head ⟨List.mem_cons_self, hhead⟩
      · have hheadLe : value head ≤ 0 :=
          q_nonpos_of_not_pos_local hhead
        have hsumLe :
            value head + listQSum value tail ≤
              listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (value head) 0 (listQSum value tail) hheadLe
          simpa only [Q'.zero_add'] using hadd
        have htail : (0 : Q') < listQSum value tail := by
          change (0 : Q') <
            value head + listQSum value tail at hsum
          exact Q'.pos_of_lt_of_le hsum hsumLe
        rcases exists_mem_pos_of_listQSum_pos_local
            value tail htail with
          ⟨item, hitem, hitemPos⟩
        exact Exists.intro item
          ⟨List.mem_cons_of_mem head hitem, hitemPos⟩

/-! ## 1. Every low-spin lower state lies in the selected completion fiber -/

def lowSpinCompletionPhysical
    (volume : Nat) (lower : EdgeLabelling)
    (completion : EdgeLabelling × EdgeLabelling) : EdgeLabelling :=
  assembleReflectedSlabLabelling (volume + 1)
    lower completion.2 completion.1

private theorem lowSpinCentralLowerState_mem_K_local
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    {volume : Nat} {state : EdgeLabelling}
    (hstate : state ∈ lowSpinCentralLowerStates volume) :
    state ∈ centralHalfStates K (volume + 1) := by
  have hpositive :=
    (lowSpinCentralKPositiveRawReplication
      w hw K hK volume).replicas_mem state (by
        simpa only [lowSpinCentralKPositiveRawReplication] using hstate)
  exact (mem_centralPositiveHalfStates_iff.mp hpositive).1

theorem lowSpinCompletionPhysical_mem
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    {volume : Nat} {state : EdgeLabelling}
    (hstate : state ∈ lowSpinCentralLowerStates volume)
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1)) :
    lowSpinCompletionPhysical volume state completion ∈
      centralPhysicalPartitionStates K (volume + 1) := by
  have hparts :=
    (mem_cartesian_iff
      (centralPositiveHalfStates
        w (Q'.le_of_lt hw) K (volume + 1))
      (centralBoundaryChannels K (volume + 1)) completion).mp
      hcompletion
  unfold lowSpinCompletionPhysical centralPhysicalPartitionStates
  exact assembleReflectedSlabLabelling_mem_full
    (lowSpinCentralLowerState_mem_K_local hw hK hstate)
    hparts.2
    (mem_centralPositiveHalfStates_iff.mp hparts.1).1

theorem coarseGrowingPhysicalRepairKey_lowSpinCompletionPhysical
    {w : Q'} (hw : (0 : Q') < w) {K volume : Nat}
    {state : EdgeLabelling}
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1)) :
    coarseGrowingPhysicalRepairKey
        w (Q'.le_of_lt hw) K volume
        (lowSpinCompletionPhysical volume state completion) =
      growingCompletionKey K volume completion := by
  have hparts :=
    (mem_cartesian_iff
      (centralPositiveHalfStates
        w (Q'.le_of_lt hw) K (volume + 1))
      (centralBoundaryChannels K (volume + 1)) completion).mp
      hcompletion
  have htarget :=
    (mem_centralPositiveHalfStates_iff.mp hparts.1).1
  have htargetPos :=
    (mem_centralPositiveHalfStates_iff.mp hparts.1).2
  unfold coarseGrowingPhysicalRepairKey canonicalGrowingCompletion
    lowSpinCompletionPhysical
  rw [centralReflectedUpperRestriction_assemble htarget,
    if_pos htargetPos,
    centralBoundaryRestriction_assemble hparts.2]

theorem lowSpinCompletionPhysical_injective_on
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    {volume : Nat} {completion : EdgeLabelling × EdgeLabelling} :
    ∀ left, left ∈ lowSpinCentralLowerStates volume →
      ∀ right, right ∈ lowSpinCentralLowerStates volume →
        lowSpinCompletionPhysical volume left completion =
          lowSpinCompletionPhysical volume right completion →
        left = right := by
  intro left hleft right hright heq
  have hlower := congrArg (centralLowerRestriction (volume + 1)) heq
  simpa only [lowSpinCompletionPhysical,
    centralLowerRestriction_assemble
      (lowSpinCentralLowerState_mem_K_local hw hK hleft),
    centralLowerRestriction_assemble
      (lowSpinCentralLowerState_mem_K_local hw hK hright)] using hlower

theorem lowSpinCompletionPhysicalWeight_eqv_reference
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    {volume : Nat} {state : EdgeLabelling}
    (hstate : state ∈ lowSpinCentralLowerStates volume)
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1)) :
    centralPhysicalPartitionWeight w K (volume + 1)
        (lowSpinCompletionPhysical volume state completion) ≈
      centralPositiveCompletionWeight w K (volume + 1)
        (lowSpinCentralReferenceState volume) completion := by
  have hparts :=
    (mem_cartesian_iff
      (centralPositiveHalfStates
        w (Q'.le_of_lt hw) K (volume + 1))
      (centralBoundaryChannels K (volume + 1)) completion).mp
      hcompletion
  obtain ⟨index, _hindex, rfl⟩ := List.mem_map.mp hstate
  have heq := lowSpinCentralKAssembledTerm_eqv_between
    w hK index (lowSpinCentralReferenceIndex volume)
    completion.2 completion.1 hparts.2
    (mem_centralPositiveHalfStates_iff.mp hparts.1).1
  simpa only [centralPhysicalPartitionWeight,
    centralPositiveCompletionWeight, lowSpinCompletionPhysical,
    lowSpinCentralReferenceState] using heq

/-! ## 2. The growing physical fiber contains `volume + 1` equal terms -/

theorem replicatedCompletionMass_le_growingPhysicalRepairFiber
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1)) :
    Q'.ofNat (volume + 1) *
        centralPositiveCompletionWeight w K (volume + 1)
          (lowSpinCentralReferenceState volume) completion ≤
      coarseGrowingPhysicalRepairFiberWeight
        w (Q'.le_of_lt hw) K volume
        (growingCompletionKey K volume completion) := by
  let states := lowSpinCentralLowerStates volume
  let physicals := centralPhysicalPartitionStates K (volume + 1)
  let physicalWeight := centralPhysicalPartitionWeight
    w K (volume + 1)
  let repair := coarseGrowingPhysicalRepairKey
    w (Q'.le_of_lt hw) K volume
  let key := growingCompletionKey K volume completion
  let completionWeight := centralPositiveCompletionWeight
    w K (volume + 1) (lowSpinCentralReferenceState volume) completion
  let fiber := physicals.filter
    (fun physical => decide (key = repair physical))
  have hsum :
      listQSum (fun _state => completionWeight) states ≤
        listQSum physicalWeight fiber := by
    apply listQSum_le_of_injective_nodup
      states fiber (fun _state => completionWeight)
      physicalWeight
      (fun state => lowSpinCompletionPhysical volume state completion)
    · exact lowSpinCentralLowerStates_nodup volume
    · exact (centralPhysicalPartitionStates_nodup
        K (volume + 1)).filter _
    · intro state hstate
      apply List.mem_filter.mpr
      refine ⟨lowSpinCompletionPhysical_mem
          hw hK hstate hcompletion, ?_⟩
      apply decide_eq_true
      exact (coarseGrowingPhysicalRepairKey_lowSpinCompletionPhysical
        hw hcompletion).symm
    · intro left hleft right hright heq
      exact lowSpinCompletionPhysical_injective_on
        hw hK left hleft right hright heq
    · intro state hstate
      exact Q'.le_of_eqv (Q'.eqv_symm
        (lowSpinCompletionPhysicalWeight_eqv_reference
          hw hK hstate hcompletion))
    · intro physical _hphysical
      exact centralPhysicalPartitionWeight_nonnegative
        (Q'.le_of_lt hw) K (volume + 1) physical
  have hconstant := listQSum_const_local completionWeight states
  have hlength : states.length = volume + 1 := by
    simpa only [states] using lowSpinCentralLowerStates_length volume
  rw [hlength] at hconstant
  unfold coarseGrowingPhysicalRepairFiberWeight fiberWeight
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hconstant))
    hsum

/-! ## 3. Necessary fixed-marginal decay -/

namespace CoarseGrowingPhysicalFiberCrossBound

theorem count_mul_fixedRaw_le_ceiling_mul_fixedPartition_of_completion
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingPhysicalFiberCrossBound
      w hw K hK volume ceiling)
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1))
    (hcompletionPos : (0 : Q') <
      centralPositiveCompletionWeight w K (volume + 1)
        (lowSpinCentralReferenceState volume) completion) :
    Q'.ofNat (volume + 1) *
        fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K ≤
      ceiling * fixedHalfPhysicalPartition w K := by
  let count := Q'.ofNat (volume + 1)
  let fixedRaw := fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K
  let fixedPartition := fixedHalfPhysicalPartition w K
  let completionWeight := centralPositiveCompletionWeight
    w K (volume + 1) (lowSpinCentralReferenceState volume) completion
  let key := growingCompletionKey K volume completion
  let physicalFiber := coarseGrowingPhysicalRepairFiberWeight
    w (Q'.le_of_lt hw) K volume key
  have hkey : key ∈ growingCompletionKeys
      w (Q'.le_of_lt hw) K volume := by
    unfold key growingCompletionKeys
    exact List.mem_map.mpr ⟨completion, hcompletion, rfl⟩
  have hreplicated : count * completionWeight ≤ physicalFiber := by
    simpa only [count, completionWeight, physicalFiber, key] using
      replicatedCompletionMass_le_growingPhysicalRepairFiber
        hw hK volume hcompletion
  have hfixedRawNonnegative : (0 : Q') ≤ fixedRaw := by
    unfold fixedRaw fixedHalfSpinOneRawRow
    exact centralPhysicalPositiveRawRowMass_nonnegative
      (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1)
  have hscaled :
      fixedRaw * (count * completionWeight) ≤
        fixedRaw * physicalFiber :=
    Q'.mul_le_mul_of_nonneg_left _ _ fixedRaw
      hreplicated hfixedRawNonnegative
  have hcapacity := bound.weighted_fiber_cross key hkey
  have hkeyWeight := growingCompletionKeyWeight_at_completion
    hcompletion
  have htarget :
      ceiling *
          (growingCompletionKeyWeight
              w (Q'.le_of_lt hw) K volume key * fixedPartition) ≈
        ceiling * (completionWeight * fixedPartition) := by
    exact Q'.mul_eqv_congr_left ceiling _ _
      (Q'.mul_eqv_congr_right _ _ fixedPartition hkeyWeight)
  have hleftReorder :
      fixedRaw * (count * completionWeight) ≈
        completionWeight * (count * fixedRaw) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv fixedRaw (count * completionWeight))
      (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv count completionWeight fixedRaw)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left count _ _
            (Q'.mul_comm_eqv completionWeight fixedRaw))
          (Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv count fixedRaw completionWeight))
            (Q'.mul_comm_eqv
              (count * fixedRaw) completionWeight))))
  have hrightReorder :
      ceiling * (completionWeight * fixedPartition) ≈
        completionWeight * (ceiling * fixedPartition) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv ceiling
        (completionWeight * fixedPartition))
      (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv completionWeight fixedPartition ceiling)
        (Q'.mul_eqv_congr_left completionWeight _ _
          (Q'.mul_comm_eqv fixedPartition ceiling)))
  have hcancelReady :
      completionWeight * (count * fixedRaw) ≤
        completionWeight * (ceiling * fixedPartition) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleftReorder)
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ hcapacity
          (Q'.le_trans' _ _ _ (Q'.le_of_eqv htarget)
            (Q'.le_of_eqv hrightReorder))))
  have hcancel := Q'.le_of_mul_le_mul_left
    hcancelReady hcompletionPos
  simpa only [count, fixedRaw, fixedPartition] using hcancel

/-- Every coarse physical-fiber bound necessarily absorbs the literal
`volume + 1` low-spin multiplicity through the fixed spin-one normalization.
The positive completion used for cancellation is selected constructively from
the positive reference raw row. -/
theorem count_mul_fixedRaw_le_ceiling_mul_fixedPartition
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingPhysicalFiberCrossBound
      w hw K hK volume ceiling) :
    Q'.ofNat (volume + 1) *
        fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K ≤
      ceiling * fixedHalfPhysicalPartition w K := by
  let completionWeight := centralPositiveCompletionWeight
    w K (volume + 1) (lowSpinCentralReferenceState volume)
  let completions := centralPositiveCompletionPairs
    w (Q'.le_of_lt hw) K (volume + 1)
  have hreference :=
    (lowSpinCentralKPositiveRawReplication
      w hw K hK volume).reference_mem
  have hrawPos : (0 : Q') <
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) K (volume + 1)
        (lowSpinCentralReferenceState volume) :=
    centralPhysicalPositiveRawRowMass_pos hreference
  have hrow := centralPhysicalPositiveRawRowMass_eqv_completionSum
    (Q'.le_of_lt hw) K (volume + 1)
    (lowSpinCentralReferenceState volume)
  have hsumPos : (0 : Q') <
      listQSum completionWeight completions :=
    Q'.pos_of_lt_of_le hrawPos (Q'.le_of_eqv hrow)
  rcases exists_mem_pos_of_listQSum_pos_local
      completionWeight completions hsumPos with
    ⟨completion, hcompletion, hcompletionPos⟩
  exact count_mul_fixedRaw_le_ceiling_mul_fixedPartition_of_completion
    bound hcompletion hcompletionPos

/-- Normalized statement of the same necessary condition: a uniform coarse
ceiling must dominate `volume + 1` times the fixed-half spin-one marginal. -/
theorem count_mul_fixedMarginal_le_ceiling
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingPhysicalFiberCrossBound
      w hw K hK volume ceiling) :
    Q'.ofNat (volume + 1) *
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≤
      ceiling := by
  let count := Q'.ofNat (volume + 1)
  let raw := fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K
  let partition := fixedHalfPhysicalPartition w K
  have hpartition : (0 : Q') < partition := by
    unfold partition fixedHalfPhysicalPartition
    exact slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw) K (centralExtent 0)
  have hraw :=
    count_mul_fixedRaw_le_ceiling_mul_fixedPartition bound
  have hquotient : Q'.divPos (count * raw) partition hpartition ≤
      ceiling := by
    apply Q'.divPos_le_of_le_mul
    simpa only [count, raw, partition] using hraw
  have hmarginal :
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≈
        Q'.divPos raw partition hpartition := by
    have hrow :=
      centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
        (w := w) (hw := Q'.le_of_lt hw) (K := K) (half := 0)
        (source := centralLowerSpinCubeState 1)
        (centralLowerSpinCubeState_mem_centralHalfStates hK)
    simpa only [raw, partition, fixedHalfSpinOneRawRow,
      fixedHalfPhysicalPartition,
      centralPhysicalPositiveRawRowMass,
      centralPhysicalFiniteVacuumSectorPartitionReciprocal,
      Q'.divPos] using hrow
  have hscaled :
      count *
          centralPhysicalRowMarginal
            w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≈
        Q'.divPos (count * raw) partition hpartition := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left count _ _ hmarginal)
      (by
        unfold Q'.divPos
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv count raw
            (Q'.recipPos partition hpartition)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled) hquotient

end CoarseGrowingPhysicalFiberCrossBound

/-! ## 4. Matched-diagonal consequence -/

theorem matched_count_mul_fixedMarginal_le_ceiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicCoarseCanonicalRawPartitionFiberBound bridge)
    (scale : Nat) :
    Q'.ofNat (scale + 1) *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale) 0
          (centralLowerSpinCubeState 1) ≤
      bound.ceiling := by
  exact CoarseGrowingPhysicalFiberCrossBound.count_mul_fixedMarginal_le_ceiling
    ((bound.fiberBound scale).toGrowingPhysicalFiberCrossBound)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary.coarseGrowingPhysicalRepairKey_lowSpinCompletionPhysical
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary.lowSpinCompletionPhysicalWeight_eqv_reference
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary.replicatedCompletionMass_le_growingPhysicalRepairFiber
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary.CoarseGrowingPhysicalFiberCrossBound.count_mul_fixedRaw_le_ceiling_mul_fixedPartition
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary.CoarseGrowingPhysicalFiberCrossBound.count_mul_fixedMarginal_le_ceiling
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary.matched_count_mul_fixedMarginal_le_ceiling
