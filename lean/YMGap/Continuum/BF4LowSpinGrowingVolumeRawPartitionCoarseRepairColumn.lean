/-
# Exact completion columns for the coarse growing-physical repair

The coarse repair fiber is initially presented as a filtered sum over full
growing slabs.  This module reindexes that fiber at every retained completion:
it is exactly the column obtained by fixing the reflected-upper target and
boundary channel and summing the complete physical term over all lower
states.

The fallback branch in `canonicalGrowingCompletion` causes no extra mass.
When the reflected-upper row is not positive, symmetry and nonnegativity of
the normalized joint law force every associated physical term to be zero.

This is a finite structural reduction.  It does not prove a uniform column
Harnack estimate, spin-ray compression, a cofinal gap, a continuum limit, or
the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairNecessary

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn

set_option maxRecDepth 500000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepair
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail
            (fun tailItem _ => hvalue tailItem))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe : listQSum value tail ≤
            value head + listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ ih htailLe

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → predicate item = false →
        value item ≈ 0) →
      listQSum value items ≈
        listQSum value (items.filter predicate)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail := listQSum_eq_filter_of_zero_local
        value predicate tail
        (fun item hitem =>
          hzero item (List.mem_cons_of_mem head hitem))
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr_left (value head) _ _ htail)
            (Q'.eqv_trans _ _ _
              (Q'.add_eqv_congr_right _ _ _
                (hzero head List.mem_cons_self hp))
              (Q'.eqv_of_eq (Q'.zero_add' _)))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr_left (value head) _ _ htail

/-! ## 1. The literal completion column -/

/-- Fix a positive reflected-upper target and boundary channel, then sum the
complete physical term over every bounded lower state. -/
def growingCompletionColumnWeight
    (w : Q') (K volume : Nat)
    (completion : EdgeLabelling × EdgeLabelling) : Q' :=
  listQSum
    (fun lower =>
      centralPositiveCompletionWeight
        w K (volume + 1) lower completion)
    (centralHalfStates K (volume + 1))

theorem growingCompletionColumnWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat)
    (completion : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤
      growingCompletionColumnWeight w K volume completion := by
  unfold growingCompletionColumnWeight
  apply listQSum_nonnegative_on
  intro lower _hlower
  exact centralPositiveCompletionWeight_nonnegative
    hw K (volume + 1) lower completion

/-! ## 2. Exceptional upper rows carry no physical weight -/

/-- If the reflected-upper restriction has no positive normalized row, the
individual full-slab physical term is exactly zero.  This justifies the
fallback branch of the canonical completion repair at the weight level. -/
theorem centralPhysicalPartitionWeight_eqv_zero_of_upper_not_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K half : Nat}
    {physical : EdgeLabelling}
    (hphysical : physical ∈ centralPhysicalPartitionStates K half)
    (hnot : ¬ (0 : Q') <
      centralPhysicalRowMarginal w hw K half
        (centralReflectedUpperRestriction half physical)) :
    centralPhysicalPartitionWeight w K half physical ≈ 0 := by
  have hphysical' : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half)) := by
    simpa only [centralPhysicalPartitionStates] using hphysical
  let lower := centralLowerRestriction half physical
  let upper := centralReflectedUpperRestriction half physical
  let boundary := centralBoundaryRestriction half physical
  have hlower : lower ∈ centralHalfStates K half := by
    unfold lower centralHalfStates
    exact centralLowerRestriction_mem hphysical'
  have hupper : upper ∈ centralHalfStates K half := by
    unfold upper centralHalfStates
    exact centralReflectedUpperRestriction_mem hphysical'
  have hboundary : boundary ∈ centralBoundaryChannels K half := by
    unfold boundary centralBoundaryChannels
    exact centralBoundaryRestriction_mem hphysical'
  have htermLeKernel :
      centralPhysicalPartitionWeight w K half physical ≤
        centralPhysicalReflectedKernel w K half lower upper := by
    unfold centralPhysicalPartitionWeight centralPhysicalReflectedKernel
    rw [← assembleReflectedSlabLabelling_restrictions hphysical']
    exact listQSum_member_le_nonnegative_local
      (fun fixed =>
        slabParametricKPhysicalTerm w K (centralExtent half)
          (assembleReflectedSlabLabelling half lower fixed upper))
      (fun fixed =>
        slabParametricKPhysicalTerm_nonnegative hw K
          (centralExtent half)
          (assembleReflectedSlabLabelling half lower fixed upper))
      (centralBoundaryChannels K half) hboundary
  let partition := slabParametricKPhysicalPartition
    w K (centralExtent half)
  let hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos hw K (centralExtent half)
  let reciprocal := Q'.recipPos partition hpartition
  have hreciprocal : (0 : Q') < reciprocal :=
    Q'.recipPos_pos partition hpartition
  have hscaled :
      centralPhysicalPartitionWeight w K half physical * reciprocal ≤
        centralPhysicalReflectedKernel w K half lower upper * reciprocal :=
    Q'.mul_le_mul_of_nonneg_right _ _ reciprocal htermLeKernel
      (Q'.le_of_lt hreciprocal)
  have hnormalized :
      centralPhysicalReflectedKernel w K half lower upper * reciprocal ≈ 0 := by
    have hzero :=
      centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
        hlower hupper hnot
    simpa only [centralNormalizedPhysicalReflectedKernel,
      Q'.divPos, partition, reciprocal, lower, upper] using hzero
  have hscaledZero :
      centralPhysicalPartitionWeight w K half physical * reciprocal ≤ 0 :=
    Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hnormalized)
  have hcancelReady :
      reciprocal * centralPhysicalPartitionWeight w K half physical ≤
        reciprocal * 0 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv reciprocal
          (centralPhysicalPartitionWeight w K half physical)))
      (Q'.le_trans' _ _ _ hscaledZero
        (Q'.le_of_eqv
          (Q'.eqv_symm (Q'.mul_zero_eqv reciprocal))))
  have hnonpositive :
      centralPhysicalPartitionWeight w K half physical ≤ 0 :=
    Q'.le_of_mul_le_mul_left hcancelReady hreciprocal
  exact Q'.eqv_of_le_le hnonpositive
    (centralPhysicalPartitionWeight_nonnegative hw K half physical)

/-! ## 3. A retained repair key recovers its literal completion -/

private theorem physicalCompletion_eq_of_mem_positiveRepairFiber
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs w hw K (volume + 1))
    {physical : EdgeLabelling}
    (hphysical : physical ∈
      centralPhysicalPartitionStates K (volume + 1))
    (hkey : decide
      (growingCompletionKey K volume completion =
        coarseGrowingPhysicalRepairKey w hw K volume physical) = true)
    (hpositive : (0 : Q') <
      centralPhysicalRowMarginal w hw K (volume + 1)
        (centralReflectedUpperRestriction (volume + 1) physical)) :
    (centralReflectedUpperRestriction (volume + 1) physical,
      centralBoundaryRestriction (volume + 1) physical) = completion := by
  have hphysical' : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent (volume + 1))) := by
    simpa only [centralPhysicalPartitionStates] using hphysical
  let actual : EdgeLabelling × EdgeLabelling :=
    (centralReflectedUpperRestriction (volume + 1) physical,
      centralBoundaryRestriction (volume + 1) physical)
  have hactual : actual ∈
      centralPositiveCompletionPairs w hw K (volume + 1) := by
    apply (mem_cartesian_iff _ _ _).mpr
    refine ⟨mem_centralPositiveHalfStates_iff.mpr ⟨?_, hpositive⟩, ?_⟩
    · simpa only [actual, centralHalfStates] using
        centralReflectedUpperRestriction_mem hphysical'
    · simpa only [actual, centralBoundaryChannels] using
        centralBoundaryRestriction_mem hphysical'
  have hrepair :
      coarseGrowingPhysicalRepairKey w hw K volume physical =
        growingCompletionKey K volume actual := by
    unfold coarseGrowingPhysicalRepairKey canonicalGrowingCompletion
    rw [if_pos hpositive]
  have hkeyEq :
      growingCompletionKey K volume completion =
        growingCompletionKey K volume actual := by
    exact (of_decide_eq_true hkey).trans hrepair
  have heq := growingCompletionKey_injective_on
    hcompletion hactual hkeyEq
  simpa only [actual] using heq.symm

/-! ## 4. Exact reindexing of the coarse physical fiber -/

private theorem centralLowerRestriction_injective_on_positiveRepairFiber
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs w hw K (volume + 1))
    {left right : EdgeLabelling}
    (hleftPhysical : left ∈
      centralPhysicalPartitionStates K (volume + 1))
    (hleftKey : decide
      (growingCompletionKey K volume completion =
        coarseGrowingPhysicalRepairKey w hw K volume left) = true)
    (hleftPos : (0 : Q') <
      centralPhysicalRowMarginal w hw K (volume + 1)
        (centralReflectedUpperRestriction (volume + 1) left))
    (hrightPhysical : right ∈
      centralPhysicalPartitionStates K (volume + 1))
    (hrightKey : decide
      (growingCompletionKey K volume completion =
        coarseGrowingPhysicalRepairKey w hw K volume right) = true)
    (hrightPos : (0 : Q') <
      centralPhysicalRowMarginal w hw K (volume + 1)
        (centralReflectedUpperRestriction (volume + 1) right))
    (hlower : centralLowerRestriction (volume + 1) left =
      centralLowerRestriction (volume + 1) right) :
    left = right := by
  let half := volume + 1
  have hleftCompletion :=
    physicalCompletion_eq_of_mem_positiveRepairFiber
      hcompletion hleftPhysical hleftKey hleftPos
  have hrightCompletion :=
    physicalCompletion_eq_of_mem_positiveRepairFiber
      hcompletion hrightPhysical hrightKey hrightPos
  have hleftFull : left ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half)) := by
    simpa only [half, centralPhysicalPartitionStates] using hleftPhysical
  have hrightFull : right ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half)) := by
    simpa only [half, centralPhysicalPartitionStates] using hrightPhysical
  rw [← assembleReflectedSlabLabelling_restrictions hleftFull,
    ← assembleReflectedSlabLabelling_restrictions hrightFull,
    hlower]
  rw [show centralBoundaryRestriction half left = completion.2 by
        exact congrArg Prod.snd hleftCompletion,
    show centralReflectedUpperRestriction half left = completion.1 by
        exact congrArg Prod.fst hleftCompletion,
    show centralBoundaryRestriction half right = completion.2 by
        exact congrArg Prod.snd hrightCompletion,
    show centralReflectedUpperRestriction half right = completion.1 by
        exact congrArg Prod.fst hrightCompletion]

private theorem centralPhysicalPartitionWeight_eqv_completionWeight_of_positiveRepairFiber
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs w hw K (volume + 1))
    {physical : EdgeLabelling}
    (hphysical : physical ∈
      centralPhysicalPartitionStates K (volume + 1))
    (hkey : decide
      (growingCompletionKey K volume completion =
        coarseGrowingPhysicalRepairKey w hw K volume physical) = true)
    (hpositive : (0 : Q') <
      centralPhysicalRowMarginal w hw K (volume + 1)
        (centralReflectedUpperRestriction (volume + 1) physical)) :
    centralPhysicalPartitionWeight w K (volume + 1) physical ≈
      centralPositiveCompletionWeight w K (volume + 1)
        (centralLowerRestriction (volume + 1) physical) completion := by
  let half := volume + 1
  have hcompletionEq :=
    physicalCompletion_eq_of_mem_positiveRepairFiber
      hcompletion hphysical hkey hpositive
  have hfull : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent half)) := by
    simpa only [half, centralPhysicalPartitionStates] using hphysical
  have hrecovery := assembleReflectedSlabLabelling_restrictions hfull
  have hphysicalEq : physical =
      assembleReflectedSlabLabelling half
        (centralLowerRestriction half physical)
        completion.2 completion.1 := by
    exact Eq.trans hrecovery.symm (by
      rw [show centralBoundaryRestriction half physical = completion.2 by
            exact congrArg Prod.snd hcompletionEq,
        show centralReflectedUpperRestriction half physical = completion.1 by
            exact congrArg Prod.fst hcompletionEq])
  unfold centralPhysicalPartitionWeight centralPositiveCompletionWeight
  exact Q'.eqv_of_eq (congrArg
    (slabParametricKPhysicalTerm w K (centralExtent (volume + 1)))
    (by simpa only [half] using hphysicalEq))

/-- Every lower-state term in a retained completion column occurs in the
corresponding concrete repair fiber. -/
theorem completionColumn_le_coarseGrowingPhysicalRepairFiberWeight
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (_hK : 1 ≤ K)
    (volume : Nat) {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1)) :
    growingCompletionColumnWeight w K volume completion ≤
      coarseGrowingPhysicalRepairFiberWeight
        w (Q'.le_of_lt hw) K volume
        (growingCompletionKey K volume completion) := by
  let half := volume + 1
  let hw0 := Q'.le_of_lt hw
  let lowers := centralHalfStates K half
  let physicals := centralPhysicalPartitionStates K half
  let physicalWeight := centralPhysicalPartitionWeight w K half
  let repair := coarseGrowingPhysicalRepairKey w hw0 K volume
  let key := growingCompletionKey K volume completion
  let fiber := physicals.filter
    (fun physical => decide (key = repair physical))
  let columnWeight := fun lower =>
    centralPositiveCompletionWeight w K half lower completion
  have hcolumnLeFiber := listQSum_le_of_injective_nodup
    lowers fiber columnWeight physicalWeight
    (fun lower =>
      assembleReflectedSlabLabelling
        half lower completion.2 completion.1)
    (centralHalfStates_nodup K half)
    ((centralPhysicalPartitionStates_nodup K half).filter _)
    (by
      intro lower hlower
      have hparts := (mem_cartesian_iff
        (centralPositiveHalfStates w hw0 K half)
        (centralBoundaryChannels K half) completion).mp hcompletion
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · unfold physicals half centralPhysicalPartitionStates
        exact assembleReflectedSlabLabelling_mem_full
          hlower hparts.2
          (mem_centralPositiveHalfStates_iff.mp hparts.1).1
      · apply decide_eq_true
        unfold key repair coarseGrowingPhysicalRepairKey
          canonicalGrowingCompletion
        rw [centralReflectedUpperRestriction_assemble
              (mem_centralPositiveHalfStates_iff.mp hparts.1).1,
          if_pos (mem_centralPositiveHalfStates_iff.mp hparts.1).2,
          centralBoundaryRestriction_assemble hparts.2])
    (by
      intro left hleft right hright heq
      have hlower := congrArg (centralLowerRestriction half) heq
      simpa only [centralLowerRestriction_assemble hleft,
        centralLowerRestriction_assemble hright] using hlower)
    (by
      intro lower _hlower
      exact Q'.le_of_eqv (Q'.eqv_refl _))
    (by
      intro physical _hphysical
      exact centralPhysicalPartitionWeight_nonnegative
        hw0 K half physical)
  unfold growingCompletionColumnWeight
    coarseGrowingPhysicalRepairFiberWeight fiberWeight
  exact hcolumnLeFiber

/-- Conversely, after removing the zero-support fallback states, lower
restriction injects a concrete repair fiber into its completion column. -/
theorem coarseGrowingPhysicalRepairFiberWeight_le_completionColumn
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (_hK : 1 ≤ K)
    (volume : Nat) {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1)) :
    coarseGrowingPhysicalRepairFiberWeight
        w (Q'.le_of_lt hw) K volume
        (growingCompletionKey K volume completion) ≤
      growingCompletionColumnWeight w K volume completion := by
  let half := volume + 1
  let hw0 := Q'.le_of_lt hw
  let lowers := centralHalfStates K half
  let physicals := centralPhysicalPartitionStates K half
  let physicalWeight := centralPhysicalPartitionWeight w K half
  let repair := coarseGrowingPhysicalRepairKey w hw0 K volume
  let key := growingCompletionKey K volume completion
  let fiber := physicals.filter
    (fun physical => decide (key = repair physical))
  let positiveFiber := fiber.filter
    (fun physical => decide ((0 : Q') <
      centralPhysicalRowMarginal w hw0 K half
        (centralReflectedUpperRestriction half physical)))
  let columnWeight := fun lower =>
    centralPositiveCompletionWeight w K half lower completion
  have hfiberEqPositive :
      listQSum physicalWeight fiber ≈
        listQSum physicalWeight positiveFiber := by
    unfold positiveFiber
    apply listQSum_eq_filter_of_zero_local
    intro physical hphysical hfalse
    have hparts := List.mem_filter.mp hphysical
    have hnot : ¬ (0 : Q') <
        centralPhysicalRowMarginal w hw0 K half
          (centralReflectedUpperRestriction half physical) := by
      simpa only [decide_eq_false_iff_not] using hfalse
    exact centralPhysicalPartitionWeight_eqv_zero_of_upper_not_pos
      hparts.1 hnot
  have hpositiveLeColumn :
      listQSum physicalWeight positiveFiber ≤
        listQSum columnWeight lowers := by
    apply listQSum_le_of_injective_nodup
      positiveFiber lowers physicalWeight columnWeight
      (centralLowerRestriction half)
    · exact ((centralPhysicalPartitionStates_nodup K half).filter _).filter _
    · exact centralHalfStates_nodup K half
    · intro physical hphysical
      have houter := List.mem_filter.mp hphysical
      have hbase := (List.mem_filter.mp houter.1).1
      have hbase' : physical ∈ boundedEdgeLabellings K
          (slabPhysicalFaceEdges (centralExtent half)) := by
        simpa only [physicals, centralPhysicalPartitionStates] using hbase
      unfold lowers centralHalfStates
      exact centralLowerRestriction_mem hbase'
    · intro left hleft right hright hlower
      have hleftOuter := List.mem_filter.mp hleft
      have hrightOuter := List.mem_filter.mp hright
      have hleftFiber := List.mem_filter.mp hleftOuter.1
      have hrightFiber := List.mem_filter.mp hrightOuter.1
      have hleftPos : (0 : Q') <
          centralPhysicalRowMarginal w hw0 K half
            (centralReflectedUpperRestriction half left) := by
        simpa only [decide_eq_true_eq] using hleftOuter.2
      have hrightPos : (0 : Q') <
          centralPhysicalRowMarginal w hw0 K half
            (centralReflectedUpperRestriction half right) := by
        simpa only [decide_eq_true_eq] using hrightOuter.2
      exact centralLowerRestriction_injective_on_positiveRepairFiber
        hcompletion hleftFiber.1 hleftFiber.2 hleftPos
        hrightFiber.1 hrightFiber.2 hrightPos hlower
    · intro physical hphysical
      have houter := List.mem_filter.mp hphysical
      have hfiberParts := List.mem_filter.mp houter.1
      have hpositive : (0 : Q') <
          centralPhysicalRowMarginal w hw0 K half
            (centralReflectedUpperRestriction half physical) := by
        simpa only [decide_eq_true_eq] using houter.2
      exact Q'.le_of_eqv
        (centralPhysicalPartitionWeight_eqv_completionWeight_of_positiveRepairFiber
          hcompletion hfiberParts.1 hfiberParts.2 hpositive)
    · intro lower _hlower
      exact centralPositiveCompletionWeight_nonnegative
        hw0 K half lower completion
  unfold coarseGrowingPhysicalRepairFiberWeight fiberWeight
    growingCompletionColumnWeight
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfiberEqPositive)
    hpositiveLeColumn

/-- At every positive completion, the concrete coarse repair fiber is exactly
the full lower-state completion column. -/
theorem coarseGrowingPhysicalRepairFiberWeight_eqv_completionColumn
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1)) :
    coarseGrowingPhysicalRepairFiberWeight
        w (Q'.le_of_lt hw) K volume
        (growingCompletionKey K volume completion) ≈
      growingCompletionColumnWeight w K volume completion := by
  exact Q'.eqv_of_le_le
    (coarseGrowingPhysicalRepairFiberWeight_le_completionColumn
      hw hK volume hcompletion)
    (completionColumn_le_coarseGrowingPhysicalRepairFiberWeight
      hw hK volume hcompletion)

/-! ## 5. The exact column-Harnack producer -/

/-- The remaining coarse producer written on literal completion columns.
This is equivalent to `CoarseGrowingPhysicalFiberCrossBound`, but exposes the
analytic content without a filtered full-slab repair fiber. -/
structure CoarseGrowingCompletionColumnCrossBound
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (ceiling : Q') : Type where
  weighted_column_cross : ∀ completion,
    completion ∈ centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1) →
      fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
          growingCompletionColumnWeight w K volume completion ≤
        ceiling *
          (centralPositiveCompletionWeight w K (volume + 1)
              (lowSpinCentralReferenceState volume) completion *
            fixedHalfPhysicalPartition w K)

def CoarseGrowingCompletionColumnCrossBound.toPhysicalFiberCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingCompletionColumnCrossBound
      w hw K hK volume ceiling) :
    CoarseGrowingPhysicalFiberCrossBound
      w hw K hK volume ceiling where
  weighted_fiber_cross := by
    intro key hkey
    obtain ⟨completion, hcompletion, rfl⟩ := List.mem_map.mp hkey
    have hfiber :=
      coarseGrowingPhysicalRepairFiberWeight_eqv_completionColumn
        hw hK volume hcompletion
    have hkeyWeight := growingCompletionKeyWeight_at_completion hcompletion
    have hleft :
        fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
            coarseGrowingPhysicalRepairFiberWeight
              w (Q'.le_of_lt hw) K volume
              (growingCompletionKey K volume completion) ≈
          fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
            growingCompletionColumnWeight w K volume completion :=
      Q'.mul_eqv_congr_left _ _ _ hfiber
    have hright :
        ceiling *
            (centralPositiveCompletionWeight w K (volume + 1)
                (lowSpinCentralReferenceState volume) completion *
              fixedHalfPhysicalPartition w K) ≈
          ceiling *
            (growingCompletionKeyWeight
                w (Q'.le_of_lt hw) K volume
                (growingCompletionKey K volume completion) *
              fixedHalfPhysicalPartition w K) := by
      exact Q'.mul_eqv_congr_left ceiling _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hkeyWeight))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _
        (bound.weighted_column_cross completion hcompletion)
        (Q'.le_of_eqv hright))

def CoarseGrowingPhysicalFiberCrossBound.toCompletionColumnCrossBound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CoarseGrowingPhysicalFiberCrossBound
      w hw K hK volume ceiling) :
    CoarseGrowingCompletionColumnCrossBound
      w hw K hK volume ceiling where
  weighted_column_cross := by
    intro completion hcompletion
    have hfiber :=
      coarseGrowingPhysicalRepairFiberWeight_eqv_completionColumn
        hw hK volume hcompletion
    have hcapacity := bound.weighted_fiber_cross
      (growingCompletionKey K volume completion)
      (by
        unfold growingCompletionKeys
        exact List.mem_map.mpr ⟨completion, hcompletion, rfl⟩)
    have hkeyWeight := growingCompletionKeyWeight_at_completion hcompletion
    have hleft :
        fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
            growingCompletionColumnWeight w K volume completion ≈
          fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
            coarseGrowingPhysicalRepairFiberWeight
              w (Q'.le_of_lt hw) K volume
              (growingCompletionKey K volume completion) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hfiber)
    have hright :
        ceiling *
            (growingCompletionKeyWeight
                w (Q'.le_of_lt hw) K volume
                (growingCompletionKey K volume completion) *
              fixedHalfPhysicalPartition w K) ≈
          ceiling *
            (centralPositiveCompletionWeight w K (volume + 1)
                (lowSpinCentralReferenceState volume) completion *
              fixedHalfPhysicalPartition w K) := by
      exact Q'.mul_eqv_congr_left ceiling _ _
        (Q'.mul_eqv_congr_right _ _ _ hkeyWeight)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hcapacity (Q'.le_of_eqv hright))

/-! ## 6. Matched-diagonal equivalence -/

structure MatchedDyadicCoarseGrowingCompletionColumnCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  columnBound : ∀ scale,
    CoarseGrowingCompletionColumnCrossBound
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale ceiling

def MatchedDyadicCoarseGrowingCompletionColumnCrossBound.toRawPartitionFiberBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound : MatchedDyadicCoarseGrowingCompletionColumnCrossBound bridge) :
    MatchedDyadicCoarseCanonicalRawPartitionFiberBound bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  fiberBound := fun scale =>
    ((bound.columnBound scale).toPhysicalFiberCrossBound).toRawPartitionFiberBound

def MatchedDyadicCoarseCanonicalRawPartitionFiberBound.toCompletionColumnCrossBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge : MatchedDyadicSameActionAFBridge
      family law spacing coupling}
    (bound : MatchedDyadicCoarseCanonicalRawPartitionFiberBound bridge) :
    MatchedDyadicCoarseGrowingCompletionColumnCrossBound bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  columnBound := fun scale =>
    CoarseGrowingPhysicalFiberCrossBound.toCompletionColumnCrossBound
      ((bound.fiberBound scale).toGrowingPhysicalFiberCrossBound)

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn.centralPhysicalPartitionWeight_eqv_zero_of_upper_not_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn.coarseGrowingPhysicalRepairFiberWeight_eqv_completionColumn
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn.CoarseGrowingCompletionColumnCrossBound.toPhysicalFiberCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn.CoarseGrowingPhysicalFiberCrossBound.toCompletionColumnCrossBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn.MatchedDyadicCoarseGrowingCompletionColumnCrossBound.toRawPartitionFiberBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCoarseRepairColumn.MatchedDyadicCoarseCanonicalRawPartitionFiberBound.toCompletionColumnCrossBound
