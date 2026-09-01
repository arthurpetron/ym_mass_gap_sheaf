/-
# Weighted-fiber raw-row/partition switching gate

The injective raw-row/partition switch is a useful but strong sufficient
producer.  A physically natural repair may merge many light configurations
into one target while controlling their total inverse-fiber weight.  This
module recodes the crossed configuration lists by occurrence indices and
states exactly that weaker constructive producer.

For every displayed target occurrence, the complete source weight repaired
to it is bounded by `ceiling` times that target occurrence's weight.  Exact
finite pushforward/Fubini summation gives the same raw cross inequality and
the same matched diagonal spin-one comparison as the injective compiler.

The weighted repair data are intentionally not inhabited here.  No bound for
the remaining spin ray, all-vector gap, continuum limit, or Clay theorem is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
import YMGap.Continuum.FiniteListIndexQuadraticBridge

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate

set_option maxRecDepth 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem range_nodup_local : ∀ count : Nat,
    (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          by
            intro value hvalue last hlast heq
            have hvalueLt : value < count := List.mem_range.mp hvalue
            have hlastEq : last = count := List.mem_singleton.mp hlast
            have hvalueEq : value = count := heq.trans hlastEq
            omega⟩

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

/-! ## 1. Occurrence-indexed crossed carriers -/

def rawPartitionPairFallback :
    (EdgeLabelling × EdgeLabelling) × EdgeLabelling :=
  ((zeroEdgeLabelling, zeroEdgeLabelling), zeroEdgeLabelling)

def fixedGrowingRawPartitionSourceIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) : List Nat :=
  List.range
    (fixedGrowingRawPartitionSourcePairs w hw K volume).length

def fixedGrowingRawPartitionTargetIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) : List Nat :=
  List.range
    (fixedGrowingRawPartitionTargetPairs w hw K volume).length

def fixedGrowingRawPartitionSourceIndexWeight
    (w : Q') (hw : (0 : Q') ≤ w) (K volume index : Nat) : Q' :=
  fixedGrowingRawPartitionSourceWeight w K volume
    (finiteListStateAt
      (fixedGrowingRawPartitionSourcePairs w hw K volume)
      rawPartitionPairFallback index)

def fixedGrowingRawPartitionTargetIndexWeight
    (w : Q') (hw : (0 : Q') ≤ w) (K volume index : Nat) : Q' :=
  fixedGrowingRawPartitionTargetWeight w K volume
    (finiteListStateAt
      (fixedGrowingRawPartitionTargetPairs w hw K volume)
      rawPartitionPairFallback index)

theorem fixedGrowingRawPartitionSourceIndices_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    (fixedGrowingRawPartitionSourceIndices w hw K volume).Nodup := by
  unfold fixedGrowingRawPartitionSourceIndices
  exact range_nodup_local _

theorem fixedGrowingRawPartitionTargetIndices_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    (fixedGrowingRawPartitionTargetIndices w hw K volume).Nodup := by
  unfold fixedGrowingRawPartitionTargetIndices
  exact range_nodup_local _

/-- Occurrence recoding preserves the exact crossed source sum. -/
theorem fixedGrowingRawPartitionSourceIndexSum_eqv_cross
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat) :
    listQSum
        (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
        (fixedGrowingRawPartitionSourceIndices w hw K volume) ≈
      fixedHalfSpinOneRawRow w hw K *
        growingHalfPhysicalPartition w K volume := by
  have hindex := finiteIndexSum_eq_listQSum
    (fixedGrowingRawPartitionSourcePairs w hw K volume)
    rawPartitionPairFallback
    (fixedGrowingRawPartitionSourceWeight w K volume)
  have hcross := fixedGrowingRawPartitionSourceSum_eqv_cross
    hw K volume
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (by
      simpa only [fixedGrowingRawPartitionSourceIndices,
        fixedGrowingRawPartitionSourceIndexWeight] using hindex))
    hcross

/-- Occurrence recoding preserves the exact crossed target sum. -/
theorem fixedGrowingRawPartitionTargetIndexSum_eqv_cross
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat) :
    listQSum
        (fixedGrowingRawPartitionTargetIndexWeight w hw K volume)
        (fixedGrowingRawPartitionTargetIndices w hw K volume) ≈
      growingHalfSpinOneRawRow w hw K volume *
        fixedHalfPhysicalPartition w K := by
  have hindex := finiteIndexSum_eq_listQSum
    (fixedGrowingRawPartitionTargetPairs w hw K volume)
    rawPartitionPairFallback
    (fixedGrowingRawPartitionTargetWeight w K volume)
  have hcross := fixedGrowingRawPartitionTargetSum_eqv_cross
    hw K volume
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_of_eq (by
      simpa only [fixedGrowingRawPartitionTargetIndices,
        fixedGrowingRawPartitionTargetIndexWeight] using hindex))
    hcross

/-! ## 2. Weighted inverse-fiber producer -/

/-- A deterministic occurrence-index repair whose entire weighted inverse
fiber fits under one scaled target occurrence.  Unlike the injection gate,
many source occurrences may share a target. -/
structure LowSpinFixedGrowingRawPartitionFiberSwitching
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (ceiling : Q') : Type where
  repair : Nat → Nat
  repair_mem : ∀ source,
    source ∈ fixedGrowingRawPartitionSourceIndices w hw K volume →
      repair source ∈
        fixedGrowingRawPartitionTargetIndices w hw K volume
  weighted_fiber_capacity : ∀ target,
    target ∈ fixedGrowingRawPartitionTargetIndices w hw K volume →
      fiberWeight
          (fixedGrowingRawPartitionSourceIndices w hw K volume)
          (fixedGrowingRawPartitionSourceIndexWeight w hw K volume)
          repair target ≤
        ceiling *
          fixedGrowingRawPartitionTargetIndexWeight
            w hw K volume target

namespace LowSpinFixedGrowingRawPartitionFiberSwitching

/-- Weighted inverse-fiber capacity compiles to the exact raw cross
inequality without an unweighted congestion or carrier-cardinality loss. -/
theorem rawCross
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat} {ceiling : Q'}
    (switching :
      LowSpinFixedGrowingRawPartitionFiberSwitching
        w hw K volume ceiling) :
    fixedHalfSpinOneRawRow w hw K *
        growingHalfPhysicalPartition w K volume ≤
      (ceiling * growingHalfSpinOneRawRow w hw K volume) *
        fixedHalfPhysicalPartition w K := by
  let sourceIndices :=
    fixedGrowingRawPartitionSourceIndices w hw K volume
  let targetIndices :=
    fixedGrowingRawPartitionTargetIndices w hw K volume
  let sourceWeight :=
    fixedGrowingRawPartitionSourceIndexWeight w hw K volume
  let targetWeight :=
    fixedGrowingRawPartitionTargetIndexWeight w hw K volume
  let pushedWeight :=
    fiberWeight sourceIndices sourceWeight switching.repair
  have htotal :
      listQSum pushedWeight targetIndices ≈
        listQSum sourceWeight sourceIndices :=
    fiberWeight_total
      sourceIndices sourceWeight switching.repair targetIndices
      (fixedGrowingRawPartitionTargetIndices_nodup
        w hw K volume)
      switching.repair_mem
  have hcapacity :
      listQSum pushedWeight targetIndices ≤
        listQSum (fun target => ceiling * targetWeight target)
          targetIndices := by
    apply listQSum_le_termwise_local
    intro target htarget
    exact switching.weighted_fiber_capacity target htarget
  have hsource := fixedGrowingRawPartitionSourceIndexSum_eqv_cross
    hw K volume
  have htarget := fixedGrowingRawPartitionTargetIndexSum_eqv_cross
    hw K volume
  have hfactor :
      listQSum (fun target => ceiling * targetWeight target)
          targetIndices ≈
        ceiling * listQSum targetWeight targetIndices :=
    listQSum_mul_left ceiling targetWeight targetIndices
  have hscaledTarget :
      listQSum (fun target => ceiling * targetWeight target)
          targetIndices ≈
        (ceiling * growingHalfSpinOneRawRow w hw K volume) *
          fixedHalfPhysicalPartition w K := by
    exact Q'.eqv_trans _ _ _ hfactor
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left ceiling _ _ htarget)
        (Q'.eqv_symm (Q'.mul_assoc_eqv ceiling
          (growingHalfSpinOneRawRow w hw K volume)
          (fixedHalfPhysicalPartition w K))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal)
      (Q'.le_trans' _ _ _ hcapacity
        (Q'.le_of_eqv hscaledTarget)))

/-- The weighted-fiber switch therefore proves the normalized spin-one
comparison at the same finite parameters. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    {ceiling : Q'} (volume : Nat)
    (switching :
      LowSpinFixedGrowingRawPartitionFiberSwitching
        w (Q'.le_of_lt hw) K volume ceiling) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≤
      ceiling *
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (volume + 1)
          (lowSpinCentralReferenceState volume) := by
  apply (fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference_iff_cross
    hw hK ceiling volume).mpr
  exact switching.rawCross

end LowSpinFixedGrowingRawPartitionFiberSwitching

/-! ## 3. A uniform weighted-fiber ceiling on the matched diagonal -/

structure MatchedDyadicLowSpinRawPartitionFiberSwitching
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  switching : ∀ scale,
    LowSpinFixedGrowingRawPartitionFiberSwitching
      (matchedAllSpinWeight family coupling scale)
      (Q'.le_of_lt
        (matchedAllSpinWeight_pos family coupling scale))
      (matchedAllSpinCutoff family coupling scale)
      scale ceiling

namespace MatchedDyadicLowSpinRawPartitionFiberSwitching

/-- A single matched weighted-fiber ceiling produces the necessary normalized
spin-one diagonal comparison at every scale. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (switching :
      MatchedDyadicLowSpinRawPartitionFiberSwitching bridge)
    (scale : Nat) :
    centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (Q'.le_of_lt
          (matchedAllSpinWeight_pos family coupling scale))
        (matchedAllSpinCutoff family coupling scale) 0
        (centralLowerSpinCubeState 1) ≤
      switching.ceiling *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale)
          (scale + 1)
          (lowSpinCentralReferenceState scale) := by
  exact LowSpinFixedGrowingRawPartitionFiberSwitching.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    (hw := matchedAllSpinWeight_pos family coupling scale)
    (hK := one_le_matchedAllSpinCutoff bridge scale)
    scale (switching.switching scale)

end MatchedDyadicLowSpinRawPartitionFiberSwitching

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate.fixedGrowingRawPartitionSourceIndexSum_eqv_cross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate.fixedGrowingRawPartitionTargetIndexSum_eqv_cross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate.LowSpinFixedGrowingRawPartitionFiberSwitching.rawCross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate.LowSpinFixedGrowingRawPartitionFiberSwitching.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate.MatchedDyadicLowSpinRawPartitionFiberSwitching.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
