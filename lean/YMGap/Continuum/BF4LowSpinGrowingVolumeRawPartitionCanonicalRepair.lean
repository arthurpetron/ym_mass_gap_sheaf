/-
# Canonical crossed-slab repair for the low-spin volume bridge

The weighted-fiber switching gate leaves both the deterministic repair and
its physical fiber estimate abstract.  This module constructs the canonical
repair suggested by the crossed product itself.

From a source pair consisting of a fixed-half row completion and a full
growing-half slab labelling, it:

* reads the growing slab's reflected-upper target and fixed-plane boundary;
* uses those as the growing-row completion when the target is retained;
* assembles the original fixed-half completion above the spin-one source as
  the target fixed-half partition state; and
* sends zero-support exceptional targets to a fixed retained fallback.

Target configurations are represented by three faithful mixed-radix codes,
so inverse fibers are decidable without assuming equality of function-valued
edge labellings.  The repair and its exact target membership are proved here.
The one remaining field is the weighted inverse-fiber estimate for this
specific repair.  No such estimate, matched ray compression, all-vector gap,
continuum limit, or Clay theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair

set_option maxRecDepth 500000
set_option maxHeartbeats 3000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem code_injective_on_bounded
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

private theorem zeroEdgeLabelling_mem_bounded_local
    (K : Nat) (ids : List Nat) :
    zeroEdgeLabelling ∈ boundedEdgeLabellings K ids := by
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < K + 1
    omega
  · intro _ _
    rfl

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

/-! ## 1. Faithful decidable keys for target configurations -/

structure RawPartitionTargetKey where
  growingTargetCode : Nat
  growingBoundaryCode : Nat
  fixedPhysicalCode : Nat
  deriving DecidableEq

def fixedGrowingRawPartitionTargetKey
    (K volume : Nat)
    (pair : (EdgeLabelling × EdgeLabelling) × EdgeLabelling) :
    RawPartitionTargetKey where
  growingTargetCode :=
    edgeLabellingCode (K + 1)
      (centralLowerFaceIds (volume + 1)) pair.1.1
  growingBoundaryCode :=
    edgeLabellingCode (K + 1)
      (centralFixedFaceIds (volume + 1)) pair.1.2
  fixedPhysicalCode :=
    edgeLabellingCode (K + 1)
      (slabPhysicalFaceEdges (centralExtent 0)) pair.2

def fixedGrowingRawPartitionTargetKeys
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    List RawPartitionTargetKey :=
  (fixedGrowingRawPartitionTargetPairs w hw K volume).map
    (fixedGrowingRawPartitionTargetKey K volume)

theorem fixedGrowingRawPartitionTargetKey_injective_on
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {left right :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hleft : left ∈
      fixedGrowingRawPartitionTargetPairs w hw K volume)
    (hright : right ∈
      fixedGrowingRawPartitionTargetPairs w hw K volume)
    (hkey :
      fixedGrowingRawPartitionTargetKey K volume left =
        fixedGrowingRawPartitionTargetKey K volume right) :
    left = right := by
  have hleftParts :=
    (mem_cartesian_iff
      (centralPositiveCompletionPairs w hw K (volume + 1))
      (centralPhysicalPartitionStates K 0) left).mp hleft
  have hrightParts :=
    (mem_cartesian_iff
      (centralPositiveCompletionPairs w hw K (volume + 1))
      (centralPhysicalPartitionStates K 0) right).mp hright
  have hleftCompletion :=
    (mem_cartesian_iff
      (centralPositiveHalfStates w hw K (volume + 1))
      (centralBoundaryChannels K (volume + 1)) left.1).mp
      hleftParts.1
  have hrightCompletion :=
    (mem_cartesian_iff
      (centralPositiveHalfStates w hw K (volume + 1))
      (centralBoundaryChannels K (volume + 1)) right.1).mp
      hrightParts.1
  have hcodes :
      edgeLabellingCode (K + 1)
            (centralLowerFaceIds (volume + 1)) left.1.1 =
          edgeLabellingCode (K + 1)
            (centralLowerFaceIds (volume + 1)) right.1.1 ∧
        edgeLabellingCode (K + 1)
            (centralFixedFaceIds (volume + 1)) left.1.2 =
          edgeLabellingCode (K + 1)
            (centralFixedFaceIds (volume + 1)) right.1.2 ∧
        edgeLabellingCode (K + 1)
            (slabPhysicalFaceEdges (centralExtent 0)) left.2 =
          edgeLabellingCode (K + 1)
            (slabPhysicalFaceEdges (centralExtent 0)) right.2 := by
    unfold fixedGrowingRawPartitionTargetKey at hkey
    simpa only [RawPartitionTargetKey.mk.injEq] using hkey
  have htargetCode :
      edgeLabellingCode (K + 1)
          (centralLowerFaceIds (volume + 1)) left.1.1 =
        edgeLabellingCode (K + 1)
          (centralLowerFaceIds (volume + 1)) right.1.1 :=
    hcodes.1
  have hboundaryCode :
      edgeLabellingCode (K + 1)
          (centralFixedFaceIds (volume + 1)) left.1.2 =
        edgeLabellingCode (K + 1)
          (centralFixedFaceIds (volume + 1)) right.1.2 :=
    hcodes.2.1
  have hphysicalCode :
      edgeLabellingCode (K + 1)
          (slabPhysicalFaceEdges (centralExtent 0)) left.2 =
        edgeLabellingCode (K + 1)
          (slabPhysicalFaceEdges (centralExtent 0)) right.2 :=
    hcodes.2.2
  have htarget : left.1.1 = right.1.1 :=
    code_injective_on_bounded
      (mem_centralPositiveHalfStates_iff.mp hleftCompletion.1).1
      (mem_centralPositiveHalfStates_iff.mp hrightCompletion.1).1
      htargetCode
  have hboundary : left.1.2 = right.1.2 :=
    code_injective_on_bounded
      hleftCompletion.2 hrightCompletion.2 hboundaryCode
  have hphysical : left.2 = right.2 := by
    apply code_injective_on_bounded
    · simpa only [centralPhysicalPartitionStates] using hleftParts.2
    · simpa only [centralPhysicalPartitionStates] using hrightParts.2
    · exact hphysicalCode
  apply Prod.ext
  · exact Prod.ext htarget hboundary
  · exact hphysical

theorem fixedGrowingRawPartitionTargetKeys_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    (fixedGrowingRawPartitionTargetKeys w hw K volume).Nodup := by
  unfold fixedGrowingRawPartitionTargetKeys
  apply nodup_map_of_injOn
  · exact fixedGrowingRawPartitionTargetPairs_nodup
      w hw K volume
  · intro left hleft right hright hkey
    exact fixedGrowingRawPartitionTargetKey_injective_on
      hleft hright hkey

/-- The target weight presented on the decidable key carrier.  Faithfulness
of the key makes each displayed fiber a singleton, but total pushforward is
all the compiler needs. -/
def fixedGrowingRawPartitionTargetKeyWeight
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (key : RawPartitionTargetKey) : Q' :=
  fiberWeight
    (fixedGrowingRawPartitionTargetPairs w hw K volume)
    (fixedGrowingRawPartitionTargetWeight w K volume)
    (fixedGrowingRawPartitionTargetKey K volume)
    key

theorem fixedGrowingRawPartitionTargetKeySum_eqv_cross
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat) :
    listQSum
        (fixedGrowingRawPartitionTargetKeyWeight w hw K volume)
        (fixedGrowingRawPartitionTargetKeys w hw K volume) ≈
      growingHalfSpinOneRawRow w hw K volume *
        fixedHalfPhysicalPartition w K := by
  have htotal := fiberWeight_total
    (fixedGrowingRawPartitionTargetPairs w hw K volume)
    (fixedGrowingRawPartitionTargetWeight w K volume)
    (fixedGrowingRawPartitionTargetKey K volume)
    (fixedGrowingRawPartitionTargetKeys w hw K volume)
    (fixedGrowingRawPartitionTargetKeys_nodup w hw K volume)
    (by
      intro pair hpair
      unfold fixedGrowingRawPartitionTargetKeys
      exact List.mem_map.mpr ⟨pair, hpair, rfl⟩)
  exact Q'.eqv_trans _ _ _ htotal
    (fixedGrowingRawPartitionTargetSum_eqv_cross hw K volume)

/-! ## 2. The canonical value-level crossed repair -/

/-- Read the retained growing completion from a full slab.  A non-retained
upper restriction is sent to the fixed low-spin/zero-boundary fallback; such
branches are the zero-support cases whose weight must vanish in the eventual
fiber estimate. -/
def canonicalGrowingCompletion
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (physical : EdgeLabelling) : EdgeLabelling × EdgeLabelling :=
  let target :=
    centralReflectedUpperRestriction (volume + 1) physical
  if (0 : Q') <
      centralPhysicalRowMarginal w hw K (volume + 1) target then
    (target, centralBoundaryRestriction (volume + 1) physical)
  else
    (lowSpinCentralReferenceState volume, zeroEdgeLabelling)

theorem canonicalGrowingCompletion_mem
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat) {physical : EdgeLabelling}
    (hphysical : physical ∈
      centralPhysicalPartitionStates K (volume + 1)) :
    canonicalGrowingCompletion
        w (Q'.le_of_lt hw) K volume physical ∈
      centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K (volume + 1) := by
  have hphysical' : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges (centralExtent (volume + 1))) := by
    simpa only [centralPhysicalPartitionStates] using hphysical
  let target :=
    centralReflectedUpperRestriction (volume + 1) physical
  by_cases htarget : (0 : Q') <
      centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K (volume + 1) target
  · unfold canonicalGrowingCompletion
    rw [if_pos htarget]
    apply (mem_cartesian_iff _ _ _).mpr
    refine ⟨mem_centralPositiveHalfStates_iff.mpr ⟨?_, htarget⟩,
      centralBoundaryRestriction_mem hphysical'⟩
    simpa only [centralHalfStates] using
      centralReflectedUpperRestriction_mem hphysical'
  · unfold canonicalGrowingCompletion
    rw [if_neg htarget]
    apply (mem_cartesian_iff _ _ _).mpr
    refine ⟨(lowSpinCentralKPositiveRawReplication
      w hw K hK volume).reference_mem, ?_⟩
    exact zeroEdgeLabelling_mem_bounded_local K
      (centralFixedFaceIds (volume + 1))

def canonicalFixedPartitionPhysical
    (source :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling) :
    EdgeLabelling :=
  assembleReflectedSlabLabelling 0
    (centralLowerSpinCubeState 1) source.1.2 source.1.1

theorem canonicalFixedPartitionPhysical_mem
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat)
    {source :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hsource : source ∈
      fixedGrowingRawPartitionSourcePairs
        w (Q'.le_of_lt hw) K volume) :
    canonicalFixedPartitionPhysical source ∈
      centralPhysicalPartitionStates K 0 := by
  have hparts :=
    (mem_cartesian_iff
      (centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalPartitionStates K (volume + 1))
      source).mp hsource
  have hcompletion :=
    (mem_cartesian_iff
      (centralPositiveHalfStates w (Q'.le_of_lt hw) K 0)
      (centralBoundaryChannels K 0) source.1).mp hparts.1
  have hfull := assembleReflectedSlabLabelling_mem_full
    (centralLowerSpinCubeState_mem_centralHalfStates hK)
    hcompletion.2
    (mem_centralPositiveHalfStates_iff.mp hcompletion.1).1
  simpa only [canonicalFixedPartitionPhysical,
    centralPhysicalPartitionStates] using hfull

def canonicalRawPartitionRepairTarget
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (source :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling) :
    (EdgeLabelling × EdgeLabelling) × EdgeLabelling :=
  (canonicalGrowingCompletion w hw K volume source.2,
    canonicalFixedPartitionPhysical source)

theorem canonicalRawPartitionRepairTarget_mem
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat)
    {source :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hsource : source ∈
      fixedGrowingRawPartitionSourcePairs
        w (Q'.le_of_lt hw) K volume) :
    canonicalRawPartitionRepairTarget
        w (Q'.le_of_lt hw) K volume source ∈
      fixedGrowingRawPartitionTargetPairs
        w (Q'.le_of_lt hw) K volume := by
  have hparts :=
    (mem_cartesian_iff
      (centralPositiveCompletionPairs
        w (Q'.le_of_lt hw) K 0)
      (centralPhysicalPartitionStates K (volume + 1))
      source).mp hsource
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨canonicalGrowingCompletion_mem
      hw hK volume hparts.2,
    canonicalFixedPartitionPhysical_mem hw hK volume hsource⟩

def canonicalRawPartitionRepairKey
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (source :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling) :
    RawPartitionTargetKey :=
  fixedGrowingRawPartitionTargetKey K volume
    (canonicalRawPartitionRepairTarget w hw K volume source)

theorem canonicalRawPartitionRepairKey_mem
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    (volume : Nat)
    {source :
      (EdgeLabelling × EdgeLabelling) × EdgeLabelling}
    (hsource : source ∈
      fixedGrowingRawPartitionSourcePairs
        w (Q'.le_of_lt hw) K volume) :
    canonicalRawPartitionRepairKey
        w (Q'.le_of_lt hw) K volume source ∈
      fixedGrowingRawPartitionTargetKeys
        w (Q'.le_of_lt hw) K volume := by
  unfold canonicalRawPartitionRepairKey
    fixedGrowingRawPartitionTargetKeys
  exact List.mem_map.mpr
    ⟨canonicalRawPartitionRepairTarget
        w (Q'.le_of_lt hw) K volume source,
      canonicalRawPartitionRepairTarget_mem hw hK volume hsource,
      rfl⟩

/-! ## 3. The one remaining physical fiber estimate -/

/-- The exact remaining producer: one ceiling pays every inverse fiber of the
specific canonical crossed-slab repair. -/
structure CanonicalRawPartitionFiberBound
    (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (volume : Nat) (ceiling : Q') : Type where
  weighted_fiber_capacity : ∀ key,
    key ∈ fixedGrowingRawPartitionTargetKeys
        w (Q'.le_of_lt hw) K volume →
      fiberWeight
          (fixedGrowingRawPartitionSourcePairs
            w (Q'.le_of_lt hw) K volume)
          (fixedGrowingRawPartitionSourceWeight w K volume)
          (canonicalRawPartitionRepairKey
            w (Q'.le_of_lt hw) K volume)
          key ≤
        ceiling *
          fixedGrowingRawPartitionTargetKeyWeight
            w (Q'.le_of_lt hw) K volume key

namespace CanonicalRawPartitionFiberBound

/-- The canonical fiber bound compiles directly to the division-free raw
cross inequality. -/
theorem rawCross
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CanonicalRawPartitionFiberBound
      w hw K hK volume ceiling) :
    fixedHalfSpinOneRawRow w (Q'.le_of_lt hw) K *
        growingHalfPhysicalPartition w K volume ≤
      (ceiling * growingHalfSpinOneRawRow
          w (Q'.le_of_lt hw) K volume) *
        fixedHalfPhysicalPartition w K := by
  let sourcePairs := fixedGrowingRawPartitionSourcePairs
    w (Q'.le_of_lt hw) K volume
  let sourceWeight := fixedGrowingRawPartitionSourceWeight w K volume
  let targetKeys := fixedGrowingRawPartitionTargetKeys
    w (Q'.le_of_lt hw) K volume
  let targetWeight := fixedGrowingRawPartitionTargetKeyWeight
    w (Q'.le_of_lt hw) K volume
  let repair := canonicalRawPartitionRepairKey
    w (Q'.le_of_lt hw) K volume
  let pushedWeight := fiberWeight sourcePairs sourceWeight repair
  have htotal :
      listQSum pushedWeight targetKeys ≈
        listQSum sourceWeight sourcePairs :=
    fiberWeight_total sourcePairs sourceWeight repair targetKeys
      (fixedGrowingRawPartitionTargetKeys_nodup
        w (Q'.le_of_lt hw) K volume)
      (by
        intro source hsource
        exact canonicalRawPartitionRepairKey_mem hw hK volume hsource)
  have hcapacity :
      listQSum pushedWeight targetKeys ≤
        listQSum (fun key => ceiling * targetWeight key)
          targetKeys := by
    apply listQSum_le_termwise_local
    intro key hkey
    exact bound.weighted_fiber_capacity key hkey
  have hsource := fixedGrowingRawPartitionSourceSum_eqv_cross
    (Q'.le_of_lt hw) K volume
  have htarget := fixedGrowingRawPartitionTargetKeySum_eqv_cross
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
        (Q'.eqv_symm (Q'.mul_assoc_eqv ceiling
          (growingHalfSpinOneRawRow
            w (Q'.le_of_lt hw) K volume)
          (fixedHalfPhysicalPartition w K))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsource)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal)
      (Q'.le_trans' _ _ _ hcapacity
        (Q'.le_of_eqv hscaledTarget)))

/-- Consequently the canonical fiber bound proves the normalized atom
comparison at its displayed finite parameters. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {w : Q'} {hw : (0 : Q') < w} {K : Nat} {hK : 1 ≤ K}
    {volume : Nat} {ceiling : Q'}
    (bound : CanonicalRawPartitionFiberBound
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

end CanonicalRawPartitionFiberBound

/-! ## 4. One canonical fiber ceiling on the matched diagonal -/

structure MatchedDyadicCanonicalRawPartitionFiberBound
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
    CanonicalRawPartitionFiberBound
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale ceiling

namespace MatchedDyadicCanonicalRawPartitionFiberBound

theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicCanonicalRawPartitionFiberBound bridge)
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
  CanonicalRawPartitionFiberBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    (bound.fiberBound scale)

end MatchedDyadicCanonicalRawPartitionFiberBound

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair.fixedGrowingRawPartitionTargetKey_injective_on
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair.fixedGrowingRawPartitionTargetKeySum_eqv_cross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair.canonicalGrowingCompletion_mem
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair.canonicalRawPartitionRepairTarget_mem
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair.canonicalRawPartitionRepairKey_mem
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair.CanonicalRawPartitionFiberBound.rawCross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair.CanonicalRawPartitionFiberBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionCanonicalRepair.MatchedDyadicCanonicalRawPartitionFiberBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
