/-
# Raw-row/partition switching gate for the growing-volume low-spin bridge

The normalized fixed-half/growing-half spin-one comparison is exactly a
cross-multiplied inequality between one raw row and the opposite finite slab
partition.  This module exposes a concrete sufficient producer for that
inequality: inject each weighted pair

  fixed-half row completion x growing-half partition state

into a pair

  growing-half row completion x fixed-half partition state

with one uniform pointwise ceiling.  Constructive finite weighted summation
then proves the raw cross inequality and the corresponding normalized atom
comparison on a matched dyadic schedule.

The switching data are intentionally not constructed here.  An injection is
a strong sufficient condition, not a necessary characterization, and this
module does not compress the remaining fixed-half spin ray, produce an
all-vector gap, take a continuum limit, or prove the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate

set_option maxRecDepth 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

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

private theorem mul_eqv_congr_local
    {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right left left' right hleft)
    (Q'.mul_eqv_congr_left left' right right' hright)

/-! ## 1. Exact finite completion and partition carriers -/

/-- The complete positive-target/boundary carrier of one raw row at arbitrary
cutoff and reflection half. -/
def centralPositiveCompletionPairs
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    List (EdgeLabelling × EdgeLabelling) :=
  cartesian
    (centralPositiveHalfStates w hw K half)
    (centralBoundaryChannels K half)

/-- The complete physical summand carried by one source and one flattened
`(target, boundary)` completion. -/
def centralPositiveCompletionWeight
    (w : Q') (K half : Nat) (source : EdgeLabelling)
    (completion : EdgeLabelling × EdgeLabelling) : Q' :=
  slabParametricKPhysicalTerm w K (centralExtent half)
    (assembleReflectedSlabLabelling
      half source completion.2 completion.1)

/-- The literal physical carrier of the slab partition at one reflection
half. -/
def centralPhysicalPartitionStates (K half : Nat) :
    List EdgeLabelling :=
  boundedEdgeLabellings K
    (slabPhysicalFaceEdges (centralExtent half))

def centralPhysicalPartitionWeight
    (w : Q') (K half : Nat) (physical : EdgeLabelling) : Q' :=
  slabParametricKPhysicalTerm w K (centralExtent half) physical

theorem centralPositiveCompletionPairs_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (centralPositiveCompletionPairs w hw K half).Nodup := by
  unfold centralPositiveCompletionPairs
  exact cartesian_nodup _ _
    (centralPositiveHalfStates_nodup w hw K half)
    (centralBoundaryChannels_nodup K half)

theorem centralPhysicalPartitionStates_nodup
    (K half : Nat) :
    (centralPhysicalPartitionStates K half).Nodup := by
  unfold centralPhysicalPartitionStates
  exact boundedEdgeLabellings_nodup K _ (by
    unfold slabPhysicalFaceEdges
    exact range_nodup_local _)

theorem centralPositiveCompletionWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (source : EdgeLabelling)
    (completion : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤
      centralPositiveCompletionWeight w K half source completion := by
  unfold centralPositiveCompletionWeight
  exact slabParametricKPhysicalTerm_nonnegative
    hw K (centralExtent half) _

theorem centralPhysicalPartitionWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (physical : EdgeLabelling) :
    (0 : Q') ≤ centralPhysicalPartitionWeight w K half physical := by
  unfold centralPhysicalPartitionWeight
  exact slabParametricKPhysicalTerm_nonnegative
    hw K (centralExtent half) physical

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-- A raw row is exactly the flattened weighted completion sum, uniformly in
the finite cutoff and reflection half. -/
theorem centralPhysicalPositiveRawRowMass_eqv_completionSum
    {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (source : EdgeLabelling) :
    centralPhysicalPositiveRawRowMass w hw K half source ≈
      listQSum
        (centralPositiveCompletionWeight w K half source)
        (centralPositiveCompletionPairs w hw K half) := by
  unfold centralPhysicalPositiveRawRowMass
    centralPositiveCompletionPairs
    centralPositiveCompletionWeight
    centralPhysicalReflectedKernel
  exact Q'.eqv_symm
    (listQSum_cartesian_eq_nested_local
      (fun completion : EdgeLabelling × EdgeLabelling =>
        slabParametricKPhysicalTerm w K (centralExtent half)
          (assembleReflectedSlabLabelling
            half source completion.2 completion.1))
      (centralPositiveHalfStates w hw K half)
      (centralBoundaryChannels K half))

theorem slabParametricKPhysicalPartition_eqv_partitionSum
    (w : Q') (K half : Nat) :
    slabParametricKPhysicalPartition w K (centralExtent half) ≈
      listQSum
        (centralPhysicalPartitionWeight w K half)
        (centralPhysicalPartitionStates K half) := by
  unfold slabParametricKPhysicalPartition
    centralPhysicalPartitionWeight centralPhysicalPartitionStates
  exact Q'.eqv_refl _

/-! ## 2. Crossed source and target products -/

def fixedGrowingRawPartitionSourcePairs
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    List ((EdgeLabelling × EdgeLabelling) × EdgeLabelling) :=
  cartesian
    (centralPositiveCompletionPairs w hw K 0)
    (centralPhysicalPartitionStates K (volume + 1))

def fixedGrowingRawPartitionTargetPairs
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    List ((EdgeLabelling × EdgeLabelling) × EdgeLabelling) :=
  cartesian
    (centralPositiveCompletionPairs w hw K (volume + 1))
    (centralPhysicalPartitionStates K 0)

def fixedGrowingRawPartitionSourceWeight
    (w : Q') (K volume : Nat)
    (pair : (EdgeLabelling × EdgeLabelling) × EdgeLabelling) : Q' :=
  centralPositiveCompletionWeight w K 0
      (centralLowerSpinCubeState 1) pair.1 *
    centralPhysicalPartitionWeight w K (volume + 1) pair.2

def fixedGrowingRawPartitionTargetWeight
    (w : Q') (K volume : Nat)
    (pair : (EdgeLabelling × EdgeLabelling) × EdgeLabelling) : Q' :=
  centralPositiveCompletionWeight w K (volume + 1)
      (lowSpinCentralReferenceState volume) pair.1 *
    centralPhysicalPartitionWeight w K 0 pair.2

theorem fixedGrowingRawPartitionSourcePairs_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    (fixedGrowingRawPartitionSourcePairs w hw K volume).Nodup := by
  unfold fixedGrowingRawPartitionSourcePairs
  exact cartesian_nodup _ _
    (centralPositiveCompletionPairs_nodup w hw K 0)
    (centralPhysicalPartitionStates_nodup K (volume + 1))

theorem fixedGrowingRawPartitionTargetPairs_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat) :
    (fixedGrowingRawPartitionTargetPairs w hw K volume).Nodup := by
  unfold fixedGrowingRawPartitionTargetPairs
  exact cartesian_nodup _ _
    (centralPositiveCompletionPairs_nodup
      w hw K (volume + 1))
    (centralPhysicalPartitionStates_nodup K 0)

theorem fixedGrowingRawPartitionTargetWeight_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat)
    (pair : (EdgeLabelling × EdgeLabelling) × EdgeLabelling) :
    (0 : Q') ≤ fixedGrowingRawPartitionTargetWeight w K volume pair := by
  unfold fixedGrowingRawPartitionTargetWeight
  exact Q'.mul_nonneg _ _
    (centralPositiveCompletionWeight_nonnegative
      hw K (volume + 1) (lowSpinCentralReferenceState volume) pair.1)
    (centralPhysicalPartitionWeight_nonnegative hw K 0 pair.2)

theorem fixedGrowingRawPartitionSourceSum_eqv_cross
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat) :
    listQSum
        (fixedGrowingRawPartitionSourceWeight w K volume)
        (fixedGrowingRawPartitionSourcePairs w hw K volume) ≈
      fixedHalfSpinOneRawRow w hw K *
        growingHalfPhysicalPartition w K volume := by
  have hproduct := listQSum_cartesian_product
    (centralPositiveCompletionWeight w K 0
      (centralLowerSpinCubeState 1))
    (centralPhysicalPartitionWeight w K (volume + 1))
    (centralPositiveCompletionPairs w hw K 0)
    (centralPhysicalPartitionStates K (volume + 1))
  have hrow := centralPhysicalPositiveRawRowMass_eqv_completionSum
    hw K 0 (centralLowerSpinCubeState 1)
  have hpartition := slabParametricKPhysicalPartition_eqv_partitionSum
    w K (volume + 1)
  exact Q'.eqv_trans _ _ _ hproduct
    (mul_eqv_congr_local
      (Q'.eqv_symm hrow) (Q'.eqv_symm hpartition))

theorem fixedGrowingRawPartitionTargetSum_eqv_cross
    {w : Q'} (hw : (0 : Q') ≤ w) (K volume : Nat) :
    listQSum
        (fixedGrowingRawPartitionTargetWeight w K volume)
        (fixedGrowingRawPartitionTargetPairs w hw K volume) ≈
      growingHalfSpinOneRawRow w hw K volume *
        fixedHalfPhysicalPartition w K := by
  have hproduct := listQSum_cartesian_product
    (centralPositiveCompletionWeight w K (volume + 1)
      (lowSpinCentralReferenceState volume))
    (centralPhysicalPartitionWeight w K 0)
    (centralPositiveCompletionPairs w hw K (volume + 1))
    (centralPhysicalPartitionStates K 0)
  have hrow := centralPhysicalPositiveRawRowMass_eqv_completionSum
    hw K (volume + 1) (lowSpinCentralReferenceState volume)
  have hpartition := slabParametricKPhysicalPartition_eqv_partitionSum
    w K 0
  exact Q'.eqv_trans _ _ _ hproduct
    (mul_eqv_congr_local
      (Q'.eqv_symm hrow) (Q'.eqv_symm hpartition))

/-! ## 3. A constructive weighted switching producer -/

/-- At fixed coupling, cutoff, and volume, a weighted injection between the
two crossed products.  The ceiling is an explicit parameter so that a matched
family can demand the same value on its diagonal at every scale. -/
structure LowSpinFixedGrowingRawPartitionSwitching
    (w : Q') (hw : (0 : Q') ≤ w) (K volume : Nat)
    (ceiling : Q') : Type where
  encode :
    ((EdgeLabelling × EdgeLabelling) × EdgeLabelling) →
      ((EdgeLabelling × EdgeLabelling) × EdgeLabelling)
  encode_mem : ∀ pair,
    pair ∈ fixedGrowingRawPartitionSourcePairs w hw K volume →
      encode pair ∈
        fixedGrowingRawPartitionTargetPairs w hw K volume
  encode_injective : ∀ first,
    first ∈ fixedGrowingRawPartitionSourcePairs w hw K volume →
      ∀ second,
        second ∈ fixedGrowingRawPartitionSourcePairs w hw K volume →
          encode first = encode second → first = second
  sourceWeight_le : ∀ pair,
    pair ∈ fixedGrowingRawPartitionSourcePairs w hw K volume →
      fixedGrowingRawPartitionSourceWeight w K volume pair ≤
        ceiling *
          fixedGrowingRawPartitionTargetWeight w K volume
            (encode pair)

namespace LowSpinFixedGrowingRawPartitionSwitching

/-- Weighted injectivity compiles the configuration-level switch into the
exact division-free raw-row/partition inequality. -/
theorem rawCross
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat} {ceiling : Q'}
    (switching :
      LowSpinFixedGrowingRawPartitionSwitching
        w hw K volume ceiling)
    (hceiling : (0 : Q') ≤ ceiling) :
    fixedHalfSpinOneRawRow w hw K *
        growingHalfPhysicalPartition w K volume ≤
      (ceiling * growingHalfSpinOneRawRow w hw K volume) *
        fixedHalfPhysicalPartition w K := by
  let sourcePairs :=
    fixedGrowingRawPartitionSourcePairs w hw K volume
  let targetPairs :=
    fixedGrowingRawPartitionTargetPairs w hw K volume
  let sourceWeight :=
    fixedGrowingRawPartitionSourceWeight w K volume
  let targetWeight :=
    fixedGrowingRawPartitionTargetWeight w K volume
  have hsum :
      listQSum sourceWeight sourcePairs ≤
        listQSum
          (fun pair => ceiling * targetWeight pair)
          targetPairs := by
    apply listQSum_le_of_injective_nodup
      sourcePairs targetPairs sourceWeight
      (fun pair => ceiling * targetWeight pair)
      switching.encode
    · exact fixedGrowingRawPartitionSourcePairs_nodup
        w hw K volume
    · exact fixedGrowingRawPartitionTargetPairs_nodup
        w hw K volume
    · intro pair hpair
      exact switching.encode_mem pair hpair
    · intro first hfirst second hsecond heq
      exact switching.encode_injective
        first hfirst second hsecond heq
    · intro pair hpair
      exact switching.sourceWeight_le pair hpair
    · intro pair _hpair
      exact Q'.mul_nonneg _ _ hceiling
        (fixedGrowingRawPartitionTargetWeight_nonnegative
          hw K volume pair)
  have hsource := fixedGrowingRawPartitionSourceSum_eqv_cross
    hw K volume
  have htarget := fixedGrowingRawPartitionTargetSum_eqv_cross
    hw K volume
  have hfactor :
      listQSum
          (fun pair => ceiling * targetWeight pair)
          targetPairs ≈
        ceiling *
          listQSum targetWeight targetPairs :=
    listQSum_mul_left ceiling targetWeight targetPairs
  have hscaledTarget :
      listQSum
          (fun pair => ceiling * targetWeight pair)
          targetPairs ≈
        (ceiling * growingHalfSpinOneRawRow w hw K volume) *
          fixedHalfPhysicalPartition w K := by
    exact Q'.eqv_trans _ _ _ hfactor
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left ceiling _ _ htarget)
        (Q'.eqv_symm (Q'.mul_assoc_eqv ceiling
          (growingHalfSpinOneRawRow w hw K volume)
          (fixedHalfPhysicalPartition w K))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hscaledTarget))

/-- The switching compiler gives the normalized fixed-half/growing-half
spin-one comparison. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {w : Q'} (hw : (0 : Q') < w) {K : Nat} (hK : 1 ≤ K)
    {ceiling : Q'} (hceiling : (0 : Q') ≤ ceiling)
    (volume : Nat)
    (switching :
      LowSpinFixedGrowingRawPartitionSwitching
        w (Q'.le_of_lt hw) K volume ceiling) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) K 0 (centralLowerSpinCubeState 1) ≤
      ceiling *
        centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) K (volume + 1)
          (lowSpinCentralReferenceState volume) := by
  apply (fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference_iff_cross
    hw hK ceiling volume).mpr
  exact switching.rawCross hceiling

end LowSpinFixedGrowingRawPartitionSwitching

/-! ## 4. One ceiling on a matched cofinal schedule -/

/-- A single weighted-switching ceiling and its constructive injection data at
every matched scale.  This structure produces only the necessary spin-one
volume comparison; the rest of the fixed-half ray remains a separate input. -/
structure MatchedDyadicLowSpinRawPartitionSwitching
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
    LowSpinFixedGrowingRawPartitionSwitching
      (matchedAllSpinWeight family coupling scale)
      (Q'.le_of_lt
        (matchedAllSpinWeight_pos family coupling scale))
      (matchedAllSpinCutoff family coupling scale)
      scale
      ceiling

namespace MatchedDyadicLowSpinRawPartitionSwitching

theorem ceiling_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (switching : MatchedDyadicLowSpinRawPartitionSwitching bridge) :
    (0 : Q') ≤ switching.ceiling :=
  Q'.le_trans' _ _ _ (by decide) switching.one_le_ceiling

/-- A uniform matched switching family compiles to the exact necessary
fixed-half/growing-half normalized atom comparison at every scale. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (switching : MatchedDyadicLowSpinRawPartitionSwitching bridge)
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
  exact LowSpinFixedGrowingRawPartitionSwitching.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
      (hw := matchedAllSpinWeight_pos family coupling scale)
      (hK := one_le_matchedAllSpinCutoff bridge scale)
      (hceiling := switching.ceiling_nonnegative)
      scale
      (switching := switching.switching scale)

end MatchedDyadicLowSpinRawPartitionSwitching

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate.centralPhysicalPositiveRawRowMass_eqv_completionSum
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate.fixedGrowingRawPartitionSourceSum_eqv_cross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate.fixedGrowingRawPartitionTargetSum_eqv_cross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate.LowSpinFixedGrowingRawPartitionSwitching.rawCross
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate.LowSpinFixedGrowingRawPartitionSwitching.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionSwitchingGate.MatchedDyadicLowSpinRawPartitionSwitching.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
