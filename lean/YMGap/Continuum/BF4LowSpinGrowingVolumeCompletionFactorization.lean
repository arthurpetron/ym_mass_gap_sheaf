/-
# Exact low-spin source/completion factorization

The selected low-spin cube is face- and link-separated from the unchanged
fixed/upper completion remainder.  This module identifies the complete slab
assembly with their binary union and applies exact cutoff-one component
factorization.  The resulting completion weight is independent of which
selected lower time slice carries the common six-face cube.

No continuum limit, cofinal all-vector gap, OS/GNS reconstruction, or Clay
theorem is asserted here.  No `Classical`, choice, `native_decide`, `sorry`,
new axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation
import YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceCompletionInjectionGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate.LowSpinCentralFixedAdaptiveRawRowHarnack
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4LowSpinGrowingVolumeReplicaGeometry
open YMGap.Continuum.BF4LowSpinGrowingVolumeSourceInterfaceSeparation
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4AllSpinLinkSeparatedFactorization
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4DyadicSlabCubeManyTimeSliceProjectedFamily
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientWeights
open YMGap.Continuum.Z4LinkSeparatedComponentFactorization
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The full assembly is the binary union -/

/-- The complete reflected assembly is the pointwise binary union of the
selected lower source and the source-free completion remainder. -/
theorem lowSpinCentralAssembled_eq_binaryUnion
    {volume : Nat} (index : LowSpinCentralIndex volume)
    (boundary target : EdgeLabelling) :
    assembleReflectedSlabLabelling (volume + 1)
        (lowSpinCentralLowerState volume index) boundary target =
      binaryUnionLabel
        (lowSpinCentralLowerState volume index)
        (lowSpinCentralCompletionRemainder volume boundary target) := by
  funext id
  unfold lowSpinCentralCompletionRemainder binaryUnionLabel
  by_cases hphysical : id ∈
      slabPhysicalFaceEdges (centralExtent (volume + 1))
  · cases hside : plaquetteHalfSide (volume + 1)
        (slabPlaquetteAt (centralExtent (volume + 1)) id)
    · rw [assembleReflectedSlabLabelling_lower hphysical hside,
        assembleReflectedSlabLabelling_lower hphysical hside]
      rfl
    · have hnotLower : id ∉ centralLowerFaceIds (volume + 1) := by
        intro hlower
        have hlowerSide := (mem_centralLowerFaceIds.mp hlower).2
        rw [hside] at hlowerSide
        cases hlowerSide
      have hsourceZero : lowSpinCentralLowerState volume index id = 0 := by
        unfold lowSpinCentralLowerState centralLowerRestriction
        rw [if_neg hnotLower]
      rw [assembleReflectedSlabLabelling_fixed hphysical hside,
        assembleReflectedSlabLabelling_fixed hphysical hside,
        hsourceZero]
      simp
    · have hnotLower : id ∉ centralLowerFaceIds (volume + 1) := by
        intro hlower
        have hlowerSide := (mem_centralLowerFaceIds.mp hlower).2
        rw [hside] at hlowerSide
        cases hlowerSide
      have hsourceZero : lowSpinCentralLowerState volume index id = 0 := by
        unfold lowSpinCentralLowerState centralLowerRestriction
        rw [if_neg hnotLower]
      rw [assembleReflectedSlabLabelling_upper hphysical hside,
        assembleReflectedSlabLabelling_upper hphysical hside,
        hsourceZero]
      simp
  · have hnotLower : id ∉ centralLowerFaceIds (volume + 1) := by
      intro hlower
      exact hphysical (mem_centralLowerFaceIds.mp hlower).1
    have hsourceZero : lowSpinCentralLowerState volume index id = 0 := by
      unfold lowSpinCentralLowerState centralLowerRestriction
      rw [if_neg hnotLower]
    rw [assembleReflectedSlabLabelling_zero_off_physical
        (volume + 1) _ _ _ hphysical,
      assembleReflectedSlabLabelling_zero_off_physical
        (volume + 1) _ _ _ hphysical,
      hsourceZero]

private theorem lookupLabelFrom_binaryUnion
    (left right : EdgeLabelling) :
    ∀ (start : Nat) (faces : List Z4Plaq) (target : Z4Plaq),
      lookupLabelFrom (binaryUnionLabel left right) start faces target =
        lookupLabelFrom left start faces target +
          lookupLabelFrom right start faces target
  | _, [], _ => rfl
  | start, head :: tail, target => by
      by_cases heq : target = head
      · simp [lookupLabelFrom, heq, binaryUnionLabel]
      · simp [lookupLabelFrom, heq,
          lookupLabelFrom_binaryUnion left right (start + 1) tail target]

/-- Zero extension from the corrected slab preserves pointwise binary
unions. -/
theorem slabToAmbientPhysical_binaryUnion
    (extent : Nat) (left right : EdgeLabelling) :
    slabToAmbientPhysical extent (binaryUnionLabel left right) =
      binaryUnionLabel
        (slabToAmbientPhysical extent left)
        (slabToAmbientPhysical extent right) := by
  funext targetId
  unfold slabToAmbientPhysical slabGeometricSpin binaryUnionLabel
  by_cases hlt : targetId < plaquetteEdgeCount (extent + 1)
  · simp only [if_pos hlt]
    exact lookupLabelFrom_binaryUnion left right 0
      (boundaryCompleteSlabPlaquettes extent)
      (boxPlaquetteAt (extent + 1) targetId)
  · simp only [if_neg hlt]

/-- In the common ambient box, the complete assembly is the binary union of
the literal time-slice cube and the unchanged completion remainder. -/
theorem lowSpinCentralAssembledAmbient_eq_binaryUnion
    {volume : Nat} (index : LowSpinCentralIndex volume)
    (boundary target : EdgeLabelling) :
    slabToAmbientPhysical (centralExtent (volume + 1))
        (assembleReflectedSlabLabelling (volume + 1)
          (lowSpinCentralLowerState volume index) boundary target) =
      binaryUnionLabel
        (timeSlicePhysical (2 * volume)
          (lowSpinCentralTimeSliceIndex index))
        (lowSpinCentralCompletionRemainderAmbient
          volume boundary target) := by
  have heq := congrArg
    (slabToAmbientPhysical (centralExtent (volume + 1)))
    (lowSpinCentralAssembled_eq_binaryUnion index boundary target)
  rw [slabToAmbientPhysical_binaryUnion,
    lowSpinCentralLowerState_eq_slabPhysical index,
    lowSpinCentralSlabPhysical_roundtrip index] at heq
  simpa only [lowSpinCentralLowerState_eq_slabPhysical,
    lowSpinCentralCompletionRemainderAmbient] using heq

/-! ## 2. Exact cutoff-one physical-term factorization -/

private theorem zeroEdgeLabelling_mem_bounded_local
    (cutoff : Nat) (ids : List Nat) :
    zeroEdgeLabelling ∈ boundedEdgeLabellings cutoff ids := by
  apply boundedEdgeLabellings_complete
  · intro _ _
    change 0 < cutoff + 1
    omega
  · intro _ _
    rfl

private theorem lowSpinCentralCompletion_members
    {w : Q'} {hw : (0 : Q') < w} {volume : Nat}
    {completion : EdgeLabelling × EdgeLabelling}
    (hcompletion : completion ∈
      lowSpinCentralCompletionPairs w hw volume) :
    completion.1 ∈ centralHalfStates 1 (volume + 1) ∧
      completion.2 ∈ centralBoundaryChannels 1 (volume + 1) := by
  unfold lowSpinCentralCompletionPairs at hcompletion
  have hparts := (mem_cartesian_iff _ _ completion).mp hcompletion
  exact ⟨(mem_centralPositiveHalfStates_iff.mp hparts.1).1,
    hparts.2⟩

private theorem lowSpinCentralSourceAmbient_mem_bounded
    {volume : Nat} (index : LowSpinCentralIndex volume) :
    timeSlicePhysical (2 * volume)
        (lowSpinCentralTimeSliceIndex index) ∈
      boundedEdgeLabellings 1
        (List.range
          (plaquetteEdgeCount (centralAmbient (volume + 1)))) := by
  have hphysical := timeSlicePhysical_mem
    (lowSpinCentralTimeSliceIndex index)
  simpa [explicitPhysicalLabellings, physicalFaceEdges,
    lowSpinCentralAmbient_eq volume] using hphysical

private theorem lowSpinCentralCompletionRemainderAmbient_mem_bounded
    {volume : Nat} {boundary target : EdgeLabelling}
    (hboundary : boundary ∈
      centralBoundaryChannels 1 (volume + 1))
    (htarget : target ∈ centralHalfStates 1 (volume + 1)) :
    lowSpinCentralCompletionRemainderAmbient volume boundary target ∈
      boundedEdgeLabellings 1
        (List.range
          (plaquetteEdgeCount (centralAmbient (volume + 1)))) := by
  have hslab := assembleReflectedSlabLabelling_mem_full
    (zeroEdgeLabelling_mem_bounded_local 1
      (centralLowerFaceIds (volume + 1)))
    hboundary htarget
  unfold lowSpinCentralCompletionRemainderAmbient
  exact slabToAmbientPhysical_mem_bounded hslab

/-- Each complete reflected summand is exactly the common six-face source
weight times the physical weight of the unchanged completion remainder. -/
theorem lowSpinCentralCompletionWeight_eqv_source_mul_remainder
    {w : Q'} {hw : (0 : Q') < w} {volume : Nat}
    (index : LowSpinCentralIndex volume)
    (completion : EdgeLabelling × EdgeLabelling)
    (hcompletion : completion ∈
      lowSpinCentralCompletionPairs w hw volume) :
    lowSpinCentralCompletionWeight w volume
        (lowSpinCentralLowerState volume index) completion ≈
      (coeffW w 1) ^ 6 *
        parametricKPhysicalTerm w 1 (centralAmbient (volume + 1))
          (lowSpinCentralCompletionRemainderAmbient
            volume completion.2 completion.1) := by
  have hmembers := lowSpinCentralCompletion_members hcompletion
  have hfullBounded := assembleReflectedSlabLabelling_mem_full
    (lowSpinCentralLowerState_mem index) hmembers.2 hmembers.1
  have hambient := slabParametricKPhysicalTerm_ambient w hfullBounded
  unfold lowSpinCentralCompletionWeight
  rw [lowSpinCentralAssembledAmbient_eq_binaryUnion
    index completion.2 completion.1] at hambient
  have hfactor := parametricKPhysicalTerm_union_factor (w := w)
    (lowSpinCentralSourceAmbient_mem_bounded index)
    (lowSpinCentralCompletionRemainderAmbient_mem_bounded
      hmembers.2 hmembers.1)
    (lowSpinCentralSource_completionRemainder_faceDisjoint
      index completion.2 completion.1)
    (lowSpinCentralSource_completionRemainder_linkSeparated
      index completion.2 completion.1)
  have hsource :
      parametricKPhysicalTerm w 1 (centralAmbient (volume + 1))
          (timeSlicePhysical (2 * volume)
            (lowSpinCentralTimeSliceIndex index)) ≈
        (coeffW w 1) ^ 6 := by
    rw [← lowSpinCentralAmbient_eq volume]
    exact Q'.eqv_trans _ _ _
      (parametricKPhysicalTerm_one_eqv_localized
        w (4 + 2 * volume)
        (timeSlicePhysical (2 * volume)
          (lowSpinCentralTimeSliceIndex index)))
      (timeSliceProduction_eqv_spinOneCubeWeight
        w (lowSpinCentralTimeSliceIndex index))
  exact Q'.eqv_trans _ _ _ hambient
    (Q'.eqv_trans _ _ _ hfactor
      (Q'.mul_eqv_congr_right _ _ _ hsource))

/-! ## 3. Slice-independence and the ceiling-one Harnack producer -/

/-- With the completion held fixed, every selected low-spin time slice has
exactly the same complete physical summand. -/
theorem lowSpinCentralCompletionWeight_eqv_between
    {w : Q'} {hw : (0 : Q') < w} {volume : Nat}
    (left right : LowSpinCentralIndex volume)
    (completion : EdgeLabelling × EdgeLabelling)
    (hcompletion : completion ∈
      lowSpinCentralCompletionPairs w hw volume) :
    lowSpinCentralCompletionWeight w volume
        (lowSpinCentralLowerState volume left) completion ≈
      lowSpinCentralCompletionWeight w volume
        (lowSpinCentralLowerState volume right) completion := by
  exact Q'.eqv_trans _ _ _
    (lowSpinCentralCompletionWeight_eqv_source_mul_remainder
      left completion hcompletion)
    (Q'.eqv_symm
      (lowSpinCentralCompletionWeight_eqv_source_mul_remainder
        right completion hcompletion))

/-- Consequently, the complete positive raw rows of any two selected
low-spin time slices are exactly equal. -/
theorem lowSpinCentralPositiveRawRows_eqv
    {w : Q'} {hw : (0 : Q') < w} {volume : Nat}
    (left right : LowSpinCentralIndex volume) :
    centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralLowerState volume left) ≈
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralLowerState volume right) := by
  have hleft := centralPhysicalPositiveRawRowMass_eqv_completionSum
    hw volume (lowSpinCentralLowerState volume left)
  have hright := centralPhysicalPositiveRawRowMass_eqv_completionSum
    hw volume (lowSpinCentralLowerState volume right)
  have hsum := listQSum_congr_on
    (lowSpinCentralCompletionWeight w volume
      (lowSpinCentralLowerState volume left))
    (lowSpinCentralCompletionWeight w volume
      (lowSpinCentralLowerState volume right))
    (lowSpinCentralCompletionPairs w hw volume)
    (fun completion hcompletion =>
      lowSpinCentralCompletionWeight_eqv_between
        left right completion hcompletion)
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hsum (Q'.eqv_symm hright))

/-- In particular, the literal slice-zero row equals the constructively
selected adaptive minimum row at every volume. -/
theorem lowSpinCentralFixedAdaptiveRawRows_eqv
    {w : Q'} {hw : (0 : Q') < w} (volume : Nat) :
    centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralReferenceState volume) ≈
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralAdaptiveReferenceState w hw volume) := by
  unfold lowSpinCentralReferenceState
    lowSpinCentralAdaptiveReferenceState
  exact lowSpinCentralPositiveRawRows_eqv (hw := hw)
    (lowSpinCentralReferenceIndex volume)
    (lowSpinCentralAdaptiveReferenceIndex w hw volume)

/-- Identity on target/boundary completions is a uniform injection with the
optimal volume-independent ceiling `1`. -/
def lowSpinCentralFixedAdaptiveCompletionIdentity
    (w : Q') (hw : (0 : Q') < w) :
    LowSpinCentralFixedAdaptiveCompletionInjection w hw :=
  LowSpinCentralFixedAdaptiveCompletionInjection.ofSameCompletionWeightBound
    1 (Q'.le_refl' 1) (by
      intro volume completion hcompletion
      have heq :
          lowSpinCentralCompletionWeight w volume
              (lowSpinCentralReferenceState volume) completion ≈
            lowSpinCentralCompletionWeight w volume
              (lowSpinCentralAdaptiveReferenceState w hw volume)
              completion := by
        unfold lowSpinCentralReferenceState
          lowSpinCentralAdaptiveReferenceState
        exact lowSpinCentralCompletionWeight_eqv_between
          (lowSpinCentralReferenceIndex volume)
          (lowSpinCentralAdaptiveReferenceIndex w hw volume)
          completion hcompletion
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ heq
          (Q'.eqv_symm (Q'.one_mul_eqv _))))

/-- The previously conditional fixed/adaptive Harnack datum is now inhabited
with ceiling `1`. -/
def lowSpinCentralFixedAdaptiveRawRowHarnack
    (w : Q') (hw : (0 : Q') < w) :
    LowSpinCentralFixedAdaptiveRawRowHarnack w hw :=
  (lowSpinCentralFixedAdaptiveCompletionIdentity w hw).toRawRowHarnack

/-- All computed replica/reference ratios are one, so the literal fixed-row
floor is exactly one at every volume. -/
theorem lowSpinCentralComputedRawRowRatioFloor_eq_one
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    lowSpinCentralComputedRawRowRatioFloor w hw volume = 1 := by
  apply rawRowRatioFloor_eq_one_of_reference_le
    (lowSpinCentralPositiveRawReplication w hw volume)
  intro state hstate
  change state ∈ lowSpinCentralLowerStates volume at hstate
  obtain ⟨index, _hindex, rfl⟩ := List.mem_map.mp hstate
  exact Q'.le_of_eqv
    (lowSpinCentralPositiveRawRows_eqv (hw := hw)
      (lowSpinCentralReferenceIndex volume) index)

/-- The computed effective multiplicity is therefore semantically exactly
the literal count `volume + 1`. -/
theorem lowSpinCentralComputedEffectiveMultiplicity_eqv_count
    (w : Q') (hw : (0 : Q') < w) (volume : Nat) :
    lowSpinCentralComputedEffectiveMultiplicity w hw volume ≈
      Q'.ofNat (volume + 1) := by
  have heffective := lowSpinCentralComputedEffectiveMultiplicity_eqv
    w hw volume
  rw [lowSpinCentralComputedRawRowRatioFloor_eq_one w hw volume]
    at heffective
  exact Q'.eqv_trans _ _ _ heffective
    (Q'.mul_one_eqv (Q'.ofNat (volume + 1)))

private theorem one_le_epsilon_mul_ofNat_succ_of_den_le
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {volume : Nat} (hvolume : epsilon.den ≤ volume) :
    (1 : Q') ≤ epsilon * Q'.ofNat (volume + 1) := by
  have hnum : (0 : Int) < epsilon.num := Q'.num_pos_of_pos hepsilon
  show (1 : Q').num *
        ((epsilon * Q'.ofNat (volume + 1)).den : Int) ≤
      (epsilon * Q'.ofNat (volume + 1)).num *
        ((1 : Q').den : Int)
  show (1 : Int) *
        ((epsilon * Q'.ofNat (volume + 1)).den : Int) ≤
      (epsilon.num * ((volume + 1 : Nat) : Int)) * (1 : Int)
  rw [Q'.mul_den_cast]
  change (1 : Int) * ((epsilon.den : Int) * 1) ≤
    (epsilon.num * ((volume + 1 : Nat) : Int)) * 1
  simp only [Int.one_mul, Int.mul_one]
  have hden : (epsilon.denPred + 1 : Int) ≤ (volume : Int) :=
    Int.ofNat_le.mpr hvolume
  have honeNum : (1 : Int) ≤ epsilon.num := by omega
  have hvolumeNonnegative : (0 : Int) ≤ (volume : Int) :=
    Int.natCast_nonneg volume
  have hscaled : (volume : Int) ≤ epsilon.num * (volume : Int) := by
    have := Int.mul_le_mul_of_nonneg_right honeNum hvolumeNonnegative
    simpa only [Int.one_mul] using this
  have hsucc : epsilon.num * (volume : Int) ≤
      epsilon.num * ((volume + 1 : Nat) : Int) := by
    apply Int.mul_le_mul_of_nonneg_left
    · exact Int.ofNat_le.mpr (Nat.le_succ volume)
    · omega
  exact Int.le_trans hden (Int.le_trans hscaled hsucc)

/-- The denominator of `epsilon` is an explicit modulus for the prescribed
literal slice-zero stationary marginal. -/
theorem lowSpinCentralFixedReferenceMarginal_le_epsilon
    (w : Q') (hw : (0 : Q') < w)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (volume : Nat) (hvolume : epsilon.den ≤ volume) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralReferenceState volume) ≤
      epsilon := by
  let effective :=
    lowSpinCentralComputedEffectiveMultiplicity w hw volume
  have heffectivePos : (0 : Q') < effective :=
    lowSpinCentralComputedEffectiveMultiplicity_pos w hw volume
  have heffective : effective ≈ Q'.ofNat (volume + 1) :=
    lowSpinCentralComputedEffectiveMultiplicity_eqv_count w hw volume
  have honeCount :
      (1 : Q') ≤ epsilon * Q'.ofNat (volume + 1) :=
    one_le_epsilon_mul_ofNat_succ_of_den_le hepsilon hvolume
  have hepsilonEffective :
      epsilon * effective ≈ epsilon * Q'.ofNat (volume + 1) :=
    Q'.mul_eqv_congr_left epsilon effective
      (Q'.ofNat (volume + 1)) heffective
  have honeEffective : (1 : Q') ≤ epsilon * effective :=
    Q'.le_trans' _ _ _ honeCount
      (Q'.le_of_eqv (Q'.eqv_symm hepsilonEffective))
  have hreciprocal : Q'.divPos 1 effective heffectivePos ≤ epsilon :=
    Q'.divPos_le_of_le_mul 1 effective heffectivePos honeEffective
  exact Q'.le_trans' _ _ _
    (lowSpinCentralReferenceMarginal_le_reciprocalEffectiveMultiplicity
      w hw volume)
    hreciprocal

/-- Located tail-zero data for the prescribed literal slice-zero marginal,
now unconditional at every fixed positive coupling. -/
def lowSpinCentralFixedReferenceMarginalTailZero
    (w : Q') (hw : (0 : Q') < w) :
    FixedReferenceMarginalTailZero w hw where
  rate epsilon := epsilon.den
  marginal_le := by
    intro epsilon hepsilon volume hvolume
    exact lowSpinCentralFixedReferenceMarginal_le_epsilon
      w hw epsilon hepsilon volume hvolume

end YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralAssembledAmbient_eq_binaryUnion
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralCompletionWeight_eqv_source_mul_remainder
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralPositiveRawRows_eqv
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralFixedAdaptiveRawRows_eqv
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralFixedAdaptiveCompletionIdentity
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralFixedAdaptiveRawRowHarnack
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralComputedRawRowRatioFloor_eq_one
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralComputedEffectiveMultiplicity_eqv_count
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralFixedReferenceMarginal_le_epsilon
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeCompletionFactorization.lowSpinCentralFixedReferenceMarginalTailZero
