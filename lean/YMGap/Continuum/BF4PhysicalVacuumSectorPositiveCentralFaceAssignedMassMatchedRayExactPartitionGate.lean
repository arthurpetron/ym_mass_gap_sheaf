/-
# Exact raw-numerator partition gate for the matched spin-cube ray

The explicit residual-carrier envelope is a useful sufficient estimate, but
it may be much larger than the literal ray numerator.  This file therefore
returns to the exact finite quantity: the sum of the positive raw reflected
row masses of the admitted excited spin-cube sources.

The normalized ray mass is proved to be exactly that raw numerator divided by
the complete corrected-slab physical partition.  Consequently ray-mass tail
zero is equivalent, with the same located rate, to the cross-multiplied exact
partition-domination inequality.  The earlier explicit numerator is also
proved to dominate this exact numerator.

No exact partition-domination estimate is inhabited here.  No congestion
bound, finite gap, physical normalization, continuum theory, or Clay
conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPartitionDominationGate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4MatchedPhysicalFiniteHeatWindow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorStationaryPosterior
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPartitionDominationGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Literal raw ray numerator -/

/-- Sum of the unnormalised positive raw-row masses of exactly the excited
spin-cube sources `1,...,K`. -/
def centralLowerExcitedSpinCubeExactRawNumerator
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : Q' :=
  listQSum
    (fun offset =>
      centralPhysicalPositiveRawRowMass w hw K 0
        (centralLowerSpinCubeState (offset + 1)))
    (List.range K)

/-- The normalized ray mass is exactly the literal raw ray numerator times
the common physical partition reciprocal. -/
theorem centralLowerExcitedSpinCubeRayMass_eqv_exactRawNumerator_mul_reciprocal
    {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) :
    centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw0) K ≈
      centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K *
        centralPhysicalFiniteVacuumSectorPartitionReciprocal
          w (Q'.le_of_lt hw0) K 0 := by
  let reciprocal :=
    centralPhysicalFiniteVacuumSectorPartitionReciprocal
      w (Q'.le_of_lt hw0) K 0
  refine Q'.eqv_trans _
    (listQSum
      (fun offset =>
        centralPhysicalFiniteWeight w (Q'.le_of_lt hw0) K 0
          (centralLowerExcitedSpinCubeIndex
            w (Q'.le_of_lt hw0) K offset))
      (List.range K)) _
    (centralLowerExcitedSpinCubeRayMass_eqv_offset_sum
      w (Q'.le_of_lt hw0) K) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun offset =>
        centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0
            (centralLowerSpinCubeState (offset + 1)) * reciprocal)
      (List.range K)) _ ?_ ?_
  · apply listQSum_congr_on
    intro offset hoffsetMem
    have hoffset : offset < K := List.mem_range.mp hoffsetMem
    have hstate := centralPhysicalFiniteStateAt_spinCubeIndex_eq
      hw0 (by omega : offset + 1 ≤ K)
    have hrow :=
      centralPhysicalRowMarginal_eqv_positiveRawRowMass_mul_partitionReciprocal
        (w := w) (hw := Q'.le_of_lt hw0) (K := K) (half := 0)
        (source := centralLowerSpinCubeState (offset + 1))
        (centralLowerSpinCubeState_mem_centralHalfStates (by omega))
    unfold centralPhysicalFiniteWeight
    unfold centralLowerExcitedSpinCubeIndex
    rw [hstate]
    simpa only [reciprocal, centralPhysicalPositiveRawRowMass] using hrow
  · exact Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (fun offset =>
          centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0
            (centralLowerSpinCubeState (offset + 1)))
        reciprocal (List.range K))
      (Q'.mul_eqv_congr_right _ _ reciprocal (by
        unfold centralLowerExcitedSpinCubeExactRawNumerator
        exact Q'.eqv_refl _))

/-- Quotient form of the preceding exact normalization identity. -/
theorem centralLowerExcitedSpinCubeRayMass_eqv_exactRawNumerator_divPos
    {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) :
    centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw0) K ≈
      Q'.divPos
        (centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K)
        (slabParametricKPhysicalPartition w K (centralExtent 0))
        (slabParametricKPhysicalPartition_pos
          (Q'.le_of_lt hw0) K (centralExtent 0)) := by
  exact Q'.eqv_trans _ _ _
    (centralLowerExcitedSpinCubeRayMass_eqv_exactRawNumerator_mul_reciprocal
      hw0 K)
    (by
      unfold centralPhysicalFiniteVacuumSectorPartitionReciprocal Q'.divPos
      exact Q'.eqv_refl _)

/-- Exact cross-multiplication for the literal ray numerator. -/
theorem centralLowerExcitedSpinCubeRayMass_le_iff_exactPartitionDomination
    {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) (epsilon : Q') :
    centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw0) K ≤ epsilon ↔
      centralLowerExcitedSpinCubeExactRawNumerator
          w (Q'.le_of_lt hw0) K ≤
        epsilon *
          slabParametricKPhysicalPartition w K (centralExtent 0) := by
  let numerator := centralLowerExcitedSpinCubeExactRawNumerator
    w (Q'.le_of_lt hw0) K
  let partition := slabParametricKPhysicalPartition w K (centralExtent 0)
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      (Q'.le_of_lt hw0) K (centralExtent 0)
  have hray :
      centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw0) K ≈
        Q'.divPos numerator partition hpartition :=
    centralLowerExcitedSpinCubeRayMass_eqv_exactRawNumerator_divPos hw0 K
  constructor
  · intro hnormalized
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ partition
      hnormalized (Q'.le_of_lt hpartition)
    have hcollapse :
        centralLowerExcitedSpinCubeRayMass w (Q'.le_of_lt hw0) K *
            partition ≈ numerator :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ partition hray)
        (Q'.divPos_mul_eqv numerator partition hpartition)
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hcollapse) hscaled
  · intro hdomination
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hray)
      (Q'.divPos_le_of_le_mul
        numerator partition hpartition hdomination)

/-! ## 2. Relation to the explicit sufficient envelope -/

/-- The literal raw ray numerator is bounded by the earlier explicit
sixth-power/residual-carrier numerator. -/
theorem centralLowerExcitedSpinCubeExactRawNumerator_le_rawNumeratorEnvelope
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) :
    centralLowerExcitedSpinCubeExactRawNumerator
        w (Q'.le_of_lt hw0) K ≤
      centralLowerExcitedSpinCubeRawNumeratorEnvelope w K := by
  let ceiling := explicitFixedNomeCentralSpinCubeResidualCarrierCeiling w
  have hsum :
      listQSum
          (fun offset =>
            centralPhysicalPositiveRawRowMass w (Q'.le_of_lt hw0) K 0
              (centralLowerSpinCubeState (offset + 1)))
          (List.range K) ≤
        listQSum
          (fun offset => ((coeffW w (offset + 1)) ^ 6) * ceiling)
          (List.range K) := by
    apply listQSum_le_termwise_local
    intro offset hoffsetMem
    exact
      centralLowerSpinCubePositiveRawRow_le_activity_mul_explicitFixedNomeCeiling
        (w := w) (cutoff := K) (spin := offset + 1) hw0 hw1 (by
          have hoffset := List.mem_range.mp hoffsetMem
          omega)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv (by
      unfold centralLowerExcitedSpinCubeRawNumeratorEnvelope
      exact listQSum_mul_right
        (fun offset => (coeffW w (offset + 1)) ^ 6)
        ceiling (List.range K)))

/-! ## 3. Matched exact partition domination -/

def matchedExcitedSpinCubeExactRawNumerator
    (family : MatchedBlockFamily)
    (coupling : Nat → Q') (scale : Nat) : Q' :=
  centralLowerExcitedSpinCubeExactRawNumerator
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale)

/-- Located tail domination for the literal matched ray numerator. -/
structure MatchedDyadicExcitedSpinCubeExactRawPartitionDomination
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  rate : Q' → Nat
  numerator_le : ∀ epsilon, (0 : Q') < epsilon →
    ∀ scale, rate epsilon ≤ scale →
      matchedExcitedSpinCubeExactRawNumerator
          family coupling scale ≤
        epsilon *
          slabParametricKPhysicalPartition
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (centralExtent 0)

def MatchedDyadicExcitedSpinCubeExactRawPartitionDomination.toRayMassTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (domination :
      MatchedDyadicExcitedSpinCubeExactRawPartitionDomination bridge) :
    MatchedDyadicExcitedSpinCubeRayMassTailZero bridge where
  rate := domination.rate
  rayMass_le := by
    intro epsilon hepsilon scale hscale
    exact
      (centralLowerExcitedSpinCubeRayMass_le_iff_exactPartitionDomination
        (matchedAllSpinWeight_pos family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        epsilon).mpr
      (domination.numerator_le epsilon hepsilon scale hscale)

/-- Ray-mass tail zero gives the exact cross-multiplied domination with the
same located rate; hence this exact producer loses no analytic content. -/
def MatchedDyadicExcitedSpinCubeRayMassTailZero.toExactRawPartitionDomination
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (tail : MatchedDyadicExcitedSpinCubeRayMassTailZero bridge) :
    MatchedDyadicExcitedSpinCubeExactRawPartitionDomination bridge where
  rate := tail.rate
  numerator_le := by
    intro epsilon hepsilon scale hscale
    exact
      (centralLowerExcitedSpinCubeRayMass_le_iff_exactPartitionDomination
        (matchedAllSpinWeight_pos family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        epsilon).mp
      (tail.rayMass_le epsilon hepsilon scale hscale)

/-- The explicit coarse partition-domination producer implies the exact one,
while the converse is deliberately not asserted. -/
def MatchedDyadicExcitedSpinCubeRawPartitionDomination.toExact
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (domination :
      MatchedDyadicExcitedSpinCubeRawPartitionDomination bridge) :
    MatchedDyadicExcitedSpinCubeExactRawPartitionDomination bridge where
  rate := domination.rate
  numerator_le := by
    intro epsilon hepsilon scale hscale
    exact Q'.le_trans' _ _ _
      (centralLowerExcitedSpinCubeExactRawNumerator_le_rawNumeratorEnvelope
        (matchedAllSpinWeight_pos family coupling scale)
        (matchedPhysicalWeight_lt_one bridge scale)
        (matchedAllSpinCutoff family coupling scale))
      (domination.numerator_le epsilon hepsilon scale hscale)

/-- Exact matched partition domination is sufficient to exclude every
cutoff-uniform assigned-ratio ceiling. -/
theorem exactRawPartitionDomination_excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (domination :
      MatchedDyadicExcitedSpinCubeExactRawPartitionDomination bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) :=
  tailZero_excludes_cofinalAssignedRatio domination.toRayMassTailZero

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate.centralLowerExcitedSpinCubeRayMass_eqv_exactRawNumerator_mul_reciprocal
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate.centralLowerExcitedSpinCubeRayMass_le_iff_exactPartitionDomination
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate.centralLowerExcitedSpinCubeExactRawNumerator_le_rawNumeratorEnvelope
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate.MatchedDyadicExcitedSpinCubeExactRawPartitionDomination.toRayMassTailZero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate.MatchedDyadicExcitedSpinCubeRayMassTailZero.toExactRawPartitionDomination
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate.MatchedDyadicExcitedSpinCubeRawPartitionDomination.toExact
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayExactPartitionGate.exactRawPartitionDomination_excludes_cofinalAssignedRatio
