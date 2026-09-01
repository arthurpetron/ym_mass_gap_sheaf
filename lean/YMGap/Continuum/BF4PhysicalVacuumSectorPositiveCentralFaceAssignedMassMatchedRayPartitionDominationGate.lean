/-
# Exact partition-domination gate for the matched spin-cube ray

The explicit raw envelope for the normalized excited spin-cube ray is a
literal quotient: its raw numerator is divided by the complete corrected-slab
physical partition.  This file removes the reciprocal notation and proves
that an epsilon bound on the normalized envelope is equivalent to the exact
cross-multiplied partition-domination inequality

  rawNumerator <= epsilon * physicalPartition.

Thus a located tail estimate for that concrete inequality constructs ray-mass
tail zero and excludes the cutoff-uniform assigned-ratio route.  No such
partition-growth estimate is inhabited here.  In particular, the general
vacuum lower bound `1 <= physicalPartition` is not claimed to be sufficient.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPartitionDominationGate

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayRawEnvelope
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact raw numerator / physical partition quotient -/

/-- The cutoff-finite raw numerator in the explicit ray envelope, before the
common physical partition reciprocal is applied. -/
def centralLowerExcitedSpinCubeRawNumeratorEnvelope
    (w : Q') (K : Nat) : Q' :=
  listQSum
      (fun offset => (coeffW w (offset + 1)) ^ 6)
      (List.range K) *
    explicitFixedNomeCentralSpinCubeResidualCarrierCeiling w

/-- The explicit normalized envelope is exactly the raw numerator divided by
the complete corrected-slab physical partition. -/
theorem centralLowerExcitedSpinCubeRawEnvelope_eqv_divPos
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralLowerExcitedSpinCubeRawEnvelope w hw K ≈
      Q'.divPos
        (centralLowerExcitedSpinCubeRawNumeratorEnvelope w K)
        (slabParametricKPhysicalPartition w K (centralExtent 0))
        (slabParametricKPhysicalPartition_pos
          hw K (centralExtent 0)) := by
  unfold centralLowerExcitedSpinCubeRawEnvelope
    centralLowerExcitedSpinCubeRawNumeratorEnvelope
    centralPhysicalFiniteVacuumSectorPartitionReciprocal
    Q'.divPos
  exact Q'.eqv_refl _

/-- Exact cross-multiplication: bounding the normalized envelope by
`epsilon` is equivalent to making the full physical partition dominate its
raw numerator by the factor `epsilon`. -/
theorem centralLowerExcitedSpinCubeRawEnvelope_le_iff_partitionDomination
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (epsilon : Q') :
    centralLowerExcitedSpinCubeRawEnvelope w hw K ≤ epsilon ↔
      centralLowerExcitedSpinCubeRawNumeratorEnvelope w K ≤
        epsilon *
          slabParametricKPhysicalPartition w K (centralExtent 0) := by
  let numerator := centralLowerExcitedSpinCubeRawNumeratorEnvelope w K
  let partition := slabParametricKPhysicalPartition w K (centralExtent 0)
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos hw K (centralExtent 0)
  have henvelope :
      centralLowerExcitedSpinCubeRawEnvelope w hw K ≈
        Q'.divPos numerator partition hpartition := by
    exact centralLowerExcitedSpinCubeRawEnvelope_eqv_divPos w hw K
  constructor
  · intro hnormalized
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ partition
      hnormalized (Q'.le_of_lt hpartition)
    have hcollapse :
        centralLowerExcitedSpinCubeRawEnvelope w hw K * partition ≈
          numerator := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ partition henvelope)
        (Q'.divPos_mul_eqv numerator partition hpartition)
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hcollapse) hscaled
  · intro hdomination
    have hquotient := Q'.divPos_le_of_le_mul
      numerator partition hpartition hdomination
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv henvelope) hquotient

/-! ## 2. Matched same-action domination producer -/

def matchedExcitedSpinCubeRawNumeratorEnvelope
    (family : MatchedBlockFamily)
    (coupling : Nat → Q') (scale : Nat) : Q' :=
  centralLowerExcitedSpinCubeRawNumeratorEnvelope
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinCutoff family coupling scale)

/-- Located tail domination of the explicit raw numerator by the actual
matched corrected-slab physical partition.  This is the concrete analytic
producer now required; no inhabitant is asserted here. -/
structure MatchedDyadicExcitedSpinCubeRawPartitionDomination
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
      matchedExcitedSpinCubeRawNumeratorEnvelope
          family coupling scale ≤
        epsilon *
          slabParametricKPhysicalPartition
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (centralExtent 0)

def MatchedDyadicExcitedSpinCubeRawPartitionDomination.toRawEnvelopeTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (domination :
      MatchedDyadicExcitedSpinCubeRawPartitionDomination bridge) :
    MatchedDyadicExcitedSpinCubeRawEnvelopeTailZero bridge where
  rate := domination.rate
  envelope_le := by
    intro epsilon hepsilon scale hscale
    exact
      (centralLowerExcitedSpinCubeRawEnvelope_le_iff_partitionDomination
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        epsilon).mpr
      (domination.numerator_le epsilon hepsilon scale hscale)

/-- The concrete matched partition-domination producer is sufficient to
exclude every cutoff-uniform assigned-ratio ceiling. -/
theorem rawPartitionDomination_excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (domination :
      MatchedDyadicExcitedSpinCubeRawPartitionDomination bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) :=
  rawEnvelopeTailZero_excludes_cofinalAssignedRatio
    domination.toRawEnvelopeTailZero

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPartitionDominationGate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPartitionDominationGate.centralLowerExcitedSpinCubeRawEnvelope_eqv_divPos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPartitionDominationGate.centralLowerExcitedSpinCubeRawEnvelope_le_iff_partitionDomination
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPartitionDominationGate.MatchedDyadicExcitedSpinCubeRawPartitionDomination.toRawEnvelopeTailZero
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayPartitionDominationGate.rawPartitionDomination_excludes_cofinalAssignedRatio
