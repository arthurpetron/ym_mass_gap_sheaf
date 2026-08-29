/-
# A positive recoupling target for the guarded reflected graft

At the unique reflected pivot, select the target at the finite written rank
of the explicit component-preserving source.  At every other corrected-slab
link, use the constructive positive-target compiler for the actual graft
source row.  Structural recursion assembles these choices into a written
global target with strictly positive recoupling product weight.

This module selects and proves positivity of the target column.  Realizing
that target as accepted auxiliary assignments and proving marked-face
disconnection are separate downstream contractions.

Constructive contract: one explicit SU(2) pivot column, normalized finite-row
positive search elsewhere, and dependent finite products only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticPositiveTarget
import YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticPositiveTarget
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
open YMGap.Continuum.FiniteBistochasticRankReindex
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2CanonicalLeftCarrierWitnessReconstruction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabInternalVacuumValenceFiveRecouplingFloor
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceDecidableEquality
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotPairing
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabTargetRealization
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

/-! ## 1. Transport the explicit pivot column through the guard word -/

theorem reflectedBentPatternActiveLinkB_pivot :
    reflectedBentPatternActiveLinkB reflectedBentSwitchPivot = true := by
  decide

theorem reflectedBentGuardGraftLeftExternalSpins_eq_pattern_at_pivot
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabLinkExternalSpins 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot =
      slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot :=
  reflectedBentGuardGraftLeftExternalSpins_eq_pattern_of_active
    D hextent state
    reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks
    reflectedBentPatternActiveLinkB_pivot

theorem reflectedBentGuardGraftRightExternalSpins_eq_pattern_at_pivot
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabLinkExternalSpins 5
        (reflectedBentGuardGraftRightPhysical D hextent state)
        reflectedBentSwitchPivot =
      slabLinkExternalSpins 5 reflectedBentSwitchRightPhysical
        reflectedBentSwitchPivot :=
  reflectedBentGuardGraftRightExternalSpins_eq_pattern_of_active
    D hextent state
    reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks
    reflectedBentPatternActiveLinkB_pivot

/-- The graft physical pair at the unique pivot, indexed directly by its
proved valence five. -/
def reflectedBentGuardGraftPivotRecouplingData
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabPhysicalPairRecouplingData 5 5 where
  leftPhysical := reflectedBentGuardGraftLeftPhysical D hextent state
  rightPhysical := reflectedBentGuardGraftRightPhysical D hextent state
  link := reflectedBentSwitchPivot
  degree_eq := reflectedBentSwitchPivot_degree_five

/-- A target-valued fallback obtained by transporting the original reflected
column through equality of all ten external spin coordinates.  The intrinsic
rank selector below never inspects this value because its source is listed. -/
def reflectedBentGuardGraftPivotTransportedTarget
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (slabPhysicalPairRecouplingKernelPackageFive
      (reflectedBentGuardGraftPivotRecouplingData
        D hextent state)).Target := by
  unfold slabPhysicalPairRecouplingKernelPackageFive
    reflectedBentGuardGraftPivotRecouplingData
  rw [reflectedBentGuardGraftLeftExternalSpins_eq_pattern_at_pivot
    D hextent state]
  rw [reflectedBentGuardGraftRightExternalSpins_eq_pattern_at_pivot
    D hextent state]
  exact reflectedBentPivotTarget

theorem reflectedBentGuardGraftPivotLeftAuxiliary_mem
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentPivotLeftAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        reflectedBentSwitchPivot := by
  rw [reflectedBentGuardGraftLeftFusionWitnesses_eq_pattern_of_active
    1 D hextent state
    reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks
    reflectedBentPatternActiveLinkB_pivot]
  exact reflectedBentPivotLeftAuxiliary_mem

theorem reflectedBentGuardGraftPivotRightAuxiliary_mem
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentPivotRightAuxiliary ∈
      slabLinkFusionWitnesses 1 5
        (reflectedBentGuardGraftRightPhysical D hextent state)
        reflectedBentSwitchPivot := by
  rw [reflectedBentGuardGraftRightFusionWitnesses_eq_pattern_of_active
    1 D hextent state
    reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks
    reflectedBentPatternActiveLinkB_pivot]
  exact valenceFiveLeftAuxiliary_mem_slabLinkFusionWitnesses
    reflectedBentSwitchRightPhysical_bounded
    reflectedBentSwitchPivot_degree_five
    reflectedBentPivotRightSource

def reflectedBentGuardGraftPivotComponentAnchor
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabPhysicalPairRecouplingWitnessData 1
      (reflectedBentGuardGraftPivotRecouplingData D hextent state) where
  leftAuxiliary := reflectedBentPivotLeftAuxiliary
  rightAuxiliary := reflectedBentPivotRightAuxiliary
  left_mem := reflectedBentGuardGraftPivotLeftAuxiliary_mem
    D hextent state
  right_mem := reflectedBentGuardGraftPivotRightAuxiliary_mem
    D hextent state

def reflectedBentGuardGraftPivotComponentSource
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (slabPhysicalPairRecouplingKernelPackageFive
      (reflectedBentGuardGraftPivotRecouplingData
        D hextent state)).Source :=
  slabPhysicalPairRecouplingProductionSource 5
    (reflectedBentGuardGraftPivotRecouplingData D hextent state)
    (reflectedBentGuardGraftPivotComponentAnchor D hextent state)

theorem reflectedBentGuardGraftPivotComponentSource_mem
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftPivotComponentSource D hextent state ∈
      (slabPhysicalPairRecouplingKernelPackageFive
        (reflectedBentGuardGraftPivotRecouplingData
          D hextent state)).kernel.sources :=
  slabPhysicalPairRecouplingProductionSource_mem
    (reflectedBentGuardGraftPivotRecouplingData D hextent state)
    (reflectedBentGuardGraftPivotComponentAnchor D hextent state)

/-- Select the target at the written rank of the desired component-preserving
production source.  This presentation makes its canonical realization an
exact finite-rank inverse rather than a dependent transport computation. -/
def reflectedBentGuardGraftPivotTargetAtComponentRank
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (slabPhysicalPairRecouplingKernelPackageFive
      (reflectedBentGuardGraftPivotRecouplingData
        D hextent state)).Target := by
  letI : DecidableEq
      (slabPhysicalPairRecouplingKernelPackageFive
        (reflectedBentGuardGraftPivotRecouplingData
          D hextent state)).Source := by
    exact slabPhysicalPairRecouplingKernelPackageSourceDecidableEq 5
      (reflectedBentGuardGraftPivotRecouplingData D hextent state)
  exact FiniteBistochasticQKernel.sourceToTargetAtEqualRank
    (slabPhysicalPairRecouplingKernelPackageFive
      (reflectedBentGuardGraftPivotRecouplingData
        D hextent state)).kernel
    (reflectedBentGuardGraftPivotTransportedTarget D hextent state)
    (reflectedBentGuardGraftPivotComponentSource D hextent state)

/-- Seal the rank calculation behind a data-bearing package so downstream
dependent target products do not repeatedly normalize the finite carrier
enumeration. -/
structure ReflectedBentGuardGraftPivotTargetPackage
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Type where
  target : (slabPhysicalPairRecouplingKernelPackageFive
    (reflectedBentGuardGraftPivotRecouplingData D hextent state)).Target
  target_eq_componentRank : target =
    reflectedBentGuardGraftPivotTargetAtComponentRank D hextent state

opaque reflectedBentGuardGraftPivotTargetPackage
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ReflectedBentGuardGraftPivotTargetPackage D hextent state :=
  { target := reflectedBentGuardGraftPivotTargetAtComponentRank
      D hextent state
    target_eq_componentRank := rfl }

abbrev reflectedBentGuardGraftPivotTarget
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :=
  (reflectedBentGuardGraftPivotTargetPackage D hextent state).target

theorem reflectedBentGuardGraftPivotTarget_eq_componentRank
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftPivotTarget D hextent state =
      reflectedBentGuardGraftPivotTargetAtComponentRank
        D hextent state :=
  (reflectedBentGuardGraftPivotTargetPackage
    D hextent state).target_eq_componentRank

theorem reflectedBentGuardGraftPivot_kernel_pos
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      (reflectedBentGuardGraftPivotRecouplingData
        D hextent state)).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      (reflectedBentGuardGraftPivotRecouplingData
        D hextent state)).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive
        (reflectedBentGuardGraftPivotRecouplingData
          D hextent state)).kernel.weight source target := by
  have hleft :=
    reflectedBentGuardGraftLeftExternalSpins_eq_pattern_at_pivot
      D hextent state
  have hright :=
    reflectedBentGuardGraftRightExternalSpins_eq_pattern_at_pivot
      D hextent state
  apply Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
  exact slabPhysicalPairRecouplingKernelPackageFive_internalVacuum_floor
    (reflectedBentGuardGraftPivotRecouplingData D hextent state)
    ((congrFun hleft 0).trans
      reflectedBentSwitchPivot_leftExternal_zero)
    ((congrFun hleft 1).trans
      reflectedBentSwitchPivot_leftExternal_one)
    ((congrFun hleft 2).trans
      reflectedBentSwitchPivot_leftExternal_two)
    ((congrFun hleft 3).trans
      reflectedBentSwitchPivot_leftExternal_three)
    ((congrFun hleft 4).trans
      reflectedBentSwitchPivot_leftExternal_four)
    ((congrFun hright 0).trans
      reflectedBentSwitchPivot_rightExternal_zero)
    ((congrFun hright 1).trans
      reflectedBentSwitchPivot_rightExternal_one)
    ((congrFun hright 2).trans
      reflectedBentSwitchPivot_rightExternal_two)
    ((congrFun hright 3).trans
      reflectedBentSwitchPivot_rightExternal_three)
    ((congrFun hright 4).trans
      reflectedBentSwitchPivot_rightExternal_four)
    source target

/-! ## 2. The actual graft row and its local positive selector -/

theorem reflectedBentGuardGraftLeftAssignment_mem_five
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLeftAssignment D hextent state ∈
      slabFusionWitnessAssignmentsOn 1 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (boundaryCompleteSlabLinks 5) := by
  have hmem := reflectedBentGuardGraftLeftAssignment_mem
    D hcutoff hextent state
  unfold slabFineFusionWitnesses at hmem
  simpa only [hcutoff, hextent] using hmem

theorem reflectedBentGuardGraftRightAssignment_mem_five
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightAssignment D hextent state ∈
      slabFusionWitnessAssignmentsOn 1 5
        (reflectedBentGuardGraftRightPhysical D hextent state)
        (boundaryCompleteSlabLinks 5) := by
  have hmem := reflectedBentGuardGraftRightAssignment_mem
    D hcutoff hextent state
  unfold slabFineFusionWitnesses at hmem
  simpa only [hcutoff, hextent] using hmem

def reflectedBentGuardGraftLocalData
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingDataAtLink 5
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state) linked

def reflectedBentGuardGraftLocalAnchor
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingWitnessDataAtLink 1 5
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state)
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem_five
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightAssignment_mem_five
      D hcutoff hextent state) linked

def reflectedBentGuardGraftLocalSource
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingProductionSource
    (slabIncidentPlaqIds 5 linked.1).length
    (reflectedBentGuardGraftLocalData D hextent state linked)
    (reflectedBentGuardGraftLocalAnchor
      D hcutoff hextent state linked)

/-- Preserve the component-separating column at the unique pivot and compute
a positive target from row normalization at every other link. -/
def reflectedBentGuardGraftTargetForData
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (degree : Nat) →
    (localData : SlabPhysicalPairRecouplingData 5 degree) →
    localData.leftPhysical =
        reflectedBentGuardGraftLeftPhysical D hextent state →
    localData.rightPhysical =
        reflectedBentGuardGraftRightPhysical D hextent state →
    (source : (slabPhysicalPairRecouplingKernelPackage
      degree localData).Source) →
      (slabPhysicalPairRecouplingKernelPackage
        degree localData).Target
  | 0, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackage
          0 localData).kernel source |>.target
  | 1, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackage
          1 localData).kernel source |>.target
  | 2, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackage
          2 localData).kernel source |>.target
  | 3, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackage
          3 localData).kernel source |>.target
  | 4, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackageFour
          localData).kernel source |>.target
  | 5, localData, hleft, hright, source => by
      by_cases hpivot : localData.link = reflectedBentSwitchPivot
      · have hdata : localData =
            reflectedBentGuardGraftPivotRecouplingData
              D hextent state := by
          cases localData with
          | mk leftPhysical rightPhysical link degree_eq =>
              dsimp at hleft hright hpivot
              cases hleft
              cases hright
              cases hpivot
              rfl
        rw [hdata]
        exact reflectedBentGuardGraftPivotTarget D hextent state
      · exact finiteBistochasticPositiveTarget
          (slabPhysicalPairRecouplingKernelPackageFive
            localData).kernel source |>.target
  | 6, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackageSix
          localData).kernel source |>.target
  | degree + 7, localData, _, _, _ => False.elim (by
      have hdegree := localData.degree_le_six
      omega)

theorem reflectedBentGuardGraftTargetForPivot_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      (reflectedBentGuardGraftPivotRecouplingData
        D hextent state)).Source) :
    reflectedBentGuardGraftTargetForData D hextent state 5
        (reflectedBentGuardGraftPivotRecouplingData D hextent state)
        rfl rfl source =
      reflectedBentGuardGraftPivotTarget D hextent state := by
  simp only [reflectedBentGuardGraftTargetForData]
  split
  · rfl
  · rename_i hnonpivot
    exact False.elim (hnonpivot rfl)

theorem reflectedBentGuardGraftTargetForData_pos
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ (degree : Nat)
      (localData : SlabPhysicalPairRecouplingData 5 degree)
      (hleft : localData.leftPhysical =
        reflectedBentGuardGraftLeftPhysical D hextent state)
      (hright : localData.rightPhysical =
        reflectedBentGuardGraftRightPhysical D hextent state)
      (source : (slabPhysicalPairRecouplingKernelPackage
        degree localData).Source),
      (0 : Q') <
        (slabPhysicalPairRecouplingKernelPackage
          degree localData).kernel.weight source
            (reflectedBentGuardGraftTargetForData
              D hextent state degree localData hleft hright source)
  | 0, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackage
          0 localData).kernel source |>.weight_pos
  | 1, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackage
          1 localData).kernel source |>.weight_pos
  | 2, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackage
          2 localData).kernel source |>.weight_pos
  | 3, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackage
          3 localData).kernel source |>.weight_pos
  | 4, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackageFour
          localData).kernel source |>.weight_pos
  | 5, localData, hleft, hright, source => by
      by_cases hpivot : localData.link = reflectedBentSwitchPivot
      · have hdata : localData =
            reflectedBentGuardGraftPivotRecouplingData
              D hextent state := by
          cases localData with
          | mk leftPhysical rightPhysical link degree_eq =>
              dsimp at hleft hright hpivot
              cases hleft
              cases hright
              cases hpivot
              rfl
        subst localData
        rw [reflectedBentGuardGraftTargetForPivot_eq]
        exact reflectedBentGuardGraftPivot_kernel_pos
          D hextent state source
            (reflectedBentGuardGraftPivotTarget D hextent state)
      · simpa [reflectedBentGuardGraftTargetForData, hpivot] using
          (finiteBistochasticPositiveTarget
            (slabPhysicalPairRecouplingKernelPackageFive
              localData).kernel source |>.weight_pos)
  | 6, localData, _, _, source =>
      finiteBistochasticPositiveTarget
        (slabPhysicalPairRecouplingKernelPackageSix
          localData).kernel source |>.weight_pos
  | degree + 7, localData, _, _, _ => False.elim (by
      have hdegree := localData.degree_le_six
      omega)

def reflectedBentGuardGraftLocalTarget
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  reflectedBentGuardGraftTargetForData D hextent state
    (slabIncidentPlaqIds 5 linked.1).length
    (reflectedBentGuardGraftLocalData D hextent state linked)
    rfl rfl
    (reflectedBentGuardGraftLocalSource
      D hcutoff hextent state linked)

theorem reflectedBentGuardGraftLocalTarget_pos
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        linked).kernel.weight
        (reflectedBentGuardGraftLocalSource
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftLocalTarget
          D hcutoff hextent state linked) :=
  reflectedBentGuardGraftTargetForData_pos D hextent state
    (slabIncidentPlaqIds 5 linked.1).length
    (reflectedBentGuardGraftLocalData D hextent state linked)
    rfl rfl
    (reflectedBentGuardGraftLocalSource
      D hcutoff hextent state linked)

/-! ## 3. Whole-slab target assembly and positive product entry -/

def reflectedBentGuardGraftTargetAssignmentFrom
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) →
      FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)
  | [] => ()
  | linked :: rest =>
      (reflectedBentGuardGraftLocalTarget
          D hcutoff hextent state linked,
        reflectedBentGuardGraftTargetAssignmentFrom
          D hcutoff hextent state rest)

theorem reflectedBentGuardGraftTargetAssignmentFrom_mem
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftTargetAssignmentFrom
          D hcutoff hextent state linkedList ∈
        finiteBistochasticTargetAssignments
          (linkedList.map fun linked =>
            slabPhysicalPairRecouplingPackageAtLink 5
              (reflectedBentGuardGraftLeftPhysical D hextent state)
              (reflectedBentGuardGraftRightPhysical D hextent state)
              linked)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, finiteBistochasticTargetAssignments,
        reflectedBentGuardGraftTargetAssignmentFrom]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftLocalTarget
          D hcutoff hextent state linked, ?_, ?_⟩
      · unfold slabPhysicalPairRecouplingPackageAtLink
        exact slabPhysicalPairRecouplingTarget_mem
          (slabIncidentPlaqIds 5 linked.1).length
          (reflectedBentGuardGraftLocalData D hextent state linked)
          (reflectedBentGuardGraftLocalTarget
            D hcutoff hextent state linked)
      · exact List.mem_map.mpr
          ⟨reflectedBentGuardGraftTargetAssignmentFrom
              D hcutoff hextent state rest,
            reflectedBentGuardGraftTargetAssignmentFrom_mem
              D hcutoff hextent state rest, rfl⟩

theorem reflectedBentGuardGraftTargetAssignmentFrom_coordinatewise_pos
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5},
      FiniteBistochasticCoordinatewisePositive
        (slabPhysicalPairRecouplingProductionSourceFrom 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (reflectedBentGuardGraftLeftAssignment D hextent state)
          (reflectedBentGuardGraftRightAssignment D hextent state)
          (reflectedBentGuardGraftLeftAssignment_mem_five
            D hcutoff hextent state)
          (reflectedBentGuardGraftRightAssignment_mem_five
            D hcutoff hextent state)
          linkedList)
        (reflectedBentGuardGraftTargetAssignmentFrom
          D hcutoff hextent state linkedList)
  | [] => True.intro
  | linked :: rest => by
      constructor
      · exact reflectedBentGuardGraftLocalTarget_pos
          D hcutoff hextent state linked
      · exact
          reflectedBentGuardGraftTargetAssignmentFrom_coordinatewise_pos
            D hcutoff hextent state rest

theorem reflectedBentGuardGraftTargetAssignmentFrom_weight_pos
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (0 : Q') <
      finiteBistochasticProductWeight
        (slabPhysicalPairRecouplingProductionSourceFrom 1 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (reflectedBentGuardGraftLeftAssignment D hextent state)
          (reflectedBentGuardGraftRightAssignment D hextent state)
          (reflectedBentGuardGraftLeftAssignment_mem_five
            D hcutoff hextent state)
          (reflectedBentGuardGraftRightAssignment_mem_five
            D hcutoff hextent state)
          linkedList)
        (reflectedBentGuardGraftTargetAssignmentFrom
          D hcutoff hextent state linkedList) :=
  finiteBistochasticProductWeight_pos_of_coordinatewise _ _
    (reflectedBentGuardGraftTargetAssignmentFrom_coordinatewise_pos
      D hcutoff hextent state linkedList)

#print axioms reflectedBentPatternActiveLinkB_pivot
#print axioms reflectedBentGuardGraftPivotTarget
#print axioms reflectedBentGuardGraftPivot_kernel_pos
#print axioms reflectedBentGuardGraftTargetForData
#print axioms reflectedBentGuardGraftTargetForData_pos
#print axioms reflectedBentGuardGraftLocalTarget_pos
#print axioms reflectedBentGuardGraftTargetAssignmentFrom_mem
#print axioms reflectedBentGuardGraftTargetAssignmentFrom_coordinatewise_pos
#print axioms reflectedBentGuardGraftTargetAssignmentFrom_weight_pos

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
