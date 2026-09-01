/-
# Exact finite-sector classifier for BF4 vacuum-root spokes

The raw vacuum-root reduction is useful for routing only after it is carried
through the normalized finite-index kernel used by the canonical vacuum
sector.  This module performs that transport without changing the carrier.

For every index in the finite vacuum sector, positivity of its normalized
kernel entry into index zero is equivalent to positivity of the represented
state's half-amplitude against the all-vacuum boundary.  Consequently the
existing list of positive root predecessors is exactly an executable filter
by this one surviving amplitude, and its cardinality is exactly the length of
that amplitude filter.

This is an exact carrier reduction.  It does not give a closed-form
classification, an asymptotic cardinality bound, a distributed routing, a
gap, a continuum limit, or a Clay conclusion.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumRootSpokeAmplitudeReduction
import YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout

namespace YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumRootSpokeAmplitudeReduction
open YMGap.Continuum.BF4PhysicalVacuumSectorMassExactSimpleRootResistanceTerminalFanout
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positive normalization preserves and reflects positive support -/

/-- Dividing a raw reflected-kernel entry by the strictly positive physical
partition preserves and reflects strict positivity. -/
theorem centralNormalizedPhysicalReflectedKernel_pos_iff_raw_pos
    {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (source target : EdgeLabelling) :
    (0 : Q') < centralNormalizedPhysicalReflectedKernel
        w hw K half source target ↔
      (0 : Q') < centralPhysicalReflectedKernel
        w K half source target := by
  let partition :=
    slabParametricKPhysicalPartition w K (centralExtent half)
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos hw K (centralExtent half)
  constructor
  · intro hnormalized
    have hproduct :
        (0 : Q') <
          centralNormalizedPhysicalReflectedKernel
              w hw K half source target * partition :=
      Q'.mul_pos hnormalized hpartition
    have hcollapse :
        centralNormalizedPhysicalReflectedKernel
            w hw K half source target * partition ≈
          centralPhysicalReflectedKernel w K half source target := by
      unfold centralNormalizedPhysicalReflectedKernel
      exact Q'.divPos_mul_eqv
        (centralPhysicalReflectedKernel w K half source target)
        partition hpartition
    exact Q'.pos_of_lt_of_le hproduct (Q'.le_of_eqv hcollapse)
  · intro hraw
    unfold centralNormalizedPhysicalReflectedKernel
    exact Q'.divPos_pos _ _ hpartition hraw

/-! ## 2. Indexed root-spoke positivity is one amplitude test -/

theorem centralPhysicalFiniteKernel_source_vacuum_pos_iff_amplitude_pos
    {w : Q'} (hw : (0 : Q') ≤ w) (K source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    (0 : Q') < centralPhysicalFiniteKernel w hw K 0 source 0 ↔
      (0 : Q') < centralHalfAmplitude w K 0
        (centralPhysicalFiniteStateAt w hw K 0 source)
        zeroEdgeLabelling := by
  have hsourceState :
      centralPhysicalFiniteStateAt w hw K 0 source ∈
        centralPhysicalFiniteVacuumSectorStates w hw K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_of_index
      w hw K 0 hsource rfl
  have hsourceHalf :
      centralPhysicalFiniteStateAt w hw K 0 source ∈
        centralHalfStates K 0 :=
    centralPhysicalFiniteVacuumSectorState_mem_halfStates
      w hw K 0 hsourceState
  unfold centralPhysicalFiniteKernel
  rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
  exact Iff.trans
    (centralNormalizedPhysicalReflectedKernel_pos_iff_raw_pos
      hw K 0
      (centralPhysicalFiniteStateAt w hw K 0 source)
      zeroEdgeLabelling)
    (centralPhysicalReflectedKernel_source_vacuum_pos_iff_amplitude_pos
      hw K (centralPhysicalFiniteStateAt w hw K 0 source) hsourceHalf)

/-! ## 3. Exact executable predecessor carrier and count -/

/-- The finite vacuum-sector indices whose represented state has positive
half-amplitude against the all-vacuum boundary. -/
def centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw K 0).filter
    (fun source => decide
      ((0 : Q') < centralHalfAmplitude w K 0
        (centralPhysicalFiniteStateAt w hw K 0 source)
        zeroEdgeLabelling))

theorem mem_positiveVacuumAmplitudeIndices_iff
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat} :
    source ∈
        centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices
          w hw K ↔
      source ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0 ∧
        (0 : Q') < centralHalfAmplitude w K 0
          (centralPhysicalFiniteStateAt w hw K 0 source)
          zeroEdgeLabelling := by
  unfold centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices
  simp only [List.mem_filter, decide_eq_true_eq]

/-- The routing-level positive root-predecessor list is definitionally on the
same finite sector and propositionally exactly the one-amplitude filter. -/
theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_amplitudeIndices
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralPhysicalFiniteVacuumSectorPositiveRootPredecessors w hw K =
      centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices
        w hw K := by
  unfold centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
    centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices
  apply List.filter_congr
  intro source hsource
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact centralPhysicalFiniteKernel_source_vacuum_pos_iff_amplitude_pos
    hw K source hsource

theorem centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_amplitudeCount
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors
        w hw K).length =
      (centralPhysicalFiniteVacuumSectorPositiveVacuumAmplitudeIndices
        w hw K).length :=
  congrArg List.length
    (centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_amplitudeIndices
      w hw K)

end YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier.centralNormalizedPhysicalReflectedKernel_pos_iff_raw_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier.centralPhysicalFiniteKernel_source_vacuum_pos_iff_amplitude_pos
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier.mem_positiveVacuumAmplitudeIndices_iff
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_eq_amplitudeIndices
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorRootSpokeAmplitudeClassifier.centralPhysicalFiniteVacuumSectorPositiveRootPredecessors_length_eq_amplitudeCount
