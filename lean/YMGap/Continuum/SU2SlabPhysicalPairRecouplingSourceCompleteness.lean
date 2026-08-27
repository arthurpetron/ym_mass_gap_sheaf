/-
# Literal source completeness for physical-pair recoupling packages

This module proves that the complete source carriers used by the physical-pair
recoupling matrices are genuinely enumerated by their written source lists.
Fixed-valence package views keep each proof below the ordinary elaboration
gate; the all-valence wrapper is assembled only after those small proofs are
opaque.

Constructive contract: explicit finite carrier enumerations only; no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.SU2CompleteCarrierDecidableEquality

namespace YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteBistochasticQKernelIndexedSum
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.SU2DirectLeftFixedOutputEnumeration
open YMGap.Continuum.SU2CanonicalHigherValenceFusionChainBridge
open YMGap.Continuum.SU2CompleteCarrierDecidableEquality
open YMGap.Continuum.SU2FixedLeftTransvectantEvaluation
open YMGap.Continuum.SU2PhysicalSchurBistochasticKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2ValenceFiveCommonAssociatorCarrier
open YMGap.Continuum.SU2ValenceFiveFirstBistochasticBlock
open YMGap.Continuum.SU2ValenceFiveSecondBistochasticBlock
open YMGap.Continuum.SU2ValenceSixPrefixBistochasticBlock
open YMGap.Continuum.SU2ValenceSixThirdBistochasticBlock
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Fixed valence four -/

theorem physicalSchurTensorSources_complete
    {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : Nat}
    (source : FixedLeftCGChannel a₁ b₁ c₁ d₁ ×
      FixedLeftCGChannel a₂ b₂ c₂ d₂) :
    source ∈
      (tensor
        (physicalSchurBistochasticKernel a₁ b₁ c₁ d₁)
        (physicalSchurBistochasticKernel a₂ b₂ c₂ d₂)).sources := by
  exact (mem_cartesian_iff _ _ source).mpr
    ⟨fixedLeftChannels_complete source.1,
      fixedLeftChannels_complete source.2⟩

/-- Every valence-four source pair occurs in the literal tensor source list. -/
theorem slabPhysicalPairRecouplingKernelPackageFour_sources_complete
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 4)
    (source : (slabPhysicalPairRecouplingKernelPackageFour D).Source) :
    source ∈
      (slabPhysicalPairRecouplingKernelPackageFour D).kernel.sources := by
  exact physicalSchurTensorSources_complete source

/-! ## 2. Fixed valence five -/

theorem valenceFiveLeftCarriers_complete
    {a b c d e : Nat}
    (source : ValenceFiveLeftCarrier a b c d e) :
    source ∈ (valenceFiveBistochasticKernel a b c d e).sources := by
  change source ∈ valenceFiveLeftCarriers a b c d e
  unfold valenceFiveLeftCarriers
  let index : ValenceFiveTransientIndex a b c d e :=
    ⟨source.y, valenceFiveLeftCarrier_y_mem_transientOutputs source⟩
  apply List.mem_flatMap.mpr
  refine ⟨index, List.mem_attach _ index, ?_⟩
  unfold valenceFiveLeftFiber
  apply List.mem_map.mpr
  refine ⟨source.firstLeft, fixedLeftChannels_complete source.firstLeft, ?_⟩
  exact valenceFiveLeftCarrier_eq_of_y_k_eq
    { y := index.val
      firstLeft := source.firstLeft
      suffix := transientSuffix index }
    source rfl rfl

theorem valenceFiveTensorSources_complete
    {a₁ b₁ c₁ d₁ e₁ a₂ b₂ c₂ d₂ e₂ : Nat}
    (source : ValenceFiveLeftCarrier a₁ b₁ c₁ d₁ e₁ ×
      ValenceFiveLeftCarrier a₂ b₂ c₂ d₂ e₂) :
    source ∈
      (tensor
        (valenceFiveBistochasticKernel a₁ b₁ c₁ d₁ e₁)
        (valenceFiveBistochasticKernel a₂ b₂ c₂ d₂ e₂)).sources := by
  exact (mem_cartesian_iff _ _ source).mpr
    ⟨valenceFiveLeftCarriers_complete source.1,
      valenceFiveLeftCarriers_complete source.2⟩

theorem slabPhysicalPairRecouplingKernelPackageFive_sources_complete
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 5)
    (source : (slabPhysicalPairRecouplingKernelPackageFive D).Source) :
    source ∈
      (slabPhysicalPairRecouplingKernelPackageFive D).kernel.sources :=
  valenceFiveTensorSources_complete source

/-! ## 3. Fixed valence six -/

theorem valenceSixLeftCarriers_complete
    {a b c d e f : Nat}
    (source : ValenceSixLeftCarrier a b c d e f) :
    source ∈ (valenceSixBistochasticKernel a b c d e f).sources := by
  change source ∈
    (valenceSixPrefixBistochasticKernel a b c d e f).sources
  unfold valenceSixPrefixBistochasticKernel
  apply indexedSources_complete
  intro z localSource
  exact valenceFiveLeftCarriers_complete localSource

theorem valenceSixTensorSources_complete
    {a₁ b₁ c₁ d₁ e₁ f₁ a₂ b₂ c₂ d₂ e₂ f₂ : Nat}
    (source : ValenceSixLeftCarrier a₁ b₁ c₁ d₁ e₁ f₁ ×
      ValenceSixLeftCarrier a₂ b₂ c₂ d₂ e₂ f₂) :
    source ∈
      (tensor
        (valenceSixBistochasticKernel a₁ b₁ c₁ d₁ e₁ f₁)
        (valenceSixBistochasticKernel a₂ b₂ c₂ d₂ e₂ f₂)).sources := by
  exact (mem_cartesian_iff _ _ source).mpr
    ⟨valenceSixLeftCarriers_complete source.1,
      valenceSixLeftCarriers_complete source.2⟩

theorem slabPhysicalPairRecouplingKernelPackageSix_sources_complete
    {extent : Nat} (D : SlabPhysicalPairRecouplingData extent 6)
    (source : (slabPhysicalPairRecouplingKernelPackageSix D).Source) :
    source ∈
      (slabPhysicalPairRecouplingKernelPackageSix D).kernel.sources :=
  valenceSixTensorSources_complete source

/-! ## 4. The all-valence package -/

/-- Every source of the physical-pair recoupling package occurs in its
literal source list, uniformly over every geometrically possible link
degree. -/
theorem slabPhysicalPairRecouplingKernelPackage_sources_complete
    {extent : Nat} :
    (degree : Nat) → (D : SlabPhysicalPairRecouplingData extent degree) →
      (source : (slabPhysicalPairRecouplingKernelPackage degree D).Source) →
      source ∈
        (slabPhysicalPairRecouplingKernelPackage degree D).kernel.sources
  | 0, _, source => by cases source; exact List.mem_cons_self
  | 1, _, source => by cases source; exact List.mem_cons_self
  | 2, _, source => by cases source; exact List.mem_cons_self
  | 3, _, source => by cases source; exact List.mem_cons_self
  | 4, D, source =>
      slabPhysicalPairRecouplingKernelPackageFour_sources_complete D source
  | 5, D, source =>
      slabPhysicalPairRecouplingKernelPackageFive_sources_complete D source
  | 6, D, source =>
      slabPhysicalPairRecouplingKernelPackageSix_sources_complete D source
  | degree + 7, D, _ => False.elim (by
      have hdegree := D.degree_le_six
      omega)

/-- In particular, the production row selected by any accepted auxiliary
pair is a member of the complete common matrix source list. -/
theorem slabPhysicalPairRecouplingProductionSource_mem
    {K extent degree : Nat}
    (D : SlabPhysicalPairRecouplingData extent degree)
    (W : SlabPhysicalPairRecouplingWitnessData K D) :
    slabPhysicalPairRecouplingProductionSource degree D W ∈
      (slabPhysicalPairRecouplingKernelPackage degree D).kernel.sources :=
  slabPhysicalPairRecouplingKernelPackage_sources_complete degree D _

/-! ## 5. Whole-slab product membership -/

/-- Local source-list membership assembles structurally over every sublist of
attached boundary links. -/
theorem slabPhysicalPairRecouplingProductionSourceFrom_mem
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent)) :
    ∀ linkedList :
        List {link // link ∈ boundaryCompleteSlabLinks extent},
      slabPhysicalPairRecouplingProductionSourceFrom
          K extent leftPhysical rightPhysical
          leftAssignment rightAssignment left_mem right_mem linkedList ∈
        finiteBistochasticSourceAssignments
          (linkedList.map fun linked =>
            slabPhysicalPairRecouplingPackageAtLink
              extent leftPhysical rightPhysical linked)
  | [] => List.mem_cons_self
  | linked :: rest => by
      apply List.mem_flatMap.mpr
      refine ⟨slabPhysicalPairRecouplingProductionSource
          (slabIncidentPlaqIds extent linked.1).length
          (slabPhysicalPairRecouplingDataAtLink
            extent leftPhysical rightPhysical linked)
          (slabPhysicalPairRecouplingWitnessDataAtLink
            K extent leftPhysical rightPhysical
            leftAssignment rightAssignment left_mem right_mem linked), ?_, ?_⟩
      · exact slabPhysicalPairRecouplingProductionSource_mem
          (slabPhysicalPairRecouplingDataAtLink
            extent leftPhysical rightPhysical linked)
          (slabPhysicalPairRecouplingWitnessDataAtLink
            K extent leftPhysical rightPhysical
            leftAssignment rightAssignment left_mem right_mem linked)
      · apply List.mem_map.mpr
        exact ⟨slabPhysicalPairRecouplingProductionSourceFrom
            K extent leftPhysical rightPhysical
            leftAssignment rightAssignment left_mem right_mem rest,
          slabPhysicalPairRecouplingProductionSourceFrom_mem
            K extent leftPhysical rightPhysical
            leftAssignment rightAssignment left_mem right_mem rest,
          rfl⟩

/-- The accepted whole-slab production row belongs to the global common
matrix source list. -/
theorem slabPhysicalPairRecouplingProductionSource_global_mem
    (K extent : Nat) (leftPhysical rightPhysical : SlabLabelling)
    (leftAssignment rightAssignment : SlabFusionWitnessAssignment)
    (left_mem : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent leftPhysical
        (boundaryCompleteSlabLinks extent))
    (right_mem : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent rightPhysical
        (boundaryCompleteSlabLinks extent)) :
    slabPhysicalPairRecouplingProductionSource K extent
        leftPhysical rightPhysical leftAssignment rightAssignment
        left_mem right_mem ∈
      (slabPhysicalPairRecouplingKernel
        extent leftPhysical rightPhysical).sources :=
  slabPhysicalPairRecouplingProductionSourceFrom_mem
    K extent leftPhysical rightPhysical leftAssignment rightAssignment
    left_mem right_mem (boundaryCompleteSlabLinks extent).attach

end YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness

#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.slabPhysicalPairRecouplingKernelPackageFour_sources_complete
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.valenceFiveLeftCarriers_complete
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.slabPhysicalPairRecouplingKernelPackageFive_sources_complete
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.valenceSixLeftCarriers_complete
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.slabPhysicalPairRecouplingKernelPackageSix_sources_complete
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.slabPhysicalPairRecouplingKernelPackage_sources_complete
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.slabPhysicalPairRecouplingProductionSource_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.slabPhysicalPairRecouplingProductionSourceFrom_mem
#print axioms YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness.slabPhysicalPairRecouplingProductionSource_global_mem
