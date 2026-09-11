/-
# Globalize the complete first-stretched source carrier

The fixed-physical complete-source compiler is not itself a probability row:
its weight is charged against the whole physical partition.  This module
therefore performs the missing outer finite Fubini first.  It ranges over the
genuine bounded extent-one physical carrier and retains, in each dependent
fiber, every nonredundant complete first-stretched source together with its
deterministic adaptive peel.

The resulting source is a physical/raw pair.  Equality of that pair recovers
the dependent global entry, and equality of the serialized lowered-target key
recovers the common root, size, lowered physical field, and lowered presented
assignment even when the two source physical fields differ.  The latter uses
the genuine bounded-carrier fact that both source fields vanish off the slab.

This module is only the global carrier and exact-key compiler.  It does not
yet sum its weight or claim a transition, posterior, operator, or continuum
bound.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCongestion

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The dependent global carrier -/

/-- A bounded physical field carries the canonical boundedness proof consumed
by the fixed-physical cube compiler. -/
def cubeInwardMatePhysicalBoundedOfMem
    (K : Nat) (physical : EdgeLabelling)
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    SlabFaceLabellingBounded K 1 physical := by
  intro faceId hface
  exact Nat.lt_succ_iff.mp
    ((boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
      physical hphysical).1 faceId hface)

/-- One genuine bounded physical source block, with membership retained as
Type-level data. -/
abbrev CubeInwardMatePhysicalSource (K : Nat) :=
  { physical : EdgeLabelling //
    physical ∈ boundedEdgeLabellings K (slabPhysicalFaceEdges 1) }

/-- One complete first-stretched source in the dependent block over a genuine
bounded physical field. -/
structure GlobalEnumeratedCubeInwardMateFullSource
    (K : Nat) (hK : 1 ≤ K) : Type where
  physicalSource : CubeInwardMatePhysicalSource K
  entry : EnumeratedCubeInwardMateFullSource
    K physicalSource.1 hK
      (cubeInwardMatePhysicalBoundedOfMem
        K physicalSource.1 physicalSource.2)

/-- The global block over one attached physical field. -/
def globalEnumeratedCubeInwardMateFullSourceBlock
    (K : Nat) (hK : 1 ≤ K) (physicalSource : CubeInwardMatePhysicalSource K) :
    List (GlobalEnumeratedCubeInwardMateFullSource K hK) :=
  (enumeratedCubeInwardMateFullSources
      K physicalSource.1 hK
        (cubeInwardMatePhysicalBoundedOfMem
          K physicalSource.1 physicalSource.2)).map
    (fun entry =>
      { physicalSource := physicalSource
        entry := entry })

/-- Every complete first-stretched source over every genuine bounded physical
field, with no physical block omitted. -/
def globalEnumeratedCubeInwardMateFullSources
    (K : Nat) (hK : 1 ≤ K) :
    List (GlobalEnumeratedCubeInwardMateFullSource K hK) :=
  (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach.flatMap
    (globalEnumeratedCubeInwardMateFullSourceBlock K hK)

namespace GlobalEnumeratedCubeInwardMateFullSource

/-- The physical field of a global entry. -/
def physical {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    EdgeLabelling :=
  source.physicalSource.1

/-- The complete raw source paired with its physical field. -/
def rawSource {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  (source.physical, source.entry.raw)

/-- The already constructed flat adaptive inverse data. -/
def adaptiveInverseData {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    PresentedAdaptiveInverseData K 1 :=
  source.entry.adaptiveInverseData

@[simp] theorem adaptiveInverseData_sourcePhysical
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    source.adaptiveInverseData.sourcePhysical = source.physical :=
  source.entry.adaptiveInverseData_sourcePhysical

@[simp] theorem adaptiveInverseData_sourceRaw
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    source.adaptiveInverseData.sourceRaw = source.entry.raw :=
  source.entry.adaptiveInverseData_sourceRaw

theorem adaptiveInverseData_source_eq
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    (source.adaptiveInverseData.sourcePhysical,
        source.adaptiveInverseData.sourceRaw) = source.rawSource := by
  apply Prod.ext
  · exact source.adaptiveInverseData_sourcePhysical
  · exact source.adaptiveInverseData_sourceRaw

/-- The exact anchor BF4 weight of a global entry. -/
def weight {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :=
  cubeInwardMateFullSourceEntryWeight K source.entry

/-- The exact serialized lowered-target key. -/
def targetKey {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    CubeInwardMateFullPeelTargetKey :=
  presentedAdaptiveInverseTargetKey source.adaptiveInverseData

/-! ## 2. Exact recovery and bounded target data -/

/-- A physical/raw source pair recovers its dependent global entry. -/
theorem eq_of_rawSource_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hraw : left.rawSource = right.rawSource) : left = right := by
  have hphysical : left.physical = right.physical :=
    congrArg Prod.fst hraw
  have hphysicalSource : left.physicalSource = right.physicalSource :=
    Subtype.ext hphysical
  cases left with
  | mk leftPhysicalSource leftEntry =>
      cases right with
      | mk rightPhysicalSource rightEntry =>
          dsimp only at hphysicalSource
          cases hphysicalSource
          have hentryRaw :
              (leftPhysicalSource.1, leftEntry.raw) =
                (leftPhysicalSource.1, rightEntry.raw) := by
            apply Prod.ext
            · rfl
            · exact congrArg Prod.snd hraw
          have hentry :=
            EnumeratedCubeInwardMateFullSource.eq_of_rawSource_eq
              leftEntry rightEntry hentryRaw
          cases hentry
          rfl

/-- Every global source physical field vanishes off the actual slab carrier. -/
theorem physical_eq_zero_of_not_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (faceId : Nat) (hface : faceId ∉ slabPhysicalFaceEdges 1) :
    source.physical faceId = 0 :=
  (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
    source.physical source.physicalSource.2).2 faceId hface

/-- Supported peeling therefore also vanishes off the slab carrier. -/
theorem lowerPhysical_eq_zero_of_not_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (faceId : Nat) (hface : faceId ∉ slabPhysicalFaceEdges 1) :
    source.adaptiveInverseData.lowerPhysical faceId = 0 := by
  unfold adaptiveInverseData
  rw [EnumeratedCubeInwardMateFullSource.lowerPhysical_eq_physical_of_not_mem
      source.entry faceId hface]
  exact source.physical_eq_zero_of_not_mem faceId hface

/-- Equality of global exact keys reconstructs the common dependent lowered
target without assuming a common source physical field. -/
theorem target_eq_of_key_eq
    {K : Nat} {hK : 1 ≤ K}
    (left right : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hkey : left.targetKey = right.targetKey) :
    left.adaptiveInverseData.rootFaceId =
        right.adaptiveInverseData.rootFaceId ∧
      left.adaptiveInverseData.peelSize =
        right.adaptiveInverseData.peelSize ∧
      left.adaptiveInverseData.lowerPhysical =
        right.adaptiveInverseData.lowerPhysical ∧
      HEq left.adaptiveInverseData.lowerAssignment
        right.adaptiveInverseData.lowerAssignment := by
  apply PresentedAdaptiveInverseData.target_eq_of_key_eq
    left.adaptiveInverseData right.adaptiveInverseData
  · intro faceId hface
    rw [left.lowerPhysical_eq_zero_of_not_mem faceId hface,
      right.lowerPhysical_eq_zero_of_not_mem faceId hface]
  · exact hkey

/-- Every lowered global target remains in the genuine bounded physical
carrier. -/
theorem lowerPhysical_mem
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    source.adaptiveInverseData.lowerPhysical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1) :=
  EnumeratedCubeInwardMateFullSource.lowerPhysical_mem
    source.entry source.physicalSource.2

/-- Every global peel is rooted on one of the six literal cube faces. -/
theorem rootFaceId_mem_cube
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    source.adaptiveInverseData.rootFaceId ∈ centralLowerCubeFaceIds :=
  EnumeratedCubeInwardMateFullSource.rootFaceId_mem_cube source.entry

/-- Every global first-stretched peel removes at least its two certified root
faces. -/
theorem two_le_peelSize
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    2 ≤ source.adaptiveInverseData.peelSize :=
  source.entry.two_le_adaptiveInverseData_peelSize

end GlobalEnumeratedCubeInwardMateFullSource

/-! ## 3. Duplicate-freeness of the outer Fubini carrier -/

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := by
        rw [heq]
        exact htail
      obtain ⟨item, hitem, hvalueItem⟩ := List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

private theorem globalBlock_nodup
    (K : Nat) (hK : 1 ≤ K) (physicalSource : CubeInwardMatePhysicalSource K) :
    (globalEnumeratedCubeInwardMateFullSourceBlock
      K hK physicalSource).Nodup := by
  unfold globalEnumeratedCubeInwardMateFullSourceBlock
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
  · exact enumeratedCubeInwardMateFullSources_nodup
      K physicalSource.1 hK
        (cubeInwardMatePhysicalBoundedOfMem
          K physicalSource.1 physicalSource.2)
  · intro left _ right _ heq
    injection heq

private theorem range_nodup_local :
    ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

/-- The complete global first-stretched carrier has neither within-block nor
cross-physical duplicates. -/
theorem globalEnumeratedCubeInwardMateFullSources_nodup
    (K : Nat) (hK : 1 ≤ K) :
    (globalEnumeratedCubeInwardMateFullSources K hK).Nodup := by
  unfold globalEnumeratedCubeInwardMateFullSources
  apply nodup_flatMap_of_disjoint_blocks
    (globalEnumeratedCubeInwardMateFullSourceBlock K hK)
  · exact YMGap.Continuum.FiniteWeightedCartesianInjection.attach_nodup_of_nodup
      _ (YMGap.Continuum.Z4BoundedEdgeLabellingNodup.boundedEdgeLabellings_nodup
        K (slabPhysicalFaceEdges 1)
          (by
            unfold slabPhysicalFaceEdges
            exact range_nodup_local _))
  · intro physicalSource _
    exact globalBlock_nodup K hK physicalSource
  · intro left _ right _ hne value hleft
    intro hright
    have hleftPhysical : value.physicalSource = left := by
      obtain ⟨entry, _, hentry⟩ := List.mem_map.mp hleft
      exact congrArg GlobalEnumeratedCubeInwardMateFullSource.physicalSource
        hentry.symm
    have hrightPhysical : value.physicalSource = right := by
      obtain ⟨entry, _, hentry⟩ := List.mem_map.mp hright
      exact congrArg GlobalEnumeratedCubeInwardMateFullSource.physicalSource
        hentry.symm
    exact hne (hleftPhysical.symm.trans hrightPhysical)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource.cubeInwardMatePhysicalBoundedOfMem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource.GlobalEnumeratedCubeInwardMateFullSource.eq_of_rawSource_eq
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource.GlobalEnumeratedCubeInwardMateFullSource.target_eq_of_key_eq
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource.globalEnumeratedCubeInwardMateFullSources_nodup
