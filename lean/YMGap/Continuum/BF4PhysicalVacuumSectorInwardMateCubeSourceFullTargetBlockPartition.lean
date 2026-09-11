/-
# Exact partition by physical target, literal root, and peel size

Every realized complete-source target representative has three coarse
coordinates: its lowered physical spin word, its literal cube-face root, and
its peel size.  The lowered target remains in the bounded physical carrier,
the root lies in the six-face cube carrier, and the size lies below the
explicit total physical-strand ceiling.

The Cartesian product of those three finite carriers therefore covers every
representative.  Its serialized keys are duplicate-free, because bounded
physical labellings are determined by their finite supported words.  The
generic deterministic pushforward then gives exact Fubini over the literal
target/root/size blocks, with no overcounting and no omitted block.

This module proves only the exact partition.  The subsequent weighted block
capacity and geometric-tail estimates are kept as separate contractions.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPhysicalMultiplicityCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. A small generic contraction interface -/

/-- Exact finite Fubini when a duplicate-free coordinate-key carrier covers
all sources and every displayed block weight is its deterministic fiber. -/
theorem finiteCoordinateFiberWeight_total
    {Source Coordinate Key : Type} [DecidableEq Key]
    (sources : List Source) (weight : Source -> Q')
    (coordinates : List Coordinate)
    (sourceKey : Source -> Key) (coordinateKey : Coordinate -> Key)
    (blockWeight : Coordinate -> Q')
    (hkeys : (coordinates.map coordinateKey).Nodup)
    (hcoverage : forall source, source ∈ sources ->
      sourceKey source ∈ coordinates.map coordinateKey)
    (hblock : forall coordinate, coordinate ∈ coordinates ->
      blockWeight coordinate ≈
        fiberWeight sources weight sourceKey (coordinateKey coordinate)) :
    listQSum blockWeight coordinates ≈ listQSum weight sources := by
  have htotal := fiberWeight_total sources weight sourceKey
    (coordinates.map coordinateKey) hkeys hcoverage
  rw [listQSum_map] at htotal
  exact Q'.eqv_trans _ _ _
    (listQSum_congr_on blockWeight
      (fun coordinate =>
        fiberWeight sources weight sourceKey (coordinateKey coordinate))
      coordinates hblock)
    htotal

/-! ## 1. One explicit ceiling for every realized peel size -/

private theorem natListSum_map_le_length_mul_local
    {A : Type} (value : A -> Nat) (bound : Nat) :
    forall items : List A,
      (forall item, item ∈ items -> value item <= bound) ->
      natListSum (items.map value) <= items.length * bound
  | [], _ => by simp [natListSum]
  | head :: tail, hbound => by
      have hhead : value head <= bound :=
        hbound head List.mem_cons_self
      have htail : natListSum (tail.map value) <= tail.length * bound :=
        natListSum_map_le_length_mul_local value bound tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem))
      simp only [List.map_cons, natListSum, List.length_cons]
      calc
        value head + natListSum (tail.map value) <=
            bound + tail.length * bound := Nat.add_le_add hhead htail
        _ = (tail.length + 1) * bound := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Total number of physical strand slots available at cutoff `K` on the
complete extent-one slab. -/
def cubeInwardMateFullPeelMaxSize (K : Nat) : Nat :=
  (slabPhysicalFaceEdges 1).length * K

/-- Every deterministic two-root peel lies below the total physical-strand
ceiling. -/
theorem EnumeratedCubeInwardMateFullSource.adaptiveInverseData_peelSize_le
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    entry.adaptiveInverseData.peelSize <=
      cubeInwardMateFullPeelMaxSize K := by
  change
    (certifiedStretchedComponentUnionSupportedSelection
      entry.source.1 entry.source.toPresented).peelFaces.length <=
        (slabPhysicalFaceEdges 1).length * K
  rw [presentedSelection_peelFaces_length_eq_physicalDrop_l1]
  apply natListSum_map_le_length_mul_local
  intro faceId hface
  exact Nat.le_trans
    (slabFaceStrandSelectionCount_le
      (certifiedStretchedComponentUnionSupportedSelection
        entry.source.1 entry.source.toPresented).closed.selected faceId)
    (hbounded faceId hface)

/-! ## 2. The finite coordinate and key carriers -/

/-- One literal physical-target/root/size coordinate. -/
abbrev CubeInwardMateFullPeelBlockCoordinate :=
  EdgeLabelling × (Nat × Nat)

/-- The decidable serialization of one block coordinate. -/
abbrev CubeInwardMateFullPeelBlockKey :=
  List Nat × (Nat × Nat)

/-- Serialize a physical target coordinate by its complete extent-one word. -/
def cubeInwardMateFullPeelBlockCoordinateKey
    (coordinate : CubeInwardMateFullPeelBlockCoordinate) :
    CubeInwardMateFullPeelBlockKey :=
  (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) coordinate.1,
    coordinate.2)

/-- The coarse target/root/size key of one realized representative. -/
def cubeInwardMateFullPeelRepresentativeBlockKey
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) : CubeInwardMateFullPeelBlockKey :=
  (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
      representative.adaptiveInverseData.lowerPhysical,
    (representative.adaptiveInverseData.rootFaceId,
      representative.adaptiveInverseData.peelSize))

/-- Complete finite Cartesian carrier of bounded physical targets, the six
literal roots, and every size through the physical-strand ceiling. -/
def cubeInwardMateFullPeelBlockCoordinates (K : Nat) :
    List CubeInwardMateFullPeelBlockCoordinate :=
  cartesian
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (cartesian centralLowerCubeFaceIds
      (List.range (cubeInwardMateFullPeelMaxSize K + 1)))

private theorem range_nodup_local :
    forall count : Nat, (List.range count).Nodup
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

/-- The literal coordinate carrier contains no duplicate triple. -/
theorem cubeInwardMateFullPeelBlockCoordinates_nodup (K : Nat) :
    (cubeInwardMateFullPeelBlockCoordinates K).Nodup := by
  unfold cubeInwardMateFullPeelBlockCoordinates
  apply cartesian_nodup
  · apply boundedEdgeLabellings_nodup
    unfold slabPhysicalFaceEdges
    exact range_nodup_local _
  · apply cartesian_nodup
    · unfold centralLowerCubeFaceIds
      decide
    · exact range_nodup_local _

/-- Serialization remains injective on the coordinate carrier, because its
bounded physical targets vanish off the serialized face list. -/
theorem cubeInwardMateFullPeelBlockCoordinateKeys_nodup (K : Nat) :
    ((cubeInwardMateFullPeelBlockCoordinates K).map
      cubeInwardMateFullPeelBlockCoordinateKey).Nodup := by
  apply nodup_map_of_injOn
  · exact cubeInwardMateFullPeelBlockCoordinates_nodup K
  · intro left hleft right hright hkey
    have hleftTarget :=
      (mem_cartesian_iff
        (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
        (cartesian centralLowerCubeFaceIds
          (List.range (cubeInwardMateFullPeelMaxSize K + 1))) left).mp hleft
    have hrightTarget :=
      (mem_cartesian_iff
        (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
        (cartesian centralLowerCubeFaceIds
          (List.range (cubeInwardMateFullPeelMaxSize K + 1))) right).mp hright
    have htargetWord :
        finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) left.1 =
          finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) right.1 :=
      congrArg Prod.fst hkey
    have htarget : left.1 = right.1 := by
      apply edgeLabelling_eq_of_word_eq_of_supported
        (slabPhysicalFaceEdges 1)
      · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
          left.1 hleftTarget.1).2
      · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
          right.1 hrightTarget.1).2
      · exact htargetWord
    exact Prod.ext htarget
      (congrArg (fun key : CubeInwardMateFullPeelBlockKey => key.2) hkey)

/-! ## 3. Coverage and exact deterministic Fubini -/

/-- Every realized representative key occurs in the complete coordinate-key
carrier. -/
theorem cubeInwardMateFullPeelRepresentativeBlockKey_mem
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    cubeInwardMateFullPeelRepresentativeBlockKey representative ∈
      (cubeInwardMateFullPeelBlockCoordinates K).map
        cubeInwardMateFullPeelBlockCoordinateKey := by
  apply List.mem_map.mpr
  let coordinate : CubeInwardMateFullPeelBlockCoordinate :=
    (representative.adaptiveInverseData.lowerPhysical,
      (representative.adaptiveInverseData.rootFaceId,
        representative.adaptiveInverseData.peelSize))
  refine ⟨coordinate, ?_, rfl⟩
  unfold cubeInwardMateFullPeelBlockCoordinates
  exact (mem_cartesian_iff
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (cartesian centralLowerCubeFaceIds
      (List.range (cubeInwardMateFullPeelMaxSize K + 1))) coordinate).mpr
    ⟨EnumeratedCubeInwardMateFullSource.lowerPhysical_mem
        representative hphysical,
      (mem_cartesian_iff centralLowerCubeFaceIds
        (List.range (cubeInwardMateFullPeelMaxSize K + 1)) coordinate.2).mpr
        ⟨EnumeratedCubeInwardMateFullSource.rootFaceId_mem_cube
            representative,
          List.mem_range.mpr (Nat.lt_succ_of_le
            (EnumeratedCubeInwardMateFullSource.adaptiveInverseData_peelSize_le
              representative))⟩⟩

/-- The deterministic coarse-key fiber is literally the previously defined
physical-target/root/size block. -/
theorem cubeInwardMateFullPeelBlock_fiberWeight_eq
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (weight : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded -> Q')
    (target : EdgeLabelling) (rootFaceId peelSize : Nat) :
    fiberWeight
        (cubeInwardMateFullPeelTargetRepresentatives
          K physical hK hbounded)
        weight cubeInwardMateFullPeelRepresentativeBlockKey
        (cubeInwardMateFullPeelBlockCoordinateKey
          (target, (rootFaceId, peelSize))) =
      listQSum weight
        (cubeInwardMateFullPeelTargetBlockRepresentatives
          K physical hK hbounded target rootFaceId peelSize) := by
  unfold fiberWeight cubeInwardMateFullPeelTargetBlockRepresentatives
  apply congrArg (listQSum weight)
  apply List.filter_congr
  intro representative _
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hkey
    have hkey' := of_decide_eq_true hkey
    have hword := congrArg Prod.fst hkey'
    have hrootSize := congrArg Prod.snd hkey'
    have hroot := congrArg Prod.fst hrootSize
    have hsize := congrArg Prod.snd hrootSize
    apply decide_eq_true
    exact ⟨hroot.symm, hsize.symm, hword.symm⟩
  · intro hblock
    have hblock' := of_decide_eq_true hblock
    apply decide_eq_true
    apply Prod.ext
    · exact hblock'.2.2.symm
    · apply Prod.ext
      · exact hblock'.1.symm
      · exact hblock'.2.1.symm

/-! A named scalar boundary keeps the exact partition theorem from repeatedly
normalizing the large dependent representative type. -/

/-- Exact weight of one literal coarse coordinate block. -/
def cubeInwardMateFullPeelTargetBlockWeight
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (weight : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded -> Q')
    (coordinate : CubeInwardMateFullPeelBlockCoordinate) : Q' :=
  listQSum weight
    (cubeInwardMateFullPeelTargetBlockRepresentatives
      K physical hK hbounded coordinate.1
        coordinate.2.1 coordinate.2.2)

/-- Total weight of all literal target/root/size blocks. -/
def cubeInwardMateFullPeelTargetBlocksWeight
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (weight : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded -> Q') : Q' :=
  listQSum (cubeInwardMateFullPeelTargetBlockWeight weight)
    (cubeInwardMateFullPeelBlockCoordinates K)

/-- Total weight of the distinct realized target representatives. -/
def cubeInwardMateFullPeelRepresentativesWeight
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (weight : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded -> Q') : Q' :=
  listQSum weight
    (cubeInwardMateFullPeelTargetRepresentatives
      K physical hK hbounded)

#print axioms cubeInwardMateFullPeelMaxSize
#print axioms finiteCoordinateFiberWeight_total
#print axioms EnumeratedCubeInwardMateFullSource.adaptiveInverseData_peelSize_le
#print axioms cubeInwardMateFullPeelBlockCoordinateKey
#print axioms cubeInwardMateFullPeelRepresentativeBlockKey
#print axioms cubeInwardMateFullPeelBlockCoordinates
#print axioms cubeInwardMateFullPeelBlockCoordinates_nodup
#print axioms cubeInwardMateFullPeelBlockCoordinateKeys_nodup
#print axioms cubeInwardMateFullPeelRepresentativeBlockKey_mem
#print axioms cubeInwardMateFullPeelBlock_fiberWeight_eq
#print axioms cubeInwardMateFullPeelTargetBlockWeight
#print axioms cubeInwardMateFullPeelTargetBlocksWeight
#print axioms cubeInwardMateFullPeelRepresentativesWeight

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
