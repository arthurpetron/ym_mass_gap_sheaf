/-
# Exact global normalization of the two SU(2) source branches

The fixed-physical all-target and first-stretched source masses now sum to the
genuine BF4 term.  This module performs the outer dependent finite Fubini over
every bounded extent-one physical field.  It constructs the global all-target
carrier beside the existing global first-stretched carrier and proves that
their two actual finite masses reconstruct the physical partition exactly.

This is a global event decomposition, not a pointwise conditional-row
minorization.  No posterior, Poincare, transfer-operator, or continuum claim
is made here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The dependent global all-target carrier -/

/-- One all-target full source over one genuine bounded physical field. -/
structure GlobalCubeInwardMateCertifiedTargetFullSource
    (K : Nat) (hK : 1 ≤ K) : Type where
  physicalSource : CubeInwardMatePhysicalSource K
  entry : CubeInwardMateCertifiedTargetFullSource K physicalSource.1

/-- The all-target block over one attached physical field. -/
def globalCubeInwardMateCertifiedTargetFullSourceBlock
    (K : Nat) (hK : 1 ≤ K) (physicalSource : CubeInwardMatePhysicalSource K) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  (cubeInwardMateCertifiedTargetFullSources
      K physicalSource.1 hK
        (cubeInwardMatePhysicalBoundedOfMem
          K physicalSource.1 physicalSource.2)).map
    (fun entry =>
      { physicalSource := physicalSource
        entry := entry })

/-- Every all-target source over every genuine bounded physical field. -/
def globalCubeInwardMateCertifiedTargetFullSources
    (K : Nat) (hK : 1 ≤ K) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach.flatMap
    (globalCubeInwardMateCertifiedTargetFullSourceBlock K hK)

namespace GlobalCubeInwardMateCertifiedTargetFullSource

/-- The physical field of one global all-target entry. -/
def physical {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    EdgeLabelling :=
  source.physicalSource.1

/-- The exact unnormalized pushforward weight of one global all-target
entry. -/
def weight {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK) : Q' :=
  cubeInwardMateCertifiedTargetFullSourceWeight
    K source.physical source.entry

end GlobalCubeInwardMateCertifiedTargetFullSource

/-! ## 2. Exact outer Fubini for both branches -/

/-- The all-target mass in one attached physical block. -/
def cubeInwardMateCertifiedTargetFullPhysicalMass
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K) : Q' :=
  listQSum
    (cubeInwardMateCertifiedTargetFullSourceWeight K physicalSource.1)
    (cubeInwardMateCertifiedTargetFullSources
      K physicalSource.1 hK
        (cubeInwardMatePhysicalBoundedOfMem
          K physicalSource.1 physicalSource.2))

/-- The first-stretched mass in one attached physical block. -/
def cubeInwardMateFirstStretchedFullPhysicalMass
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K) : Q' :=
  listQSum (cubeInwardMateFullSourceEntryWeight K)
    (enumeratedCubeInwardMateFullSources
      K physicalSource.1 hK
        (cubeInwardMatePhysicalBoundedOfMem
          K physicalSource.1 physicalSource.2))

/-- The flat global all-target mass is the nested sum of its fixed-physical
blocks. -/
theorem globalCubeInwardMateCertifiedTargetFullSources_weight_eqv_nested
    (K : Nat) (hK : 1 ≤ K) :
    listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK) ≈
      listQSum (cubeInwardMateCertifiedTargetFullPhysicalMass K hK)
        (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach := by
  unfold globalCubeInwardMateCertifiedTargetFullSources
  refine Q'.eqv_trans _
    (listQSum
      (fun physicalSource =>
        listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
          (globalCubeInwardMateCertifiedTargetFullSourceBlock
            K hK physicalSource))
      (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach) _
    (listQSum_flatMap
      GlobalCubeInwardMateCertifiedTargetFullSource.weight
      (globalCubeInwardMateCertifiedTargetFullSourceBlock K hK)
      (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach) ?_
  apply listQSum_congr_on
  intro physicalSource _
  unfold globalCubeInwardMateCertifiedTargetFullSourceBlock
    GlobalCubeInwardMateCertifiedTargetFullSource.weight
    GlobalCubeInwardMateCertifiedTargetFullSource.physical
    cubeInwardMateCertifiedTargetFullPhysicalMass
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-- The existing flat global first-stretched mass is likewise the nested sum
of its fixed-physical blocks. -/
theorem globalCubeInwardMateFirstStretchedFullSources_weight_eqv_nested
    (K : Nat) (hK : 1 ≤ K) :
    listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalEnumeratedCubeInwardMateFullSources K hK) ≈
      listQSum (cubeInwardMateFirstStretchedFullPhysicalMass K hK)
        (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach := by
  unfold globalEnumeratedCubeInwardMateFullSources
  refine Q'.eqv_trans _
    (listQSum
      (fun physicalSource =>
        listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
          (globalEnumeratedCubeInwardMateFullSourceBlock
            K hK physicalSource))
      (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach) _
    (listQSum_flatMap
      GlobalEnumeratedCubeInwardMateFullSource.weight
      (globalEnumeratedCubeInwardMateFullSourceBlock K hK)
      (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach) ?_
  apply listQSum_congr_on
  intro physicalSource _
  unfold globalEnumeratedCubeInwardMateFullSourceBlock
    GlobalEnumeratedCubeInwardMateFullSource.weight
    cubeInwardMateFirstStretchedFullPhysicalMass
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-! ## 3. Exact global physical normalization -/

/-- **Exact global source normalization.**  The global all-target pushforward
mass plus the actual global first-stretched mass is the genuine extent-one BF4
physical partition. -/
theorem globalCubeInwardMateFullSourceBranches_weight_total
    (K : Nat) (hK : 1 ≤ K) :
    listQSum GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK) +
      listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalEnumeratedCubeInwardMateFullSources K hK) ≈
      slabParametricKPhysicalPartition anchorCoupling K 1 := by
  let physicalSources :=
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach
  let targetMass := cubeInwardMateCertifiedTargetFullPhysicalMass K hK
  let stretchedMass := cubeInwardMateFirstStretchedFullPhysicalMass K hK
  refine Q'.eqv_trans _
    (listQSum targetMass physicalSources +
      listQSum stretchedMass physicalSources) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (globalCubeInwardMateCertifiedTargetFullSources_weight_eqv_nested
        K hK)
      (globalCubeInwardMateFirstStretchedFullSources_weight_eqv_nested
        K hK)
  refine Q'.eqv_trans _
    (listQSum (fun physicalSource =>
      targetMass physicalSource + stretchedMass physicalSource)
      physicalSources) _
    (Q'.eqv_symm (listQSum_add targetMass stretchedMass physicalSources)) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun physicalSource =>
        slabParametricKPhysicalTerm
          anchorCoupling K 1 physicalSource.1)
      physicalSources) _ ?_ ?_
  · apply listQSum_congr_on
    intro physicalSource _
    unfold targetMass stretchedMass
      cubeInwardMateCertifiedTargetFullPhysicalMass
      cubeInwardMateFirstStretchedFullPhysicalMass
    exact cubeInwardMateFullSourceBranches_weight_total
      K physicalSource.1 hK
        (cubeInwardMatePhysicalBoundedOfMem
          K physicalSource.1 physicalSource.2)
  · unfold slabParametricKPhysicalPartition physicalSources
    rw [← listQSum_map
      (slabParametricKPhysicalTerm anchorCoupling K 1)
      Subtype.val
      (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach]
    rw [List.attach_map_subtype_val]
    exact Q'.eqv_refl _

#print axioms globalCubeInwardMateCertifiedTargetFullSources_weight_eqv_nested
#print axioms globalCubeInwardMateFirstStretchedFullSources_weight_eqv_nested
#print axioms globalCubeInwardMateFullSourceBranches_weight_total

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
