/-
# Split the sector first-stretched debt into OS-local and crossing parts

The localized good-plus-bad identity contains the complete first-stretched
mass above every full physical field whose lower restriction is in the exact
vacuum component.  The preceding OS-local target theorem identifies exactly
which of those bad sources already reroute inside that component.

This module filters each dependent physical block by that finite Boolean test
and by its Boolean complement.  Their two masses reconstruct the entire
sector first-stretched mass exactly.  Every entry in the local branch has its
lowered target in the vacuum component.  The complementary crossing mass is
therefore the only part of the `384/425` argument still requiring a new
topological estimate or a different rerouting.

No estimate on the crossing mass is claimed here, and no sector demand,
Poincare, spectral-gap, continuum, or Clay conclusion is asserted.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateFirstStretchedOSLocalTarget
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact dependent block partition -/

/-- First-stretched sources in one physical block whose entropy target fixes
the OS boundary and reflected upper coordinates. -/
def globalInwardMateOSLocalFirstStretchedSourceBlock
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K) :
    List (GlobalEnumeratedCubeInwardMateFullSource K hK) :=
  (globalEnumeratedCubeInwardMateFullSourceBlock K hK physicalSource).filter
    firstStretchedTargetOSLocalB

/-- Complementary first-stretched sources whose entropy target changes at
least one OS boundary or reflected-upper coordinate. -/
def globalInwardMateCrossingFirstStretchedSourceBlock
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K) :
    List (GlobalEnumeratedCubeInwardMateFullSource K hK) :=
  (globalEnumeratedCubeInwardMateFullSourceBlock K hK physicalSource).filter
    (fun source => !(firstStretchedTargetOSLocalB source))

theorem mem_globalInwardMateOSLocalFirstStretchedSourceBlock_iff
    {K : Nat} {hK : 1 ≤ K}
    {physicalSource : CubeInwardMatePhysicalSource K}
    {source : GlobalEnumeratedCubeInwardMateFullSource K hK} :
    source ∈ globalInwardMateOSLocalFirstStretchedSourceBlock
        K hK physicalSource ↔
      source ∈ globalEnumeratedCubeInwardMateFullSourceBlock
          K hK physicalSource ∧
        FirstStretchedTargetOSLocal source := by
  unfold globalInwardMateOSLocalFirstStretchedSourceBlock
  rw [List.mem_filter]
  constructor
  · intro hparts
    exact ⟨hparts.1,
      (firstStretchedTargetOSLocalB_eq_true_iff source).mp hparts.2⟩
  · intro hparts
    exact ⟨hparts.1,
      (firstStretchedTargetOSLocalB_eq_true_iff source).mpr hparts.2⟩

theorem mem_globalInwardMateCrossingFirstStretchedSourceBlock_iff
    {K : Nat} {hK : 1 ≤ K}
    {physicalSource : CubeInwardMatePhysicalSource K}
    {source : GlobalEnumeratedCubeInwardMateFullSource K hK} :
    source ∈ globalInwardMateCrossingFirstStretchedSourceBlock
        K hK physicalSource ↔
      source ∈ globalEnumeratedCubeInwardMateFullSourceBlock
          K hK physicalSource ∧
        firstStretchedTargetOSLocalB source = false := by
  unfold globalInwardMateCrossingFirstStretchedSourceBlock
  rw [List.mem_filter]
  constructor
  · intro hparts
    refine ⟨hparts.1, ?_⟩
    cases htest : firstStretchedTargetOSLocalB source with
    | false => rfl
    | true => simp [htest] at hparts
  · intro hparts
    exact ⟨hparts.1, by simp [hparts.2]⟩

/-! ## 2. The local and crossing masses -/

def cubeInwardMateOSLocalFirstStretchedPhysicalMass
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K) : Q' :=
  listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
    (globalInwardMateOSLocalFirstStretchedSourceBlock
      K hK physicalSource)

def cubeInwardMateCrossingFirstStretchedPhysicalMass
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K) : Q' :=
  listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
    (globalInwardMateCrossingFirstStretchedSourceBlock
      K hK physicalSource)

/-- OS-local bad mass above sector physical fields. -/
def globalInwardMateVacuumSectorOSLocalFirstStretchedMass
    (K : Nat) (hK : 1 ≤ K) : Q' :=
  listQSum
    (cubeInwardMateOSLocalFirstStretchedPhysicalMass K hK)
    (globalInwardMateVacuumSectorPhysicalSources K)

/-- The exact residual bad mass whose lowered target changes the OS boundary
or upper coordinate. -/
def globalInwardMateVacuumSectorCrossingFirstStretchedMass
    (K : Nat) (hK : 1 ≤ K) : Q' :=
  listQSum
    (cubeInwardMateCrossingFirstStretchedPhysicalMass K hK)
    (globalInwardMateVacuumSectorPhysicalSources K)

private theorem globalFirstStretchedBlock_weight_eqv_physicalMass
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K) :
    listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalEnumeratedCubeInwardMateFullSourceBlock
          K hK physicalSource) ≈
      cubeInwardMateFirstStretchedFullPhysicalMass
        K hK physicalSource := by
  unfold globalEnumeratedCubeInwardMateFullSourceBlock
    GlobalEnumeratedCubeInwardMateFullSource.weight
    cubeInwardMateFirstStretchedFullPhysicalMass
  rw [listQSum_map]
  exact Q'.eqv_refl _

/-- The two Boolean pieces reconstruct one fixed-physical first-stretched
block before the outer sector sum is taken. -/
theorem cubeInwardMateFirstStretchedPhysicalMass_split
    (K : Nat) (hK : 1 ≤ K)
    (physicalSource : CubeInwardMatePhysicalSource K) :
    cubeInwardMateOSLocalFirstStretchedPhysicalMass
          K hK physicalSource +
        cubeInwardMateCrossingFirstStretchedPhysicalMass
          K hK physicalSource ≈
      cubeInwardMateFirstStretchedFullPhysicalMass
        K hK physicalSource := by
  refine Q'.eqv_trans _
    (listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
      (globalEnumeratedCubeInwardMateFullSourceBlock
        K hK physicalSource)) _ ?_ ?_
  · unfold cubeInwardMateOSLocalFirstStretchedPhysicalMass
      cubeInwardMateCrossingFirstStretchedPhysicalMass
      globalInwardMateOSLocalFirstStretchedSourceBlock
      globalInwardMateCrossingFirstStretchedSourceBlock
    exact Q'.eqv_symm
      (listQSum_filter_partition
        GlobalEnumeratedCubeInwardMateFullSource.weight
        firstStretchedTargetOSLocalB
        (globalEnumeratedCubeInwardMateFullSourceBlock
          K hK physicalSource))
  · exact globalFirstStretchedBlock_weight_eqv_physicalMass
      K hK physicalSource

/-- **Exact sector bad-branch split.**  The OS-local and crossing masses
partition the entire first-stretched term in the localized branch identity. -/
theorem globalInwardMateVacuumSectorFirstStretched_split
    (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateVacuumSectorOSLocalFirstStretchedMass K hK +
        globalInwardMateVacuumSectorCrossingFirstStretchedMass K hK ≈
      globalInwardMateVacuumSectorFirstStretchedMass K hK := by
  let physicalSources := globalInwardMateVacuumSectorPhysicalSources K
  let localMass := cubeInwardMateOSLocalFirstStretchedPhysicalMass K hK
  let crossingMass := cubeInwardMateCrossingFirstStretchedPhysicalMass K hK
  refine Q'.eqv_trans _
    (listQSum
      (fun physicalSource =>
        localMass physicalSource + crossingMass physicalSource)
      physicalSources) _ ?_ ?_
  · unfold globalInwardMateVacuumSectorOSLocalFirstStretchedMass
      globalInwardMateVacuumSectorCrossingFirstStretchedMass
      physicalSources localMass crossingMass
    exact Q'.eqv_symm
      (listQSum_add
        (cubeInwardMateOSLocalFirstStretchedPhysicalMass K hK)
        (cubeInwardMateCrossingFirstStretchedPhysicalMass K hK)
        (globalInwardMateVacuumSectorPhysicalSources K))
  · unfold globalInwardMateVacuumSectorFirstStretchedMass physicalSources
    apply listQSum_congr_on
    intro physicalSource _
    exact cubeInwardMateFirstStretchedPhysicalMass_split
      K hK physicalSource

/-! ## 3. Every local branch endpoint stays in the sector -/

private theorem sourcePhysicalSource_eq_of_mem_globalBlock
    {K : Nat} {hK : 1 ≤ K}
    {physicalSource : CubeInwardMatePhysicalSource K}
    {source : GlobalEnumeratedCubeInwardMateFullSource K hK}
    (hsource : source ∈
      globalEnumeratedCubeInwardMateFullSourceBlock
        K hK physicalSource) :
    source.physicalSource = physicalSource := by
  unfold globalEnumeratedCubeInwardMateFullSourceBlock at hsource
  obtain ⟨entry, _hentry, heq⟩ := List.mem_map.mp hsource
  exact congrArg GlobalEnumeratedCubeInwardMateFullSource.physicalSource
    heq.symm

/-- Every OS-local first-stretched entry above a vacuum-sector physical field
has both its original and lowered lower-half states in that same component. -/
theorem globalInwardMateOSLocalFirstStretchedSource_endpoints_internal
    {K : Nat} {hK : 1 ≤ K}
    {physicalSource : CubeInwardMatePhysicalSource K}
    {source : GlobalEnumeratedCubeInwardMateFullSource K hK}
    (hphysicalSector : physicalSource ∈
      globalInwardMateVacuumSectorPhysicalSources K)
    (hsource : source ∈
      globalInwardMateOSLocalFirstStretchedSourceBlock
        K hK physicalSource) :
    firstStretchedSourceLower source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 ∧
      firstStretchedTargetLower source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 := by
  have hparts :=
    (mem_globalInwardMateOSLocalFirstStretchedSourceBlock_iff).mp hsource
  have hphysicalSource :=
    sourcePhysicalSource_eq_of_mem_globalBlock hparts.1
  have hsourcePhysical : source.physical = physicalSource.1 :=
    congrArg Subtype.val hphysicalSource
  have hsourceSector : firstStretchedSourceLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0 := by
    unfold firstStretchedSourceLower
    rw [hsourcePhysical]
    exact (mem_globalInwardMateVacuumSectorPhysicalSources_iff.mp
      hphysicalSector)
  exact ⟨hsourceSector,
    firstStretchedTargetLower_mem_vacuumSector_of_source_mem
      source hparts.2 hsourceSector⟩

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.mem_globalInwardMateOSLocalFirstStretchedSourceBlock_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.globalInwardMateVacuumSectorFirstStretched_split
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalFirstStretchedSplit.globalInwardMateOSLocalFirstStretchedSource_endpoints_internal
