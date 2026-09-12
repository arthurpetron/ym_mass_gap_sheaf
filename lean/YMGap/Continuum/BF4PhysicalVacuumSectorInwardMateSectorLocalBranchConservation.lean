/-
# Exact inward-mate branch conservation inside the vacuum-sector event

The global `41/425` successful-source estimate is obtained by complementing a
`384/425` first-stretched branch bound.  To localize that argument to the exact
finite vacuum component, its branch decomposition must first be restricted at
the physical-field level rather than by filtering the final global inequality.

This module constructs the exact finite list of bounded full-slab fields whose
lower restriction belongs to the canonical vacuum component.  Over that list,
the all-target and first-stretched auxiliary masses still sum exactly to the
physical mass, block by block.

This is the localized conservation identity, not yet the localized strict
bound: it remains to prove that the first-stretched target rerouting preserves
the same component.  No positive sector demand, Poincare, spectral-gap,
continuum, or Clay claim is made here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem range_nodup_local : ∀ count : Nat,
    (List.range count).Nodup
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

/-! ## 1. Full physical fields selected by their lower vacuum component -/

/-- Every bounded extent-one physical field whose lower restriction belongs
to the canonical finite vacuum component.  The original boundedness proof is
retained as Type-level subtype data. -/
def globalInwardMateVacuumSectorPhysicalSources (K : Nat) :
    List (CubeInwardMatePhysicalSource K) :=
  (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).attach.filter
    (fun physicalSource =>
      centralPhysicalFiniteVacuumSectorStateB
        anchorCoupling (by decide) K 0
        (centralLowerRestriction 0 physicalSource.1))

/-- Exact membership specification for the physical-field sector event. -/
theorem mem_globalInwardMateVacuumSectorPhysicalSources_iff
    {K : Nat} {physicalSource : CubeInwardMatePhysicalSource K} :
    physicalSource ∈ globalInwardMateVacuumSectorPhysicalSources K ↔
      centralLowerRestriction 0 physicalSource.1 ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 := by
  unfold globalInwardMateVacuumSectorPhysicalSources
  rw [List.mem_filter]
  constructor
  · intro hparts
    exact (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
      anchorCoupling (by decide) K 0
      (centralLowerRestriction_mem physicalSource.2)).mp hparts.2
  · intro hsector
    exact ⟨List.mem_attach _ physicalSource,
      (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
        anchorCoupling (by decide) K 0
        (centralLowerRestriction_mem physicalSource.2)).mpr hsector⟩

theorem globalInwardMateVacuumSectorPhysicalSources_nodup (K : Nat) :
    (globalInwardMateVacuumSectorPhysicalSources K).Nodup := by
  unfold globalInwardMateVacuumSectorPhysicalSources
  exact List.filter_sublist.nodup
    (attach_nodup_of_nodup _
      (YMGap.Continuum.Z4BoundedEdgeLabellingNodup.boundedEdgeLabellings_nodup
        K (slabPhysicalFaceEdges 1)
          (by
            unfold slabPhysicalFaceEdges
            exact range_nodup_local _)))

/-! ## 2. The three localized masses -/

/-- Unnormalized all-target auxiliary mass over the physical vacuum-sector
event. -/
def globalInwardMateVacuumSectorAllTargetMass
    (K : Nat) (hK : 1 ≤ K) : Q' :=
  listQSum (cubeInwardMateCertifiedTargetFullPhysicalMass K hK)
    (globalInwardMateVacuumSectorPhysicalSources K)

/-- Unnormalized first-stretched auxiliary mass over the same event. -/
def globalInwardMateVacuumSectorFirstStretchedMass
    (K : Nat) (hK : 1 ≤ K) : Q' :=
  listQSum (cubeInwardMateFirstStretchedFullPhysicalMass K hK)
    (globalInwardMateVacuumSectorPhysicalSources K)

/-- Genuine unnormalized BF4 physical mass of the full fields whose lower
restriction belongs to the vacuum component. -/
def globalInwardMateVacuumSectorPhysicalMass
    (K : Nat) : Q' :=
  listQSum
    (fun physicalSource =>
      slabParametricKPhysicalTerm
        anchorCoupling K 1 physicalSource.1)
    (globalInwardMateVacuumSectorPhysicalSources K)

/-! ## 3. Exact localized branch conservation -/

/-- **Sector-event branch conservation.**  The good and bad auxiliary
branches reconstruct the genuine physical mass after restricting to lower
states in the exact vacuum component. -/
theorem globalInwardMateVacuumSectorBranches_weight_total
    (K : Nat) (hK : 1 ≤ K) :
    globalInwardMateVacuumSectorAllTargetMass K hK +
        globalInwardMateVacuumSectorFirstStretchedMass K hK ≈
      globalInwardMateVacuumSectorPhysicalMass K := by
  let physicalSources := globalInwardMateVacuumSectorPhysicalSources K
  let targetMass := cubeInwardMateCertifiedTargetFullPhysicalMass K hK
  let stretchedMass := cubeInwardMateFirstStretchedFullPhysicalMass K hK
  refine Q'.eqv_trans _
    (listQSum
      (fun physicalSource =>
        targetMass physicalSource + stretchedMass physicalSource)
      physicalSources) _ ?_ ?_
  · unfold globalInwardMateVacuumSectorAllTargetMass
      globalInwardMateVacuumSectorFirstStretchedMass
      physicalSources targetMass stretchedMass
    exact Q'.eqv_symm
      (listQSum_add
        (cubeInwardMateCertifiedTargetFullPhysicalMass K hK)
        (cubeInwardMateFirstStretchedFullPhysicalMass K hK)
        (globalInwardMateVacuumSectorPhysicalSources K))
  · unfold globalInwardMateVacuumSectorPhysicalMass physicalSources
    apply listQSum_congr_on
    intro physicalSource _
    unfold targetMass stretchedMass
      cubeInwardMateCertifiedTargetFullPhysicalMass
      cubeInwardMateFirstStretchedFullPhysicalMass
    exact cubeInwardMateFullSourceBranches_weight_total
      K physicalSource.1 hK
        (cubeInwardMatePhysicalBoundedOfMem
          K physicalSource.1 physicalSource.2)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.mem_globalInwardMateVacuumSectorPhysicalSources_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.globalInwardMateVacuumSectorPhysicalSources_nodup
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalBranchConservation.globalInwardMateVacuumSectorBranches_weight_total
