/-
# Exact sector-local carrier for inward-mate sources

The global inward-mate source list is finite, but its lower endpoints are
function-valued labellings and therefore are not filtered by a global
decidable-equality instance.  This module instead compares labellings on the
complete finite lower-face support.  Both compared states vanish outside that
support, so the Boolean comparison is equivalent to literal equality.

The resulting filtered source list is exact: its members are precisely the
global certified sources whose lower endpoint belongs to the canonical finite
vacuum component.  Every such source's common state and mate endpoint remain
in that component by positive OS support.

This supplies a finite sector-local source carrier.  It does not yet prove a
sector-normalized traffic identity, a positive sector demand floor, separating
moves, uniform congestion, a Poincare or spectral gap, a continuum limit, or
the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
import YMGap.Continuum.CompactDualCutoffOneTotalKernel

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSPathGeometry
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateVacuumSectorRestriction
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. A finite-support Boolean classifier for the exact component -/

/-- Boolean membership test for the state-level canonical vacuum component.
It avoids decidable equality on the ambient function space by comparing only
the complete finite lower-face support. -/
def centralPhysicalFiniteVacuumSectorStateB
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (state : EdgeLabelling) : Bool :=
  (centralPhysicalFiniteVacuumSectorStates w hw K half).any
    (fun sectorState =>
      supportedLabellingEqB
        (centralLowerFaceIds half) state sectorState)

/-- On the finite lower-half carrier, the Boolean test is equivalent to
literal membership in the exact state-level vacuum component. -/
theorem centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {state : EdgeLabelling}
    (hstate : state ∈ centralHalfStates K half) :
    centralPhysicalFiniteVacuumSectorStateB w hw K half state = true ↔
      state ∈ centralPhysicalFiniteVacuumSectorStates w hw K half := by
  constructor
  · intro htest
    obtain ⟨sectorState, hsector, hmatch⟩ :=
      List.any_eq_true.mp htest
    have hsectorHalf : sectorState ∈ centralHalfStates K half :=
      centralPhysicalFiniteVacuumSectorState_mem_halfStates
        w hw K half hsector
    have heq : state = sectorState :=
      (supportedLabellingEqB_true_iff hstate hsectorHalf).mp hmatch
    exact Eq.mpr
      (congrArg
        (fun candidate => candidate ∈
          centralPhysicalFiniteVacuumSectorStates w hw K half)
        heq)
      hsector
  · intro hsector
    apply List.any_eq_true.mpr
    exact ⟨state, hsector,
      supportedLabellingEqB_true_of_eq
        (centralLowerFaceIds half) rfl⟩

/-! ## 2. Exact filtered source carrier -/

/-- Global certified inward-mate sources whose lower endpoint lies in the
canonical finite vacuum component. -/
def globalInwardMateVacuumSectorSources
    (K : Nat) (hK : 1 ≤ K) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  (globalCubeInwardMateCertifiedTargetFullSources K hK).filter
    (fun source =>
      centralPhysicalFiniteVacuumSectorStateB
        anchorCoupling (by decide) K 0 (sourceLower source))

/-- Exact membership specification for the sector-local source carrier. -/
theorem mem_globalInwardMateVacuumSectorSources_iff
    {K : Nat} {hK : 1 ≤ K}
    {source : GlobalCubeInwardMateCertifiedTargetFullSource K hK} :
    source ∈ globalInwardMateVacuumSectorSources K hK ↔
      source ∈ globalCubeInwardMateCertifiedTargetFullSources K hK ∧
        sourceLower source ∈
          centralPhysicalFiniteVacuumSectorStates
            anchorCoupling (by decide) K 0 := by
  unfold globalInwardMateVacuumSectorSources
  rw [List.mem_filter]
  constructor
  · intro hparts
    exact ⟨hparts.1,
      (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
        anchorCoupling (by decide) K 0 (sourceLower_mem source)).mp
        hparts.2⟩
  · intro hparts
    exact ⟨hparts.1,
      (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
        anchorCoupling (by decide) K 0 (sourceLower_mem source)).mpr
        hparts.2⟩

theorem globalInwardMateVacuumSectorSource_mem_allSources
    {K : Nat} {hK : 1 ≤ K}
    {source : GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈ globalInwardMateVacuumSectorSources K hK) :
    source ∈ globalCubeInwardMateCertifiedTargetFullSources K hK :=
  (mem_globalInwardMateVacuumSectorSources_iff.mp hsource).1

theorem globalInwardMateVacuumSectorSource_sourceLower_mem
    {K : Nat} {hK : 1 ≤ K}
    {source : GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈ globalInwardMateVacuumSectorSources K hK) :
    sourceLower source ∈
      centralPhysicalFiniteVacuumSectorStates
        anchorCoupling (by decide) K 0 :=
  (mem_globalInwardMateVacuumSectorSources_iff.mp hsource).2

/-- The exact sector-local source list inherits duplicate-freeness from the
global source enumeration. -/
theorem globalInwardMateVacuumSectorSources_nodup
    (K : Nat) (hK : 1 ≤ K) :
    (globalInwardMateVacuumSectorSources K hK).Nodup := by
  unfold globalInwardMateVacuumSectorSources
  exact List.filter_sublist.nodup
    (globalCubeInwardMateCertifiedTargetFullSources_nodup K hK)

/-! ## 3. Every selected path is internal to the component -/

/-- All three vertices of a sector-local inward-mate path lie in the exact
finite vacuum component. -/
theorem globalInwardMateVacuumSectorSource_path_internal
    {K : Nat} {hK : 1 ≤ K}
    {source : GlobalCubeInwardMateCertifiedTargetFullSource K hK}
    (hsource : source ∈ globalInwardMateVacuumSectorSources K hK) :
    sourceLower source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 ∧
      commonRight source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 ∧
      targetLower source ∈
        centralPhysicalFiniteVacuumSectorStates
          anchorCoupling (by decide) K 0 := by
  have hsourceLower :=
    globalInwardMateVacuumSectorSource_sourceLower_mem hsource
  have hpath := inwardMatePath_stays_in_vacuumSector source
    (globalInwardMateVacuumSectorSource_mem_allSources hsource)
    hsourceLower
  exact ⟨hsourceLower, hpath⟩

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.centralPhysicalFiniteVacuumSectorStateB_eq_true_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.mem_globalInwardMateVacuumSectorSources_iff
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.globalInwardMateVacuumSectorSources_nodup
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier.globalInwardMateVacuumSectorSource_path_internal
