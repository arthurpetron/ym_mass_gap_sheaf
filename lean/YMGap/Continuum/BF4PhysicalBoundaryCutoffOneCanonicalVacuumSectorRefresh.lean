/-
# The cutoff-one canonical vacuum sector is an exact refresh block

The cutoff-one support calculation identifies the canonical rooted component
with the vacuum/cube block.  Independently, the two genuine physical Gram
rows on that block were proved to coincide with the normalized vacuum-column
posterior.  This module joins those facts: every state in the actual
canonical vacuum sector has the same physical Markov row, fixes constants,
and annihilates the explicit nonconstant posterior-centered cube mode.

This is an exact finite `K = 1`, half-extent-zero statement.  It does not
provide a cutoff-uniform sector, a cofinal contraction, or a continuum gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneGramComparison

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneGramComparison
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumGramMarkov
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumRefreshSpectrum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The actual canonical rows are the posterior refresh -/

/-- Every genuine physical Gram row whose source lies in the canonical
cutoff-one vacuum sector is exactly the same posterior-refresh row on the
complete positive target carrier. -/
theorem cutoffOneCanonicalVacuumSectorPhysicalGramMarkov_eqv_refresh
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0)
    (target : EdgeLabelling)
    (htarget : target ∈ cutoffOneVacuumColumnCarrier w hw) :
    cutoffOneVacuumCubePhysicalGramMarkov w hw source target ≈
      cutoffOneVacuumColumnRefreshKernel w hw source target := by
  exact cutoffOneVacuumCubePhysicalGramMarkov_eqv_refresh
    hw source
    ((centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff
      hw source).mp hsource)
    target htarget

/-- Restricting an actual canonical-sector row to the exact vacuum/cube
support has total mass one. -/
theorem cutoffOneCanonicalVacuumSectorPhysicalGramMarkov_row_normalized
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0) :
    listQSum
        (cutoffOneVacuumCubePhysicalGramMarkov w hw source)
        cutoffOneVacuumCubePhysicalSources ≈
      1 := by
  exact cutoffOneVacuumCubePhysicalGramMarkov_restricted_row_normalized
    hw source
    ((centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff
      hw source).mp hsource)

/-! ## 2. Exact canonical-sector modes -/

/-- Constants are fixed on every actual canonical-sector source state. -/
theorem cutoffOneCanonicalVacuumSectorPhysicalGramAction_one
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0) :
    cutoffOneVacuumCubePhysicalGramAction w hw (fun _ => 1) source ≈
      1 := by
  exact cutoffOneVacuumCubePhysicalGramAction_one hw source
    ((centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff
      hw source).mp hsource)

/-- The explicit nonconstant posterior-centered cube mode is annihilated on
every actual canonical-sector source state. -/
theorem cutoffOneCanonicalVacuumSectorPhysicalGramAction_centeredCubeMode_zero
    {w : Q'} (hw : (0 : Q') < w)
    (source : EdgeLabelling)
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorStates
      w (Q'.le_of_lt hw) 1 0) :
    cutoffOneVacuumCubePhysicalGramAction w hw
        (cutoffOneVacuumColumnCenteredCubeMode w hw) source ≈
      0 := by
  exact cutoffOneVacuumCubePhysicalGramAction_centeredCubeMode_zero
    hw source
    ((centralPhysicalFiniteVacuumSectorStates_cutoffOne_iff
      hw source).mp hsource)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh.cutoffOneCanonicalVacuumSectorPhysicalGramMarkov_eqv_refresh
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh.cutoffOneCanonicalVacuumSectorPhysicalGramMarkov_row_normalized
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh.cutoffOneCanonicalVacuumSectorPhysicalGramAction_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalVacuumSectorRefresh.cutoffOneCanonicalVacuumSectorPhysicalGramAction_centeredCubeMode_zero
