/-
# Adapter from the grouped BF4 slice ledger to the direct physical producer

The grouped common-kernel development already carries one explicit `oneStep`
kernel per scale and row certificates for that same kernel.  This file shows
that those constructive rows assemble into the global-slice interface used by
the direct positive-physical separator producer.

The vacuum row supplies the source-independent normalization, depth, and rate
fields.  The row indexed by an arbitrary retained source supplies its gluing
identity and centered bound.  No choice is used because every row uses the
same displayed `oneStep` function and the vacuum is explicitly retained.

## Axiom gate

Finite data and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedCommonKernelPerronAction
import YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate

namespace YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4GroupedCommonKernelPerronAction
open YMGap.Continuum.BF4GroupedCommonKernelPerronAction.MatchedBF4BoundaryGroupedCoreHarnackRows
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Assemble one scale's global slice -/

/-- Row certificates for one shared kernel assemble into a single global
slice certificate. -/
def physicalBF4LocalSliceGluing_of_shared_rows
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K depth : Nat} {qS : Q'}
    (oneStep : EdgeLabelling → EdgeLabelling → Q')
    (rows :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K 0 →
          PhysicalBF4LocalContractionGluingRow
            hw K 0 source depth oneStep qS) :
    PhysicalBF4LocalSliceGluing
      hw K 0 depth oneStep qS := by
  let vacuumRow := rows zeroEdgeLabelling
    (zeroEdgeLabelling_mem_centralPositiveHalfStates hw K 0)
  exact
    { depth_at_least_three := vacuumRow.depth_at_least_three
      qS_nonnegative := vacuumRow.qS_nonnegative
      oneStep_row := vacuumRow.oneStep_row
      oneStep_column := vacuumRow.oneStep_column
      density_gluing := fun source target hsource htarget =>
        (rows source hsource).density_gluing target htarget
      one_step_centered_bound := fun source hsource =>
        (rows source hsource).one_step_centered_bound source hsource }

/-! ## 2. AF-family adapter -/

/-- The existing grouped-profile/local-row interface gives exactly the direct
physical AF certificate, with the same coupling, depth, rate, and explicit
slice kernel. -/
def ofGroupedProfileLocalRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {diagonalOrder bits depth : Nat → Nat}
    {nonlinearRate : Nat → Q'}
    (profile :
      MatchedBF4BoundaryGroupedCoreHarnackRows
        Middle family law spacing coupling
        (fun _ => 0) diagonalOrder bits depth nonlinearRate)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (localRows :
      MatchedBF4LocalContractionGluingRows
        family coupling (fun _ => 0) depth nonlinearRate oneStep) :
    PhysicalLocalGluingAFCertificate
      family law spacing coupling where
  coupling_pos := profile.coupling_pos
  coupling_le_window := profile.coupling_le_window
  depth := depth
  localRate := nonlinearRate
  localRate_le_quarter := fun scale =>
    (profile.profileAt scale).qS_le_quarter
  oneStep := oneStep
  localSlice := fun scale =>
    physicalBF4LocalSliceGluing_of_shared_rows
      (oneStep scale) (localRows scale)

end YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter

#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter.physicalBF4LocalSliceGluing_of_shared_rows
#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter.ofGroupedProfileLocalRows
