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
open YMGap.Continuum.BF4StationaryDensityBufferSplit
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

/-! ## 2. Forget the unnecessary endpoint-buffer fields -/

/-- A one-step gluing row already contains every field of the endpoint-free
local-contraction row.  Its separate endpoint bound is irrelevant to the
direct physical local-gluing certificate. -/
def physicalBF4LocalContractionGluingRow_of_oneStep
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {source : EdgeLabelling}
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {endpointBound qS : Q'}
    (row : PhysicalBF4OneStepContractionGluingRow
      hw K halfExtent source depth oneStep endpointBound qS) :
    PhysicalBF4LocalContractionGluingRow
      hw K halfExtent source depth oneStep qS where
  source_mem := row.source_mem
  depth_at_least_three := row.depth_at_least_three
  qS_nonnegative := row.qS_nonnegative
  oneStep_row := row.oneStep_row
  oneStep_column := row.oneStep_column
  density_gluing := row.density_gluing
  one_step_centered_bound := row.one_step_centered_bound

/-- A matched family of the stronger one-step rows forgets constructively to
the exact shared-kernel row family used by the direct AF adapter. -/
def localContractionRows_of_oneStepGluingRows
    {family : MatchedBlockFamily}
    {coupling : Nat → Q'}
    {halfExtent bits depth : Nat → Nat}
    {localRate : Nat → Q'}
    {oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q'}
    (rows : MatchedBF4OneStepGluingRows
      family coupling halfExtent bits depth localRate oneStep) :
    MatchedBF4LocalContractionGluingRows
      family coupling halfExtent depth localRate oneStep :=
  fun scale source hsource =>
    physicalBF4LocalContractionGluingRow_of_oneStep
      (rows scale source hsource)

/-! ## 3. AF-family adapters -/

/-- The stronger matched one-step gluing family directly constructs the
endpoint-free physical AF certificate.  Only the AF coupling window and the
local quarter cap are retained; no grouped profile or endpoint estimate is
needed. -/
def ofOneStepGluingRows
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bits depth : Nat → Nat}
    {localRate : Nat → Q'}
    (coupling_pos : ∀ scale, (0 : Q') < coupling scale)
    (coupling_le_window : ∀ scale, coupling scale ≤ law.g₁)
    (localRate_le_quarter :
      ∀ scale,
        localRate scale ≤
          YMGap.Continuum.FiveHolonomyPerronCutoff.quarter)
    (oneStep :
      ∀ (_scale : Nat), EdgeLabelling → EdgeLabelling → Q')
    (rows : MatchedBF4OneStepGluingRows
      family coupling (fun _ => 0) bits depth localRate oneStep) :
    PhysicalLocalGluingAFCertificate
      family law spacing coupling where
  coupling_pos := coupling_pos
  coupling_le_window := coupling_le_window
  depth := depth
  localRate := localRate
  localRate_le_quarter := localRate_le_quarter
  oneStep := oneStep
  localSlice := fun scale =>
    physicalBF4LocalSliceGluing_of_shared_rows
      (oneStep scale)
      (localContractionRows_of_oneStepGluingRows rows scale)

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

/-- The existing boundary grouped-profile package and its genuine one-step
gluing rows now contract directly to the physical AF local-gluing
certificate.  The grouped profile supplies only the coupling window and
quarter cap required downstream. -/
def ofGroupedProfileOneStepGluingRows
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
    (rows : MatchedBF4OneStepGluingRows
      family coupling (fun _ => 0) bits depth nonlinearRate oneStep) :
    PhysicalLocalGluingAFCertificate
      family law spacing coupling :=
  ofOneStepGluingRows
    profile.coupling_pos profile.coupling_le_window
    (fun scale => (profile.profileAt scale).qS_le_quarter)
    oneStep rows

end YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter

#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter.physicalBF4LocalSliceGluing_of_shared_rows
#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter.physicalBF4LocalContractionGluingRow_of_oneStep
#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter.localContractionRows_of_oneStepGluingRows
#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter.ofOneStepGluingRows
#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter.ofGroupedProfileLocalRows
#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFAdapter.ofGroupedProfileOneStepGluingRows
