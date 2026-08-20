/-
# Direct physical BF4 local-gluing AF certificate

The local BF4 gluing argument is intrinsically a statement about the
normalized positive physical joint law.  It does not need, and after the
cutoff-one centered fence cannot use, an exact identification with the signed
Haar quadratic.

This file extracts that surviving argument as its own AF-uniform certificate.
A local centered-row rate at most `1/4`, exact all-word gluing, and the two
endpoint buffers give a `1/16` bound directly for the physical Perron joint
quadratic on the physical stationary-mean-zero subspace.

No inhabitant is constructed here.  The genuine local slice and its gluing
identity remain the analytic producer obligation.

## Axiom gate

Finite lists and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4LocalContractionGluing
import YMGap.Continuum.BF4MatchedPhysicalAFBridge
import YMGap.Continuum.BF4WeightedJointPerronPerturbation

namespace YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pointwise physical sixteenth -/

/-- Genuine local gluing at rate at most one quarter gives a one-sixteenth
contraction for the normalized positive physical joint quadratic. -/
theorem physical_joint_quadratic_abs_le_sixteenth_of_local_gluing
    {w : Q'} {hw : (0 : Q') ≤ w} {K depth : Nat}
    {qS : Q'}
    (qS_le_quarter :
      qS ≤ YMGap.Continuum.FiveHolonomyPerronCutoff.quarter)
    (localRow_exists :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K 0 →
          Nonempty
            (Σ oneStep : EdgeLabelling → EdgeLabelling → Q',
              PhysicalBF4LocalContractionGluingRow
                hw K 0 source depth oneStep qS))
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K 0 observable) :
    Q'.abs (centralPhysicalJointQuadratic w hw K 0 observable) ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          w hw K 0 observable observable := by
  let states := centralPositiveHalfStates w hw K 0
  let physical :=
    centralNormalizedPhysicalReflectedKernel w hw K 0
  let vacuum := centralPhysicalVacuumJoint w hw K 0
  let physicalQuadratic :=
    finiteJointQuadratic states observable physical
  let vacuumQuadratic :=
    finiteJointQuadratic states observable vacuum
  have hvacuum : vacuumQuadratic ≈ 0 :=
    centralPhysicalVacuumJoint_quadratic_meanZero observable hmean
  have hdifference :
      physicalQuadratic + (-vacuumQuadratic) ≈
        physicalQuadratic := by
    exact Q'.eqv_trans _
      (physicalQuadratic + 0) _
      (Q'.add_eqv_congr_left
        physicalQuadratic (-vacuumQuadratic) 0
        (Q'.eqv_trans _ (-0) _
          (Q'.neg_eqv_congr _ _ hvacuum)
          (Q'.eqv_refl 0)))
      (Q'.eqv_of_eq (Q'.add_zero' physicalQuadratic))
  have hrow :
      ∀ state,
        state ∈ states →
          finiteJointDifferenceAbsRowMass
              states physical vacuum state ≤
            Q'.mkPos 1 16 (by decide) *
              centralPhysicalRowMarginal w hw K 0 state := by
    intro state hstate
    obtain ⟨⟨oneStep, row⟩⟩ := localRow_exists state hstate
    change physicalCenteredPhysicalRowMass
        w hw K 0 state ≤ _
    exact row.physical_centered_row_le_sixteenth qS_le_quarter
  have hperturbation :
      Q'.abs (physicalQuadratic + (-vacuumQuadratic)) ≤
        Q'.mkPos 1 16 (by decide) *
          finiteWeightedSquare
            states
            (centralPhysicalRowMarginal w hw K 0)
            observable := by
    exact finiteJointQuadratic_abs_sub_le_weightedSquare
      states observable
      (centralPhysicalRowMarginal w hw K 0)
      physical vacuum
      (Q'.mkPos 1 16 (by decide))
      (fun left right hleft hright =>
        centralNormalizedPhysicalReflectedKernel_symm
          ((mem_centralPositiveHalfStates_iff).1 hleft).1
          ((mem_centralPositiveHalfStates_iff).1 hright).1)
      (fun left right _ _ =>
        centralPhysicalVacuumJoint_symmetric
          w hw K 0 left right)
      hrow
  have hphysical :
      Q'.abs physicalQuadratic ≤
        Q'.mkPos 1 16 (by decide) *
          centralPhysicalWeightedInner
            w hw K 0 observable observable := by
    refine Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.abs_eqv_congr hdifference))
      (Q'.le_trans' _ _ _ hperturbation ?_)
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        (Q'.mkPos 1 16 (by decide))
        (finiteWeightedSquare
          states
          (centralPhysicalRowMarginal w hw K 0)
          observable)
        (centralPhysicalWeightedInner
          w hw K 0 observable observable)
        (finiteWeightedSquare_physical_eqv_inner
          w hw K 0 observable))
  exact hphysical

/-! ## 2. One genuine local slice for the whole carrier -/

/-- A single explicit BF4 slice density whose powers glue to every row of the
physical slab.  This is stronger and more geometric than choosing an
unrelated existential `oneStep` separately for each source. -/
structure PhysicalBF4LocalSliceGluing
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K halfExtent depth : Nat)
    (oneStep : EdgeLabelling → EdgeLabelling → Q')
    (qS : Q') : Type where
  depth_at_least_three : 3 ≤ depth
  qS_nonnegative : (0 : Q') ≤ qS
  oneStep_row :
    ∀ row,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              oneStep row state)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  oneStep_column :
    ∀ column,
      listQSum
          (fun state =>
            centralPhysicalRowMarginal
                w hw K halfExtent state *
              oneStep state column)
          (centralPositiveHalfStates
            w hw K halfExtent) ≈
        1
  density_gluing :
    ∀ source target,
      source ∈
          centralPositiveHalfStates
            w hw K halfExtent →
      target ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        centralPhysicalConditionalDensity
            w hw K halfExtent source target ≈
          finiteWeightedDensityCompose
            (centralPositiveHalfStates
              w hw K halfExtent)
            (centralPhysicalRowMarginal
              w hw K halfExtent)
            oneStep
            (finiteWeightedDensityCompose
              (centralPositiveHalfStates
                w hw K halfExtent)
              (centralPhysicalRowMarginal
                w hw K halfExtent)
              (finiteWeightedDensityPower
                (centralPositiveHalfStates
                  w hw K halfExtent)
                (centralPhysicalRowMarginal
                  w hw K halfExtent)
                oneStep (depth - 3))
              oneStep)
            source target
  one_step_centered_bound :
    ∀ source,
      source ∈
          centralPositiveHalfStates
            w hw K halfExtent →
        finiteWeightedCenteredRowMass
            (centralPositiveHalfStates
              w hw K halfExtent)
            (centralPhysicalRowMarginal
              w hw K halfExtent)
            oneStep source ≤
          qS

namespace PhysicalBF4LocalSliceGluing

/-- Restricting the single global slice certificate to one source produces
the row interface consumed by the already-checked tensorization theorem. -/
def toRow
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {qS : Q'}
    (slice :
      PhysicalBF4LocalSliceGluing
        hw K halfExtent depth oneStep qS)
    (source : EdgeLabelling)
    (hsource :
      source ∈
        centralPositiveHalfStates w hw K halfExtent) :
    PhysicalBF4LocalContractionGluingRow
      hw K halfExtent source depth oneStep qS where
  source_mem := hsource
  depth_at_least_three := slice.depth_at_least_three
  qS_nonnegative := slice.qS_nonnegative
  oneStep_row := slice.oneStep_row
  oneStep_column := slice.oneStep_column
  density_gluing := fun target htarget =>
    slice.density_gluing source target hsource htarget
  one_step_centered_bound := slice.one_step_centered_bound

end PhysicalBF4LocalSliceGluing

/-! ## 3. AF-uniform direct-physical certificate -/

/-- The honest AF-uniform local-gluing producer after removing both refuted
exact-Haar same-action fields. -/
structure PhysicalLocalGluingAFCertificate
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q') : Type where
  coupling_pos : ∀ scale, (0 : Q') < coupling scale
  coupling_le_window : ∀ scale, coupling scale ≤ law.g₁
  depth : Nat → Nat
  localRate : Nat → Q'
  localRate_le_quarter :
    ∀ scale,
      localRate scale ≤
        YMGap.Continuum.FiveHolonomyPerronCutoff.quarter
  /-- One explicit local slice at each scale, shared by every source row. -/
  oneStep : Nat → EdgeLabelling → EdgeLabelling → Q'
  localSlice :
    ∀ scale,
      PhysicalBF4LocalSliceGluing
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        0 (depth scale) (oneStep scale) (localRate scale)

namespace PhysicalLocalGluingAFCertificate

/-- The direct positive-physical BF4 sixteenth at every AF scale. -/
theorem physical_joint_quadratic_abs_le_sixteenth_at
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (certificate :
      PhysicalLocalGluingAFCertificate family law spacing coupling)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable) ≤
      Q'.mkPos 1 16 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          observable observable :=
  physical_joint_quadratic_abs_le_sixteenth_of_local_gluing
    (certificate.localRate_le_quarter scale)
    (fun source hsource =>
      ⟨⟨certificate.oneStep scale,
        (certificate.localSlice scale).toRow source hsource⟩⟩)
    observable hmean

end PhysicalLocalGluingAFCertificate

end YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate

#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate.physical_joint_quadratic_abs_le_sixteenth_of_local_gluing
#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate.PhysicalBF4LocalSliceGluing.toRow
#print axioms YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate.PhysicalLocalGluingAFCertificate.physical_joint_quadratic_abs_le_sixteenth_at
