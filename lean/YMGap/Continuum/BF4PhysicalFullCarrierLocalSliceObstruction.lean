/-
# Cutoff-two obstruction to every strictly contracting full-carrier BF4 slice

The literal positive BF4 carrier at cutoff two contains more than one closed
component.  The existing reducibility theorem supplies a nonzero centered
eigenvalue-one observable.  This file connects that obstruction directly to
the full-carrier local-slice interface.

First, an arbitrary centered physical row bound at rate `q` is lifted to the
corresponding absolute quadratic bound at the same rate.  Therefore a
full-carrier local slice whose exact tensorized coefficient

    (qS * qS) * qS^(depth - 2)

is strictly below one cannot exist at cutoff two.  The obstruction is not
specific to the earlier sufficient cap `qS <= 1/4`; it rules out every strict
depth-amplified full-carrier local contraction.  A genuine producer must be
sector-native.

This is a finite routing theorem, not a sector-local contraction witness and
not a thermodynamic or continuum result.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction
import YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate

namespace YMGap.Continuum.BF4PhysicalFullCarrierLocalSliceObstruction

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CommonRankOneRowTriangle
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalConditionalDensity
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Arbitrary-rate physical row-to-form contraction -/

/-- A physical centered-row estimate at an arbitrary rate contracts every
normalized positive physical joint quadratic on the stationary-mean-zero
subspace at that same rate. -/
theorem physical_joint_quadratic_abs_le_rate_of_centered_rows
    {w : Q'} {hw : (0 : Q') ≤ w} {K halfExtent : Nat} {rate : Q'}
    (centered_rows :
      ∀ source,
        source ∈ centralPositiveHalfStates w hw K halfExtent →
          physicalCenteredPhysicalRowMass
              w hw K halfExtent source ≤
            rate * centralPhysicalRowMarginal
              w hw K halfExtent source)
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K halfExtent observable) :
    Q'.abs
        (centralPhysicalJointQuadratic
          w hw K halfExtent observable) ≤
      rate * centralPhysicalWeightedInner
        w hw K halfExtent observable observable := by
  let states := centralPositiveHalfStates w hw K halfExtent
  let physical :=
    centralNormalizedPhysicalReflectedKernel w hw K halfExtent
  let vacuum := centralPhysicalVacuumJoint w hw K halfExtent
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
              rate * centralPhysicalRowMarginal
                w hw K halfExtent state := by
    intro state hstate
    change physicalCenteredPhysicalRowMass
        w hw K halfExtent state ≤ _
    exact centered_rows state hstate
  have hperturbation :
      Q'.abs (physicalQuadratic + (-vacuumQuadratic)) ≤
        rate * finiteWeightedSquare states
          (centralPhysicalRowMarginal w hw K halfExtent)
          observable := by
    exact finiteJointQuadratic_abs_sub_le_weightedSquare
      states observable
      (centralPhysicalRowMarginal w hw K halfExtent)
      physical vacuum rate
      (fun left right hleft hright =>
        centralNormalizedPhysicalReflectedKernel_symm
          ((mem_centralPositiveHalfStates_iff).1 hleft).1
          ((mem_centralPositiveHalfStates_iff).1 hright).1)
      (fun left right _ _ =>
        centralPhysicalVacuumJoint_symmetric
          w hw K halfExtent left right)
      hrow
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.abs_eqv_congr hdifference)) ?_
  refine Q'.le_trans' _ _ _ hperturbation ?_
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_left rate _ _
      (finiteWeightedSquare_physical_eqv_inner
        w hw K halfExtent observable))

/-! ## 2. The full local-slice route is impossible at cutoff two -/

/-- No shared full-carrier cutoff-two slice can have a strictly contracting
complete local power.  Such a slice would contract the explicit nonzero
centered eigenvalue-one mode. -/
theorem no_cutoffTwo_fullCarrier_localSlice_of_localPower_lt_one
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {qS : Q'}
    (hlocalPower :
      (qS * qS) * (qS ^ (depth - 2)) < (1 : Q')) :
    ¬ Nonempty
      (PhysicalBF4LocalSliceGluing
        (w := cutoffTwoHalfCoupling)
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 depth oneStep qS) := by
  intro hslice
  obtain ⟨slice⟩ := hslice
  apply no_cutoffTwo_fullCarrier_strict_abs_gap
    ((qS * qS) * (qS ^ (depth - 2))) hlocalPower
  intro observable hmean
  apply physical_joint_quadratic_abs_le_rate_of_centered_rows
  · intro source hsource
    exact (slice.toRow source hsource).physical_centered_row_le_local_power
  · exact hmean

/-- In particular, the earlier quarter-rate full-carrier interface has no
cutoff-two inhabitant, independently of the proposed depth and kernel. -/
theorem no_cutoffTwo_fullCarrier_localSlice_of_rate_le_quarter
    {depth : Nat}
    {oneStep : EdgeLabelling → EdgeLabelling → Q'}
    {qS : Q'}
    (qS_le_quarter :
      qS ≤ YMGap.Continuum.FiveHolonomyPerronCutoff.quarter) :
    ¬ Nonempty
      (PhysicalBF4LocalSliceGluing
        (w := cutoffTwoHalfCoupling)
        (by decide : (0 : Q') ≤ cutoffTwoHalfCoupling)
        2 0 depth oneStep qS) := by
  intro hslice
  obtain ⟨slice⟩ := hslice
  apply no_cutoffTwo_fullCarrier_strict_abs_gap
    (Q'.mkPos 1 16 (by decide)) (by decide)
  intro observable hmean
  exact physical_joint_quadratic_abs_le_sixteenth_of_local_gluing
    qS_le_quarter
    (fun source hsource =>
      ⟨⟨oneStep, slice.toRow source hsource⟩⟩)
    observable hmean

end YMGap.Continuum.BF4PhysicalFullCarrierLocalSliceObstruction

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFullCarrierLocalSliceObstruction.physical_joint_quadratic_abs_le_rate_of_centered_rows
#print axioms
  YMGap.Continuum.BF4PhysicalFullCarrierLocalSliceObstruction.no_cutoffTwo_fullCarrier_localSlice_of_localPower_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalFullCarrierLocalSliceObstruction.no_cutoffTwo_fullCarrier_localSlice_of_rate_le_quarter
