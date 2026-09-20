/-
# Cutoff-one canonical row-distance certificate

The positive cutoff-one conditioned/Markov bridge proves an exact zero
centered row for the canonical component.  This file converts that same
object identity into the mass-normalized stationary-product row-distance
certificate consumed by the finite quadratic compiler.  The conversion keeps
the component mass, the indexed physical kernel, and the conditioned density
explicit; no cofinal schedule or limit is introduced.

This is a finite SU(2) cutoff-one certificate only.  It is not a completed
OS-transfer gap, a cutoff-uniform statement, a thermodynamic/continuum
construction, an all-group theorem, or a Clay result.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalConditionedMarkovBridge
import YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalRowDistance

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalConditionedMarkovBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The conditioned density is the density used by the row identity -/

private theorem cutoffOneCanonicalMassNormalizedDensity_eqv_conditionedStep
    {w : Q'} (hw : (0 : Q') < w)
    {source target : Nat}
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) 1 0)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) 1 0) :
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity
        w (Q'.le_of_lt hw) 1 0 source target ≈
      centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w (Q'.le_of_lt hw) 1 0
        (canonicalFullDensityOneStepIndex
          w (Q'.le_of_lt hw) 1 0)
        source target := by
  have hstep :
      centralPhysicalFiniteVacuumSectorConditionedTimeStep
          w (Q'.le_of_lt hw) 1 0
          (canonicalFullDensityOneStepIndex
            w (Q'.le_of_lt hw) 1 0)
          source target ≈
        centralPhysicalFiniteVacuumSectorMass
          w (Q'.le_of_lt hw) 1 0 *
          centralPhysicalFiniteFullDensity
            w (Q'.le_of_lt hw) 1 0 source target := by
    exact finiteComponentConditionedKernelExtension_eqv_of_mem
      hsource htarget
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm hstep)
  exact centralPhysicalFiniteVacuumSectorMassNormalizedDensity_eqv_mass_mul_fullDensity
    hsource htarget

private theorem finiteWeightedCenteredRowMass_eqv_of_density_eqv
    {State : Type} {states : List State}
    (weight : State → Q')
    {density density' : State → State → Q'}
    {source : State}
    (hdensity : ∀ target, target ∈ states →
      density source target ≈ density' source target) :
    finiteWeightedCenteredRowMass states weight density source ≈
      finiteWeightedCenteredRowMass states weight density' source := by
  unfold finiteWeightedCenteredRowMass finiteL1Norm
  apply listQSum_congr_on
  intro target htarget
  apply Q'.abs_eqv_congr
  unfold finiteWeightedCenteredTransition finiteCenteredDensity
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.add_eqv_congr_right _ _ _ (hdensity target htarget))

/-! ## 2. Exact mass-normalized row-distance witness -/

/-- The cutoff-one canonical component has a genuine row-distance certificate
at rate `0`.  Its row field is obtained by transporting the already-proved
zero conditioned centered row through the exact density/row identity. -/
def cutoffOneCanonicalMassNormalizedRowDistanceCertificate
    {w : Q'} (hw : (0 : Q') < w) :
    FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate
      (centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) 1 0)
      (centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) 1 0)
      0
      (centralPhysicalFiniteVacuumSectorWeightSum_pos
        w (Q'.le_of_lt hw) 1 0)
      (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) 1 0)
      (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) 1 0) where
  kernelSymmetric := by
    intro left right hleft hright
    unfold centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_symm
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w (Q'.le_of_lt hw) 1 0
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w (Q'.le_of_lt hw) 1 0 hleft))).1
      ((mem_centralPositiveHalfStates_iff).1
        (centralPhysicalFiniteStateAt_mem_positive
          w (Q'.le_of_lt hw) 1 0
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w (Q'.le_of_lt hw) 1 0 hright))).1
  rowDistance := by
    intro source hsource
    let states := centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) 1 0
    let weight := centralPhysicalFiniteWeight w (Q'.le_of_lt hw) 1 0
    let mass := centralPhysicalFiniteVacuumSectorMass
      w (Q'.le_of_lt hw) 1 0
    let massPos := centralPhysicalFiniteVacuumSectorWeightSum_pos
      w (Q'.le_of_lt hw) 1 0
    let density := centralPhysicalFiniteVacuumSectorMassNormalizedDensity
      w (Q'.le_of_lt hw) 1 0
    let conditioned :=
      centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w (Q'.le_of_lt hw) 1 0
        (canonicalFullDensityOneStepIndex
          w (Q'.le_of_lt hw) 1 0)
    have hsourcePos : (0 : Q') < weight source := by
      exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
    have htargetPos : ∀ target, target ∈ states →
        (0 : Q') < weight target := by
      intro target htarget
      exact centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget
    have hdensity : ∀ target, target ∈ states →
        density source target ≈ conditioned source target := by
      intro target htarget
      exact cutoffOneCanonicalMassNormalizedDensity_eqv_conditionedStep
        hw hsource htarget
    have hrowConditioned :
        finiteWeightedCenteredRowMass states
            (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w (Q'.le_of_lt hw) 1 0)
            conditioned source ≈ 0 := by
      exact cutoffOneCanonicalConditionedCenteredRowMass_eqv_zero
        hw hsource
    have hrowDensity :
        finiteWeightedCenteredRowMass states
            (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w (Q'.le_of_lt hw) 1 0)
            density source ≈ 0 := by
      exact Q'.eqv_trans _ _ _
        (finiteWeightedCenteredRowMass_eqv_of_density_eqv
          (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
            w (Q'.le_of_lt hw) 1 0)
          (fun target htarget => hdensity target htarget))
        hrowConditioned
    have hrowDistance :=
      finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass
        (mass := mass) (mass_pos := massPos) (weight := weight)
        (joint := centralPhysicalFiniteKernel
          w (Q'.le_of_lt hw) 1 0)
        (source := source) hsourcePos htargetPos
    have hzero :
        finiteJointDifferenceAbsRowMass states
            (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) 1 0)
            (finiteCarrierMassNormalizedStationaryProductJoint
              mass massPos weight) source ≈ 0 := by
      refine Q'.eqv_trans _ _ _ hrowDistance ?_
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hrowDensity)
        (Q'.mul_zero_eqv _)
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hzero
        (Q'.eqv_symm (Q'.zero_mul_eqv (weight source))))

/-! ## 3. Quadratic compiler output on the same finite component -/

theorem cutoffOneCanonicalFiniteQuadratic_abs_le_zero
    {w : Q'} (hw : (0 : Q') < w)
    (coefficient : Nat → Q')
    (hcenter :
      listQSum
        (fun state => coefficient state *
          centralPhysicalFiniteWeight w (Q'.le_of_lt hw) 1 0 state)
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) 1 0) ≈ 0) :
    Q'.abs
        (finiteJointQuadratic
          (centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) 1 0)
          coefficient
          (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) 1 0)) ≤
      0 * finiteWeightedSquare
        (centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw) 1 0)
        (centralPhysicalFiniteWeight w (Q'.le_of_lt hw) 1 0)
        coefficient := by
  exact
    (FiniteCarrierMassNormalizedStationaryProductRowDistanceCertificate.absContraction
      (cutoffOneCanonicalMassNormalizedRowDistanceCertificate hw)
      coefficient hcenter)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalRowDistance

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalRowDistance.cutoffOneCanonicalMassNormalizedRowDistanceCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneCanonicalRowDistance.cutoffOneCanonicalFiniteQuadratic_abs_le_zero
