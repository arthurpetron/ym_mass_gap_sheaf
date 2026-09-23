/-
# Concrete fixed-nome SU(2) completed-carrier certificate

The physical BF4/GNS development already constructs, at fixed positive nome,
the canonical vacuum-sector completion, its vacuum-complement transfer, and a
literal moving-centered cube vector.  This module contracts those declarations
into one certificate so downstream code can consume one observable-connected
object instead of silently mixing carriers.

The certificate deliberately separates the analytic strict-gap input.  Its
constructor proves only the concrete carrier, normalized vacuum, explicit
vacuum-complement vector, transfer, and same-object correlator realization.
The conditional decay projection consumes a named completed-sector strict
contraction certificate; it does not manufacture one and does not claim a
thermodynamic limit, continuum QFT, or Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement
import YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
import YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityZeroDebt
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision

namespace YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalCenteredRowGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffCofinalLocalSliceGap
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4LocalContractionGluing
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing
open YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate
open YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityZeroDebt
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityPowerToLocalSlice
open YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
open YMGap.Continuum.RCStrictPositivity

/-! ## 1. One fixed-nome observable-connected object -/

abbrev SectorCarrier
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Type :=
  CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 0

abbrev SectorVacuumComplement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Type :=
  CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
    hw0 hw1 0

abbrev SectorTransfer
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Type :=
  SectorVacuumComplement hw0 hw1 → SectorVacuumComplement hw0 hw1

def concreteSectorTransfer
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    SectorTransfer hw0 hw1 :=
  centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer hw0 hw1 0

def concreteVacuumComplementVector
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    SectorVacuumComplement hw0 hw1 :=
  centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement hw0 hw1

def concreteSameObjectAutocorrelation
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Nat → CReal.RC :=
  centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation hw0 hw1

/-! The ambient normalized vacuum is retained alongside the sector carrier;
the sector embeds into that same physical cutoff completion. -/

structure ConcreteSU2CompletedCarrierCertificate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : Type 1 where
  vacuum_unit :
    centralPhysicalCutoffCompletedInner hw0 hw1 0
      (centralPhysicalCutoffCompletedVacuum hw0 hw1 0)
      (centralPhysicalCutoffCompletedVacuum hw0 hw1 0) =
      Quotient.mk CReal.crealSetoid CReal.cone
  vector_inner_positive :
    RCIsPositive
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (concreteVacuumComplementVector hw0 hw1).1
        (concreteVacuumComplementVector hw0 hw1).1)
  /-- The same completed norm retains its explicit rational coordinate floor;
  this is the witness-bearing nontriviality payload, not merely a positivity
  proposition. -/
  vector_inner_floor :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ'
          (centralPhysicalVacuumSectorCoordinateFloor
            w (Q'.le_of_lt hw0) 1 0)))
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (concreteVacuumComplementVector hw0 hw1).1
        (concreteVacuumComplementVector hw0 hw1).1)
  autocorrelation_zero_positive :
    RCIsPositive (concreteSameObjectAutocorrelation hw0 hw1 0)
  /-- The explicit floor is transported to the literal zero-time
  same-object autocorrelation of the same completed observable. -/
  autocorrelation_zero_floor :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ'
          (centralPhysicalVacuumSectorCoordinateFloor
            w (Q'.le_of_lt hw0) 1 0)))
      (concreteSameObjectAutocorrelation hw0 hw1 0)
  autocorrelation_eq_global : ∀ n,
    concreteSameObjectAutocorrelation hw0 hw1 n =
      centralPhysicalCutoffCompletedInner hw0 hw1 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          hw0 hw1 0 n
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (concreteVacuumComplementVector hw0 hw1).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (concreteVacuumComplementVector hw0 hw1).1)
  transfer_power_eq_global : ∀ n,
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (centralPhysicalVacuumSectorCylinderCompletedTransferPower
          hw0 hw1 0 n (concreteVacuumComplementVector hw0 hw1).1) =
      centralPhysicalConcreteAdaptiveCompletedMarkovPower
        hw0 hw1 0 n
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (concreteVacuumComplementVector hw0 hw1).1)

/-! ## 2. Constructor and conditional consequence -/

def concreteSU2CompletedCarrierCertificate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    ConcreteSU2CompletedCarrierCertificate hw0 hw1 where
  vacuum_unit := centralPhysicalCutoffCompletedVacuum_inner_self_eq_one
    hw0 hw1 0
  vector_inner_positive := by
    unfold concreteVacuumComplementVector
    exact centralPhysicalCutoffOneCubeMovingCentered_completedInner_isPositive
      hw0 hw1
  vector_inner_floor := by
    unfold concreteVacuumComplementVector
    exact centralPhysicalCutoffOneCubeMovingCentered_floor_le_completedInner
      hw0 hw1
  autocorrelation_zero_positive := by
    unfold concreteSameObjectAutocorrelation
    exact centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_zero_isPositive
      hw0 hw1
  autocorrelation_zero_floor := by
    unfold concreteSameObjectAutocorrelation
    unfold centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
    unfold centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
    rw [centralPhysicalCutoffOneCubeMovingCentered_autocorrelation_zero_eq_inner]
    exact centralPhysicalCutoffOneCubeMovingCentered_floor_le_completedInner
      hw0 hw1
  autocorrelation_eq_global := by
    intro n
    exact centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_eq_global
      hw0 hw1 n
  transfer_power_eq_global := by
    intro n
    exact centralPhysicalCutoffOneCubeMovingCenteredCompletedTransferPower_eq_global
      hw0 hw1 n

/-! ## 2a. Exact finite zero-cutoff seed -/

/-- The canonical full-density factorization at cutoff `0` is exposed on the
same physical SU(2) local-slice interface used by the completed carrier.
This is an exact finite seed only: its singleton carrier has no non-vacuum
direction, so it is not itself a strict gap or a cofinal producer. -/
def concreteSU2ZeroCutoffCanonicalLocalSlice
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    PhysicalBF4VacuumSectorLocalSliceGluing
      w (Q'.le_of_lt hw0) 0 0 3
      (centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w (Q'.le_of_lt hw0) 0 0
        (canonicalFullDensityOneStepIndex
          w (Q'.le_of_lt hw0) 0 0)) 0 :=
  PhysicalBF4VacuumSectorDensityPowerGluing.toLocalSliceGluing
    (canonicalFullDensityVacuumSectorDensityPowerGluing_zero
      (w := w) (hw := Q'.le_of_lt hw0) 0)

theorem concreteSU2ZeroCutoffCanonicalLocalSlice_centered_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (source : Nat)
    (hsource :
      source ∈ centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) 0 0) :
    finiteWeightedCenteredRowMass
      (centralPhysicalFiniteVacuumSectorIndices w (Q'.le_of_lt hw0) 0 0)
      (centralPhysicalFiniteVacuumSectorMassNormalizedWeight w (Q'.le_of_lt hw0) 0 0)
      (centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w (Q'.le_of_lt hw0) 0 0
        (canonicalFullDensityOneStepIndex w (Q'.le_of_lt hw0) 0 0))
      source ≤ 0 := by
  exact (concreteSU2ZeroCutoffCanonicalLocalSlice hw0 hw1).one_step_centered_bound
    source hsource

/-! ## 2b. Active ray-capacity route to the same carrier -/

/-- The canonical finite-capacity success interface from the active ray route
reaches the strict-contraction datum of this same completed SU(2) carrier.
The success family and its rate remain explicit inputs; this adapter neither
constructs cofinal success nor changes the carrier. -/
def concreteSU2CompletedStrictContractionData_of_canonicalFiniteCapacity
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (data :
      FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  data.toCompletedStrictContractionData hw0 hw1

theorem concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (gap : CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (concreteSameObjectAutocorrelation hw0 hw1 n)
        (concreteSameObjectAutocorrelation hw0 hw1 n))
      (CReal.RCmul
        (CReal.RCscale ((gap.rate * gap.rate) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 0
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector
              hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector
              hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))))
        (centralPhysicalCutoffCompletedInner hw0 hw1 0
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector
            hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector
            hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)))) := by
  exact centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay
    hw0 hw1 gap n

/-! ## 2a. Inhabited marginal-gap specialization -/

/-- The concrete completed SU(2) carrier and its literal same-object
autocorrelation inherit the already inhabited marginal-sector contraction at
the explicit nome-dependent rate `cutoffUniformRate w`.  This is a fixed-nome,
extent-one result; it is not a spacing-uniform or continuum mass gap. -/
theorem concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay_of_marginalGap
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hw : w ≤ HalfPow.half) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (concreteSameObjectAutocorrelation hw0 hw1 n)
        (concreteSameObjectAutocorrelation hw0 hw1 n))
      (CReal.RCmul
        (CReal.RCscale
          ((cutoffUniformRate w (Q'.le_of_lt hw0) *
              cutoffUniformRate w (Q'.le_of_lt hw0)) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 0
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector
              hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector
              hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))))
        (centralPhysicalCutoffCompletedInner hw0 hw1 0
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector
            hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector
            hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)))) := by
  simpa only [concreteSameObjectAutocorrelation,
    completedSectorContraction_rate] using
    (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay
      hw0 hw1
      (completedSectorContraction hw0 hw1 hw)
      n)

/-- Package the inhabited concrete completed carrier together with the
inhabited marginal strict-contraction witness used by the preceding decay
theorem. -/
def concreteSU2CompletedMarginalCarrierCertificate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hw : w ≤ HalfPow.half) :
    ConcreteSU2CompletedCarrierCertificate hw0 hw1 ×
      CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
        hw0 hw1 0 :=
  ⟨concreteSU2CompletedCarrierCertificate hw0 hw1,
    completedSectorContraction hw0 hw1 hw⟩

/-! ## 2a. Expose the completed strict-contraction witness -/

/-- The established generic cofinal local-gluing producer reaches the strict
contraction data of this very completed vacuum-sector carrier.  The physical
row adapter is the only conversion: no new rate, carrier, or transfer is
chosen here. -/
def concreteSU2CompletedStrictContractionData_of_localGluing
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) 0) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_localSlice
    hw0 hw1 (FixedNomeCofinalLocalGluing.toPhysicalLocalSliceGluing family)

/-- The strict-contraction witness above reproduces the literal same-object
autocorrelation decay at the checked physical rate `1/16`. -/
theorem concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay_of_localGluing_viaGap
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) 0) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (concreteSameObjectAutocorrelation hw0 hw1 n)
        (concreteSameObjectAutocorrelation hw0 hw1 n))
      (CReal.RCmul
      (CReal.RCscale
          ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 0
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector
              hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector
              hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))))
        (centralPhysicalCutoffCompletedInner hw0 hw1 0
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector
            hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector
            hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)))) := by
  simpa only [concreteSU2CompletedStrictContractionData_of_localGluing,
    centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_localSlice,
    FixedNomeCofinalLocalGluing.toPhysicalLocalSliceGluing,
    centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_centeredRowDistance,
    FixedNomeCofinalPhysicalLocalSliceGluing.toCenteredRowDistance,
    FixedNomeCofinalPhysicalCenteredRowDistance.toCenteredStrictGap,
    FixedNomeCofinalPhysicalCenteredRowDistance.toVacuumSectorCenteredStrictGap]
    using concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay
      hw0 hw1
      (concreteSU2CompletedStrictContractionData_of_localGluing hw0 hw1 family)
      n

/-- The same-object correlator reaches the explicit physical `1/16` rate when
the existing cofinal local-slice certificate is supplied.  This is the
smallest local-to-carrier join: the carrier, transfer, vacuum complement, and
observable remain the concrete same objects above, while the local gluing
family is the sole strictness input. -/
theorem concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay_of_localGluing
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) 0) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (concreteSameObjectAutocorrelation hw0 hw1 n)
        (concreteSameObjectAutocorrelation hw0 hw1 n))
      (CReal.RCmul
      (CReal.RCscale
          ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 0
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector
              hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
            (centralPhysicalVacuumSectorMovingCenteredGlobalVector
              hw0 hw1 1 0
              (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))))
        (centralPhysicalCutoffCompletedInner hw0 hw1 0
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector
            hw0 hw1 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
          (centralPhysicalVacuumSectorMovingCenteredGlobalVector
            hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)))) := by
  simpa only [concreteSameObjectAutocorrelation] using
    (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay_of_localSlice
      hw0 hw1
      (FixedNomeCofinalLocalGluing.toPhysicalLocalSliceGluing family) n)

end YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedStrictContractionData_of_canonicalFiniteCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2ZeroCutoffCanonicalLocalSlice
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2ZeroCutoffCanonicalLocalSlice_centered_bound
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedCarrierCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay_of_marginalGap
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedMarginalCarrierCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedStrictContractionData_of_localGluing
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay_of_localGluing_viaGap
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay_of_localGluing
