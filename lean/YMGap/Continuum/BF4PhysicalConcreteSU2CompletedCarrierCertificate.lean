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

namespace YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement
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
  autocorrelation_zero_positive :
    RCIsPositive (concreteSameObjectAutocorrelation hw0 hw1 0)
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
  autocorrelation_zero_positive := by
    unfold concreteSameObjectAutocorrelation
    exact centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_zero_isPositive
      hw0 hw1
  autocorrelation_eq_global := by
    intro n
    exact centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_eq_global
      hw0 hw1 n
  transfer_power_eq_global := by
    intro n
    exact centralPhysicalCutoffOneCubeMovingCenteredCompletedTransferPower_eq_global
      hw0 hw1 n

theorem concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (certificate : ConcreteSU2CompletedCarrierCertificate hw0 hw1)
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

end YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedCarrierCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteSU2CompletedCarrierCertificate.concreteSU2CompletedCarrierCertificate_autocorrelation_sq_decay
