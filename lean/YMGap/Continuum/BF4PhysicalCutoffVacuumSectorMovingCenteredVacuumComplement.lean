/-
# A concrete nonzero vector in the completed physical vacuum complement

The moving-centered cutoff-one cube observable has already been constructed in
the actual cutoff-removed physical completion.  Separate preceding modules
prove its vacuum orthogonality and prove that it is not the completed zero
vector.  This module contracts those two facts into the subtype that is
consumed by the completed vacuum-complement transfer machinery.

The result is a fixed-nome, fixed-half-extent SU(2) witness.  It is not a
thermodynamic or continuum construction, and it does not identify a transfer
moment or a spectral gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal
open YMGap.Continuum.RCStrictPositivity

/-! ## The explicit completed complement witness -/

/-- The moving-centered cutoff-one cube vector, packaged with its proved
vacuum-orthogonality, as an inhabitant of the actual completed complement. -/
def centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 0 :=
  ⟨centralPhysicalVacuumSectorMovingCenteredGlobalVector
      hw0 hw1 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0),
    centralPhysicalVacuumSectorMovingCenteredGlobalVector_vacuumOrthogonal
      hw0 hw1 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)⟩

/-- The explicit completed-complement witness is nonzero in the ambient
physical completion. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement_ne_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement
      hw0 hw1).1 ≠ completedPhysicalLinearZero hw0 hw1 0 := by
  intro hzero
  exact centralPhysicalCutoffOneCubeMovingCenteredGlobalVector_ne_zero
    hw0 hw1 hzero

/-- The same explicit coordinate floor is a strict positive witness for the
ambient completed inner product of the packaged vacuum-complement vector. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement_inner_isPositive
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    RCIsPositive
      (centralPhysicalCutoffCompletedInner hw0 hw1 0
        (centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement
          hw0 hw1).1
        (centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement
          hw0 hw1).1) := by
  change RCIsPositive
    (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
      (centralPhysicalVacuumSectorMovingCenteredCompletion
        hw0 hw1 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
      (centralPhysicalVacuumSectorMovingCenteredCompletion
        hw0 hw1 1 0
        (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)))
  exact centralPhysicalCutoffOneCubeMovingCentered_completedInner_isPositive
    hw0 hw1

/-! ## The same-object completed transfer channel -/

/-- The concrete moving-centered cube completion, with its proved global
vacuum orthogonality, as a sector-side vacuum-complement vector. -/
def centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 0 :=
  ⟨centralPhysicalVacuumSectorMovingCenteredCompletion
      hw0 hw1 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0), by
    exact centralPhysicalVacuumSectorMovingCenteredGlobalVector_vacuumOrthogonal
      hw0 hw1 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)⟩

/-- The literal same-object autocorrelation of the concrete cube witness after
`n` powers of the inhabited completed sector transfer. -/
def centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (n : Nat) : CReal.RC :=
  centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
    hw0 hw1 0 n
    (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
      hw0 hw1).1

/-- The specialized autocorrelation is exactly the global physical
adaptive-transfer matrix coefficient, with no change of vector or operator. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_eq_global
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (n : Nat) :
    centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
      hw0 hw1 n =
      centralPhysicalCutoffCompletedInner hw0 hw1 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          hw0 hw1 0 n
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
              hw0 hw1).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
            hw0 hw1).1) := by
  unfold centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
  exact centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_eq_global
    hw0 hw1 0 n
    (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
      hw0 hw1).1

/-- Every natural power of the inhabited sector transfer on this witness has
the corresponding global adaptive-transfer image. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedTransferPower_eq_global
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (n : Nat) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (centralPhysicalVacuumSectorCylinderCompletedTransferPower
          hw0 hw1 0 n
          (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
            hw0 hw1).1) =
      centralPhysicalConcreteAdaptiveCompletedMarkovPower
        hw0 hw1 0 n
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
            hw0 hw1).1) := by
  exact centralPhysicalVacuumSectorCylinderCompletedTransferPower_intertwines
    hw0 hw1 0 n
    (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
      hw0 hw1).1

/-- The exact zero-time same-object channel is strictly positive. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_zero_isPositive
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    RCIsPositive
      (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
        hw0 hw1 0) := by
  unfold centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
    centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
  exact centralPhysicalCutoffOneCubeMovingCentered_autocorrelation_zero_isPositive
    hw0 hw1

/-- Conditional same-object decay for this exact vector: the only analytic
input is the existing completed-sector strict-contraction certificate. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (gap : CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
          hw0 hw1 n)
        (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
          hw0 hw1 n))
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
  exact centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_sq_decay
    gap n
    (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
      hw0 hw1)

/-- Directly expose the one remaining cofinal certificate required for this
observable channel. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_cofinal_sq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {q : Q'}
    (certificate : FixedNomeCofinalCenteredStrictGap
      w (Q'.le_of_lt hw0) 0 q) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
          hw0 hw1 n)
        (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
          hw0 hw1 n))
      (CReal.RCmul
        (CReal.RCscale ((q * q) ^ n)
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
  simpa only [centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation,
    centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement,
    centralPhysicalVacuumSectorCylinderCompletedInner,
    centralPhysicalVacuumSectorMovingCenteredGlobalVector] using
    (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_cofinal_sq_decay
      hw0 hw1 0 certificate n
      (centralPhysicalCutoffOneCubeMovingCenteredSectorVacuumComplement
        hw0 hw1))

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement_ne_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredVacuumComplement_inner_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_eq_global
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedTransferPower_eq_global
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_cofinal_sq_decay
