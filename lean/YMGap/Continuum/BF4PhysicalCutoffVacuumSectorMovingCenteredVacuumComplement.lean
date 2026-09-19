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
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
import YMGap.Continuum.BF4PhysicalCutoffCofinalCenteredRowGap
import YMGap.Continuum.BF4PhysicalCutoffCofinalLocalSliceGap
import YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalCenteredRowGap
open YMGap.Continuum.BF4PhysicalCutoffCofinalLocalSliceGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal
open YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing
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

/-- The literal physical centered-row certificate is a sufficient forward
input for the same completed cube channel.  This is the explicit
forward/backward join: a cofinal row-distance family is transported through
the canonical strict-gap adapter and then consumed by the exact
same-object autocorrelation theorem above. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_cofinal_sq_decay_of_centeredRowDistance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {q : Q'}
    (family : FixedNomeCofinalPhysicalCenteredRowDistance
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
  exact centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_cofinal_sq_decay
    hw0 hw1
    (FixedNomeCofinalPhysicalCenteredRowDistance.toCenteredStrictGap family)
    n

/-- The same literal row-distance family also supplies the reusable completed
strict-contraction object for the entire sector vacuum complement.  Thus the
forward row estimate reaches the operator-level gap interface, not only the
single cube observable. -/
def centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_centeredRowDistance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {q : Q'}
    (family : FixedNomeCofinalPhysicalCenteredRowDistance
      w (Q'.le_of_lt hw0) 0 q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtRate
    hw0 hw1 0
    (FixedNomeCofinalPhysicalCenteredRowDistance.toCenteredStrictGap family)

/-- Every completed sector vector then has the geometric squared-norm decay
at the same explicit rate. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedVacuumTransferPower_norm_decay_of_centeredRowDistance
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {q : Q'}
    (family : FixedNomeCofinalPhysicalCenteredRowDistance
      w (Q'.le_of_lt hw0) 0 q) (n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 0) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 0 n vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 0 n vector).1)
      (CReal.RCscale ((q * q) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
          vector.1 vector.1)) := by
  exact centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_cofinal_norm_decay
    hw0 hw1 0
    (FixedNomeCofinalPhysicalCenteredRowDistance.toCenteredStrictGap family)
    n vector

/-- The concrete local-slice producer interface is the direct forward input
for the same completed operator channel: its existing row adapter fixes the
rate to the checked physical sixteenth. -/
def centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_localSlice
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalPhysicalLocalSliceGluing
      w (Q'.le_of_lt hw0) 0) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_centeredRowDistance
    hw0 hw1 family.toCenteredRowDistance

theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay_of_localSlice
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalPhysicalLocalSliceGluing
      w (Q'.le_of_lt hw0) 0) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
          hw0 hw1 n)
        (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
          hw0 hw1 n))
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
  exact centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_cofinal_sq_decay_of_centeredRowDistance
    hw0 hw1 family.toCenteredRowDistance n

/-! ## Sector-normalized local-slice forward/backward join -/

/-- A genuine sector-normalized local-slice family reaches the completed
operator contraction without passing through the full-carrier row-distance
interface.  The sector-local gluing compiler supplies the exact physical rate
`1/16`; the completed Markov-form Cauchy--Schwarz law is already inhabited by
the joint adaptive limit construction. -/
def centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_sectorLocalSlice
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalVacuumSectorLocalSliceGluing
      w (Q'.le_of_lt hw0) 0) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  centralPhysicalVacuumSectorCylinderCompletedStrictContractionDataAtSectorRate
    hw0 hw1 0 family.toVacuumSectorCenteredStrictGap

/-- Every completed sector vector has the geometric squared-norm decay
obtained from the sector-normalized local-slice producer. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedVacuumTransferPower_norm_decay_of_sectorLocalSlice
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalVacuumSectorLocalSliceGluing
      w (Q'.le_of_lt hw0) 0) (n : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 0) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 0 n vector).1
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
          hw0 hw1 0 n vector).1)
      (CReal.RCscale
        ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
          vector.1 vector.1)) := by
  exact centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower_norm_decay
    (centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_sectorLocalSlice
      hw0 hw1 family) n vector

/-- The concrete moving-centered cube's same-object autocorrelation inherits
the sector-normalized local-slice rate `1/16`. -/
theorem centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay_of_sectorLocalSlice
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (family : FixedNomeCofinalVacuumSectorLocalSliceGluing
      w (Q'.le_of_lt hw0) 0) (n : Nat) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
          hw0 hw1 n)
        (centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation
          hw0 hw1 n))
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
  exact centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay
    hw0 hw1
    (centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_sectorLocalSlice
      hw0 hw1 family) n

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
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_cofinal_sq_decay_of_centeredRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_centeredRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedVacuumTransferPower_norm_decay_of_centeredRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_localSlice
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay_of_localSlice
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedStrictContractionData_of_sectorLocalSlice
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedVacuumTransferPower_norm_decay_of_sectorLocalSlice
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumComplement.centralPhysicalCutoffOneCubeMovingCenteredCompletedAutocorrelation_sq_decay_of_sectorLocalSlice
