/-
# The actual completed BF4 sector strict transfer-form gap

The arbitrary-representative centered diagonal and matrix limits now prove
the upper strict form estimate on every vector in the completed root-sector
vacuum complement.  This file supplies the other half of the spectral-form
interval: finite pulled Markov positivity passes through the same outer
matrix limit, so the actual cutoff-removed completed transfer form is
nonnegative on every sector vector.

Consequently any explicit cofinal sector rate certificate packages the
literal completed statement

  0 <= <T v,v> <= q <v,v>,  0 <= q < 1.

No common rate certificate is constructed here.  No operator-norm upgrade,
thermodynamic or continuum limit, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredMatrix
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy

/-! ## 1. Positivity survives the arbitrary-representative outer limit -/

/-- Every moving pulled matrix Bishop real in the outer presentation is
nonnegative. -/
theorem centralPhysicalVacuumSectorCylinder_outerPulledMatrixSeq_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    CReal.leEv CReal.czero
      (centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X stage) := by
  let presentation :=
    (centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X).seq stage
  intro epsilon hepsilon
  refine ⟨presentation.base, fun later hlater => ?_⟩
  change (0 : Q') ≤
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) presentation.base later half
          presentation.coefficient + epsilon
  have hmatrix : (0 : Q') ≤
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) presentation.base later half
          presentation.coefficient :=
    (centralPhysicalFinitePulledVacuumSectorMatrixGNSData
      hw0 presentation.base later half hlater).self_nonneg
        presentation.coefficient
  exact Q'.le_trans' _ _ _ hmatrix
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

/-- The actual completed transfer form of one arbitrary sector completion
representative is nonnegative. -/
theorem centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.RCnonneg
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
          (Quotient.mk
            (centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).completionSetoid X))
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid X)) := by
  rw [centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerRawMatrixLimit
    hw0 hw1 half X]
  change CReal.leEv CReal.czero
    (centralPhysicalVacuumSectorOuterMatrixPairingLimit hw0 hw1 half X)
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_const CReal.czero)
    (centralPhysicalVacuumSectorCylinder_outerPulledMatrix_converges
      hw0 hw1 half X)
  intro stage
  exact
    centralPhysicalVacuumSectorCylinder_outerPulledMatrixSeq_nonnegative
      hw0 hw1 half X stage

/-- Positivity descends choice-free to every actual completed root-sector
vector. -/
theorem centralPhysicalVacuumSectorCylinder_completedTransferForm_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half) :
    CReal.RCnonneg
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
          vector) vector) := by
  refine Quotient.inductionOn vector ?_
  intro X
  exact
    centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_nonnegative
      hw0 hw1 half X

/-! ## 2. The completed strict transfer-form interval -/

/-- Concrete strict form-gap data on the actual completed root-sector vacuum
complement.  This is a form statement; an operator-norm upgrade additionally
requires the corresponding completed square-form or positive-form
Cauchy--Schwarz bridge. -/
structure CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type 1 where
  rate : Q'
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  form_nonnegative : ∀ vector :
      CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        hw0 hw1 half,
    CReal.RCnonneg
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1 vector.1)
  form_gap : ∀ vector :
      CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        hw0 hw1 half,
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1 vector.1)
      (CReal.RCscale rate
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half vector.1 vector.1))

/-- Any explicit cofinal sector certificate now gives the literal completed
strict transfer-form interval, with no separate completion/cofinality
hypothesis and with the rate unchanged. -/
def centralPhysicalVacuumSectorCylinderCompletedStrictFormGapDataAtRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictFormGapData
      hw0 hw1 half where
  rate := q
  rate_nonnegative := certificate.rate_nonnegative
  rate_lt_one := certificate.rate_lt_one
  form_nonnegative := by
    intro vector
    exact
      centralPhysicalVacuumSectorCylinder_completedTransferForm_nonnegative
        hw0 hw1 half vector.1
  form_gap := by
    intro vector
    exact
      centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate_constructed
        hw0 hw1 half certificate vector

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap.centralPhysicalVacuumSectorCylinder_outerPulledMatrixSeq_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap.centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap.centralPhysicalVacuumSectorCylinder_completedTransferForm_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap.centralPhysicalVacuumSectorCylinderCompletedStrictFormGapDataAtRate
