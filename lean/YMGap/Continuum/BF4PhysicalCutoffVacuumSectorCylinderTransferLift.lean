/-
# Exact transfer-invariance frontier for the completed BF4 root sector

The canonical root-sector cylinder completion now embeds injectively in the
global cutoff-removed physical completion.  The concrete adaptive Markov
transfer already acts on that global completion.  The remaining invariance
question is therefore an exact lifting problem: does the global transfer of
every embedded sector vector have a sector preimage?

This module records precisely that Type-level datum.  Any lift is unique by
injectivity, intertwines the pulled-back completed pairing, and preserves the
global-vacuum-orthogonal part of the sector.  No lift is constructed here;
that requires a cofinal support-preserving approximation theorem for the
adaptive cutoff action.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion

/-! ## 1. Pairing and vacuum orthogonality pulled back to the sector -/

/-- The completed sector pairing is the already constructed global physical
pairing restricted along the injective inherited-distance map. -/
def centralPhysicalVacuumSectorCylinderCompletedInner
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half) :
    CReal.RC :=
  centralPhysicalCutoffCompletedInner hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCompletionToGlobal left)
    (centralPhysicalVacuumSectorCylinderCompletionToGlobal right)

/-- The mean-zero part of the sector is defined by orthogonality of its global
image to the normalized global vacuum.  For sector-supported vectors this is
the same finite mean-zero condition used by the pulled Poincare estimates. -/
def CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half) :
    Prop :=
  CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCompletionToGlobal vector)

/-! ## 2. The exact invariant-image datum -/

/-- A constructive lift of the concrete global Markov transfer through the
injective sector embedding.  The equality field is the whole invariance
obligation; no surjectivity of the sector embedding is requested. -/
structure CentralPhysicalVacuumSectorCylinderTransferLiftData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  transfer :
    CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half →
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half
  intertwines : ∀ vector,
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (transfer vector) =
      centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal vector)

namespace CentralPhysicalVacuumSectorCylinderTransferLiftData

/-- Injectivity makes a sector lift of the concrete transfer pointwise
unique. -/
theorem transfer_eq_of_lifts
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (left right : CentralPhysicalVacuumSectorCylinderTransferLiftData
      hw0 hw1 half) :
    left.transfer = right.transfer := by
  funext vector
  apply centralPhysicalVacuumSectorCylinderCompletionToGlobal_injective
  exact Eq.trans (left.intertwines vector)
    (Eq.symm (right.intertwines vector))

/-- The lifted transfer preserves the mean-zero sector because the concrete
global transfer preserves global vacuum orthogonality. -/
theorem preserves_globalVacuumOrthogonal
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (lift : CentralPhysicalVacuumSectorCylinderTransferLiftData
      hw0 hw1 half)
    {vector :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half}
    (hvector : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half vector) :
    CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half (lift.transfer vector) := by
  unfold CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal at *
  rw [lift.intertwines]
  exact
    centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_preserves_orthogonal
      hw0 hw1 half hvector

/-- The sector transfer form is literally the global concrete transfer form
restricted to the embedded sector image. -/
theorem completedInner_transfer_eq_global
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (lift : CentralPhysicalVacuumSectorCylinderTransferLiftData
      hw0 hw1 half)
    (left right :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (lift.transfer left) right =
      centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
          hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal left))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal right) := by
  unfold centralPhysicalVacuumSectorCylinderCompletedInner
  rw [lift.intertwines]

end CentralPhysicalVacuumSectorCylinderTransferLiftData

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift.CentralPhysicalVacuumSectorCylinderTransferLiftData.transfer_eq_of_lifts
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift.CentralPhysicalVacuumSectorCylinderTransferLiftData.preserves_globalVacuumOrthogonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift.CentralPhysicalVacuumSectorCylinderTransferLiftData.completedInner_transfer_eq_global
