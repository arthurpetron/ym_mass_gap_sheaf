/-
# Completed powers and same-object moments on the BF4 root sector

The adaptive recoding theorem constructs a genuine transfer on the completed
union of canonical root-sector cylinders.  This file packages its invariant
vacuum complement, defines all natural powers of the lifted transfer, and
defines the corresponding same-object completed autocorrelation.

Every construction is tied back to the already-constructed global physical
completion.  The sector embedding intertwines every transfer power, not only
one step, and the sector autocorrelation is literally the global adaptive
same-object matrix coefficient of the embedded vector.

This is the completed carrier/moment interface needed by a future uniform
rate argument.  No strict carrier-independent rate, thermodynamic limit,
continuum QFT, or Clay mass-gap conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

/-! ## 1. The inhabited completed sector and its vacuum complement -/

/-- The concrete lifted transfer on the completed canonical root sector. -/
def centralPhysicalVacuumSectorCylinderCompletedTransfer
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half ->
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half :=
  (centralPhysicalVacuumSectorCylinderTransferLiftData
    hw0 hw1 half).transfer

/-- The actual completed mean-zero part of the canonical root sector. -/
abbrev CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type :=
  Subtype (CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
    hw0 hw1 half)

/-- The lifted transfer restricts unconditionally to the completed root-sector
vacuum complement. -/
def centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        hw0 hw1 half ->
      CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        hw0 hw1 half :=
  fun vector =>
    ⟨centralPhysicalVacuumSectorCylinderCompletedTransfer
        hw0 hw1 half vector.1,
      (centralPhysicalVacuumSectorCylinderTransferLiftData
        hw0 hw1 half).preserves_globalVacuumOrthogonal vector.2⟩

/-- The sector vacuum complement embeds canonically in the global physical
vacuum complement. -/
def centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} :
    CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  fun vector =>
    ⟨centralPhysicalVacuumSectorCylinderCompletionToGlobal vector.1,
      vector.2⟩

/-- The vacuum-complement embedding loses no sector vector. -/
theorem centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal_injective
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} :
    Function.Injective
      (centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
        (hw0 := hw0) (hw1 := hw1) (half := half)) := by
  intro left right heq
  apply Subtype.ext
  apply centralPhysicalVacuumSectorCylinderCompletionToGlobal_injective
  exact congrArg Subtype.val heq

/-- The restricted sector transfer intertwines the concrete global transfer
restricted to its completed vacuum complement. -/
theorem centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer_intertwines
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector) =
      centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovTransfer
        hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
          vector) := by
  apply Subtype.ext
  exact (centralPhysicalVacuumSectorCylinderTransferLiftData
    hw0 hw1 half).intertwines vector.1

/-! ## 2. Natural powers and exact global intertwining -/

/-- Natural powers of the concrete completed sector transfer. -/
def centralPhysicalVacuumSectorCylinderCompletedTransferPower
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Nat ->
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half ->
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half
  | 0, vector => vector
  | n + 1, vector =>
      centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransferPower
          hw0 hw1 half n vector)

/-- Matching natural powers of the concrete global adaptive BF4 transfer. -/
def centralPhysicalConcreteAdaptiveCompletedMarkovPower
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Nat ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half
  | 0, vector => vector
  | n + 1, vector =>
      centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          hw0 hw1 half n vector)

/-- The completed sector embedding intertwines every natural power. -/
theorem centralPhysicalVacuumSectorCylinderCompletedTransferPower_intertwines
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half n : Nat)
    (vector :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        (centralPhysicalVacuumSectorCylinderCompletedTransferPower
          hw0 hw1 half n vector) =
      centralPhysicalConcreteAdaptiveCompletedMarkovPower
        hw0 hw1 half n
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal vector) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        centralPhysicalVacuumSectorCylinderCompletionToGlobal
            (centralPhysicalVacuumSectorCylinderCompletedTransferPower
              hw0 hw1 half (n + 1) vector) =
          centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
            (centralPhysicalVacuumSectorCylinderCompletionToGlobal
              (centralPhysicalVacuumSectorCylinderCompletedTransferPower
                hw0 hw1 half n vector)) := by
            exact (centralPhysicalVacuumSectorCylinderTransferLiftData
              hw0 hw1 half).intertwines _
        _ = centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
            (centralPhysicalConcreteAdaptiveCompletedMarkovPower
              hw0 hw1 half n
              (centralPhysicalVacuumSectorCylinderCompletionToGlobal
                vector)) := congrArg
              (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
                hw0 hw1 half) ih
        _ = centralPhysicalConcreteAdaptiveCompletedMarkovPower
            hw0 hw1 half (n + 1)
            (centralPhysicalVacuumSectorCylinderCompletionToGlobal
              vector) := rfl

/-- Every natural power preserves the completed sector vacuum complement. -/
theorem centralPhysicalVacuumSectorCylinderCompletedTransferPower_preserves_orthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half n : Nat)
    {vector :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half}
    (hvector : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half vector) :
    CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletedTransferPower
        hw0 hw1 half n vector) := by
  induction n with
  | zero => exact hvector
  | succ n ih =>
      exact (centralPhysicalVacuumSectorCylinderTransferLiftData
        hw0 hw1 half).preserves_globalVacuumOrthogonal ih

/-- Addition of iteration counts is composition of completed sector powers. -/
theorem centralPhysicalVacuumSectorCylinderCompletedTransferPower_add
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : forall first second
    (vector :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half),
    centralPhysicalVacuumSectorCylinderCompletedTransferPower
        hw0 hw1 half (first + second) vector =
      centralPhysicalVacuumSectorCylinderCompletedTransferPower
        hw0 hw1 half first
        (centralPhysicalVacuumSectorCylinderCompletedTransferPower
          hw0 hw1 half second vector)
  | 0, second, vector => by
      simp only [Nat.zero_add,
        centralPhysicalVacuumSectorCylinderCompletedTransferPower]
  | first + 1, second, vector => by
      rw [Nat.succ_add,
        centralPhysicalVacuumSectorCylinderCompletedTransferPower,
        centralPhysicalVacuumSectorCylinderCompletedTransferPower,
        centralPhysicalVacuumSectorCylinderCompletedTransferPower_add
          hw0 hw1 half first second vector]

/-- Natural powers on the bundled completed sector vacuum complement. -/
def centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Nat ->
      CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        hw0 hw1 half ->
      CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        hw0 hw1 half :=
  fun n vector =>
    ⟨centralPhysicalVacuumSectorCylinderCompletedTransferPower
        hw0 hw1 half n vector.1,
      centralPhysicalVacuumSectorCylinderCompletedTransferPower_preserves_orthogonal
        hw0 hw1 half n vector.2⟩

/-! ## 3. The same-object completed sector autocorrelation -/

/-- Same-object autocorrelation of the actual lifted sector transfer. -/
def centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half n : Nat)
    (vector :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half) :
    CReal.RC :=
  centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCompletedTransferPower
      hw0 hw1 half n vector)
    vector

/-- The sector same-object autocorrelation is exactly the global physical
adaptive-transfer matrix coefficient on the embedded vector. -/
theorem centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_eq_global
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half n : Nat)
    (vector :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half) :
    centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
        hw0 hw1 half n vector =
      centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          hw0 hw1 half n
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal vector))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal vector) := by
  unfold centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
    centralPhysicalVacuumSectorCylinderCompletedInner
  rw [centralPhysicalVacuumSectorCylinderCompletedTransferPower_intertwines]

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedTransfer
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedVacuumComplementToGlobal_injective
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer_intertwines
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedTransferPower
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalConcreteAdaptiveCompletedMarkovPower
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedTransferPower_intertwines
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedTransferPower_preserves_orthogonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedTransferPower_add
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedVacuumTransferPower
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments.centralPhysicalVacuumSectorCylinderCompletedAutocorrelation_eq_global
