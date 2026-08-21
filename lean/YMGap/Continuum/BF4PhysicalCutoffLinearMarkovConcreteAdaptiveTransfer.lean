/-
# The concrete cutoff-removed physical BF4 Markov transfer

The adaptive completion stack previously accepted a family of dense
cross-cutoff Cauchy moduli.  The stationary-source-tail theorem now constructs
that family outright.  This file specializes the abstract adaptive stack and
exports an unconditional fixed-nome, finite-volume transfer on the actual
completed physical carrier.

The resulting map agrees with the finite-linear dense limit, fixes the vacuum,
is rational-linear, preserves vacuum orthogonality, and restricts to a
rational-linear endomorphism of the completed vacuum complement.  No finite
strict-gap certificate is used here.

## Axiom gate

Only the constructed cutoff-Cauchy data and the existing constructive
completion/quotient descent are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedAdd
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedLinear
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail

/-! ## 1. Concrete completed transfer and dense agreement -/

def centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffLinearCompletion hw0 hw1 half ->
      CentralPhysicalCutoffLinearCompletion hw0 hw1 half :=
  centralPhysicalAdaptiveCompletedMarkovTransfer
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)

theorem centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_embed
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalLinearObservable) :
    centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (embedCentralPhysicalLinearObservable hw0 hw1 half observable) =
      centralPhysicalLinearMarkovDenseTransfer
        (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) observable :=
  centralPhysicalAdaptiveCompletedMarkovTransfer_embed
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) observable

theorem centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_vacuum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      centralPhysicalCutoffCompletedVacuum hw0 hw1 half :=
  centralPhysicalAdaptiveCompletedMarkovTransfer_vacuum
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)

/-! ## 2. Rational linearity on the completed carrier -/

theorem centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (completedPhysicalLinearZero hw0 hw1 half) =
      completedPhysicalLinearZero hw0 hw1 half :=
  centralPhysicalAdaptiveCompletedMarkovTransfer_zero
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)

theorem centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_add
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (completedPhysicalLinearAdd hw0 hw1 half left right) =
      completedPhysicalLinearAdd hw0 hw1 half
        (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
          hw0 hw1 half left)
        (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
          hw0 hw1 half right) :=
  centralPhysicalAdaptiveCompletedMarkovTransfer_add
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) left right

theorem centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_smul
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (scalar : Q')
    (vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (completedPhysicalLinearSmul hw0 hw1 half scalar vector) =
      completedPhysicalLinearSmul hw0 hw1 half scalar
        (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
          hw0 hw1 half vector) :=
  centralPhysicalAdaptiveCompletedMarkovTransfer_smul
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) scalar vector

def centralPhysicalConcreteAdaptiveCompletedMarkovQLinearEndomorphism
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CompletedQLinearEndomorphismData
      (centralPhysicalCutoffCompletedQModule hw0 hw1 half) :=
  centralPhysicalAdaptiveCompletedMarkovQLinearEndomorphism
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)

/-! ## 3. Vacuum pairing and the completed vacuum complement -/

def centralPhysicalConcreteAdaptiveCompletedMarkovPairingInvariant
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalAdaptiveCompletedMarkovVacuumPairingInvariant
      hw0 hw1 half
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) :=
  centralPhysicalAdaptiveCompletedMarkovPairingInvariant
    hw0 hw1 half (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)

theorem centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_preserves_orthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    {vector : CentralPhysicalCutoffLinearCompletion hw0 hw1 half}
    (hvector : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half vector) :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
        hw0 hw1 half vector) :=
  centralPhysicalAdaptiveCompletedMarkovTransfer_preserves_orthogonal
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) hvector

def centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovTransfer
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  centralPhysicalAdaptiveCompletedVacuumComplementMarkovTransfer
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)

def centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovQLinearEndomorphism
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CompletedQLinearEndomorphismData
      (centralPhysicalCutoffCompletedVacuumComplementQModule
        hw0 hw1 half) :=
  centralPhysicalAdaptiveCompletedVacuumComplementMarkovQLinearEndomorphism
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)

/-! ## Axiom audit -/

#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_embed
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_vacuum
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_zero
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_add
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_smul
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovQLinearEndomorphism
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovPairingInvariant
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_preserves_orthogonal
#print axioms centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovTransfer
#print axioms centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovQLinearEndomorphism

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
