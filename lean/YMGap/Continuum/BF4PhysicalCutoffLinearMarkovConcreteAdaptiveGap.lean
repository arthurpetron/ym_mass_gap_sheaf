/-
# Concrete adaptive BF4 gap implication after cutoff-Cauchy closure

The physical dense cross-cutoff datum is now a theorem rather than a caller
input.  This file specializes the completed contraction and correlation stack
to that datum.  A constructively cofinal family of finite centered
sixteenths is therefore the sole remaining fixed-nome finite-volume gap input.

Given that certificate, the actual cutoff-removed vacuum-complement transfer
contracts at `1/16`; all of its natural powers satisfy geometric squared-norm
decay; and same-object completed matrix coefficients obey the corresponding
Cauchy--Schwarz decay estimate.

No cofinal finite sixteenth is constructed here, and no thermodynamic or
continuum conclusion is asserted.

## Axiom gate

Only specialization of the constructed Cauchy datum and existing constructive
completion inequalities are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCorrelationDecay

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveGap

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffCofinalConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffConnectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCofinalGap
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveContraction
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCorrelationDecay
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail

/-! ## 1. The only remaining fixed-nome strictness input -/

def centralPhysicalConcreteAdaptiveCompletedMarkovCofinalStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
      hw0 hw1 half
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) :=
  centralPhysicalAdaptiveCompletedMarkovCofinalStrictContractionData
    hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) certificate

def centralPhysicalConcreteAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) half) :
    CentralPhysicalAdaptiveCompletedMarkovStrictContractionData
      hw0 hw1 half
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) :=
  centralPhysicalAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData
    hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) certificate

/-! ## 2. Concrete powers and geometric norm decay -/

def centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    Nat ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half ->
      CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half :=
  centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)

theorem centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower_cofinal_norm_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
          hw0 hw1 half n vector).1
        (centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
          hw0 hw1 half n vector).1)
      (CReal.RCscale
        ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          vector.1 vector.1)) :=
  centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_cofinal_norm_decay
    hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)
    certificate n vector

theorem centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower_localGluing_norm_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
          hw0 hw1 half n vector).1
        (centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
          hw0 hw1 half n vector).1)
      (CReal.RCscale
        ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          vector.1 vector.1)) :=
  centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_localGluing_norm_decay
    hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)
    certificate n vector

/-! ## 3. Same-object completed correlation decay -/

theorem centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower_cofinal_matrixCoefficientSq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalCenteredSixteenth
      w (Q'.le_of_lt hw0) half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half)
    (test : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
            hw0 hw1 half n vector).1 test)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
            hw0 hw1 half n vector).1 test))
      (CReal.RCmul
        (CReal.RCscale
          ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            vector.1 vector.1))
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test)) :=
  centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_cofinal_matrixCoefficientSq_decay
    hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)
    certificate n vector test

theorem centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower_localGluing_matrixCoefficientSq_decay
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (certificate : FixedNomeCofinalLocalGluing
      w (Q'.le_of_lt hw0) half)
    (n : Nat)
    (vector : CentralPhysicalCutoffCompletedVacuumComplement hw0 hw1 half)
    (test : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
            hw0 hw1 half n vector).1 test)
        (centralPhysicalCutoffCompletedInner hw0 hw1 half
          (centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
            hw0 hw1 half n vector).1 test))
      (CReal.RCmul
        (CReal.RCscale
          ((physicalCutoffSixteenth * physicalCutoffSixteenth) ^ n)
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            vector.1 vector.1))
        (centralPhysicalCutoffCompletedInner hw0 hw1 half test test)) :=
  centralPhysicalAdaptiveCompletedVacuumComplementMarkovPower_localGluing_matrixCoefficientSq_decay
    hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)
    certificate n vector test

/-! ## Axiom audit -/

#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovCofinalStrictContractionData
#print axioms centralPhysicalConcreteAdaptiveCompletedMarkovCofinalLocalGluingStrictContractionData
#print axioms centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower
#print axioms centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower_cofinal_norm_decay
#print axioms centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower_localGluing_norm_decay
#print axioms centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower_cofinal_matrixCoefficientSq_decay
#print axioms centralPhysicalConcreteAdaptiveCompletedVacuumComplementMarkovPower_localGluing_matrixCoefficientSq_decay

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveGap
