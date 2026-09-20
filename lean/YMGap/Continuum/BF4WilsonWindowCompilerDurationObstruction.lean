/-
# The vacuum-window compiler is not an observable kernel on arbitrary inputs

A trivial-representation loop has the same FREE source polynomial as one.
At duration two the old window compiler sends it to two-step propagation,
but sends one to the identity. The existing normalized excitation separates
these operators. Thus even source-polynomial equality, not just OS-null
equality, is insufficient for the old compiler's all-input extensionality.

The distinct duration-preserving compiler passes this test: every trivial
character insertion at an allowed offset acts by the full supplied duration,
exactly as the constant observable does. Old vacuum-state theorems remain valid.
This corrects an operator-semantics join, not the continuum or Clay frontier.
-/

import YMGap.Continuum.BF4WilsonChronologicalKernel
import YMGap.Continuum.BF4WilsonSpatialUnionSpinZeroMultiplier
import YMGap.Continuum.BF4WilsonVacuumOperatorSeparation
import YMGap.Continuum.BF4WilsonBacktrackSourceIdentity

namespace YMGap.Continuum.BF4WilsonWindowCompilerDurationObstruction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra
open YMGap.Continuum.BF4WilsonChronologicalKernel
open YMGap.Continuum.BF4WilsonWindowRealization
open YMGap.Continuum.BF4WilsonExpressionExpansion
open YMGap.Continuum.BF4WilsonTimedWordOrder
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear (completedAdd_zero)
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws (completedSmul_one)
open YMGap.Continuum.BF4WilsonSpatialUnionSpinZeroMultiplier
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "Op" => act hw0 hw1 hsmall hd hs

theorem oldCompiler_one {base : Nat} (H : Nat) (x : V) :
    Op (compileWindow H (.one : WindowExpression base)) x = x := by
  simp only [compileWindow, expand, termsProgram, wordProgram, orderWord, orderedProgram,
    act, completedSmul_one, completedAdd_zero]

theorem oldCompiler_trivialLoop {base : Nat} (H : Nat) (L : SourceLoop base) (x : V) :
    Op (compileWindow H (.loop 0 L 0)) x = completedTime hw0 hw1 hsmall hd hs H x := by
  simp only [compileWindow, expand, termsProgram, wordProgram, orderWord, insertWord,
    orderedProgram, act, Nat.sub_zero, completedMultiply_spin_zero,
    completedSmul_one, completedAdd_zero]

/-- Both endpoints now retain total duration H on every completed input. -/
theorem kernel_trivialLoop {base : Nat} (H offset : Nat) (ho : offset ≤ H)
    (L : SourceLoop base) (x : V) :
    Op (compileKernel H (.loop offset L 0)) x =
      Op (compileKernel H (.one : WindowExpression base)) x := by
  rw [compileKernel_one]
  simp only [compileKernel, expand, termsKernel, wordKernel, orderWord, insertWord,
    orderedKernel, act, completedMultiply_spin_zero, completedSmul_one, completedAdd_zero]
  rw [← completedTime_add, Nat.sub_add_cancel ho]

def trivialWindow : WindowExpression 1 := .loop 0 BF4WilsonBacktrackSourceIdentity.sourceLoop 0

private theorem zeroOffset_trivial_source {base : Nat} (L : SourceLoop base) :
    sourcePolynomial (.loop 0 L 0) = sourcePolynomial (.one : WindowExpression base) := by
  simp only [sourcePolynomial, sourceCharacter, BF4GeometricSpinNetworkMehler.characterPolynomial,
    Nat.zero_mul, SU2QuaternionPartialFactorizedHaar.liftBoundary]

theorem trivialWindow_source : sourcePolynomial trivialWindow = sourcePolynomial (.one : WindowExpression 1) :=
  zeroOffset_trivial_source BF4WilsonBacktrackSourceIdentity.sourceLoop

open BF4WilsonSpatialUnionNormalizedExcitation
open BF4ExactSlabPlaquetteSmallNomeCertificate (nome_pos nome_lt_one)
open BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

/-- Explicit original observables with identical source polynomial but different OLD actions. -/
theorem oldCompiler_not_source_extensional :
    ¬ OperatorEq nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2
      existingNome_entropyRate.2 (compileWindow 2 trivialWindow)
      (compileWindow 2 (.one : WindowExpression 1)) := by
  intro h
  have hbad := h unitExcitation
  rw [oldCompiler_one] at hbad
  change act nome_pos nome_lt_one existingNome_guards.1 existingNome_guards.2
    existingNome_entropyRate.2 (compileWindow 2 (.loop 0 BF4WilsonBacktrackSourceIdentity.sourceLoop 0))
    unitExcitation = _ at hbad
  rw [oldCompiler_trivialLoop] at hbad
  exact BF4WilsonVacuumOperatorSeparation.twoStep_moves_unitExcitation hbad

end YMGap.Continuum.BF4WilsonWindowCompilerDurationObstruction

#print axioms YMGap.Continuum.BF4WilsonWindowCompilerDurationObstruction.oldCompiler_one
#print axioms YMGap.Continuum.BF4WilsonWindowCompilerDurationObstruction.oldCompiler_trivialLoop
#print axioms YMGap.Continuum.BF4WilsonWindowCompilerDurationObstruction.kernel_trivialLoop
#print axioms YMGap.Continuum.BF4WilsonWindowCompilerDurationObstruction.trivialWindow
#print axioms YMGap.Continuum.BF4WilsonWindowCompilerDurationObstruction.trivialWindow_source
#print axioms YMGap.Continuum.BF4WilsonWindowCompilerDurationObstruction.oldCompiler_not_source_extensional
