/-
# Same vacuum vector does not mean the same original Wilson operator

The identity program and two-step time program both return the original
vacuum. The existing norm-one orthogonal excitation separates their actions:
the strict original form bound forbids that excitation being time-fixed.

These are explicit programs and a constructed test vector at w=1/1024.
Thus identifying programs merely by their vacuum output cannot justify an
operator representation. The all-input OperatorEq relation is the appropriate
relation for the finite operator calculus. No continuum conclusion follows.
-/
import YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra
import YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation

namespace YMGap.Continuum.BF4WilsonVacuumOperatorSeparation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completed_twoStep_form_gap)
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs
local notation "Op" => act nome_pos nome_lt_one hsmall hd hs
local notation "Eval" => evaluate nome_pos nome_lt_one hsmall hd hs

def identityProgram : Program 1 := .vacuum
def twoStepProgram : Program 1 := .time 2 .vacuum

theorem vacuum_outputs_equal : Eval twoStepProgram = Eval identityProgram :=
  completedUnit_fixed nome_pos nome_lt_one hsmall hd hs 2

theorem twoStep_moves_unitExcitation : T 2 unitExcitation ≠ unitExcitation := by
  intro hfixed
  have h := completed_twoStep_form_gap nome_pos nome_lt_one hsmall hd hs
    unitExcitation unitExcitation_orthogonal
  rw [hfixed, unitExcitation_norm] at h
  have hscalar : leEv cone (ofQ' rayleighCeiling) :=
    leEv_trans h (leEv_of_equiv (CRealAlg.cmul_cone (ofQ' rayleighCeiling)))
  have hbad : (1 : Q') ≤ rayleighCeiling :=
    YMGap.Continuum.GNSQuotient.GNSData.RCofQ'_le_reflect hscalar
  exact Int.not_lt.mpr hbad rayleighCeiling_lt_one

/-- The distinguishing input is concrete data, not an existentially selected vector. -/
theorem actions_differ_on_excitation : Op twoStepProgram unitExcitation ≠ Op identityProgram unitExcitation :=
  twoStep_moves_unitExcitation

theorem not_operatorEq : ¬ OperatorEq nome_pos nome_lt_one hsmall hd hs twoStepProgram identityProgram :=
  fun h => actions_differ_on_excitation (h unitExcitation)

/-- A constructive counterexample with both programs, their common vacuum
output, and the actual separating vector retained as data. -/
def separationWitness :
    Σ' p : Program 1, Σ' q : Program 1, Σ' x : V,
      (Eval p = Eval q) ×' (Op p x ≠ Op q x) :=
  ⟨twoStepProgram, identityProgram, unitExcitation, vacuum_outputs_equal, actions_differ_on_excitation⟩

end YMGap.Continuum.BF4WilsonVacuumOperatorSeparation

#print axioms YMGap.Continuum.BF4WilsonVacuumOperatorSeparation.identityProgram
#print axioms YMGap.Continuum.BF4WilsonVacuumOperatorSeparation.twoStepProgram
#print axioms YMGap.Continuum.BF4WilsonVacuumOperatorSeparation.vacuum_outputs_equal
#print axioms YMGap.Continuum.BF4WilsonVacuumOperatorSeparation.twoStep_moves_unitExcitation
#print axioms YMGap.Continuum.BF4WilsonVacuumOperatorSeparation.actions_differ_on_excitation
#print axioms YMGap.Continuum.BF4WilsonVacuumOperatorSeparation.not_operatorEq
#print axioms YMGap.Continuum.BF4WilsonVacuumOperatorSeparation.separationWitness
