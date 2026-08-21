/-
# Atomic reduction of the physical BF4 Markov Cauchy residual

The pointwise-data adaptive transfer asks for a cross-cutoff Cauchy modulus
for every finite rational-linear observable.  Most of that apparent analytic
burden is algebraic duplication: the cutoff action preserves zero, addition,
and rational scaling by construction, while the cutoff-removed squared
seminorm completion already proves that addition and scaling send Cauchy
sequences to Cauchy sequences.

This file contracts the full pointwise residual to one modulus for each atomic
`[0,1]` observable.  Structural recursion then constructs a modulus for every
finite-linear expression and hence the exact
`CentralPhysicalLinearMarkovDenseCauchyData` consumed by the adaptive
completed-transfer chain.

No atomic nonconstant modulus is constructed here.  Those bounded-observable
cross-cutoff estimates are the remaining analytic content of this branch.

## Axiom gate

Only finite inductive syntax and the proved constructive continuity of
addition and rational scaling are used.  There is no classical choice,
noncomputable declaration, custom axiom, or placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCauchy

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. The genuinely analytic atomic residual -/

/-- Cross-cutoff Markov Cauchy data only for atomic physical `[0,1]`
observables.  Finite rational-linear closure is derived below. -/
structure CentralPhysicalLinearMarkovAtomicCauchyData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type where
  modulus : forall observable :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable,
    CentralPhysicalLinearMarkovCrossCutoffModulus
      hw0 hw1 half (atom observable)

/-! ## 2. Structural compilation to all finite-linear observables -/

/-- The zero observable has a constant zero cutoff-action sequence. -/
def centralPhysicalLinearMarkovZeroCrossCutoffModulus
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalLinearMarkovCrossCutoffModulus hw0 hw1 half zero := by
  let D := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let Z := D.constant zero
  exact
    { rate := Z.modulus
      cauchy := by
        intro epsilon hepsilon m n hm hn
        exact Z.isCauchy epsilon hepsilon m n hm hn }

/-- Atomic Cauchy data extend by structural recursion over zero, atoms,
addition, and rational scaling to every finite-linear observable. -/
def centralPhysicalLinearMarkovCrossCutoffModulusOfAtoms
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (atomic : CentralPhysicalLinearMarkovAtomicCauchyData hw0 hw1 half) :
    forall observable : CentralPhysicalLinearObservable,
      CentralPhysicalLinearMarkovCrossCutoffModulus
        hw0 hw1 half observable
  | zero => centralPhysicalLinearMarkovZeroCrossCutoffModulus hw0 hw1 half
  | atom observable => atomic.modulus observable
  | add left right => by
      let leftModulus :=
        centralPhysicalLinearMarkovCrossCutoffModulusOfAtoms atomic left
      let rightModulus :=
        centralPhysicalLinearMarkovCrossCutoffModulusOfAtoms atomic right
      let leftCauchy := centralPhysicalLinearMarkovCutoffCauchy leftModulus
      let rightCauchy := centralPhysicalLinearMarkovCutoffCauchy rightModulus
      let sumCauchy :=
        (physicalLinearAddQuadraticLipschitz hw0 hw1 half).mapCauchy
          leftCauchy rightCauchy
      exact
        { rate := sumCauchy.modulus
          cauchy := by
            intro epsilon hepsilon m n hm hn
            exact sumCauchy.isCauchy epsilon hepsilon m n hm hn }
  | smul scalar observable => by
      let modulus :=
        centralPhysicalLinearMarkovCrossCutoffModulusOfAtoms atomic observable
      let cauchy := centralPhysicalLinearMarkovCutoffCauchy modulus
      let scaledCauchy :=
        (physicalLinearSmulContinuous hw0 hw1 half scalar).mapCauchy cauchy
      exact
        { rate := scaledCauchy.modulus
          cauchy := by
            intro epsilon hepsilon m n hm hn
            exact scaledCauchy.isCauchy epsilon hepsilon m n hm hn }

/-! ## 3. Exact handoff to the adaptive completed-transfer chain -/

/-- Atomic cross-cutoff estimates are sufficient for the full dense Cauchy
datum required by the adaptive completed transfer. -/
def CentralPhysicalLinearMarkovAtomicCauchyData.toDenseCauchyData
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (atomic : CentralPhysicalLinearMarkovAtomicCauchyData hw0 hw1 half) :
    CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half where
  modulus := centralPhysicalLinearMarkovCrossCutoffModulusOfAtoms atomic

/-! ## Axiom audit -/

#print axioms CentralPhysicalLinearMarkovAtomicCauchyData
#print axioms centralPhysicalLinearMarkovZeroCrossCutoffModulus
#print axioms centralPhysicalLinearMarkovCrossCutoffModulusOfAtoms
#print axioms CentralPhysicalLinearMarkovAtomicCauchyData.toDenseCauchyData

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAtomicCauchy
