/-
# A nontrivial finite physical SU(2) completed endpoint

The generic concrete endpoint packages the completed carrier, transfer,
vacuum, and same-object coefficient at every finite physical stage.  This
module adds the missing non-vacuity witness at the explicit cutoff-two
half-coupling sector: the centered indicator of the closed cube sector has
zero stationary mean and strictly positive completed norm.  The imported
obstruction module identifies the corresponding joint quadratic with that
norm.

This is a finite SU(2) witness only.  It does not provide a cofinal family,
an observable pin across spacing scales, a thermodynamic/continuum limit, or
the Clay theorem.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or `noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalConcreteCompletedEndpoint
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction

namespace YMGap.Continuum.BF4PhysicalConcreteCutoffTwoNontrivialEndpoint

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalConcreteCompletedEndpoint
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. The explicit finite nontrivial observable -/

abbrev cutoffTwoWeight : Q' := cutoffTwoHalfCoupling

abbrev cutoffTwoWeightNonnegative : (0 : Q') ≤ cutoffTwoWeight := by
  decide

def cutoffTwoConcreteEndpoint :
    ConcreteEndpoint cutoffTwoWeight cutoffTwoWeightNonnegative 2 0 :=
  ConcreteEndpoint.ofExisting cutoffTwoWeight cutoffTwoWeightNonnegative 2 0

theorem centeredIndicator_meanZero :
    CentralPhysicalMeanZero cutoffTwoWeight cutoffTwoWeightNonnegative 2 0
      cutoffTwoCenteredSectorIndicator :=
  cutoffTwoCenteredSectorIndicator_meanZero

theorem centeredIndicator_norm_pos :
    (0 : Q') <
      centralPhysicalWeightedInner cutoffTwoWeight
        cutoffTwoWeightNonnegative 2 0
        cutoffTwoCenteredSectorIndicator
        cutoffTwoCenteredSectorIndicator :=
  cutoffTwoCenteredSectorIndicator_norm_pos

/-! ## 2. Bundle the finite non-vacuity witness

The positive norm is intentionally recorded at the weighted-inner level.  The
existing obstruction module separately identifies the joint quadratic with
this norm; keeping that conversion out of this carrier package avoids hiding
the finite-sector obstruction behind a larger dependent elaboration. -/

structure NontrivialEndpoint : Type 1 where
  endpoint : ConcreteEndpoint cutoffTwoWeight cutoffTwoWeightNonnegative 2 0
  observable : EdgeLabelling → Q'
  observable_eq : observable = cutoffTwoCenteredSectorIndicator
  mean_zero : CentralPhysicalMeanZero cutoffTwoWeight
      cutoffTwoWeightNonnegative 2 0 observable
  norm_pos : (0 : Q') <
      centralPhysicalWeightedInner cutoffTwoWeight
        cutoffTwoWeightNonnegative 2 0 observable observable

def NontrivialEndpoint.ofExisting : NontrivialEndpoint where
  endpoint := cutoffTwoConcreteEndpoint
  observable := cutoffTwoCenteredSectorIndicator
  observable_eq := rfl
  mean_zero := centeredIndicator_meanZero
  norm_pos := centeredIndicator_norm_pos


end YMGap.Continuum.BF4PhysicalConcreteCutoffTwoNontrivialEndpoint

#print axioms
  YMGap.Continuum.BF4PhysicalConcreteCutoffTwoNontrivialEndpoint.cutoffTwoConcreteEndpoint
#print axioms
  YMGap.Continuum.BF4PhysicalConcreteCutoffTwoNontrivialEndpoint.NontrivialEndpoint.ofExisting
