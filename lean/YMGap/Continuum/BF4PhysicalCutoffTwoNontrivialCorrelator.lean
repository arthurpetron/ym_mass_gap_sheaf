/-
# Cutoff-two nontrivial same-object correlator

This module contracts the explicit cutoff-two centered observable, its
positive completed norm, and the already-built finite endpoint into one
non-vacuous same-object coefficient statement.  All aliases are finite-stage
aliases; no cofinal, thermodynamic, continuum, or Clay claim is made.
-/

import YMGap.Continuum.BF4PhysicalConcreteCutoffTwoNontrivialEndpoint
import YMGap.Continuum.RCStrictPositivity

namespace YMGap.Continuum.BF4PhysicalCutoffTwoNontrivialCorrelator

set_option autoImplicit false
set_option maxRecDepth 300000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorReducibilityObstruction
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalConcreteCompletedEndpoint
open YMGap.Continuum.BF4PhysicalConcreteCutoffTwoNontrivialEndpoint
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

abbrev cutoffTwoObservable : EdgeLabelling → Q' :=
  cutoffTwoCenteredSectorIndicator

abbrev cutoffTwoJoint : Q' :=
  centralPhysicalJointQuadratic cutoffTwoWeight
    cutoffTwoWeightNonnegative 2 0 cutoffTwoObservable

abbrev cutoffTwoNorm : Q' :=
  centralPhysicalWeightedInner cutoffTwoWeight
    cutoffTwoWeightNonnegative 2 0 cutoffTwoObservable cutoffTwoObservable

abbrev cutoffTwoCoefficient : CReal.RC :=
  (centralPhysicalSmulGNS cutoffTwoWeight
    cutoffTwoWeightNonnegative 2 0).toGNSData.cinnerCompl
    (centralPhysicalCompletedObservable cutoffTwoWeight
      cutoffTwoWeightNonnegative 2 0 cutoffTwoObservable)
    (centralPhysicalCompletedMarkovTransfer cutoffTwoWeight
      cutoffTwoWeightNonnegative 2 0
      (centralPhysicalCompletedObservable cutoffTwoWeight
        cutoffTwoWeightNonnegative 2 0 cutoffTwoObservable))

theorem cutoffTwo_joint_pos : (0 : Q') < cutoffTwoJoint := by
  let norm : Q' := cutoffTwoNorm
  have hnorm : (0 : Q') < norm := by
    exact centeredIndicator_norm_pos
  have hnorm_le_joint : norm ≤ cutoffTwoJoint := by
    exact Q'.ge_of_eqv cutoffTwoCenteredSectorIndicator_joint_eqv_norm
  exact Q'.pos_of_lt_of_le hnorm hnorm_le_joint

theorem cutoffTwo_same_object_coefficient_eq_joint :
    cutoffTwoCoefficient = physicalConstantRC cutoffTwoJoint := by
  exact cutoffTwoConcreteEndpoint.dense_same_object cutoffTwoObservable

theorem cutoffTwo_same_object_coefficient_isPositive :
    RCIsPositive cutoffTwoCoefficient := by
  rw [cutoffTwo_same_object_coefficient_eq_joint]
  exact ⟨cutoffTwoJoint, cutoffTwo_joint_pos,
    physicalConstantRC_le_of_rat (Q'.le_of_eqv
      (Q'.eqv_refl cutoffTwoJoint))⟩

structure NontrivialSameObjectCorrelator : Type 1 where
  endpoint : ConcreteEndpoint cutoffTwoWeight cutoffTwoWeightNonnegative 2 0
  observable : EdgeLabelling → Q'
  observable_eq : observable = cutoffTwoObservable
  mean_zero : CentralPhysicalMeanZero cutoffTwoWeight
      cutoffTwoWeightNonnegative 2 0 observable
  norm_pos : (0 : Q') <
      centralPhysicalWeightedInner cutoffTwoWeight
        cutoffTwoWeightNonnegative 2 0 observable observable
  joint_pos : (0 : Q') <
      centralPhysicalJointQuadratic cutoffTwoWeight
        cutoffTwoWeightNonnegative 2 0 observable
  same_object_eq_joint :
    (centralPhysicalSmulGNS cutoffTwoWeight
      cutoffTwoWeightNonnegative 2 0).toGNSData.cinnerCompl
      (centralPhysicalCompletedObservable cutoffTwoWeight
        cutoffTwoWeightNonnegative 2 0 observable)
      (centralPhysicalCompletedMarkovTransfer cutoffTwoWeight
        cutoffTwoWeightNonnegative 2 0
        (centralPhysicalCompletedObservable cutoffTwoWeight
          cutoffTwoWeightNonnegative 2 0 observable)) =
      physicalConstantRC
        (centralPhysicalJointQuadratic cutoffTwoWeight
          cutoffTwoWeightNonnegative 2 0 observable)
  same_object_positive : RCIsPositive cutoffTwoCoefficient

def NontrivialSameObjectCorrelator.ofExisting :
    NontrivialSameObjectCorrelator where
  endpoint := cutoffTwoConcreteEndpoint
  observable := cutoffTwoObservable
  observable_eq := rfl
  mean_zero := centeredIndicator_meanZero
  norm_pos := centeredIndicator_norm_pos
  joint_pos := cutoffTwo_joint_pos
  same_object_eq_joint := by
    exact cutoffTwoConcreteEndpoint.dense_same_object cutoffTwoObservable
  same_object_positive := cutoffTwo_same_object_coefficient_isPositive

end YMGap.Continuum.BF4PhysicalCutoffTwoNontrivialCorrelator

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffTwoNontrivialCorrelator.cutoffTwo_joint_pos
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffTwoNontrivialCorrelator.cutoffTwo_same_object_coefficient_eq_joint
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffTwoNontrivialCorrelator.cutoffTwo_same_object_coefficient_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffTwoNontrivialCorrelator.NontrivialSameObjectCorrelator.ofExisting
