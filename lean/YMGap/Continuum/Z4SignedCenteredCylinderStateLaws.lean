/-
# State laws for the unconditional signed centered cylinder limit

The uniform-shift boundary theorem supplies an unconditional centered
receding `CReal` for every finite Boolean cylinder predicate.  This file
packages those values, on each fixed canonical root chart, as a normalized
positive finitely additive Boolean cylinder functional.

All identities are inherited from the literal finite compatible-gas law at
every diagonal stage.  No presentation quotient, countable additivity,
configuration-space measure, or Osterwalder--Schrader reconstruction is
asserted here.
-/

import YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

namespace YMGap.Continuum.Z4SignedCenteredCylinderStateLaws

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderFunctional
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricTargetCylinderStability
open YMGap.Continuum.Z4SignedCenteredExhaustion
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact state laws at every rational diagonal stage -/

theorem couplingParametricCenteredRecedingCylinderSequence_normalized
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat)) (stage : Nat) :
    couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling base roots (fun _ => true) stage ≈ (1 : Q') := by
  unfold couplingParametricCenteredRecedingCylinderSequence
    centeredRecedingCylinderEvent cylinderEvent
  exact couplingParametricKCompatibleEventProbability_true_eqv_one
    hcoupling (centeredRecedingStageCutoff base stage)
      (centeredRecedingStageBase base stage)

theorem couplingParametricCenteredRecedingCylinderSequence_empty
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat)) (stage : Nat) :
    couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling base roots (fun _ => false) stage ≈ (0 : Q') := by
  unfold couplingParametricCenteredRecedingCylinderSequence
    centeredRecedingCylinderEvent cylinderEvent
  exact couplingParametricKCompatibleEventProbability_false_eqv_zero
    hcoupling (centeredRecedingStageCutoff base stage)
      (centeredRecedingStageBase base stage)

theorem couplingParametricCenteredRecedingCylinderSequence_complement
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) :
    couplingParametricCenteredRecedingCylinderSequence
          coupling hcoupling base roots predicate stage +
        couplingParametricCenteredRecedingCylinderSequence
          coupling hcoupling base roots
            (complementCylinderPredicate predicate) stage ≈
      (1 : Q') := by
  unfold couplingParametricCenteredRecedingCylinderSequence
    centeredRecedingCylinderEvent cylinderEvent complementCylinderPredicate
  exact couplingParametricKCompatibleEventProbability_add_complement_eqv_one
    hcoupling (centeredRecedingStageCutoff base stage)
      (centeredRecedingStageBase base stage)
      (fun family => predicate
        (familyOccurrenceFingerprint
          (centeredRecedingStageRoots base stage roots) family))

theorem couplingParametricCenteredRecedingCylinderSequence_disjoint_additive
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (first second : List Bool → Bool)
    (hdisjoint : CylinderPredicatesDisjoint first second)
    (stage : Nat) :
    couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling base roots
          (cylinderPredicateUnion first second) stage ≈
      couplingParametricCenteredRecedingCylinderSequence
          coupling hcoupling base roots first stage +
        couplingParametricCenteredRecedingCylinderSequence
          coupling hcoupling base roots second stage := by
  unfold couplingParametricCenteredRecedingCylinderSequence
    centeredRecedingCylinderEvent cylinderEvent cylinderPredicateUnion
  apply couplingParametricKCompatibleEventProbability_union_eqv_add
  intro family hfirst
  exact hdisjoint
    (familyOccurrenceFingerprint
      (centeredRecedingStageRoots base stage roots) family) hfirst

theorem couplingParametricCenteredRecedingCylinderSequence_appendIgnored
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots extra : List (List Nat))
    (predicate : List Bool → Bool) (stage : Nat) :
    couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling base (roots ++ extra)
          (extendCylinderPredicate roots.length predicate) stage =
      couplingParametricCenteredRecedingCylinderSequence
        coupling hcoupling base roots predicate stage := by
  unfold couplingParametricCenteredRecedingCylinderSequence
  rw [centeredRecedingCylinderEvent_appendIgnored]

/-! ## 2. The unconditional centered functional on one canonical chart -/

def couplingParametricCenteredCylinderFunctionalAtAnchor
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (List Bool → Bool) → CReal :=
  fun predicate =>
    couplingParametricCenteredRecedingCylinderLimitAtAnchor
      coupling hcoupling hle predicate hroots

@[simp] theorem couplingParametricCenteredCylinderFunctionalAtAnchor_approx
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    (couplingParametricCenteredCylinderFunctionalAtAnchor
      coupling hcoupling hle hroots predicate).approx stage =
        couplingParametricCenteredRecedingCylinderSequence
          coupling hcoupling base roots predicate stage := rfl

private theorem equiv_ofQ'_of_eqv_local {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) := by
  intro epsilon hepsilon
  refine ⟨0, fun _ _ => ?_⟩
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_self_of_nonneg b epsilon (Q'.le_of_lt hepsilon))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h)
      (Q'.add_le_self_of_nonneg a epsilon (Q'.le_of_lt hepsilon))

private theorem creal_equiv_of_approx_eqv_local {A B : CReal}
    (h : ∀ stage, A.approx stage ≈ B.approx stage) :
    CReal.Equiv A B :=
  CReal.Equiv_of_lifted_approx_equal
    (fun stage => equiv_ofQ'_of_eqv_local (h stage))

theorem couplingParametricCenteredCylinderFunctionalAtAnchor_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.ofQ' 0 ≤ couplingParametricCenteredCylinderFunctionalAtAnchor
      coupling hcoupling hle hroots predicate := by
  exact couplingParametricCenteredRecedingCylinderLimitAtAnchor_nonnegative
    hcoupling hle predicate hroots

theorem couplingParametricCenteredCylinderFunctionalAtAnchor_le_one
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    couplingParametricCenteredCylinderFunctionalAtAnchor
        coupling hcoupling hle hroots predicate ≤ CReal.ofQ' 1 := by
  exact couplingParametricCenteredRecedingCylinderLimitAtAnchor_le_one
    hcoupling hle predicate hroots

theorem couplingParametricCenteredCylinderFunctionalAtAnchor_normalized
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CReal.Equiv
      (couplingParametricCenteredCylinderFunctionalAtAnchor
        coupling hcoupling hle hroots (fun _ => true))
      (CReal.ofQ' 1) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact couplingParametricCenteredRecedingCylinderSequence_normalized
    hcoupling base roots stage

theorem couplingParametricCenteredCylinderFunctionalAtAnchor_empty
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    CReal.Equiv
      (couplingParametricCenteredCylinderFunctionalAtAnchor
        coupling hcoupling hle hroots (fun _ => false))
      (CReal.ofQ' 0) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact couplingParametricCenteredRecedingCylinderSequence_empty
    hcoupling base roots stage

theorem couplingParametricCenteredCylinderFunctionalAtAnchor_complement
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (CReal.add
        (couplingParametricCenteredCylinderFunctionalAtAnchor
          coupling hcoupling hle hroots predicate)
        (couplingParametricCenteredCylinderFunctionalAtAnchor
          coupling hcoupling hle hroots
            (complementCylinderPredicate predicate)))
      (CReal.ofQ' 1) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact couplingParametricCenteredRecedingCylinderSequence_complement
    hcoupling base roots predicate stage

theorem couplingParametricCenteredCylinderFunctionalAtAnchor_disjoint_additive
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (first second : List Bool → Bool)
    (hdisjoint : CylinderPredicatesDisjoint first second) :
    CReal.Equiv
      (couplingParametricCenteredCylinderFunctionalAtAnchor
        coupling hcoupling hle hroots
          (cylinderPredicateUnion first second))
      (CReal.add
        (couplingParametricCenteredCylinderFunctionalAtAnchor
          coupling hcoupling hle hroots first)
        (couplingParametricCenteredCylinderFunctionalAtAnchor
          coupling hcoupling hle hroots second)) := by
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact couplingParametricCenteredRecedingCylinderSequence_disjoint_additive
    hcoupling base roots first second hdisjoint stage

theorem couplingParametricCenteredCylinderFunctionalAtAnchor_refinement
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots extra : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (hextra : ∀ root, root ∈ extra →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let happend : ∀ root, root ∈ roots ++ extra →
        root ∈ canonicalSurfacePolymers base :=
      fun root hroot => by
        rcases List.mem_append.mp hroot with hleft | hright
        · exact hroots root hleft
        · exact hextra root hright
    CReal.Equiv
      (couplingParametricCenteredCylinderFunctionalAtAnchor
        coupling hcoupling hle happend
          (extendCylinderPredicate roots.length predicate))
      (couplingParametricCenteredCylinderFunctionalAtAnchor
        coupling hcoupling hle hroots predicate) := by
  dsimp only
  apply creal_equiv_of_approx_eqv_local
  intro stage
  exact Q'.eqv_of_eq
    (couplingParametricCenteredRecedingCylinderSequence_appendIgnored
      hcoupling base roots extra predicate stage)

#print axioms couplingParametricCenteredRecedingCylinderSequence_normalized
#print axioms couplingParametricCenteredRecedingCylinderSequence_empty
#print axioms couplingParametricCenteredRecedingCylinderSequence_complement
#print axioms couplingParametricCenteredRecedingCylinderSequence_disjoint_additive
#print axioms couplingParametricCenteredRecedingCylinderSequence_appendIgnored
#print axioms couplingParametricCenteredCylinderFunctionalAtAnchor
#print axioms couplingParametricCenteredCylinderFunctionalAtAnchor_nonnegative
#print axioms couplingParametricCenteredCylinderFunctionalAtAnchor_le_one
#print axioms couplingParametricCenteredCylinderFunctionalAtAnchor_normalized
#print axioms couplingParametricCenteredCylinderFunctionalAtAnchor_empty
#print axioms couplingParametricCenteredCylinderFunctionalAtAnchor_complement
#print axioms couplingParametricCenteredCylinderFunctionalAtAnchor_disjoint_additive
#print axioms couplingParametricCenteredCylinderFunctionalAtAnchor_refinement

end YMGap.Continuum.Z4SignedCenteredCylinderStateLaws
