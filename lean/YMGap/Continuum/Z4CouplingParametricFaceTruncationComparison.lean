/-
# Same-law comparison of two face-component truncations

In one finite compatible-support law, the size-`<m` face event is nested in
the size-`<n` face event whenever `m <= n`.  Their difference is contained in
the already bounded event that the marked face belongs to a component of size
at least `m`.  This gives a cutoff-uniform, volume-uniform absolute probability
comparison with the explicit pinned tail.

The result is deliberately stated for an arbitrary finite box and physical
face identifier.  The central-face diagonal can therefore compare two
truncation floors after transporting both to any common larger volume.
-/

import YMGap.Continuum.Z4CanonicalCentralFaceTruncationNesting

namespace YMGap.Continuum.Z4CouplingParametricFaceTruncationComparison

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalCentralFaceTruncationNesting
open YMGap.Continuum.Z4CanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CouplingParametricCanonicalFaceEventPinnedTail
open YMGap.Continuum.Z4CouplingParametricCylinderJointFunctional
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def canonicalFaceTruncationDifferenceEvent
    (base face smallFloor largeFloor : Nat) :
    List (List Nat) → Bool :=
  fun family =>
    canonicalFaceTruncatedCylinderEvent base face largeFloor family &&
      !(canonicalFaceTruncatedCylinderEvent base face smallFloor family)

theorem canonicalFaceTruncationDifference_implies_remainder
    {base face smallFloor largeFloor : Nat}
    {family : List (List Nat)}
    (hdifference : canonicalFaceTruncationDifferenceEvent
      base face smallFloor largeFloor family = true) :
    canonicalFaceTruncationRemainderEvent
        base face smallFloor family = true := by
  have hparts := (Bool.and_eq_true _ _).mp hdifference
  have hlarge := hparts.1
  have hsmallFalse :
      canonicalFaceTruncatedCylinderEvent
        base face smallFloor family = false := by
    cases hsmall : canonicalFaceTruncatedCylinderEvent
        base face smallFloor family with
    | false => rfl
    | true =>
        rw [hsmall] at hparts
        cases hparts.2
  have hface : familyContainsFaceB face family = true :=
    canonicalFaceTruncatedCylinderEvent_implies_face hlarge
  unfold canonicalFaceTruncationRemainderEvent
  rw [hface, hsmallFalse]
  rfl

theorem canonicalFaceTruncatedLarge_eq_small_or_difference
    {base face smallFloor largeFloor : Nat}
    (hfloor : smallFloor ≤ largeFloor)
    (family : List (List Nat)) :
    canonicalFaceTruncatedCylinderEvent base face largeFloor family =
      (canonicalFaceTruncatedCylinderEvent base face smallFloor family ||
        canonicalFaceTruncationDifferenceEvent
          base face smallFloor largeFloor family) := by
  cases hsmall : canonicalFaceTruncatedCylinderEvent
      base face smallFloor family with
  | false =>
      unfold canonicalFaceTruncationDifferenceEvent
      simp only [hsmall, Bool.not_false, Bool.and_true, Bool.false_or]
  | true =>
      have hlarge := canonicalFaceTruncatedCylinderEvent_mono_size
        hfloor family hsmall
      rw [hlarge]
      simp only [Bool.true_or]

theorem canonicalFaceTruncatedSmall_difference_disjoint
    (base face smallFloor largeFloor : Nat)
    (family : List (List Nat))
    (hsmall : canonicalFaceTruncatedCylinderEvent
      base face smallFloor family = true) :
    canonicalFaceTruncationDifferenceEvent
      base face smallFloor largeFloor family = false := by
  unfold canonicalFaceTruncationDifferenceEvent
  rw [hsmall]
  simp only [Bool.not_true, Bool.and_false]

theorem couplingParametricKCanonicalFaceTruncationDifferenceProbability_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff base face smallFloor largeFloor : Nat) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff base
        (canonicalFaceTruncationDifferenceEvent
          base face smallFloor largeFloor) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ smallFloor := by
  exact Q'.le_trans' _ _ _
    (couplingParametricKCompatibleSupportEventProbability_mono
      hcoupling cutoff base _ _
      (fun _family _hfamily hdifference =>
        canonicalFaceTruncationDifference_implies_remainder hdifference))
    (couplingParametricKFaceTruncationRemainderProbability_le_tail
      hcoupling hle cutoff base face smallFloor)

theorem couplingParametricKCanonicalFaceTruncatedProbability_mono_size
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff base face : Nat) {smallFloor largeFloor : Nat}
    (hfloor : smallFloor ≤ largeFloor) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff base
        (canonicalFaceTruncatedCylinderEvent base face smallFloor) ≤
      couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff base
        (canonicalFaceTruncatedCylinderEvent base face largeFloor) := by
  exact couplingParametricKCompatibleSupportEventProbability_mono
    hcoupling cutoff base _ _
    (fun family _hfamily hsmall =>
      canonicalFaceTruncatedCylinderEvent_mono_size
        hfloor family hsmall)

theorem couplingParametricKCanonicalFaceTruncatedLargeProbability_le_small_add_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff base face : Nat) {smallFloor largeFloor : Nat}
    (hfloor : smallFloor ≤ largeFloor) :
    couplingParametricKCompatibleSupportEventProbability
        coupling hcoupling cutoff base
        (canonicalFaceTruncatedCylinderEvent base face largeFloor) ≤
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff base
          (canonicalFaceTruncatedCylinderEvent base face smallFloor) +
        Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ smallFloor := by
  have hevent :
      canonicalFaceTruncatedCylinderEvent base face largeFloor =
        (fun family =>
          canonicalFaceTruncatedCylinderEvent
              base face smallFloor family ||
            canonicalFaceTruncationDifferenceEvent
              base face smallFloor largeFloor family) := by
    funext family
    exact canonicalFaceTruncatedLarge_eq_small_or_difference
      hfloor family
  have hdecomposition :
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff base
          (canonicalFaceTruncatedCylinderEvent base face largeFloor) ≈
        couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff base
            (canonicalFaceTruncatedCylinderEvent
              base face smallFloor) +
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff base
            (canonicalFaceTruncationDifferenceEvent
              base face smallFloor largeFloor) := by
    rw [hevent]
    exact couplingParametricKCompatibleEventProbability_union_eqv_add
      hcoupling cutoff base
      (canonicalFaceTruncatedCylinderEvent base face smallFloor)
      (canonicalFaceTruncationDifferenceEvent
        base face smallFloor largeFloor)
      (canonicalFaceTruncatedSmall_difference_disjoint
        base face smallFloor largeFloor)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdecomposition)
    (Q'.add_le_add_left _ _ _
      (couplingParametricKCanonicalFaceTruncationDifferenceProbability_le_tail
        hcoupling hle cutoff base face smallFloor largeFloor))

/-- The load-bearing same-law estimate: changing only the component-size
truncation changes the face-event probability by at most the omitted-component
tail, uniformly in the finite volume and representation cutoff. -/
theorem couplingParametricKCanonicalFaceTruncatedProbability_abs_sub_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff base face : Nat) {smallFloor largeFloor : Nat}
    (hfloor : smallFloor ≤ largeFloor) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff base
            (canonicalFaceTruncatedCylinderEvent base face largeFloor) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff base
            (canonicalFaceTruncatedCylinderEvent base face smallFloor)) ≤
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ smallFloor := by
  let smallProbability :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff base
      (canonicalFaceTruncatedCylinderEvent base face smallFloor)
  let largeProbability :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff base
      (canonicalFaceTruncatedCylinderEvent base face largeFloor)
  have hmono : smallProbability ≤ largeProbability := by
    dsimp only [smallProbability, largeProbability]
    exact couplingParametricKCanonicalFaceTruncatedProbability_mono_size
      hcoupling cutoff base face hfloor
  have hupper : largeProbability ≤ smallProbability +
      Q'.ofNat 2 * anchorDecoratedEffectiveRatio ^ smallFloor := by
    dsimp only [smallProbability, largeProbability]
    exact
      couplingParametricKCanonicalFaceTruncatedLargeProbability_le_small_add_tail
        hcoupling hle cutoff base face hfloor
  have hnonnegative : (0 : Q') ≤ largeProbability - smallProbability :=
    Q'.sub_nonneg_of_le hmono
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg hnonnegative]
  exact Q'.sub_le_of_le_add hupper

#print axioms canonicalFaceTruncationDifference_implies_remainder
#print axioms canonicalFaceTruncatedLarge_eq_small_or_difference
#print axioms couplingParametricKCanonicalFaceTruncationDifferenceProbability_le_tail
#print axioms couplingParametricKCanonicalFaceTruncatedProbability_mono_size
#print axioms couplingParametricKCanonicalFaceTruncatedLargeProbability_le_small_add_tail
#print axioms couplingParametricKCanonicalFaceTruncatedProbability_abs_sub_le_tail

end YMGap.Continuum.Z4CouplingParametricFaceTruncationComparison
