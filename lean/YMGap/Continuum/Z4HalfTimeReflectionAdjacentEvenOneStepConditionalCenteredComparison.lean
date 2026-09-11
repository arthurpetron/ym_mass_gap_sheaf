/-
# Conditional adjacent-even events converge to the mixed centered chart

This leaf composes the two independent finite errors already proved for the
one-step event: removing the corrected-slab conditioning, and transporting the
ambient marked event to its exact mixed centered recoding.  A canonical default
atom transported from the central lower cube makes the comparison total even
when the marked root list is empty.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepConditionalStability
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepVolumeComparison
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepConditionalCenteredComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepConditionalStability
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEventLaw
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepVolumeComparison
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

private theorem reassoc_cancel_adjacentEven
    (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem abs_sub_triangle_adjacentEven (a b c : Q') :
    Q'.abs (a - b) ≤ Q'.abs (a - c) + Q'.abs (c - b) := by
  have hdecompose : a - b ≈ (a - c) + (c - b) := by
    exact Q'.eqv_symm (reassoc_cancel_adjacentEven a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a - c) (c - b))

/-! ## 1. A constructive default atom independent of the marked roots -/

def adjacentEvenCentralLowerCanonicalAtom
    (radius : Nat) (hradius : 1 ≤ radius) :
    CanonicalAtom (adjacentEvenAmbient radius) :=
  ⟨transportPolymer (centralAmbient radius) (adjacentEvenAmbient radius)
      (centralLowerCubeRoot radius),
    transportPolymer_mem_canonicalSurfacePolymers
      (centralAmbient_le_adjacentEvenAmbient radius)
      (centralLowerCubeRoot_canonical hradius)⟩

def adjacentEvenStrictJointDefaultRoot
    (base stage : Nat) :
    CanonicalAtom
      (adjacentEvenAmbient (strictQueryBase (base + 1) + stage)) :=
  adjacentEvenCentralLowerCanonicalAtom _ (by
    unfold strictQueryBase uniformPaddedBase
    omega)

/-! ## 2. The explicit sum of the two finite boundary errors -/

theorem couplingPhysicalGivenSlabAdjacentEvenStrictJointPredicate_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
            (slabMarkedCylinderEvent
              (adjacentEvenStrictJointCanonicalAtoms
                (strictQueryBase (base + 1) + stage) base roots
                (Nat.le_add_right (strictQueryBase (base + 1)) stage)
                hroots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase (base + 1) + stage))
            (sourceCylinderEvent
              (adjacentEvenOneStepCenteredRoots base stage roots)
              predicate)) ≤
      couplingSlabConditionalBoundaryEpsilon
          (2 * roots.length) (stage + 4) +
        spinSummedCylinderBoundaryEpsilon
          (2 * roots.length) stage := by
  let atoms := adjacentEvenStrictJointCanonicalAtoms
    (strictQueryBase (base + 1) + stage) base roots
    (Nat.le_add_right (strictQueryBase (base + 1)) stage) hroots
  let ambientEvent := slabMarkedCylinderEvent atoms predicate
  let centeredEvent := sourceCylinderEvent
    (adjacentEvenOneStepCenteredRoots base stage roots) predicate
  let conditional := couplingParametricKPhysicalGivenSlabProbability
    coupling hcoupling cutoff
    (adjacentEvenExtent (strictQueryBase (base + 1) + stage)) ambientEvent
  let ambient := couplingKFamilyEventProbability
    coupling hcoupling cutoff
    (adjacentEvenAmbient (strictQueryBase (base + 1) + stage)) ambientEvent
  let centeredPhysical := couplingKFamilyEventProbability
    coupling hcoupling cutoff
    (centeredBoxBase (strictQueryBase (base + 1) + stage)) centeredEvent
  let centeredCompatible :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff
      (centeredBoxBase (strictQueryBase (base + 1) + stage)) centeredEvent
  let defaultRoot := adjacentEvenStrictJointDefaultRoot base stage
  have hconditionalRaw :=
    couplingPhysicalAdjacentEvenStrictJointPredicate_givenSlab_abs_sub_le
      (stage := stage) hcoupling hle cutoff hroots predicate defaultRoot
  have hconditional : Q'.abs (conditional - ambient) ≤
      couplingSlabConditionalBoundaryEpsilon
        (2 * roots.length) (stage + 4) := by
    have horiented : Q'.abs (conditional - ambient) ≤
        Q'.abs (ambient - conditional) :=
      Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          conditional ambient)
    exact Q'.le_trans' _ _ _ horiented
      (by simpa only [conditional, ambient, ambientEvent, atoms, defaultRoot]
        using hconditionalRaw)
  have hadjacent : Q'.abs (ambient - centeredPhysical) ≤
      spinSummedCylinderBoundaryEpsilon
        (2 * roots.length) stage := by
    simpa only [ambient, centeredPhysical, ambientEvent, centeredEvent, atoms]
      using
        (couplingPhysicalAdjacentEvenStrictJoint_cross_centered_abs_sub_le
          (stage := stage) hcoupling hle cutoff hroots predicate)
  have htriangle := abs_sub_triangle_adjacentEven
    conditional centeredPhysical ambient
  have hsum := Q'.add_le_add hconditional hadjacent
  have hphysical : Q'.abs (conditional - centeredPhysical) ≤
      couplingSlabConditionalBoundaryEpsilon
          (2 * roots.length) (stage + 4) +
        spinSummedCylinderBoundaryEpsilon
          (2 * roots.length) stage :=
    Q'.le_trans' _ _ _ htriangle hsum
  have hbridge : centeredPhysical ≈ centeredCompatible :=
    couplingKFamilyEventProbability_eqv_compatible
      coupling hcoupling cutoff
      (centeredBoxBase (strictQueryBase (base + 1) + stage)) centeredEvent
  have hdifference :
      conditional - centeredPhysical ≈
        conditional - centeredCompatible :=
    Q'.add_eqv_congr_left conditional
      (-centeredPhysical) (-centeredCompatible)
      (Q'.neg_eqv_congr centeredPhysical centeredCompatible hbridge)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr (Q'.eqv_symm hdifference)))
    (by simpa only [conditional, centeredCompatible, ambientEvent,
        centeredEvent, atoms] using hphysical)

theorem couplingPhysicalGivenSlabAdjacentEvenStrictJointPair_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
            (adjacentEvenStrictJointPairFamilyEvent
              (strictQueryBase (base + 1) + stage)
              base roots left right) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase (base + 1) + stage))
            (adjacentEvenOneStepCenteredPairEvent
              base stage roots left right)) ≤
      couplingSlabConditionalBoundaryEpsilon
          (2 * roots.length) (stage + 4) +
        spinSummedCylinderBoundaryEpsilon
          (2 * roots.length) stage := by
  have hbound :=
    couplingPhysicalGivenSlabAdjacentEvenStrictJointPredicate_cross_centered_abs_sub_le
      (stage := stage) hcoupling hle cutoff hroots
      (centralStrictJointPairPredicate roots.length left right)
  rw [adjacentEvenStrictJointMarkedCylinderEvent_eq
    (strictQueryBase (base + 1) + stage) base roots
    (Nat.le_add_right (strictQueryBase (base + 1)) stage)
    hroots left right] at hbound
  simpa only [adjacentEvenOneStepCenteredPairEvent] using hbound

/-! ## 3. A common constructive half-power modulus -/

theorem couplingPhysicalGivenSlabAdjacentEvenStrictJointPredicate_half_pow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
            (slabMarkedCylinderEvent
              (adjacentEvenStrictJointCanonicalAtoms
                (strictQueryBase (base + 1) + stage) base roots
                (Nat.le_add_right (strictQueryBase (base + 1)) stage)
                hroots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase (base + 1) + stage))
            (sourceCylinderEvent
              (adjacentEvenOneStepCenteredRoots base stage roots)
              predicate)) ≤
      strictJointConditionalCenteredCoefficient (2 * roots.length) *
        HalfPow.half ^ stage := by
  have hraw :=
    couplingPhysicalGivenSlabAdjacentEvenStrictJointPredicate_cross_centered_abs_sub_le
      (stage := stage) hcoupling hle cutoff hroots predicate
  have hconditionalRaw :=
    couplingSlabConditionalBoundaryEpsilon_le_coefficient_half_pow
      (2 * roots.length) (stage + 1)
  have hconditional :
      couplingSlabConditionalBoundaryEpsilon
          (2 * roots.length) (stage + 4) ≤
        spinSummedCylinderBoundaryCoefficient (2 * roots.length) *
          HalfPow.half ^ stage := by
    have hnext :
        spinSummedCylinderBoundaryCoefficient (2 * roots.length) *
            HalfPow.half ^ (stage + 1) ≤
          spinSummedCylinderBoundaryCoefficient (2 * roots.length) *
            HalfPow.half ^ stage :=
      Q'.mul_le_mul_of_nonneg_left _ _ _
        (ExpNeg.pow_half_antitone stage 1)
        (spinSummedCylinderBoundaryCoefficient_nonnegative
          (2 * roots.length))
    exact Q'.le_trans' _ _ _
      (by simpa only [show stage + 1 + 3 = stage + 4 by omega]
        using hconditionalRaw)
      hnext
  have hadjacent :=
    spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      (2 * roots.length) stage
  have hsum := Q'.add_le_add hconditional hadjacent
  have hreorder :
      spinSummedCylinderBoundaryCoefficient (2 * roots.length) *
            HalfPow.half ^ stage +
          spinSummedCylinderBoundaryCoefficient (2 * roots.length) *
            HalfPow.half ^ stage ≈
        strictJointConditionalCenteredCoefficient (2 * roots.length) *
          HalfPow.half ^ stage := by
    exact Q'.eqv_symm
      (Q'.add_mul_eqv
        (spinSummedCylinderBoundaryCoefficient (2 * roots.length))
        (spinSummedCylinderBoundaryCoefficient (2 * roots.length))
        (HalfPow.half ^ stage))
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hreorder))

theorem couplingPhysicalGivenSlabAdjacentEvenStrictJointPair_half_pow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
            (adjacentEvenStrictJointPairFamilyEvent
              (strictQueryBase (base + 1) + stage)
              base roots left right) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase (base + 1) + stage))
            (adjacentEvenOneStepCenteredPairEvent
              base stage roots left right)) ≤
      strictJointConditionalCenteredCoefficient (2 * roots.length) *
        HalfPow.half ^ stage := by
  have hbound :=
    couplingPhysicalGivenSlabAdjacentEvenStrictJointPredicate_half_pow
      (stage := stage) hcoupling hle cutoff hroots
      (centralStrictJointPairPredicate roots.length left right)
  rw [adjacentEvenStrictJointMarkedCylinderEvent_eq
    (strictQueryBase (base + 1) + stage) base roots
    (Nat.le_add_right (strictQueryBase (base + 1)) stage)
    hroots left right] at hbound
  simpa only [adjacentEvenOneStepCenteredPairEvent] using hbound

/-! ## 4. Quantitative centered swap symmetry from the exact EventLaw -/

def couplingParametricKCompatibleAdjacentEvenCenteredPairProbability
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (cutoff base stage : Nat) (roots : List (List Nat))
    (left right : List Bool) : Q' :=
  couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling cutoff
    (centeredBoxBase (strictQueryBase (base + 1) + stage))
    (adjacentEvenOneStepCenteredPairEvent base stage roots left right)

def adjacentEvenOneStepCenteredSwapCoefficient
    (rootCount : Nat) : Q' :=
  strictJointConditionalCenteredCoefficient rootCount +
    strictJointConditionalCenteredCoefficient rootCount

theorem adjacentEvenOneStepCenteredSwapCoefficient_nonnegative
    (rootCount : Nat) :
    (0 : Q') ≤ adjacentEvenOneStepCenteredSwapCoefficient rootCount := by
  unfold adjacentEvenOneStepCenteredSwapCoefficient
  exact Q'.zero_le_add _ _
    (strictJointConditionalCenteredCoefficient_nonnegative rootCount)
    (strictJointConditionalCenteredCoefficient_nonnegative rootCount)

theorem couplingParametricKCompatibleAdjacentEvenCenteredPair_swap_abs_le_half_pow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    Q'.abs
        (couplingParametricKCompatibleAdjacentEvenCenteredPairProbability
            coupling hcoupling cutoff base stage roots left right -
          couplingParametricKCompatibleAdjacentEvenCenteredPairProbability
            coupling hcoupling cutoff base stage roots right left) ≤
      adjacentEvenOneStepCenteredSwapCoefficient (2 * roots.length) *
        HalfPow.half ^ stage := by
  let conditionedLeft :=
    couplingParametricKPhysicalGivenSlabProbability
      coupling hcoupling cutoff
      (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
      (adjacentEvenStrictJointPairFamilyEvent
        (strictQueryBase (base + 1) + stage)
        base roots left right)
  let conditionedRight :=
    couplingParametricKPhysicalGivenSlabProbability
      coupling hcoupling cutoff
      (adjacentEvenExtent (strictQueryBase (base + 1) + stage))
      (adjacentEvenStrictJointPairFamilyEvent
        (strictQueryBase (base + 1) + stage)
        base roots right left)
  let centeredLeft :=
    couplingParametricKCompatibleAdjacentEvenCenteredPairProbability
      coupling hcoupling cutoff base stage roots left right
  let centeredRight :=
    couplingParametricKCompatibleAdjacentEvenCenteredPairProbability
      coupling hcoupling cutoff base stage roots right left
  let error := strictJointConditionalCenteredCoefficient
    (2 * roots.length) * HalfPow.half ^ stage
  have hleftRaw :=
    couplingPhysicalGivenSlabAdjacentEvenStrictJointPair_half_pow
      (stage := stage) hcoupling hle cutoff hroots left right
  have hleft : Q'.abs (centeredLeft - conditionedLeft) ≤ error := by
    have horiented : Q'.abs (centeredLeft - conditionedLeft) ≤
        Q'.abs (conditionedLeft - centeredLeft) :=
      Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          centeredLeft conditionedLeft)
    exact Q'.le_trans' _ _ _ horiented
      (by simpa only [conditionedLeft, centeredLeft, error,
          couplingParametricKCompatibleAdjacentEvenCenteredPairProbability]
        using hleftRaw)
  have hrightRaw :=
    couplingPhysicalGivenSlabAdjacentEvenStrictJointPair_half_pow
      (stage := stage) hcoupling hle cutoff hroots right left
  have hright : Q'.abs (conditionedRight - centeredRight) ≤ error := by
    simpa only [conditionedRight, centeredRight, error,
      couplingParametricKCompatibleAdjacentEvenCenteredPairProbability]
      using hrightRaw
  have hconditioned : conditionedLeft ≈ conditionedRight := by
    simpa only [conditionedLeft, conditionedRight] using
      (couplingParametricKPhysicalGivenSlab_adjacentEvenStrictJointPair_eqv
        coupling hcoupling cutoff
        (Nat.le_add_right (strictQueryBase (base + 1)) stage)
        hroots left right)
  have hconditionedRight :
      Q'.abs (conditionedLeft - centeredRight) ≤ error := by
    have hdifference :
        conditionedLeft - centeredRight ≈
          conditionedRight - centeredRight :=
      Q'.add_eqv_congr_right conditionedLeft conditionedRight
        (-centeredRight) hconditioned
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) hright
  have htriangle := abs_sub_triangle_adjacentEven
    centeredLeft centeredRight conditionedLeft
  have hsum := Q'.add_le_add hleft hconditionedRight
  have htwice : Q'.abs (centeredLeft - centeredRight) ≤
      error + error := Q'.le_trans' _ _ _ htriangle hsum
  have hreorder : error + error ≈
      adjacentEvenOneStepCenteredSwapCoefficient (2 * roots.length) *
        HalfPow.half ^ stage := by
    dsimp only [error]
    exact Q'.eqv_symm
      (Q'.add_mul_eqv
        (strictJointConditionalCenteredCoefficient (2 * roots.length))
        (strictJointConditionalCenteredCoefficient (2 * roots.length))
        (HalfPow.half ^ stage))
  exact Q'.le_trans' _ _ _ htwice (Q'.le_of_eqv hreorder)

#print axioms adjacentEvenCentralLowerCanonicalAtom
#print axioms adjacentEvenStrictJointDefaultRoot
#print axioms couplingPhysicalGivenSlabAdjacentEvenStrictJointPredicate_cross_centered_abs_sub_le
#print axioms couplingPhysicalGivenSlabAdjacentEvenStrictJointPair_cross_centered_abs_sub_le
#print axioms couplingPhysicalGivenSlabAdjacentEvenStrictJointPredicate_half_pow
#print axioms couplingPhysicalGivenSlabAdjacentEvenStrictJointPair_half_pow
#print axioms adjacentEvenOneStepCenteredSwapCoefficient_nonnegative
#print axioms couplingParametricKCompatibleAdjacentEvenCenteredPair_swap_abs_le_half_pow

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepConditionalCenteredComparison
