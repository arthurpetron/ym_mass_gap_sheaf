/-
# Corrected-slab descent for the projected mixed joint event

The strict-joint carrier geometry never used the special pair predicate.
This file exposes that fact once for an arbitrary Boolean predicate, composes
it with the existing adjacent odd/even comparison, and specializes the result
to the projected four-block event of the doubled-time mixed OS entry.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointRecoding
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStability
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalStabilityGeneral
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSEntryEvent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SpinSummedCylinderCofinal
open YMGap.Continuum.Z4SpinSummedCylinderJointCofinal
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

private theorem reassoc_cancel_local (u middle residual : Q') :
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

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a - b) ≤ Q'.abs (a - c) + Q'.abs (c - b) := by
  have hdecompose : a - b ≈ (a - c) + (c - b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a - c) (c - b))

/-- The corrected-slab carrier bound for a strict joint chart is uniform in
the Boolean predicate. -/
theorem couplingPhysicalStrictJointPredicate_givenSlab_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool)
    (defaultRoot : CanonicalAtom
      (centralAmbient (strictQueryBase base + stage))) :
    let atoms := centralStrictJointCanonicalAtoms
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (centralAmbient (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (centralExtent (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate)) ≤
      couplingSlabConditionalBoundaryEpsilon
        (roots.length + roots.length) (stage + 3) := by
  dsimp only
  let atoms := centralStrictJointCanonicalAtoms
    (strictQueryBase base + stage) base roots
    (Nat.le_add_right (strictQueryBase base) stage) hroots
  have hsupported : ∀ atom, atom ∈ atoms →
      canonicalPolymerSlabSupportedB
        (centralExtent (strictQueryBase base + stage)) atom.val = true := by
    simpa only [atoms] using
      (centralStrictJointCanonicalAtoms_supported
        (strictQueryBase base + stage) base roots
        (Nat.le_add_right (strictQueryBase base) stage) hroots)
  have hfloorPredicate :
      ∀ entry : SlabConnectedSourceEntry
          (centralExtent (strictQueryBase base + stage)) atoms predicate,
        stage + 3 ≤
          (slabConnectedCarrierSupport defaultRoot entry).length := by
    intro entry
    simpa only [atoms] using
      (centralStrictJointConnectedCarrierSupport_floor
        hroots defaultRoot entry)
  have hfloorComplement :
      ∀ entry : SlabConnectedSourceEntry
          (centralExtent (strictQueryBase base + stage)) atoms
            (complementSlabPredicate predicate),
        stage + 3 ≤
          (slabConnectedCarrierSupport defaultRoot entry).length := by
    intro entry
    simpa only [atoms] using
      (centralStrictJointConnectedCarrierSupport_floor
        hroots defaultRoot entry)
  have hbound :=
    couplingPhysicalAmbient_givenSlabProbability_abs_sub_le_of_floors
      (extent := centralExtent (strictQueryBase base + stage))
      (roots := atoms) hcoupling hle cutoff predicate defaultRoot
      hsupported (stage + 3) hfloorPredicate hfloorComplement
  have hlength : atoms.length = roots.length + roots.length := by
    simpa only [atoms] using
      (centralStrictJointCanonicalAtoms_length
        (strictQueryBase base + stage) base roots
        (Nat.le_add_right (strictQueryBase base) stage) hroots)
  have hboundRoots := hlength ▸ hbound
  simpa only [atoms, centralAmbient] using hboundRoots

/-- A generic strict-joint corrected-slab event approaches its centered
compatible event with the same two boundary tails as the pair specialization.
-/
theorem couplingPhysicalGivenSlabStrictJointPredicate_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let atoms := centralStrictJointCanonicalAtoms
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (centralExtent (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredBoxBase (strictQueryBase base + stage))
            (centralStrictJointCenteredCylinderEvent
              base stage roots predicate)) ≤
      couplingSlabConditionalBoundaryEpsilon
          (roots.length + roots.length) (stage + 3) +
        spinSummedCylinderBoundaryEpsilon
          (roots.length + roots.length) stage := by
  dsimp only
  let atoms := centralStrictJointCanonicalAtoms
    (strictQueryBase base + stage) base roots
    (Nat.le_add_right (strictQueryBase base) stage) hroots
  let ambientEvent := slabMarkedCylinderEvent atoms predicate
  let centeredEvent := centralStrictJointCenteredCylinderEvent
    base stage roots predicate
  let conditional := couplingParametricKPhysicalGivenSlabProbability
    coupling hcoupling cutoff
    (centralExtent (strictQueryBase base + stage)) ambientEvent
  let ambient := couplingKFamilyEventProbability
    coupling hcoupling cutoff
    (centralAmbient (strictQueryBase base + stage)) ambientEvent
  let centeredPhysical := couplingKFamilyEventProbability
    coupling hcoupling cutoff
    (centeredBoxBase (strictQueryBase base + stage)) centeredEvent
  let centeredCompatible :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff
      (centeredBoxBase (strictQueryBase base + stage)) centeredEvent
  have hradius : 1 ≤ strictQueryBase base + stage := by
    unfold strictQueryBase uniformPaddedBase
    omega
  let defaultRoot : CanonicalAtom
      (centralAmbient (strictQueryBase base + stage)) :=
    centralLowerCanonicalAtom
      (strictQueryBase base + stage) hradius
  have hconditionalRaw :=
    couplingPhysicalStrictJointPredicate_givenSlab_abs_sub_le
      hcoupling hle cutoff hroots predicate defaultRoot
  have hconditional : Q'.abs (conditional - ambient) ≤
      couplingSlabConditionalBoundaryEpsilon
        (roots.length + roots.length) (stage + 3) := by
    have horiented : Q'.abs (conditional - ambient) ≤
        Q'.abs (ambient - conditional) :=
      Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          conditional ambient)
    exact Q'.le_trans' _ _ _ horiented
      (by simpa only [conditional, ambient, ambientEvent, atoms]
        using hconditionalRaw)
  have hadjacent : Q'.abs (ambient - centeredPhysical) ≤
      spinSummedCylinderBoundaryEpsilon
        (roots.length + roots.length) stage := by
    simpa only [ambient, centeredPhysical, ambientEvent, centeredEvent,
      atoms, centralStrictJointCenteredCylinderEvent] using
      (couplingPhysicalStrictJoint_cross_centered_abs_sub_le
        (stage := stage) hcoupling hle cutoff hroots predicate)
  have htriangle := abs_sub_triangle_local
    conditional centeredPhysical ambient
  have hsum := Q'.add_le_add hconditional hadjacent
  have hphysical : Q'.abs (conditional - centeredPhysical) ≤
      couplingSlabConditionalBoundaryEpsilon
          (roots.length + roots.length) (stage + 3) +
        spinSummedCylinderBoundaryEpsilon
          (roots.length + roots.length) stage :=
    Q'.le_trans' _ _ _ htriangle hsum
  have hbridge : centeredPhysical ≈ centeredCompatible :=
    couplingKFamilyEventProbability_eqv_compatible
      coupling hcoupling cutoff
      (centeredBoxBase (strictQueryBase base + stage)) centeredEvent
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

/-- Half-power form of the generic predicate bridge. -/
theorem couplingPhysicalGivenSlabStrictJointPredicate_to_centeredSequence_half_pow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let cutoff := centralStrictJointCenteredStageCutoff base stage
    let atoms := centralStrictJointCanonicalAtoms
      (strictQueryBase base + stage) base roots
      (Nat.le_add_right (strictQueryBase base) stage) hroots
    Q'.abs
        (couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling cutoff
            (centralExtent (strictQueryBase base + stage))
            (slabMarkedCylinderEvent atoms predicate) -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots predicate stage) ≤
      strictJointConditionalCenteredCoefficient
          (roots.length + roots.length) * HalfPow.half ^ stage := by
  dsimp only
  have hraw :=
    couplingPhysicalGivenSlabStrictJointPredicate_cross_centered_abs_sub_le
      hcoupling hle
      (centralStrictJointCenteredStageCutoff base stage)
      hroots predicate (stage := stage)
  dsimp only at hraw
  have hconditional :=
    couplingSlabConditionalBoundaryEpsilon_le_coefficient_half_pow
      (roots.length + roots.length) stage
  have hadjacent :=
    spinSummedCylinderBoundaryEpsilon_le_coefficient_half_pow
      (roots.length + roots.length) stage
  have hsum := Q'.add_le_add hconditional hadjacent
  have hreorder :
      spinSummedCylinderBoundaryCoefficient
            (roots.length + roots.length) * HalfPow.half ^ stage +
          spinSummedCylinderBoundaryCoefficient
            (roots.length + roots.length) * HalfPow.half ^ stage ≈
        strictJointConditionalCenteredCoefficient
            (roots.length + roots.length) * HalfPow.half ^ stage := by
    exact Q'.eqv_symm
      (Q'.add_mul_eqv
        (spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length))
        (spinSummedCylinderBoundaryCoefficient
          (roots.length + roots.length))
        (HalfPow.half ^ stage))
  exact Q'.le_trans' _ _ _
    (by simpa only [couplingParametricStrictJointCenteredSequence]
      using hraw)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hreorder))

/-- Each oriented mixed OS entry approaches the centered limit of the
projected ordinary joint chart with an explicit derived half-power modulus.
-/
theorem strictJointDoubledTimeMixedOSOrientedEntrySequence_abs_sub_jointCentered_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base)
    (left right : List Bool) (stage : Nat) :
    Q'.abs
        (strictJointDoubledTimeMixedOSOrientedEntrySequence
            coupling hcoupling shift vector left right stage -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling (base + (shift + shift))
            (strictJointDoubledTimeMixedJointRoots shift vector)
            (strictJointDoubledTimeMixedJointPredicate
              vector.roots.length left right) stage) ≤
      strictJointConditionalCenteredCoefficient
          ((strictJointDoubledTimeMixedJointRoots shift vector).length +
            (strictJointDoubledTimeMixedJointRoots shift vector).length) *
        HalfPow.half ^ stage := by
  let outer := base + (shift + shift)
  let radius := strictQueryBase outer + stage
  let roots := strictJointDoubledTimeMixedJointRoots shift vector
  let predicate := strictJointDoubledTimeMixedJointPredicate
    vector.roots.length left right
  have hcanonical := strictJointDoubledTimeMixedJointRoots_canonical
    shift vector
  have hentry :=
    strictJointDoubledTimeMixedOSOrientedEntrySequence_eqv_cylinder
      hcoupling shift vector left right stage
  have hevent := strictJointDoubledTimeMixedJointEvent_eq_common
    shift radius vector left right
  have hmarked :
      slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms radius outer roots
            (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
          predicate =
        sourceCylinderEvent
          (centralStrictJointCylinderRoots radius outer roots)
          predicate := by
    funext family
    unfold slabMarkedCylinderEvent sourceCylinderEvent
    exact congrArg (fun markedRoots => cylinderEvent markedRoots predicate family)
      (centralStrictJointCanonicalAtoms_values radius outer roots
        (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
  have hraw :=
    couplingPhysicalGivenSlabStrictJointPredicate_to_centeredSequence_half_pow
      hcoupling hle hcanonical predicate (stage := stage)
  dsimp only at hraw
  have heventMarked :
      slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms radius outer roots
            (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
          predicate =
        sourceCylinderEvent
          (strictJointDoubledTimeCommonCylinderRoots radius shift vector)
          (centralStrictJointPairPredicate
            vector.roots.length left right) := by
    exact hmarked.trans hevent
  rw [heventMarked] at hraw
  have hdifference :
      strictJointDoubledTimeMixedOSOrientedEntrySequence
            coupling hcoupling shift vector left right stage -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling outer roots predicate stage ≈
        couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling
            (centralStrictJointCenteredStageCutoff outer stage)
            (centralExtent radius)
            (sourceCylinderEvent
              (strictJointDoubledTimeCommonCylinderRoots
                radius shift vector)
              (centralStrictJointPairPredicate
                vector.roots.length left right)) -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling outer roots predicate stage :=
    Q'.add_eqv_congr_right _ _ _ hentry
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (by simpa only [outer, radius, roots, predicate] using hraw)

#print axioms couplingPhysicalStrictJointPredicate_givenSlab_abs_sub_le
#print axioms couplingPhysicalGivenSlabStrictJointPredicate_cross_centered_abs_sub_le
#print axioms couplingPhysicalGivenSlabStrictJointPredicate_to_centeredSequence_half_pow
#print axioms strictJointDoubledTimeMixedOSOrientedEntrySequence_abs_sub_jointCentered_le

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge
