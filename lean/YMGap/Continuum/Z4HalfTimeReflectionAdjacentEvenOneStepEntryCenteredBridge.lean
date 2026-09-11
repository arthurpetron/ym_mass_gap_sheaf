/-
# Corrected-slab bridge for the adjacent-even one-step entry

The direct one-step reflection entry is evaluated in the existing odd
corrected slab.  Its ordinary joint chart consists of the canonically
transported lower roots and the one-step translated upper roots.  Projecting
the associated four-block centered chart selects exactly that entry.

This file deliberately uses the generic odd-slab-to-centered comparison.
The adjacent-even finite carrier enters only through the separately proved
swap theorem for the resulting centered limit; no false equality of the odd
and even finite carriers is asserted here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepLimitSymmetry
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEntryCenteredBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalCylinderCofinal
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepLimitSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabFiniteKConditionalLaw
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBipairConditional
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSEntryEvent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSFiniteEntries
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointCenteredBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4HalfTimeReflectionUpperSupportLocalQuery
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The selected cylinder in the ordinary odd carrier -/

/-- The lower transported and upper one-step translated query roots at a
common reflection radius. -/
def adjacentEvenOneStepCommonCylinderRoots
    (radius base : Nat) (roots : List (List Nat)) : List (List Nat) :=
  centralStrictLowerCylinderRoots radius (base + 1)
      (transportedCylinderRoots base (base + 1) roots) ++
    centralStrictUpperCylinderRoots radius (base + 1)
      (roots.map (timeShiftCanonicalRoot 1 base))

/-- The first/fourth projection of the ordinary joint chart is literally the
selected lower-transported/upper-translated cylinder at every radius. -/
theorem adjacentEvenOneStepProjectedJointEvent_eq_common
    (radius base : Nat) (roots : List (List Nat))
    (left right : List Bool) :
    sourceCylinderEvent
        (centralStrictJointCylinderRoots radius (base + 1)
          (adjacentEvenOneStepProjectedRoots base roots))
        (orientedDoubledTimeJointPredicate
          roots.length roots.length left right) =
      sourceCylinderEvent
        (adjacentEvenOneStepCommonCylinderRoots radius base roots)
        (centralStrictJointPairPredicate roots.length left right) := by
  unfold centralStrictJointCylinderRoots
    centralStrictLowerCylinderRoots centralStrictUpperCylinderRoots
    adjacentEvenOneStepProjectedRoots
    adjacentEvenOneStepCommonCylinderRoots
  simp only [List.map_append]
  apply orientedProjectedFourBlockCylinderEvent_eq
  · simp only [transportedCylinderRoots, List.length_map]
  · simp only [List.length_map]
  · simp only [transportedCylinderRoots, List.length_map]

/-! ## 2. The direct normalized support entry -/

/-- The normalized support bipair entry for transported lower roots and
one-step translated upper roots in the existing odd corrected slab. -/
def adjacentEvenOneStepEntrySequence
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (base : Nat) (roots : List (List Nat))
    (left right : List Bool) (stage : Nat) : Q' :=
  let outer := base + 1
  let radius := strictQueryBase outer + stage
  centralNormalizedSupportBipairLaw coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage) radius
    (centralStrictLocalQueryCode radius outer
      (transportedCylinderRoots base outer roots))
    (centralStrictLocalQueryCode radius outer
      (roots.map (timeShiftCanonicalRoot 1 base)))
    left right

/-- The support bipair is exactly the corrected-slab probability of the
selected cylinder.  This is a rational equivalence, not a claim identifying
the odd corrected slab with the adjacent-even slab. -/
theorem adjacentEvenOneStepEntrySequence_eqv_cylinder
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) (stage : Nat) :
    adjacentEvenOneStepEntrySequence
        coupling hcoupling base roots left right stage ≈
      couplingParametricKPhysicalGivenSlabProbability
        coupling hcoupling
        (centralStrictJointCenteredStageCutoff (base + 1) stage)
        (centralExtent (strictQueryBase (base + 1) + stage))
        (sourceCylinderEvent
          (adjacentEvenOneStepCommonCylinderRoots
            (strictQueryBase (base + 1) + stage) base roots)
          (centralStrictJointPairPredicate roots.length left right)) := by
  let outer := base + 1
  let radius := strictQueryBase outer + stage
  have hbase : strictQueryBase outer ≤ radius :=
    Nat.le_add_right (strictQueryBase outer) stage
  have htransported : ∀ root,
      root ∈ transportedCylinderRoots base outer roots →
        root ∈ canonicalSurfacePolymers outer :=
    transportedCylinderRoots_canonical
      (Nat.le_add_right base 1) hroots
  have htranslated : ∀ root,
      root ∈ roots.map (timeShiftCanonicalRoot 1 base) →
        root ∈ canonicalSurfacePolymers outer := by
    intro root hroot
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hroot
    exact timeShiftCanonicalRoot_canonical (hroots source hsource)
  have hentry := centralNormalizedSupportBipairLaw_eq_physicalGivenSlab
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage) radius
    (centralStrictLocalQueryCode radius outer
      (transportedCylinderRoots base outer roots))
    (centralStrictLocalQueryCode radius outer
      (roots.map (timeShiftCanonicalRoot 1 base)))
    left right
  have hevent := couplingPhysicalGivenSlab_strictBipair_eq_cylinder
    coupling hcoupling
    (centralStrictJointCenteredStageCutoff outer stage)
    hbase hbase htransported htranslated left right
  rw [hevent] at hentry
  simpa only [adjacentEvenOneStepEntrySequence,
    adjacentEvenOneStepCommonCylinderRoots, transportedCylinderRoots,
    List.length_map, outer, radius] using hentry

/-! ## 3. Quantitative descent to the centered pair sequence -/

/-- Every direct one-step odd-carrier entry approaches the projected
centered pair sequence with the already derived half-power modulus. -/
theorem adjacentEvenOneStepEntrySequence_abs_sub_centeredPair_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) (stage : Nat) :
    Q'.abs
        (adjacentEvenOneStepEntrySequence
            coupling hcoupling base roots left right stage -
          couplingParametricAdjacentEvenOneStepCenteredPairSequence
            coupling hcoupling base roots left right stage) ≤
      strictJointConditionalCenteredCoefficient
          ((adjacentEvenOneStepProjectedRoots base roots).length +
            (adjacentEvenOneStepProjectedRoots base roots).length) *
        HalfPow.half ^ stage := by
  let outer := base + 1
  let radius := strictQueryBase outer + stage
  let projectedRoots := adjacentEvenOneStepProjectedRoots base roots
  let predicate := orientedDoubledTimeJointPredicate
    roots.length roots.length left right
  have hcanonical := adjacentEvenOneStepProjectedRoots_canonical hroots
  have hentry := adjacentEvenOneStepEntrySequence_eqv_cylinder
    hcoupling hroots left right stage
  have hevent := adjacentEvenOneStepProjectedJointEvent_eq_common
    radius base roots left right
  have hmarked :
      slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms radius outer projectedRoots
            (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
          predicate =
        sourceCylinderEvent
          (centralStrictJointCylinderRoots radius outer projectedRoots)
          predicate := by
    funext family
    unfold slabMarkedCylinderEvent sourceCylinderEvent
    exact congrArg
      (fun markedRoots => cylinderEvent markedRoots predicate family)
      (centralStrictJointCanonicalAtoms_values
        radius outer projectedRoots
        (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
  have hraw :=
    couplingPhysicalGivenSlabStrictJointPredicate_to_centeredSequence_half_pow
      hcoupling hle hcanonical predicate (stage := stage)
  dsimp only at hraw
  have heventMarked :
      slabMarkedCylinderEvent
          (centralStrictJointCanonicalAtoms radius outer projectedRoots
            (Nat.le_add_right (strictQueryBase outer) stage) hcanonical)
          predicate =
        sourceCylinderEvent
          (adjacentEvenOneStepCommonCylinderRoots radius base roots)
          (centralStrictJointPairPredicate roots.length left right) :=
    hmarked.trans hevent
  rw [heventMarked] at hraw
  have hdifference :
      adjacentEvenOneStepEntrySequence
            coupling hcoupling base roots left right stage -
          couplingParametricAdjacentEvenOneStepCenteredPairSequence
            coupling hcoupling base roots left right stage ≈
        couplingParametricKPhysicalGivenSlabProbability
            coupling hcoupling
            (centralStrictJointCenteredStageCutoff outer stage)
            (centralExtent radius)
            (sourceCylinderEvent
              (adjacentEvenOneStepCommonCylinderRoots radius base roots)
              (centralStrictJointPairPredicate roots.length left right)) -
          couplingParametricStrictJointCenteredSequence
            coupling hcoupling outer projectedRoots predicate stage :=
    Q'.add_eqv_congr_right _ _ _ hentry
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
    (by simpa only [outer, radius, projectedRoots, predicate,
        couplingParametricAdjacentEvenOneStepCenteredPairSequence]
      using hraw)

#print axioms adjacentEvenOneStepProjectedJointEvent_eq_common
#print axioms adjacentEvenOneStepEntrySequence_eqv_cylinder
#print axioms adjacentEvenOneStepEntrySequence_abs_sub_centeredPair_le

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepEntryCenteredBridge
