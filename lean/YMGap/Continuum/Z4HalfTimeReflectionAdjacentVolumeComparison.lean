/-
# Adjacent odd/even comparison for the fixed local face-query chart

The centered stage box has odd side `2r+1`; the half-time ambient box has
the adjacent even side `2r+2`.  This file proves that the same fixed finite
root cylinder has the standard cross-volume boundary modulus across that
single box increment.  The protected origin-box distance is nevertheless
`stage+1`, because the roots recede from the outer boundary as the centered
stage grows.
-/

import YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
import YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalCylinderStability
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCrossVolumeStability
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricTargetCylinderStability
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalFaceQueryChart
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4SignedCenteredFixedObservableRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingDiagonal
open YMGap.Continuum.Z4SpinSummedTargetCylinderStability
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The growing protected origin box -/

def centeredFaceQueryInner (base stage : Nat) : Nat :=
  base + stage + base

theorem centeredFaceQueryInner_add_distance
    (base stage : Nat) :
    centeredFaceQueryInner base stage + (stage + 1) =
      centeredRecedingStageBase base stage := by
  unfold centeredFaceQueryInner centeredRecedingStageBase
    centeredRecedingStageRadius centeredBoxBase
  omega

theorem centeredOffsetCanonicalRoot_inside_originBox
    {base stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    PolymerInsideBox (centeredFaceQueryInner base stage)
      (centeredRecedingStageBase base stage)
      (centeredOffsetCanonicalRoot (base + stage) base root) := by
  intro plaquette hplaquette
  have hsupport := centeredOffsetCanonicalRoot_sameSupport
    (Nat.le_add_right base stage) hroot
  have hshifted := hsupport.1 plaquette hplaquette
  obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hshifted
  have hsourceBox := geometricPolymer_subset_box
    (canonicalSurfacePolymer_mem_faceSupports hroot) source hsource
  have hcoordinates := (mem_boxPlaquettes source base).1 hsourceBox
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
  change a < base ∧ b < base ∧ c < base ∧ d < base at hcoordinates
  rw [← hsourceEq]
  apply (mem_boxPlaquettes _ _).2
  simp only [uniformShiftPlaquette, uniformShiftVertex,
    centeredFaceQueryInner]
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem centeredRecedingStageRoots_inside_originBox
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target, target ∈ centeredRecedingStageRoots base stage roots →
      PolymerInsideBox (centeredFaceQueryInner base stage)
        (centeredRecedingStageBase base stage) target := by
  intro target htarget
  unfold centeredRecedingStageRoots centeredRecedingStageRadius
    centeredOffsetCylinderRoots at htarget
  obtain ⟨source, hsource, htargetEq⟩ := List.mem_map.mp htarget
  rw [← htargetEq]
  exact centeredOffsetCanonicalRoot_inside_originBox
    (hroots source hsource)

theorem centeredStageBase_le_centralAmbient (base stage : Nat) :
    centeredRecedingStageBase base stage ≤
      centralAmbient (base + stage) := by
  unfold centeredRecedingStageBase centeredRecedingStageRadius
  rw [centralAmbient_eq_centeredBoxBase_add_one]
  omega

/-! ## 2. Equality of the direct even chart and generic transported event -/

theorem centralFaceQuerySlabEvent_eq_transportedCenteredEvent
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    let hsmall := centeredStageBase_le_centralAmbient base stage
    let hstageRoots := centeredRecedingStageRoots_canonical hroots
    slabMarkedCylinderEvent
        (centralFaceQueryCanonicalAtoms
          (base + stage) base roots (Nat.le_add_right base stage) hroots)
        predicate =
      markedCylinderEvent
        (transportedCanonicalCylinderAtoms hsmall
          (centeredRecedingStageRoots base stage roots) hstageRoots)
        predicate := by
  dsimp only
  unfold slabMarkedCylinderEvent markedCylinderEvent
  apply congrArg (fun rawRoots => cylinderEvent rawRoots predicate)
  calc
    (centralFaceQueryCanonicalAtoms
        (base + stage) base roots (Nat.le_add_right base stage)
          hroots).map Subtype.val =
        centralFaceQueryCylinderRoots (base + stage) base roots :=
      centralFaceQueryCanonicalAtoms_values
        (base + stage) base roots (Nat.le_add_right base stage) hroots
    _ = transportedCylinderRoots
          (centeredRecedingStageBase base stage)
          (centralAmbient (base + stage))
          (centeredRecedingStageRoots base stage roots) :=
      centralFaceQueryCylinderRoots_eq_transported_centered hroots
    _ = (transportedCanonicalCylinderAtoms
          (centeredStageBase_le_centralAmbient base stage)
          (centeredRecedingStageRoots base stage roots)
          (centeredRecedingStageRoots_canonical hroots)).map
            Subtype.val :=
      (transportedCanonicalCylinderAtoms_values
        (centeredStageBase_le_centralAmbient base stage)
        (centeredRecedingStageRoots base stage roots)
        (centeredRecedingStageRoots_canonical hroots)).symm

/-! ## 3. Adjacent compatible and literal physical laws -/

theorem couplingParametricKCompatibleCentralFaceQuery_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (centralAmbient (base + stage))
            (slabMarkedCylinderEvent
              (centralFaceQueryCanonicalAtoms
                (base + stage) base roots
                (Nat.le_add_right base stage) hroots)
              predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff
            (centeredRecedingStageBase base stage)
            (centeredRecedingCylinderEvent
              base stage roots predicate)) ≤
      spinSummedCylinderBoundaryEpsilon roots.length (stage + 1) := by
  let hsmall := centeredStageBase_le_centralAmbient base stage
  let stageRoots := centeredRecedingStageRoots base stage roots
  let hstageRoots : ∀ root, root ∈ stageRoots →
      root ∈ canonicalSurfacePolymers
        (centeredRecedingStageBase base stage) :=
    centeredRecedingStageRoots_canonical hroots
  have hbound :=
    couplingParametricKCompatibleCylinderProbability_cross_volume_abs_sub_le
      hcoupling hle cutoff hsmall stageRoots hstageRoots predicate
      (centeredRecedingStageRoots_inside_originBox hroots)
      (centeredFaceQueryInner_add_distance base stage)
  have hevent := centralFaceQuerySlabEvent_eq_transportedCenteredEvent
    (base := base) (stage := stage) (roots := roots) hroots predicate
  have hlength : stageRoots.length = roots.length := by
    simpa only [stageRoots] using
      (centeredRecedingStageRoots_length base stage roots)
  rw [← hevent] at hbound
  simpa only [stageRoots, sourceCylinderEvent,
    centeredRecedingCylinderEvent, hlength] using hbound

theorem couplingPhysicalAdjacentDifference_eqv_compatible
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {large small : Nat}
    (largeEvent smallEvent : List (List Nat) → Bool) :
    couplingKFamilyEventProbability coupling hcoupling cutoff large
          largeEvent -
        couplingKFamilyEventProbability coupling hcoupling cutoff small
          smallEvent ≈
      couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff large largeEvent -
        couplingParametricKCompatibleSupportEventProbability
          coupling hcoupling cutoff small smallEvent :=
  Q'.add_eqv_congr'
    (couplingKFamilyEventProbability_eqv_compatible
      coupling hcoupling cutoff large largeEvent)
    (Q'.neg_eqv_congr _ _
      (couplingKFamilyEventProbability_eqv_compatible
        coupling hcoupling cutoff small smallEvent))

theorem couplingPhysicalCentralFaceQuery_cross_centered_abs_sub_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingKFamilyEventProbability coupling hcoupling cutoff
            (centralAmbient (base + stage))
            (slabMarkedCylinderEvent
              (centralFaceQueryCanonicalAtoms
                (base + stage) base roots
                (Nat.le_add_right base stage) hroots)
              predicate) -
          couplingKFamilyEventProbability coupling hcoupling cutoff
            (centeredRecedingStageBase base stage)
            (centeredRecedingCylinderEvent
              base stage roots predicate)) ≤
      spinSummedCylinderBoundaryEpsilon roots.length (stage + 1) := by
  let largeEvent := slabMarkedCylinderEvent
    (centralFaceQueryCanonicalAtoms
      (base + stage) base roots (Nat.le_add_right base stage) hroots)
    predicate
  let smallEvent := centeredRecedingCylinderEvent
    base stage roots predicate
  have hbridge := couplingPhysicalAdjacentDifference_eqv_compatible
    (large := centralAmbient (base + stage))
    (small := centeredRecedingStageBase base stage)
    hcoupling cutoff largeEvent smallEvent
  have hcompatible :=
    couplingParametricKCompatibleCentralFaceQuery_cross_centered_abs_sub_le
      (base := base) (stage := stage) (roots := roots)
      hcoupling hle cutoff hroots predicate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hbridge))
    (by simpa only [largeEvent, smallEvent] using hcompatible)

#print axioms centeredOffsetCanonicalRoot_inside_originBox
#print axioms centeredRecedingStageRoots_inside_originBox
#print axioms centralFaceQuerySlabEvent_eq_transportedCenteredEvent
#print axioms couplingParametricKCompatibleCentralFaceQuery_cross_centered_abs_sub_le
#print axioms couplingPhysicalAdjacentDifference_eqv_compatible
#print axioms couplingPhysicalCentralFaceQuery_cross_centered_abs_sub_le

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentVolumeComparison
