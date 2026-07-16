/-
# Cofinal base transport for the strict reflected cylinder chart

The common-box source in the doubled-time Young inequality is a canonical
renaming of the original local cylinder.  This file starts the required
cofinal identification constructively.  It proves exact lower-query and
aligned centered-root transport, then compares the two aligned centered
probability schedules through their explicit common cutoff.

No translation invariance, contraction, or continuum reconstruction is
asserted here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSYoung
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationScheduleAlignment

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSJointFixedStageRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationScheduleAlignment
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

private theorem sameSupport_map_local
    {left right : List Z4Plaq} (reindex : Z4Plaq → Z4Plaq)
    (hsupport : sameSupport (L := z4Chain.toLattice) left right) :
    sameSupport (L := z4Chain.toLattice)
      (left.map reindex) (right.map reindex) := by
  constructor
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.1 source hsource, rfl⟩
  · intro plaquette hplaquette
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
    exact List.mem_map.mpr
      ⟨source, hsupport.2 source hsource, rfl⟩

/-! ## 1. Exact source-name transport -/

/-- The unreflected strict upper query, like the lower query, depends only on
the geometric source support and not on its finite-box numerical name. -/
theorem centralStrictUpperCanonicalRoot_transportBase_eq
    {base outer radius : Nat} (hbase : base ≤ outer)
    (houter : strictQueryBase outer ≤ radius)
    {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictUpperCanonicalRoot radius outer
        (transportPolymer base outer root) =
      centralStrictUpperCanonicalRoot radius base root := by
  have hbaseRadius : strictQueryBase base ≤ radius := by
    unfold strictQueryBase uniformPaddedBase at houter ⊢
    omega
  have htransported : transportPolymer base outer root ∈
      canonicalSurfacePolymers outer :=
    transportPolymer_mem_canonicalSurfacePolymers hbase hroot
  have hleft := centralStrictUpperCanonicalRoot_canonical
    houter htransported
  have hright := centralStrictUpperCanonicalRoot_canonical
    hbaseRadius hroot
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport hleft hright
  have hleftRaw := centralStrictUpperCanonicalRoot_raw_sameSupport_local
    houter htransported
  have hrightRaw := centralStrictUpperCanonicalRoot_raw_sameSupport_local
    hbaseRadius hroot
  have htransport := transportPolymer_sameSupport hbase
    (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hmapped := sameSupport_map_local
    (strictJointRawUpperQueryPlaquette radius) htransport
  exact sameSupport_trans hleftRaw
    (sameSupport_trans (sameSupport_symm hmapped)
      (sameSupport_symm hrightRaw))

/-- Exact transport of the entire lower-root list at a common query radius. -/
theorem centralStrictLowerCylinderRoots_transportBase_eq
    {base outer radius : Nat} (hbase : base ≤ outer)
    (houter : strictQueryBase outer ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCylinderRoots radius outer
        (transportedCylinderRoots base outer roots) =
      centralStrictLowerCylinderRoots radius base roots := by
  unfold centralStrictLowerCylinderRoots transportedCylinderRoots
  rw [List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact centralStrictLowerCanonicalRoot_transportBase_eq
    hbase houter (hroots root hroot)

/-- The complete lower-support fingerprint is literally unchanged by a
canonical source-box transport at any common admissible radius. -/
theorem centralStrictLocalQueryCode_transportBase_eq
    {base outer radius : Nat} (hbase : base ≤ outer)
    (houter : strictQueryBase outer ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centralStrictLocalQueryCode radius outer
        (transportedCylinderRoots base outer roots) =
      centralStrictLocalQueryCode radius base roots := by
  unfold centralStrictLocalQueryCode
  rw [centralStrictLowerCylinderRoots_transportBase_eq
    hbase houter hroots]

/-! ## 2. Aligned centered roots -/

theorem centralStrictLowerCenteredStageRoot_transportBase_aligned
    {base padding stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictLowerCenteredStageRoot
        (base + padding) stage
        (transportPolymer base (base + padding) root) =
      centralStrictLowerCenteredStageRoot
        base (stage + padding) root := by
  let outer := base + padding
  have hbaseOuter : base ≤ outer := by
    dsimp only [outer]
    omega
  have htransported : transportPolymer base outer root ∈
      canonicalSurfacePolymers outer :=
    transportPolymer_mem_canonicalSurfacePolymers hbaseOuter hroot
  have hradius : strictQueryBase outer + stage =
      strictQueryBase base + (stage + padding) := by
    dsimp only [outer]
    exact strictJointTimeTranslation_scheduleRadius_eq base padding stage
  have hleftCanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage)
    (centralStrictLowerCenteredSourceRoot_canonical htransported)
  rw [strictJointCenteredStageBase_eq, hradius] at hleftCanonical
  have hrightCanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage + padding)
    (centralStrictLowerCenteredSourceRoot_canonical hroot)
  rw [strictJointCenteredStageBase_eq] at hrightCanonical
  have hle := strictJointCenteredStageBase_le_centralAmbient
    base (stage + padding)
  apply transportPolymer_injective_on_canonical hle
    hleftCanonical hrightCanonical
  have hleftTransport :=
    centralStrictLowerCanonicalRoot_eq_transport_centeredStage
      (base := outer) (stage := stage) htransported
  rw [hradius] at hleftTransport
  have hrightTransport :=
    centralStrictLowerCanonicalRoot_eq_transport_centeredStage
      (base := base) (stage := stage + padding) hroot
  have hcorner := centralStrictLowerCanonicalRoot_transportBase_eq
    hbaseOuter
    (Nat.le_add_right (strictQueryBase outer) stage)
    hroot
  rw [hradius] at hcorner
  exact Eq.trans hleftTransport.symm
    (Eq.trans hcorner hrightTransport)

theorem centralStrictUpperCenteredStageRoot_transportBase_aligned
    {base padding stage : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers base) :
    centralStrictUpperCenteredStageRoot
        (base + padding) stage
        (transportPolymer base (base + padding) root) =
      centralStrictUpperCenteredStageRoot
        base (stage + padding) root := by
  let outer := base + padding
  have hbaseOuter : base ≤ outer := by
    dsimp only [outer]
    omega
  have htransported : transportPolymer base outer root ∈
      canonicalSurfacePolymers outer :=
    transportPolymer_mem_canonicalSurfacePolymers hbaseOuter hroot
  have hradius : strictQueryBase outer + stage =
      strictQueryBase base + (stage + padding) := by
    dsimp only [outer]
    exact strictJointTimeTranslation_scheduleRadius_eq base padding stage
  have hleftCanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage)
    (centralStrictUpperCenteredSourceRoot_canonical htransported)
  rw [strictJointCenteredStageBase_eq, hradius] at hleftCanonical
  have hrightCanonical := uniformShiftCanonicalRoot_canonical
    (padding := stage + padding)
    (centralStrictUpperCenteredSourceRoot_canonical hroot)
  rw [strictJointCenteredStageBase_eq] at hrightCanonical
  have hle := strictJointCenteredStageBase_le_centralAmbient
    base (stage + padding)
  apply transportPolymer_injective_on_canonical hle
    hleftCanonical hrightCanonical
  have hleftTransport :=
    centralStrictUpperCanonicalRoot_eq_transport_centeredStage
      (base := outer) (stage := stage) htransported
  rw [hradius] at hleftTransport
  have hrightTransport :=
    centralStrictUpperCanonicalRoot_eq_transport_centeredStage
      (base := base) (stage := stage + padding) hroot
  have hcorner := centralStrictUpperCanonicalRoot_transportBase_eq
    hbaseOuter
    (Nat.le_add_right (strictQueryBase outer) stage)
    hroot
  rw [hradius] at hcorner
  exact Eq.trans hleftTransport.symm
    (Eq.trans hcorner hrightTransport)

/-- At the radius-aligned stages, the complete lower/upper centered chart is
literally the same list after canonical base transport. -/
theorem centralStrictJointCenteredStageRoots_transportBase_aligned
    {base padding stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    centralStrictJointCenteredStageRoots
        (base + padding) stage
        (transportedCylinderRoots base (base + padding) roots) =
      centralStrictJointCenteredStageRoots
        base (stage + padding) roots := by
  rw [centralStrictJointCenteredStageRoots_split,
    centralStrictJointCenteredStageRoots_split]
  unfold transportedCylinderRoots
  simp only [List.map_map]
  congr 1
  · apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact centralStrictLowerCenteredStageRoot_transportBase_aligned
      (hroots root hroot)
  · apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    exact centralStrictUpperCenteredStageRoot_transportBase_aligned
      (hroots root hroot)

theorem centralStrictJointCenteredCylinderEvent_transportBase_aligned
    {base padding stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    centralStrictJointCenteredCylinderEvent
        (base + padding) stage
        (transportedCylinderRoots base (base + padding) roots) predicate =
      centralStrictJointCenteredCylinderEvent
        base (stage + padding) roots predicate := by
  unfold centralStrictJointCenteredCylinderEvent
  rw [centralStrictJointCenteredStageRoots_transportBase_aligned hroots]

/-! ## 3. The common-cutoff aligned comparison -/

private theorem abs_sub_via_common_le
    {left common right leftError rightError : Q'}
    (hleft : Q'.abs (left + (-common)) ≤ leftError)
    (hright : Q'.abs (common + (-right)) ≤ rightError) :
    Q'.abs (left + (-right)) ≤ leftError + rightError := by
  have hdecompose : left + (-right) ≈
      (left + (-common)) + (common + (-right)) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv left (-common) (common + (-right))) ?_
    refine Q'.add_eqv_congr_left left _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-common) common (-right))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((-common) + common) 0 (-right)
        (Q'.neg_add_self_eqv common)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-right))
  have htriangle := Q'.abs_add_le'
    (left + (-common)) (common + (-right))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.le_trans' _ _ _ htriangle (Q'.add_le_add hleft hright))

/-- The two radius-aligned centered schedules differ only by their derived
cutoffs.  Refining both to the existing common cutoff gives a completely
explicit `2 * 2^-stage` comparison. -/
theorem couplingParametricStrictJointCenteredSequence_base_transport_aligned_abs_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (base padding stage : Nat) {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    Q'.abs
        (couplingParametricStrictJointCenteredSequence
            coupling hcoupling (base + padding)
            (transportedCylinderRoots base (base + padding) roots)
            predicate stage +
          (-couplingParametricStrictJointCenteredSequence
            coupling hcoupling base roots predicate (stage + padding))) ≤
      HalfPow.half ^ stage + HalfPow.half ^ stage := by
  let targetEvent := centralStrictJointCenteredCylinderEvent
    (base + padding) stage
    (transportedCylinderRoots base (base + padding) roots) predicate
  let sourceEvent := centralStrictJointCenteredCylinderEvent
    base (stage + padding) roots predicate
  let common := couplingParametricKCompatibleSupportEventProbability
    coupling hcoupling
    (strictJointTimeTranslationScheduleCommonCutoff base padding stage)
    (centeredBoxBase (strictQueryBase (base + padding) + stage))
    targetEvent
  have hevent : targetEvent = sourceEvent := by
    exact centralStrictJointCenteredCylinderEvent_transportBase_aligned
      hroots predicate
  have htargetRaw :=
    couplingParametricStrictJoint_targetCutoff_to_common_abs_le
      hcoupling hle base padding stage targetEvent
  have htarget : Q'.abs
      (couplingParametricStrictJointCenteredSequence
          coupling hcoupling (base + padding)
          (transportedCylinderRoots base (base + padding) roots)
          predicate stage + (-common)) ≤
        HalfPow.half ^ stage := by
    have horiented := Q'.le_of_eqv
      (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
        (couplingParametricStrictJointCenteredSequence
          coupling hcoupling (base + padding)
          (transportedCylinderRoots base (base + padding) roots)
          predicate stage) common)
    exact Q'.le_trans' _ _ _ horiented
      (by simpa only [couplingParametricStrictJointCenteredSequence,
          common, targetEvent] using htargetRaw)
  have hsourceRaw :=
    couplingParametricStrictJoint_sourceCutoff_to_common_abs_le_stage
      hcoupling hle base padding stage sourceEvent
  have hsource : Q'.abs
      (common +
        (-couplingParametricStrictJointCenteredSequence
          coupling hcoupling base roots predicate (stage + padding))) ≤
        HalfPow.half ^ stage := by
    dsimp only [common]
    rw [hevent,
      strictJointTimeTranslation_scheduleCenteredBox_eq
        base padding stage]
    simpa only [couplingParametricStrictJointCenteredSequence,
      sourceEvent] using hsourceRaw
  exact abs_sub_via_common_le htarget hsource

#print axioms centralStrictUpperCanonicalRoot_transportBase_eq
#print axioms centralStrictLowerCylinderRoots_transportBase_eq
#print axioms centralStrictLocalQueryCode_transportBase_eq
#print axioms centralStrictLowerCenteredStageRoot_transportBase_aligned
#print axioms centralStrictUpperCenteredStageRoot_transportBase_aligned
#print axioms centralStrictJointCenteredStageRoots_transportBase_aligned
#print axioms centralStrictJointCenteredCylinderEvent_transportBase_aligned
#print axioms couplingParametricStrictJointCenteredSequence_base_transport_aligned_abs_le

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransport
