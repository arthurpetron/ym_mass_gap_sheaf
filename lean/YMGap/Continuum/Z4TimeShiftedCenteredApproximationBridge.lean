/-
# Centered finite-law bridge for affine Euclidean-time translation

This file discharges the translated-cell exit geometry used by the normalized
shifted-cylinder estimate and connects its embedded probability to the exact
source finite law.  It also records why the existing corner presentation
cannot make the protected distance diverge: a fixed root coordinate gives a
literal upper bound on every admissible symmetric-core distance.
-/

import YMGap.Continuum.Z4FiniteCylinderTimeTranslationColimit
import YMGap.Continuum.Z4TimeShiftedTargetCylinderStability

namespace YMGap.Continuum.Z4TimeShiftedCenteredApproximationBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4TimeShiftedCylinderSwitchSummation
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedEmbeddedRegion
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open YMGap.Continuum.Z4TimeShiftedTargetCylinderStability
open Dir4

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact coordinate description of the translated cell -/

def timeShiftCellLower (shift : Nat) : Z4Vertex :=
  (0, 0, 0, shift)

theorem mem_timeShiftedPlaquetteList_iff_coordinates
    (shift base : Nat) (plaquette : Z4Plaq) :
    plaquette ∈ timeShiftedPlaquetteList shift base ↔
      cPlaq plaquette x0 < base ∧
      cPlaq plaquette x1 < base ∧
      cPlaq plaquette x2 < base ∧
      shift ≤ cPlaq plaquette x3 ∧
      cPlaq plaquette x3 < shift + base := by
  constructor
  · intro hmem
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
    rw [← heq]
    have hcoords := (mem_boxPlaquettes source base).1 hsource
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := source
    simp only [timeShiftPlaquette, timeShiftVertex, cPlaq, vComp]
    simp only at hcoords
    exact ⟨hcoords.1, hcoords.2.1, hcoords.2.2.1,
      Nat.le_add_left shift d,
      by simpa only [Nat.add_comm] using
        Nat.add_lt_add_right hcoords.2.2.2 shift⟩
  · intro hcoords
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
    simp only [cPlaq, vComp] at hcoords
    unfold timeShiftedPlaquetteList
    apply List.mem_map.mpr
    let source : Z4Plaq := ((a, b, c, d - shift), plane)
    refine ⟨source, ?_, ?_⟩
    · apply (mem_boxPlaquettes source base).2
      dsimp only [source]
      exact ⟨hcoords.1, hcoords.2.1, hcoords.2.2.1, by omega⟩
    · dsimp only [source]
      simp only [timeShiftPlaquette, timeShiftVertex, Prod.mk.injEq]
      rw [Nat.sub_add_cancel hcoords.2.2.2.1]
      simp

theorem outside_timeShiftCell_of_not_mem
    {shift base : Nat} {plaquette : Z4Plaq}
    (hnot : plaquette ∉ timeShiftedPlaquetteList shift base) :
    outsideShiftedBoxB (timeShiftCellLower shift) base plaquette = true := by
  apply (outsideShiftedBoxB_true_iff
    (timeShiftCellLower shift) base plaquette).2
  have hcoordinates : ¬(
      cPlaq plaquette x0 < base ∧
      cPlaq plaquette x1 < base ∧
      cPlaq plaquette x2 < base ∧
      shift ≤ cPlaq plaquette x3 ∧
      cPlaq plaquette x3 < shift + base) := by
    intro hcoordinates
    exact hnot ((mem_timeShiftedPlaquetteList_iff_coordinates
      shift base plaquette).2 hcoordinates)
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := plaquette
  simp only [cPlaq, vComp] at hcoordinates
  simp only [timeShiftCellLower, cPlaq, vComp, Nat.zero_add,
    Nat.not_lt_zero, false_or]
  by_cases ha : a < base
  · by_cases hb : b < base
    · by_cases hc : c < base
      · by_cases hdlo : shift ≤ d
        · by_cases hdhi : d < shift + base
          · exact False.elim
              (hcoordinates ⟨ha, hb, hc, hdlo, hdhi⟩)
          · exact Or.inr (Or.inr (Or.inr
              (Or.inr (Nat.le_of_not_gt hdhi))))
        · exact Or.inr (Or.inr (Or.inr
            (Or.inl (Nat.lt_of_not_ge hdlo))))
      · exact Or.inr (Or.inr (Or.inl (Nat.le_of_not_gt hc)))
    · exact Or.inr (Or.inl (Nat.le_of_not_gt hb))
  · exact Or.inl (Nat.le_of_not_gt ha)

theorem outside_timeShiftCell_of_not_mem_of_side_eq
    {shift base inner distance : Nat}
    (hside : inner + distance + distance = base)
    {plaquette : Z4Plaq}
    (hnot : plaquette ∉ timeShiftedPlaquetteList shift base) :
    outsideShiftedBoxB (timeShiftCellLower shift)
      (inner + distance + distance) plaquette = true := by
  rw [hside]
  exact outside_timeShiftCell_of_not_mem hnot

/-! ## 2. A checked fence around the fixed-corner route -/

theorem distance_le_first_coordinate_of_timeShiftCore
    {shift inner distance : Nat} {plaquette : Z4Plaq}
    (hcore : insideShiftedBoxB
      (addUniform (timeShiftCellLower shift) distance)
      inner plaquette = true) :
    distance ≤ cPlaq plaquette x0 := by
  have hparts := (insideShiftedBoxB_true_iff
    (addUniform (timeShiftCellLower shift) distance)
    inner plaquette).1 hcore
  have hfirst := hparts.1
  rw [vComp_addUniform] at hfirst
  simp only [timeShiftCellLower, vComp, Nat.zero_add] at hfirst
  exact hfirst

theorem fixedCornerRoot_has_no_unbounded_timeShiftCore
    {shift inner : Nat} (plaquette : Z4Plaq) :
    ¬ (∀ distance : Nat,
      insideShiftedBoxB
        (addUniform (timeShiftCellLower shift) distance)
        inner plaquette = true) := by
  intro hall
  have hbound := distance_le_first_coordinate_of_timeShiftCore
    (hall (cPlaq plaquette x0 + 1))
  omega

/-! ## 3. Exact source law and the shifted full-target approximation -/

def timeShiftCylinderCanonicalAtoms
    (shift base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    List (CanonicalAtom (base + shift)) :=
  roots.attach.map (fun root =>
    ⟨timeShiftCanonicalRoot shift base root.val,
      timeShiftCanonicalRoot_canonical
        (hroots root.val root.property)⟩)

theorem timeShiftCylinderCanonicalAtoms_length
    (shift base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (timeShiftCylinderCanonicalAtoms shift base roots hroots).length =
      roots.length := by
  unfold timeShiftCylinderCanonicalAtoms
  rw [List.length_map, List.length_attach]

theorem timeShiftCylinderCanonicalAtoms_values
    (shift base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    (timeShiftCylinderCanonicalAtoms shift base roots hroots).map
        Subtype.val =
      timeShiftedCylinderRoots shift base roots := by
  unfold timeShiftCylinderCanonicalAtoms timeShiftedCylinderRoots
  calc
    _ = roots.attach.map (fun root =>
          timeShiftCanonicalRoot shift base root.val) := by
        rw [List.map_map]
        rfl
    _ = (roots.attach.map Subtype.val).map
          (timeShiftCanonicalRoot shift base) := by
        rw [List.map_map]
        rfl
    _ = roots.map (timeShiftCanonicalRoot shift base) := by
        rw [List.attach_map_subtype_val]

theorem timeShiftMarkedCylinderEvent_canonicalAtoms
    (shift base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    timeShiftMarkedCylinderEvent
        (timeShiftCylinderCanonicalAtoms shift base roots hroots)
        predicate =
      timeShiftTargetCylinderEvent shift base roots predicate := by
  unfold timeShiftMarkedCylinderEvent timeShiftTargetCylinderEvent
  rw [timeShiftCylinderCanonicalAtoms_values]

theorem timeShiftCylinderCanonicalAtoms_inside
    (shift base : Nat) (roots : List (List Nat))
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    ∀ target,
      target ∈ timeShiftCylinderCanonicalAtoms shift base roots hroots →
        targetRootInsideTimeShiftB shift base target.val = true := by
  intro target htarget
  obtain ⟨source, hsource, heq⟩ := List.mem_map.mp htarget
  subst target
  apply (targetRootInsideTimeShiftB_true_iff shift base _).2
  exact targetRootInside_timeShiftCanonicalRoot
    (hroots source.val source.property)

def canonicalAtomStart {n : Nat} (root : CanonicalAtom n) : Nat :=
  (canonicalSurfacePolymers_allNonempty
    n root.val root.property).1

theorem canonicalAtomStart_mem {n : Nat} (root : CanonicalAtom n) :
    canonicalAtomStart root ∈ root.val :=
  (canonicalSurfacePolymers_allNonempty
    n root.val root.property).2

set_option maxHeartbeats 4000000 in
theorem couplingParametricKTimeShiftFullTargetProbability_abs_sub_source_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff shift base : Nat)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool)
    {inner distance : Nat}
    (hside : inner + distance + distance = base)
    (hcore : ∀ target,
      target ∈ timeShiftCylinderCanonicalAtoms shift base roots hroots →
        insideShiftedBoxB
          (addUniform (timeShiftCellLower shift) distance) inner
          (boxPlaquetteAt (base + shift)
            (canonicalAtomStart target)) = true) :
    Q'.abs
        (couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff (base + shift)
            (timeShiftTargetCylinderEvent shift base roots predicate) -
          couplingParametricKCompatibleSupportEventProbability
            coupling hcoupling cutoff base
            (sourceCylinderEvent roots predicate)) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon
        roots.length distance := by
  let targetRoots :=
    timeShiftCylinderCanonicalAtoms shift base roots hroots
  have htargetInside : ∀ target, target ∈ targetRoots →
      targetRootInsideTimeShiftB shift base target.val = true :=
    timeShiftCylinderCanonicalAtoms_inside shift base roots hroots
  have htargetBound :=
    couplingParametricKTimeShiftTargetCylinderProbability_abs_sub_embedded_le
      hcoupling hle cutoff (roots := targetRoots)
      (predicate := predicate) htargetInside canonicalAtomStart
      (fun root _ => canonicalAtomStart_mem root)
      (fun root hroot => hcore root hroot)
      (fun plaquette hplaquette =>
        outside_timeShiftCell_of_not_mem_of_side_eq
          hside hplaquette)
  have hevent : timeShiftMarkedCylinderEvent targetRoots predicate =
      timeShiftTargetCylinderEvent shift base roots predicate :=
    timeShiftMarkedCylinderEvent_canonicalAtoms
      shift base roots hroots predicate
  rw [hevent] at htargetBound
  have hsource :=
    couplingParametricKCompatibleCylinderProbability_eqv_embedded_timeShift
      coupling hcoupling cutoff (shift := shift) (base := base)
      hroots predicate
  let fullProbability :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff (base + shift)
      (timeShiftTargetCylinderEvent shift base roots predicate)
  let sourceProbability :=
    couplingParametricKCompatibleSupportEventProbability
      coupling hcoupling cutoff base
      (sourceCylinderEvent roots predicate)
  let embeddedProbability :=
    couplingParametricKTimeShiftEmbeddedTargetEventProbability
      coupling hcoupling cutoff shift base
      (timeShiftTargetCylinderEvent shift base roots predicate)
  have hdifference :
      (fullProbability - sourceProbability).eqv
        (fullProbability - embeddedProbability) :=
    Q'.add_eqv_congr_left fullProbability
      (-sourceProbability) (-embeddedProbability)
      (Q'.neg_eqv_congr sourceProbability embeddedProbability hsource)
  have habs : Q'.abs (fullProbability - sourceProbability) ≤
      timeShiftSpinSummedCylinderBoundaryEpsilon
        targetRoots.length distance :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference)) htargetBound
  simpa only [targetRoots,
    timeShiftCylinderCanonicalAtoms_length] using habs

#print axioms mem_timeShiftedPlaquetteList_iff_coordinates
#print axioms outside_timeShiftCell_of_not_mem
#print axioms distance_le_first_coordinate_of_timeShiftCore
#print axioms fixedCornerRoot_has_no_unbounded_timeShiftCore
#print axioms timeShiftCylinderCanonicalAtoms_values
#print axioms timeShiftCylinderCanonicalAtoms_inside
#print axioms couplingParametricKTimeShiftFullTargetProbability_abs_sub_source_le

end YMGap.Continuum.Z4TimeShiftedCenteredApproximationBridge
