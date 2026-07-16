/-
# Descent of nonnegative time translation to the cylinder colimit

The geometric time-shift semigroup is shown to preserve the explicit
common-refinement relation on finite cylinder presentations.  The key point
is constructive and finite: an equality of Boolean cylinder events remains
an equality after any simultaneous renaming of their coordinates.  Canonical
box transport commutes exactly with time shift, so that Boolean renaming
applies at every common outer box.

Consequently the translated value of an arbitrary finite-cylinder colimit
state is independent of the chosen representative.  This is descent of the
action, not invariance of the physical state under that action.  Proving the
latter still requires a boundary-uniform comparison of translated finite
laws.
-/

import YMGap.Continuum.Z4CouplingParametricCylinderColimitState
import YMGap.Continuum.Z4FiniteCylinderTimeTranslation

namespace YMGap.Continuum.Z4FiniteCylinderTimeTranslationColimit

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCylinderColimitState
open YMGap.Continuum.Z4FiniteCylinderPresentationColimit
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Boolean cylinder events are stable under coordinate renaming -/

private theorem familyContainsPolymerB_filter_rename
    {A : Type} [BEq A] [LawfulBEq A]
    (rename : A → A) (domain family : List A) {item : A}
    (hitem : item ∈ domain) :
    decide (rename item ∈ family) =
      decide (item ∈
        domain.filter (fun source => decide (rename source ∈ family))) := by
  by_cases hrenamed : rename item ∈ family
  · have hfiltered : item ∈
        domain.filter (fun source => decide (rename source ∈ family)) :=
      List.mem_filter.mpr ⟨hitem, by simpa only [decide_eq_true_eq]⟩
    simp [hrenamed, hfiltered]
  · have hfiltered : item ∉
        domain.filter (fun source => decide (rename source ∈ family)) := by
      intro hmem
      have htest := (List.mem_filter.mp hmem).2
      exact hrenamed (of_decide_eq_true htest)
    simp [hrenamed, hfiltered]

private theorem familyOccurrenceFingerprint_rename
    (rename : List Nat → List Nat)
    (domain roots family : List (List Nat))
    (hroots : ∀ root, root ∈ roots → root ∈ domain) :
    familyOccurrenceFingerprint (roots.map rename) family =
      familyOccurrenceFingerprint roots
        (domain.filter (fun source => decide (rename source ∈ family))) := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
      simp only [familyOccurrenceFingerprint, List.map_cons]
      unfold familyContainsPolymerB
      rw [familyContainsPolymerB_filter_rename rename domain family
        (hroots root List.mem_cons_self)]
      exact congrArg (List.cons
        (decide (root ∈
          domain.filter (fun source => decide (rename source ∈ family)))))
        (ih (fun item hitem =>
          hroots item (List.mem_cons_of_mem root hitem)))

/-- A functional equality between two finite Boolean cylinder events survives
simultaneous renaming of all coordinates.  Injectivity is not needed because
the finite preimage family records every source coordinate whose image occurs
in the target family. -/
theorem cylinderEvent_rename_eq_of_eq
    (rename : List Nat → List Nat)
    {leftRoots rightRoots : List (List Nat)}
    {leftPredicate rightPredicate : List Bool → Bool}
    (hevent : cylinderEvent leftRoots leftPredicate =
      cylinderEvent rightRoots rightPredicate) :
    cylinderEvent (leftRoots.map rename) leftPredicate =
      cylinderEvent (rightRoots.map rename) rightPredicate := by
  funext family
  let domain := leftRoots ++ rightRoots
  let preimageFamily :=
    domain.filter (fun source => decide (rename source ∈ family))
  have hleft := familyOccurrenceFingerprint_rename
    rename domain leftRoots family
    (fun root hroot => List.mem_append.mpr (Or.inl hroot))
  have hright := familyOccurrenceFingerprint_rename
    rename domain rightRoots family
    (fun root hroot => List.mem_append.mpr (Or.inr hroot))
  change leftPredicate
      (familyOccurrenceFingerprint (leftRoots.map rename) family) =
    rightPredicate
      (familyOccurrenceFingerprint (rightRoots.map rename) family)
  rw [hleft, hright]
  exact congrFun hevent preimageFamily

/-! ## 2. Canonical box transport commutes with time shift -/

theorem timeShiftCanonicalRoot_transport
    {base middle shift : Nat} (hbase : base ≤ middle)
    {root : List Nat} (hroot : root ∈ canonicalSurfacePolymers base) :
    transportPolymer (base + shift) (middle + shift)
        (timeShiftCanonicalRoot shift base root) =
      timeShiftCanonicalRoot shift middle
        (transportPolymer base middle root) := by
  have hshiftBase := timeShiftCanonicalRoot_canonical
    (shift := shift) hroot
  have htransported := transportPolymer_mem_canonicalSurfacePolymers
    hbase hroot
  have hleftCanonical := transportPolymer_mem_canonicalSurfacePolymers
    (Nat.add_le_add_right hbase shift) hshiftBase
  have hrightCanonical := timeShiftCanonicalRoot_canonical
    (shift := shift) htransported
  apply canonicalSurfacePolymer_eq_of_geometric_sameSupport
    hleftCanonical hrightCanonical
  have hshiftBaseSupport := timeShiftCanonicalRoot_sameSupport
    (shift := shift) hroot
  have htransportSupport := transportPolymer_sameSupport hbase
    (canonicalSurfacePolymer_mem_faceSupports hroot)
  have hshiftTransportSupport := transportPolymer_sameSupport
    (Nat.add_le_add_right hbase shift)
    (canonicalSurfacePolymer_mem_faceSupports hshiftBase)
  have hmiddleShiftSupport := timeShiftCanonicalRoot_sameSupport
    (shift := shift) htransported
  exact sameSupport_trans (sameSupport_symm hshiftTransportSupport)
    (sameSupport_trans hshiftBaseSupport
      (sameSupport_trans
        (by
          constructor
          · intro plaquette hplaquette
            obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
            exact List.mem_map.mpr
              ⟨source, htransportSupport.1 source hsource, rfl⟩
          · intro plaquette hplaquette
            obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hplaquette
            exact List.mem_map.mpr
              ⟨source, htransportSupport.2 source hsource, rfl⟩)
        (sameSupport_symm hmiddleShiftSupport)))

theorem transportedCylinderRoots_timeShift
    {base middle shift : Nat} (hbase : base ≤ middle)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base) :
    transportedCylinderRoots (base + shift) (middle + shift)
        (roots.map (timeShiftCanonicalRoot shift base)) =
      (transportedCylinderRoots base middle roots).map
        (timeShiftCanonicalRoot shift middle) := by
  unfold transportedCylinderRoots
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro root hroot
  simp only [Function.comp_apply]
  exact timeShiftCanonicalRoot_transport hbase (hroots root hroot)

/-! ## 3. Descent through explicit common refinements -/

theorem cylinderPresentationRefines_timeShift
    {source target : FiniteCylinderPresentation}
    (hrefines : CylinderPresentationRefines source target)
    (shift : Nat) :
    CylinderPresentationRefines
      (timeShiftFiniteCylinderPresentation source shift)
      (timeShiftFiniteCylinderPresentation target shift) := by
  refine ⟨Nat.add_le_add_right hrefines.base_le shift, ?_⟩
  intro outer houter
  change target.chart.base + shift ≤ outer at houter
  let middle := outer - shift
  have hshiftOuter : shift ≤ outer := by omega
  have hmiddleAdd : middle + shift = outer := by
    unfold middle
    omega
  have htargetMiddle : target.chart.base ≤ middle := by
    unfold middle
    omega
  have hsourceMiddle : source.chart.base ≤ middle :=
    Nat.le_trans hrefines.base_le htargetMiddle
  have htargetRoots := transportedCylinderRoots_timeShift
    (shift := shift) htargetMiddle target.chart.rootsCanonical
  have hsourceRoots := transportedCylinderRoots_timeShift
    (shift := shift) hsourceMiddle source.chart.rootsCanonical
  rw [hmiddleAdd] at htargetRoots hsourceRoots
  have horiginal := hrefines.event_eq middle htargetMiddle
  change cylinderEvent
      (transportedCylinderRoots (target.chart.base + shift) outer
        (target.chart.roots.map
          (timeShiftCanonicalRoot shift target.chart.base)))
      target.predicate =
    cylinderEvent
      (transportedCylinderRoots (source.chart.base + shift) outer
        (source.chart.roots.map
          (timeShiftCanonicalRoot shift source.chart.base)))
      source.predicate
  rw [htargetRoots, hsourceRoots]
  apply cylinderEvent_rename_eq_of_eq
    (timeShiftCanonicalRoot shift middle)
  exact horiginal

theorem cylinderPresentationEquivalent_timeShift
    {left right : FiniteCylinderPresentation}
    (hequivalent : CylinderPresentationEquivalent left right)
    (shift : Nat) :
    CylinderPresentationEquivalent
      (timeShiftFiniteCylinderPresentation left shift)
      (timeShiftFiniteCylinderPresentation right shift) := by
  rcases hequivalent with ⟨common, hleft, hright⟩
  exact ⟨timeShiftFiniteCylinderPresentation common shift,
    cylinderPresentationRefines_timeShift hleft shift,
    cylinderPresentationRefines_timeShift hright shift⟩

/-- For any already constructed colimit state, evaluation after time shift is
well-defined on presentation equivalence classes.  This is representative
independence, not the additional covariance equation `state(τ A)=state(A)`. -/
theorem FiniteCylinderColimitState.timeShift_respects
    (state : FiniteCylinderColimitState)
    {left right : FiniteCylinderPresentation}
    (hequivalent : CylinderPresentationEquivalent left right)
    (shift : Nat) :
    CReal.Equiv
      (state.evaluate (timeShiftFiniteCylinderPresentation left shift))
      (state.evaluate (timeShiftFiniteCylinderPresentation right shift)) :=
  state.respects _ _
    (cylinderPresentationEquivalent_timeShift hequivalent shift)

#print axioms cylinderEvent_rename_eq_of_eq
#print axioms timeShiftCanonicalRoot_transport
#print axioms transportedCylinderRoots_timeShift
#print axioms cylinderPresentationRefines_timeShift
#print axioms cylinderPresentationEquivalent_timeShift
#print axioms FiniteCylinderColimitState.timeShift_respects

end YMGap.Continuum.Z4FiniteCylinderTimeTranslationColimit
