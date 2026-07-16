/-
# Finite-volume canonical-root occurrence at arbitrary coupling

For every canonical connected surface polymer, its literal fundamental-spin
component labelling is present at every representation cutoff at least one.
The canonical family decoded from this labelling contains the original
polymer, so the corresponding physical summand survives the lifted occurrence
mask.  Consequently the exact root activity lower-bounds the full lifted event
numerator at every nonnegative coupling.  Strict positivity of the activity
then gives strict positivity of the normalized finite-volume occurrence law.
-/

import YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
import YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

namespace YMGap.Continuum.Z4ParametricCanonicalRootOccurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A canonical polymer occurs in its literal component labelling -/

private theorem nil_mem_sublists_local {A : Type} :
    ∀ ambient : List A, [] ∈ sublists ambient
  | [] => List.mem_cons_self
  | _ :: tail => by
      rw [sublists_cons']
      exact List.mem_append_left _ (nil_mem_sublists_local tail)

private theorem singleton_mem_sublists_of_mem_local {A : Type} :
    ∀ (ambient : List A) (item : A), item ∈ ambient →
      [item] ∈ sublists ambient
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rw [sublists_cons']
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨[], nil_mem_sublists_local tail, rfl⟩
      · exact List.mem_append_left _
          (singleton_mem_sublists_of_mem_local tail item htail)

private theorem singleton_mem_canonicalCompatibleAmbientFamilies
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    [polymer] ∈ canonicalCompatibleAmbientFamilies n := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨singleton_mem_sublists_of_mem_local
      (canonicalSurfacePolymers n) polymer hpolymer,
    rfl⟩

theorem familyUnionSupport_singleton_eq
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    familyUnionSupport n [polymer] = polymer := by
  have hsupport : polymer ∈ cutoffOneFaceSupports n :=
    canonicalSurfacePolymer_mem_faceSupports hpolymer
  apply sublists_eq_of_mem_iff (physicalFaceEdges n)
    (familyUnionSupport n [polymer]) polymer
    (physicalFaceEdges_nodup n)
    (familyUnionSupport_mem_cutoffOneFaceSupports n [polymer])
    hsupport
  intro face
  rw [mem_familyUnionSupport_iff]
  constructor
  · rintro ⟨_, candidate, hcandidate, hface⟩
    have hcandidateEq : candidate = polymer := by
      simpa using hcandidate
    rwa [hcandidateEq] at hface
  · intro hface
    have hambient : face ∈ physicalFaceEdges n :=
      mem_of_mem_sublists (physicalFaceEdges n) polymer hsupport face hface
    exact ⟨hambient, polymer, List.mem_cons_self, hface⟩

theorem canonicalPolymer_mem_own_canonicalSurfaceFamily
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    polymer ∈ canonicalSurfaceFamily n polymer := by
  have hfamily : [polymer] ∈ canonicalCompatibleAmbientFamilies n :=
    singleton_mem_canonicalCompatibleAmbientFamilies hpolymer
  have hmember :=
    (canonicalSurfaceFamily_mem_iff_compatibleFamily hfamily polymer).2
      List.mem_cons_self
  rw [familyUnionSupport_singleton_eq hpolymer] at hmember
  exact hmember

theorem canonicalPolymer_mem_componentLabelAmbientFamily
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    polymer ∈
      physicalCanonicalAmbientFamily n (componentLabel polymer) := by
  have hsupport : polymer ∈ cutoffOneFaceSupports n :=
    canonicalSurfacePolymer_mem_faceSupports hpolymer
  rw [physicalCanonicalAmbientFamily_componentLabel hsupport,
    mem_ambientOrderedFamily_iff]
  exact ⟨hpolymer,
    canonicalPolymer_mem_own_canonicalSurfaceFamily hpolymer⟩

theorem componentLabel_liftedOccurrenceEvent_true
    {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    cutoffOneLiftedFamilyEvent n (familyContainsPolymerB polymer)
        (componentLabel polymer) = true := by
  unfold cutoffOneLiftedFamilyEvent familyContainsPolymerB
  simp only [decide_eq_true_eq]
  exact canonicalPolymer_mem_componentLabelAmbientFamily hpolymer

/-! ## 2. The literal physical term lower-bounds the lifted numerator -/

theorem parametricKOccurrenceEventTerm_componentLabel_eq
    (w : Q') (cutoff : Nat) {n : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    parametricKEventTerm w cutoff n
        (cutoffOneLiftedFamilyEvent n (familyContainsPolymerB polymer))
        (componentLabel polymer) =
      parametricKPhysicalTerm w cutoff n (componentLabel polymer) := by
  unfold parametricKEventTerm
  rw [if_pos (componentLabel_liftedOccurrenceEvent_true hpolymer)]

theorem parametricKPhysicalTerm_componentLabel_le_occurrenceNumerator
    {w : Q'} (hw : (0 : Q') ≤ w)
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    parametricKPhysicalTerm w cutoff n (componentLabel polymer) ≤
      parametricKEventNumerator w cutoff n
        (cutoffOneLiftedFamilyEvent n (familyContainsPolymerB polymer)) := by
  have hsupport : polymer ∈ cutoffOneFaceSupports n :=
    canonicalSurfacePolymer_mem_faceSupports hpolymer
  have hbounded : componentLabel polymer ∈
      boundedEdgeLabellings cutoff
        (List.range (plaquetteEdgeCount n)) :=
    componentLabel_mem_bounded_of_one_le hcutoff hsupport
  have hmember := listQSum_member_le
    (parametricKEventTerm w cutoff n
      (cutoffOneLiftedFamilyEvent n (familyContainsPolymerB polymer)))
    (parametricKEventTerm_nonnegative hw cutoff n _)
    (boundedEdgeLabellings cutoff
      (List.range (plaquetteEdgeCount n))) hbounded
  unfold parametricKEventNumerator
  rw [parametricKOccurrenceEventTerm_componentLabel_eq
    w cutoff hpolymer] at hmember
  exact hmember

theorem canonicalSurfaceActivity_eqv_componentLabelPhysicalTerm
    (w : Q') {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    canonicalSurfaceActivity w n polymer ≈
      parametricKPhysicalTerm w cutoff n (componentLabel polymer) := by
  have hsupport : polymer ∈ cutoffOneFaceSupports n :=
    canonicalSurfacePolymer_mem_faceSupports hpolymer
  have hone : componentLabel polymer ∈
      boundedEdgeLabellings 1
        (List.range (plaquetteEdgeCount n)) :=
    componentLabel_mem_explicitPhysicalLabellings_one hsupport
  have hstable := parametricKPhysicalTerm_cutoff_stable
    (w := w) hcutoff hone
  have honeEq :
      parametricKPhysicalTerm w 1 n (componentLabel polymer) ≈
        canonicalSurfaceActivity w n polymer := by
    unfold canonicalSurfaceActivity
    exact parametricKPhysicalTerm_one_eqv_localized
      w n (componentLabel polymer)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm honeEq)
    (Q'.eqv_of_eq hstable.symm)

theorem canonicalSurfaceActivity_le_occurrenceNumerator
    {w : Q'} (hw : (0 : Q') ≤ w)
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n) :
    canonicalSurfaceActivity w n polymer ≤
      parametricKEventNumerator w cutoff n
        (cutoffOneLiftedFamilyEvent n (familyContainsPolymerB polymer)) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (canonicalSurfaceActivity_eqv_componentLabelPhysicalTerm
        w hcutoff hpolymer))
    (parametricKPhysicalTerm_componentLabel_le_occurrenceNumerator
      hw hcutoff hpolymer)

theorem parametricKCanonicalPolymerOccurrenceNumerator_pos_of_activity
    {w : Q'} (hw : (0 : Q') ≤ w)
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hactivity : (0 : Q') < canonicalSurfaceActivity w n polymer) :
    (0 : Q') <
      parametricKEventNumerator w cutoff n
        (cutoffOneLiftedFamilyEvent n
          (familyContainsPolymerB polymer)) :=
  Q'.pos_of_lt_of_le hactivity
    (canonicalSurfaceActivity_le_occurrenceNumerator
      hw hcutoff hpolymer)

/-! ## 3. Strictly positive normalized occurrence -/

def couplingKCanonicalPolymerOccurrenceProbability
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff n : Nat) (polymer : List Nat) : Q' :=
  couplingKFamilyEventProbability w hw cutoff n
    (familyContainsPolymerB polymer)

theorem couplingKCanonicalPolymerOccurrenceProbability_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff n : Nat) (polymer : List Nat) :
    (0 : Q') ≤ couplingKCanonicalPolymerOccurrenceProbability
      w hw cutoff n polymer :=
  couplingKFamilyEventProbability_nonnegative w hw cutoff n _

theorem couplingKCanonicalPolymerOccurrenceProbability_le_one
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff n : Nat) (polymer : List Nat) :
    couplingKCanonicalPolymerOccurrenceProbability
        w hw cutoff n polymer ≤ (1 : Q') :=
  couplingKFamilyEventProbability_le_one w hw cutoff n _

theorem couplingKCanonicalPolymerOccurrenceProbability_pos_of_activity
    {w : Q'} (hw : (0 : Q') ≤ w)
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers n)
    (hactivity : (0 : Q') < canonicalSurfaceActivity w n polymer) :
    (0 : Q') < couplingKCanonicalPolymerOccurrenceProbability
      w hw cutoff n polymer := by
  unfold couplingKCanonicalPolymerOccurrenceProbability
    couplingKFamilyEventProbability
  exact Q'.divPos_pos _ _
    (couplingKPhysicalPartition_pos hw cutoff n)
    (parametricKCanonicalPolymerOccurrenceNumerator_pos_of_activity
      hw hcutoff hpolymer hactivity)

#print axioms familyUnionSupport_singleton_eq
#print axioms canonicalPolymer_mem_componentLabelAmbientFamily
#print axioms componentLabel_liftedOccurrenceEvent_true
#print axioms parametricKPhysicalTerm_componentLabel_le_occurrenceNumerator
#print axioms canonicalSurfaceActivity_le_occurrenceNumerator
#print axioms couplingKCanonicalPolymerOccurrenceProbability_pos_of_activity

end YMGap.Continuum.Z4ParametricCanonicalRootOccurrence
