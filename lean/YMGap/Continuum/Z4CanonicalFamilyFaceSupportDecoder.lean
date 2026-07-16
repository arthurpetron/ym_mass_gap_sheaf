/-
# Recovering occupied faces from a canonical component family

The canonical gas records connected occupied components rather than raw face
bits.  For reflection positivity we must read the occupied lower and reflected
upper face supports back from that family.  Flattening a physical canonical
family has exactly the same membership predicate as the original excited-face
support.  Hence its indicator labelling preserves every positive/zero test
after restriction from the ambient corner box to the corrected slab.

This supplies a literal family event for a prescribed pair of lower/reflected
upper supports.  By the exhaustive-cylinder decoder, that event is one finite
Boolean cylinder event on the complete canonical root chart.
-/

import YMGap.Continuum.Z4CanonicalExhaustiveCylinder
import YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientPartition
import YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
import YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram

namespace YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalExhaustiveCylinder
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSupportPushforwardGram
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeLocality

/-! ## 1. Flattening recovers the complete excited support -/

theorem physicalCanonicalAmbientFamily_mem_compatible
    (n : Nat) (physical : EdgeLabelling) :
    physicalCanonicalAmbientFamily n physical ∈
      canonicalCompatibleAmbientFamilies n := by
  let support := excitedPlaquetteIds n physical
  have hsupport : support ∈ cutoffOneFaceSupports n := by
    unfold support excitedPlaquetteIds cutoffOneFaceSupports
    exact filter_mem_sublists _ _
  let components := canonicalSurfaceFamily n support
  have hgas : components ∈ canonicalConnectedSurfaceGas n := by
    unfold components canonicalConnectedSurfaceGas
    exact List.mem_map.mpr ⟨support, hsupport, rfl⟩
  exact gasFamily_ambientOrdered_mem_compatibleFamilies hgas

/-- A face occurs in the flattened canonical component family exactly when
it is excited in the original physical labelling. -/
theorem mem_physicalCanonicalAmbientFamily_flatten_iff
    (n : Nat) (physical : EdgeLabelling) (face : Nat) :
    face ∈ (physicalCanonicalAmbientFamily n physical).flatten ↔
      face ∈ excitedPlaquetteIds n physical := by
  let support := excitedPlaquetteIds n physical
  have hsupport : support ∈ cutoffOneFaceSupports n := by
    unfold support excitedPlaquetteIds cutoffOneFaceSupports
    exact filter_mem_sublists _ _
  let components := canonicalSurfaceFamily n support
  have hgas : components ∈ canonicalConnectedSurfaceGas n := by
    unfold components canonicalConnectedSurfaceGas
    exact List.mem_map.mpr ⟨support, hsupport, rfl⟩
  have hcover : Covers support components :=
    canonicalSurfaceFamily_covers hsupport
  have hordered : ∀ polymer,
      polymer ∈ ambientOrderedFamily n components ↔
        polymer ∈ components :=
    gasFamily_mem_ambientOrderedFamily_iff hgas
  change face ∈ (ambientOrderedFamily n components).flatten ↔
    face ∈ support
  constructor
  · intro hface
    obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
      List.mem_flatten.mp hface
    exact (hcover face).2
      ⟨polymer, (hordered polymer).1 hpolymer, hfacePolymer⟩
  · intro hface
    obtain ⟨polymer, hpolymer, hfacePolymer⟩ := (hcover face).1 hface
    exact List.mem_flatten.mpr
      ⟨polymer, (hordered polymer).2 hpolymer, hfacePolymer⟩

/-- The binary face labelling reconstructed from an arbitrary canonical
family. -/
def canonicalFamilyFaceIndicator
    (family : List (List Nat)) : EdgeLabelling :=
  componentLabel family.flatten

theorem excitedPlaquetteIds_familyIndicator_physical
    (n : Nat) (physical : EdgeLabelling) :
    excitedPlaquetteIds n
        (canonicalFamilyFaceIndicator
          (physicalCanonicalAmbientFamily n physical)) =
      excitedPlaquetteIds n physical := by
  unfold excitedPlaquetteIds
  apply List.filter_congr
  intro face hface
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hpositive
    change 1 ≤ componentLabel
      (physicalCanonicalAmbientFamily n physical).flatten face at hpositive
    have hmem : face ∈
        (physicalCanonicalAmbientFamily n physical).flatten := by
      by_cases hmem : face ∈
          (physicalCanonicalAmbientFamily n physical).flatten
      · exact hmem
      · rw [componentLabel_eq_zero_of_not_mem hmem] at hpositive
        omega
    have hexcited :=
      (mem_physicalCanonicalAmbientFamily_flatten_iff
        n physical face).1 hmem
    simpa only [decide_eq_true_eq] using
      (List.mem_filter.mp hexcited).2
  · intro hpositive
    have hexcited : face ∈ excitedPlaquetteIds n physical := by
      unfold excitedPlaquetteIds
      exact List.mem_filter.mpr
        ⟨hface, decide_eq_true hpositive⟩
    have hmem :=
      (mem_physicalCanonicalAmbientFamily_flatten_iff
        n physical face).2 hexcited
    change 1 ≤ componentLabel
      (physicalCanonicalAmbientFamily n physical).flatten face
    rw [componentLabel_eq_one_iff.mpr hmem]
    exact Nat.le_refl 1

/-! ## 2. Support is preserved by ambient-to-slab restriction -/

theorem ambientToSlabPhysical_positive_iff_of_excited_eq
    {extent : Nat} {left right : EdgeLabelling}
    (hsupport : excitedPlaquetteIds (extent + 1) left =
      excitedPlaquetteIds (extent + 1) right)
    {sourceId : Nat} (hsource : sourceId ∈ slabPhysicalFaceEdges extent) :
    1 ≤ ambientToSlabPhysical extent left sourceId ↔
      1 ≤ ambientToSlabPhysical extent right sourceId := by
  have hslab := slabPlaquetteAt_mem hsource
  have hbox : slabPlaquetteAt extent sourceId ∈
      boxPlaquettes (extent + 1) :=
    (mem_boundaryCompleteSlabPlaquettes extent _).mp hslab |>.1
  obtain ⟨targetId, hindexed⟩ := exists_mem_enumerate hbox
  rw [ambientToSlabPhysical_eq_on_physical hsource,
    ambientToSlabPhysical_eq_on_physical hsource,
    geometricSpinOfPhysical_eq_of_enumerate hindexed,
    geometricSpinOfPhysical_eq_of_enumerate hindexed]
  have htarget : targetId ∈ physicalFaceEdges (extent + 1) := by
    unfold physicalFaceEdges plaquetteEdgeCount
    exact List.mem_range.mpr (enumerate_index_lt hindexed)
  have hleft : targetId ∈ excitedPlaquetteIds (extent + 1) left ↔
      1 ≤ left targetId := by
    unfold excitedPlaquetteIds
    simp only [List.mem_filter, decide_eq_true_eq, htarget, true_and]
  have hright : targetId ∈ excitedPlaquetteIds (extent + 1) right ↔
      1 ≤ right targetId := by
    unfold excitedPlaquetteIds
    simp only [List.mem_filter, decide_eq_true_eq, htarget, true_and]
  rw [← hleft, ← hright, hsupport]

private theorem filter_eq_of_predicate_on_mem {A : Type}
    (left right : A → Bool) : ∀ xs : List A,
    (∀ x, x ∈ xs → left x = right x) →
      xs.filter left = xs.filter right
  | [], _ => rfl
  | head :: tail, h => by
      have hhead := h head List.mem_cons_self
      have htail : ∀ x, x ∈ tail → left x = right x :=
        fun x hx => h x (List.mem_cons_of_mem head hx)
      simp only [List.filter_cons, hhead]
      rw [filter_eq_of_predicate_on_mem left right tail htail]

theorem centralLowerSupportCode_familyIndicator
    (half : Nat) (physical : EdgeLabelling) :
    centralHalfSupportCode half
        (centralLowerRestriction half
          (ambientToSlabPhysical (centralExtent half)
            (canonicalFamilyFaceIndicator
              (physicalCanonicalAmbientFamily (centralAmbient half)
                physical)))) =
      centralHalfSupportCode half
        (centralLowerRestriction half
          (ambientToSlabPhysical (centralExtent half) physical)) := by
  have hsupport := excitedPlaquetteIds_familyIndicator_physical
    (centralAmbient half) physical
  unfold centralHalfSupportCode
  apply filter_eq_of_predicate_on_mem
  intro id hid
  simp only [centralLowerRestriction, if_pos hid]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ambientToSlabPhysical_positive_iff_of_excited_eq
    hsupport (mem_centralLowerFaceIds.mp hid).1

theorem centralReflectedUpperSupportCode_familyIndicator
    (half : Nat) (physical : EdgeLabelling) :
    centralHalfSupportCode half
        (centralReflectedUpperRestriction half
          (ambientToSlabPhysical (centralExtent half)
            (canonicalFamilyFaceIndicator
              (physicalCanonicalAmbientFamily (centralAmbient half)
                physical)))) =
      centralHalfSupportCode half
        (centralReflectedUpperRestriction half
          (ambientToSlabPhysical (centralExtent half) physical)) := by
  have hsupport := excitedPlaquetteIds_familyIndicator_physical
    (centralAmbient half) physical
  unfold centralHalfSupportCode
  apply filter_eq_of_predicate_on_mem
  intro id hid
  simp only [centralReflectedUpperRestriction, if_pos hid]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ambientToSlabPhysical_positive_iff_of_excited_eq
    hsupport
    (slabFaceReflectId_physical (mem_centralLowerFaceIds.mp hid).1)

/-! ## 3. The support-pair event is one exhaustive finite cylinder -/

def centralFamilyLowerSupportCode
    (half : Nat) (family : List (List Nat)) : List Nat :=
  centralHalfSupportCode half
    (centralLowerRestriction half
      (ambientToSlabPhysical (centralExtent half)
        (canonicalFamilyFaceIndicator family)))

def centralFamilyReflectedUpperSupportCode
    (half : Nat) (family : List (List Nat)) : List Nat :=
  centralHalfSupportCode half
    (centralReflectedUpperRestriction half
      (ambientToSlabPhysical (centralExtent half)
        (canonicalFamilyFaceIndicator family)))

def centralFamilySupportPairEvent
    (half : Nat) (leftSupport rightSupport : List Nat)
    (family : List (List Nat)) : Bool :=
  decide
    (centralFamilyLowerSupportCode half family = leftSupport ∧
      centralFamilyReflectedUpperSupportCode half family = rightSupport)

def centralFamilySupportPairCylinderPredicate
    (half : Nat) (leftSupport rightSupport : List Nat) :
    List Bool → Bool :=
  exhaustiveCylinderPredicate (centralAmbient half)
    (centralFamilySupportPairEvent half leftSupport rightSupport)

/-! ### The exhaustive chart restricted to slab-supported polymers -/

def centralSlabCanonicalPolymers (half : Nat) : List (List Nat) :=
  (canonicalSurfacePolymers (centralAmbient half)).filter
    (canonicalPolymerSlabSupportedB (centralExtent half))

def centralSlabCanonicalAtoms (half : Nat) :
    List (CanonicalAtom (centralAmbient half)) :=
  familyCanonicalAtoms (centralAmbient half)
    (centralSlabCanonicalPolymers half)
    (fun _polymer hpolymer => (List.mem_filter.mp hpolymer).1)

theorem centralSlabCanonicalAtoms_values (half : Nat) :
    (centralSlabCanonicalAtoms half).map Subtype.val =
      centralSlabCanonicalPolymers half := by
  unfold centralSlabCanonicalAtoms
  exact familyCanonicalAtoms_values (centralAmbient half)
    (centralSlabCanonicalPolymers half) _

theorem centralSlabCanonicalAtoms_length (half : Nat) :
    (centralSlabCanonicalAtoms half).length =
      (centralSlabCanonicalPolymers half).length := by
  have h := congrArg List.length (centralSlabCanonicalAtoms_values half)
  simpa only [List.length_map] using h

theorem centralSlabCanonicalAtoms_supported (half : Nat) :
    ∀ root, root ∈ centralSlabCanonicalAtoms half →
      canonicalPolymerSlabSupportedB (centralExtent half) root.val = true := by
  intro root hroot
  have hvalue : root.val ∈
      (centralSlabCanonicalAtoms half).map Subtype.val :=
    List.mem_map.mpr ⟨root, hroot, rfl⟩
  rw [centralSlabCanonicalAtoms_values] at hvalue
  exact (List.mem_filter.mp hvalue).2

def centralSlabExhaustiveCylinderPredicate
    (half : Nat) (event : List (List Nat) → Bool) :
    List Bool → Bool :=
  fun bits => event
    (selectByBoolFingerprint (centralSlabCanonicalPolymers half) bits)

private theorem centralSlabCanonicalPolymers_nodup (half : Nat) :
    (centralSlabCanonicalPolymers half).Nodup := by
  unfold centralSlabCanonicalPolymers
  exact List.filter_sublist.nodup
    (canonicalSurfacePolymers_nodup (centralAmbient half))

/-- On a family already known to lie in the corrected slab, occurrence bits
against all slab-supported canonical polymers reconstruct that family
literally. -/
theorem centralSlabOccurrenceFingerprint_recovers
    {half : Nat} {family : List (List Nat)}
    (hfamily : family ∈
      canonicalCompatibleAmbientFamilies (centralAmbient half))
    (hsupported : canonicalFamilySlabSupportedB
      (centralExtent half) family = true) :
    selectByBoolFingerprint (centralSlabCanonicalPolymers half)
        (familyOccurrenceFingerprint
          (centralSlabCanonicalPolymers half) family) = family := by
  rw [selectByBoolFingerprint_occurrence_eq_filter]
  have hselected :
      (centralSlabCanonicalPolymers half).filter
          (fun root => familyContainsPolymerB root family) ∈
        sublists (canonicalSurfacePolymers (centralAmbient half)) := by
    unfold centralSlabCanonicalPolymers
    rw [List.filter_filter]
    exact filter_mem_sublists _ _
  apply sublists_eq_of_mem_iff
    (canonicalSurfacePolymers (centralAmbient half))
    ((centralSlabCanonicalPolymers half).filter
      (fun root => familyContainsPolymerB root family))
    family
    (canonicalSurfacePolymers_nodup (centralAmbient half))
    hselected (compatibleAmbientFamily_sublist hfamily)
  intro root
  constructor
  · intro hroot
    have hcontains := (List.mem_filter.mp hroot).2
    unfold familyContainsPolymerB at hcontains
    exact of_decide_eq_true hcontains
  · intro hroot
    apply List.mem_filter.mpr
    constructor
    · unfold centralSlabCanonicalPolymers
      apply List.mem_filter.mpr
      refine ⟨compatibleAmbientFamily_member_ambient hfamily hroot, ?_⟩
      have hall : family.all
          (canonicalPolymerSlabSupportedB (centralExtent half)) = true := by
        rw [← canonicalFamilySlabSupportedB_eq_polymerAll]
        exact hsupported
      exact List.all_eq_true.mp hall root hroot
    · unfold familyContainsPolymerB
      exact decide_eq_true hroot

theorem centralSlabExhaustiveCylinderEvent_eq
    {half : Nat} (event : List (List Nat) → Bool)
    {family : List (List Nat)}
    (hfamily : family ∈
      canonicalCompatibleAmbientFamilies (centralAmbient half))
    (hsupported : canonicalFamilySlabSupportedB
      (centralExtent half) family = true) :
    sourceCylinderEvent (centralSlabCanonicalPolymers half)
        (centralSlabExhaustiveCylinderPredicate half event) family =
      event family := by
  unfold sourceCylinderEvent cylinderEvent
    centralSlabExhaustiveCylinderPredicate
  rw [centralSlabOccurrenceFingerprint_recovers hfamily hsupported]

def centralSlabSupportPairCylinderPredicate
    (half : Nat) (leftSupport rightSupport : List Nat) :
    List Bool → Bool :=
  centralSlabExhaustiveCylinderPredicate half
    (centralFamilySupportPairEvent half leftSupport rightSupport)

theorem centralFamilyLowerSupportCode_physical
    (half : Nat) (physical : EdgeLabelling) :
    centralFamilyLowerSupportCode half
        (physicalCanonicalAmbientFamily (centralAmbient half) physical) =
      centralHalfSupportCode half
        (centralLowerRestriction half
          (ambientToSlabPhysical (centralExtent half) physical)) :=
  centralLowerSupportCode_familyIndicator half physical

theorem centralFamilyReflectedUpperSupportCode_physical
    (half : Nat) (physical : EdgeLabelling) :
    centralFamilyReflectedUpperSupportCode half
        (physicalCanonicalAmbientFamily (centralAmbient half) physical) =
      centralHalfSupportCode half
        (centralReflectedUpperRestriction half
          (ambientToSlabPhysical (centralExtent half) physical)) :=
  centralReflectedUpperSupportCode_familyIndicator half physical

/-- The exhaustive occurrence fingerprint evaluates to the literal pair of
lower/reflected-upper support equalities on every physical configuration. -/
theorem centralFamilySupportPairCylinderEvent_physical
    (half : Nat) (leftSupport rightSupport : List Nat)
    (physical : EdgeLabelling) :
    sourceCylinderEvent (canonicalSurfacePolymers (centralAmbient half))
        (centralFamilySupportPairCylinderPredicate
          half leftSupport rightSupport)
        (physicalCanonicalAmbientFamily (centralAmbient half) physical) =
      decide
        (centralHalfSupportCode half
              (centralLowerRestriction half
                (ambientToSlabPhysical (centralExtent half) physical)) =
            leftSupport ∧
          centralHalfSupportCode half
              (centralReflectedUpperRestriction half
                (ambientToSlabPhysical (centralExtent half) physical)) =
            rightSupport) := by
  unfold centralFamilySupportPairCylinderPredicate
  rw [exhaustiveCylinderEvent_eq
    (centralFamilySupportPairEvent half leftSupport rightSupport)
    (physicalCanonicalAmbientFamily_mem_compatible
      (centralAmbient half) physical)]
  unfold centralFamilySupportPairEvent
  rw [centralFamilyLowerSupportCode_physical,
    centralFamilyReflectedUpperSupportCode_physical]

/-- Supported-chart version used by the corrected-slab conditional law. -/
theorem centralSlabSupportPairCylinderEvent_physical
    (half : Nat) (leftSupport rightSupport : List Nat)
    (physical : EdgeLabelling)
    (hsupported : ambientSlabSupportedB (centralExtent half) physical = true) :
    sourceCylinderEvent (centralSlabCanonicalPolymers half)
        (centralSlabSupportPairCylinderPredicate
          half leftSupport rightSupport)
        (physicalCanonicalAmbientFamily (centralAmbient half) physical) =
      decide
        (centralHalfSupportCode half
              (centralLowerRestriction half
                (ambientToSlabPhysical (centralExtent half) physical)) =
            leftSupport ∧
          centralHalfSupportCode half
              (centralReflectedUpperRestriction half
                (ambientToSlabPhysical (centralExtent half) physical)) =
            rightSupport) := by
  unfold centralSlabSupportPairCylinderPredicate
  rw [centralSlabExhaustiveCylinderEvent_eq
    (centralFamilySupportPairEvent half leftSupport rightSupport)
    (physicalCanonicalAmbientFamily_mem_compatible
      (centralAmbient half) physical)
    ((physicalCanonicalAmbientFamily_slabSupported_iff
      (centralExtent half) physical).2 hsupported)]
  unfold centralFamilySupportPairEvent
  rw [centralFamilyLowerSupportCode_physical,
    centralFamilyReflectedUpperSupportCode_physical]

#print axioms physicalCanonicalAmbientFamily_mem_compatible
#print axioms mem_physicalCanonicalAmbientFamily_flatten_iff
#print axioms excitedPlaquetteIds_familyIndicator_physical
#print axioms ambientToSlabPhysical_positive_iff_of_excited_eq
#print axioms centralLowerSupportCode_familyIndicator
#print axioms centralReflectedUpperSupportCode_familyIndicator
#print axioms centralFamilySupportPairCylinderEvent_physical
#print axioms centralSlabCanonicalAtoms_supported
#print axioms centralSlabOccurrenceFingerprint_recovers
#print axioms centralSlabExhaustiveCylinderEvent_eq
#print axioms centralSlabSupportPairCylinderEvent_physical

end YMGap.Continuum.Z4CanonicalFamilyFaceSupportDecoder
