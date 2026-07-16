/-
# Cutoff-one canonical event for corrected-slab support

The ambient image theorem phrases corrected-slab support on physical face
labellings.  The strong-coupling switching and cylinder machinery instead
uses compatible families of canonical connected polymers.  At cutoff one the
canonical component family covers exactly the excited physical support, so
the two support predicates agree pointwise.  This file proves that bridge and
the resulting exact anchor event-numerator identity.
-/

import YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
import YMGap.Continuum.Z4CutoffOneEventBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabAmbientImage
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The literal canonical-family support event -/

/-- Every face identifier of every occupied connected polymer decodes to a
plaquette retained by the corrected slab. -/
def canonicalFamilySlabSupportedB
    (extent : Nat) (family : List (List Nat)) : Bool :=
  family.all fun polymer =>
    polymer.all fun face =>
      decide (boxPlaquetteAt (extent + 1) face ∈
        boundaryCompleteSlabPlaquettes extent)

theorem canonicalFamilySlabSupportedB_true_iff
    (extent : Nat) (family : List (List Nat)) :
    canonicalFamilySlabSupportedB extent family = true ↔
      ∀ polymer, polymer ∈ family → ∀ face, face ∈ polymer →
        boxPlaquetteAt (extent + 1) face ∈
          boundaryCompleteSlabPlaquettes extent := by
  unfold canonicalFamilySlabSupportedB
  constructor
  · intro hfamily polymer hpolymer face hface
    have hpolymerAll := List.all_eq_true.mp hfamily polymer hpolymer
    exact of_decide_eq_true
      (List.all_eq_true.mp hpolymerAll face hface)
  · intro hsupport
    apply List.all_eq_true.mpr
    intro polymer hpolymer
    apply List.all_eq_true.mpr
    intro face hface
    exact decide_eq_true (hsupport polymer hpolymer face hface)

/-! ## 2. Exact pointwise equivalence with physical support -/

theorem physicalCanonicalAmbientFamily_slabSupported_iff
    (extent : Nat) (physical : EdgeLabelling) :
    canonicalFamilySlabSupportedB extent
        (physicalCanonicalAmbientFamily (extent + 1) physical) = true ↔
      ambientSlabSupportedB extent physical = true := by
  let n := extent + 1
  let support := excitedPlaquetteIds n physical
  have hsupport : support ∈ cutoffOneFaceSupports n := by
    unfold support excitedPlaquetteIds cutoffOneFaceSupports
    exact filter_mem_sublists _ _
  let components := canonicalSurfaceFamily n support
  have hgas : components ∈ canonicalConnectedSurfaceGas n := by
    unfold components canonicalConnectedSurfaceGas
    exact List.mem_map.mpr ⟨support, hsupport, rfl⟩
  have hcover : Covers support components := by
    unfold components
    exact canonicalSurfaceFamily_covers hsupport
  have hordered : ∀ polymer,
      polymer ∈ ambientOrderedFamily n components ↔
        polymer ∈ components :=
    gasFamily_mem_ambientOrderedFamily_iff hgas
  have hphysicalFamily :
      physicalCanonicalAmbientFamily n physical =
        ambientOrderedFamily n components := by
    rfl
  constructor
  · intro hcanonical
    apply (ambientSlabSupportedB_true_iff_excited_support
      extent physical).2
    intro face hface
    have hfaceSupport : face ∈ support := hface
    obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
      (hcover face).1 hfaceSupport
    have hpolymerOrdered := (hordered polymer).2 hpolymer
    have hpredicate :=
      (canonicalFamilySlabSupportedB_true_iff extent
        (physicalCanonicalAmbientFamily n physical)).1 hcanonical
    exact hpredicate polymer (by
      rw [hphysicalFamily]
      exact hpolymerOrdered) face hfacePolymer
  · intro hphysical
    apply (canonicalFamilySlabSupportedB_true_iff extent
      (physicalCanonicalAmbientFamily n physical)).2
    intro polymer hpolymer face hface
    have hpolymerOrdered : polymer ∈ ambientOrderedFamily n components := by
      rw [← hphysicalFamily]
      exact hpolymer
    have hpolymerComponent := (hordered polymer).1 hpolymerOrdered
    have hfaceSupport : face ∈ support :=
      (hcover face).2 ⟨polymer, hpolymerComponent, hface⟩
    exact (ambientSlabSupportedB_true_iff_excited_support
      extent physical).1 hphysical face hfaceSupport

theorem cutoffOneLiftedSlabEvent_eq_physical
    (extent : Nat) :
    cutoffOneLiftedFamilyEvent (extent + 1)
        (canonicalFamilySlabSupportedB extent) =
      ambientSlabSupportedB extent := by
  funext physical
  apply Bool.eq_iff_iff.mpr
  exact physicalCanonicalAmbientFamily_slabSupported_iff extent physical

/-- Intersection of an arbitrary canonical cylinder event with corrected-slab
support. -/
def canonicalSlabRestrictedEvent
    (extent : Nat) (event : List (List Nat) → Bool) :
    List (List Nat) → Bool :=
  fun family => canonicalFamilySlabSupportedB extent family && event family

theorem cutoffOneLiftedSlabRestrictedEvent_eq_physical
    (extent : Nat) (event : List (List Nat) → Bool) :
    cutoffOneLiftedFamilyEvent (extent + 1)
        (canonicalSlabRestrictedEvent extent event) =
      (fun physical => ambientSlabSupportedB extent physical &&
        cutoffOneLiftedFamilyEvent (extent + 1) event physical) := by
  funext physical
  unfold cutoffOneLiftedFamilyEvent canonicalSlabRestrictedEvent
  have hsupport : canonicalFamilySlabSupportedB extent
      (physicalCanonicalAmbientFamily (extent + 1) physical) =
        ambientSlabSupportedB extent physical := by
    apply Bool.eq_iff_iff.mpr
    exact physicalCanonicalAmbientFamily_slabSupported_iff extent physical
  rw [hsupport]

/-! ## 3. Exact anchor numerator identity -/

/-- The anchor cutoff-one numerator of the physical corrected-slab support
event is exactly the canonical compatible-gas support numerator. -/
theorem anchorPhysicalSlabSupportNumerator_eqv_canonical
    (extent : Nat) :
    parametricKEventNumerator anchorCoupling 1 (extent + 1)
        (ambientSlabSupportedB extent) ≈
      anchorEventNumerator (extent + 1)
        (canonicalFamilySlabSupportedB extent) := by
  rw [← cutoffOneLiftedSlabEvent_eq_physical extent]
  exact anchorParametricKEventNumerator_one_eqv_anchorEventNumerator
    (extent + 1) (canonicalFamilySlabSupportedB extent)

/-- The same exact bridge with an arbitrary canonical event retained inside
the corrected-slab support condition. -/
theorem anchorPhysicalSlabRestrictedNumerator_eqv_canonical
    (extent : Nat) (event : List (List Nat) → Bool) :
    parametricKEventNumerator anchorCoupling 1 (extent + 1)
        (fun physical => ambientSlabSupportedB extent physical &&
          cutoffOneLiftedFamilyEvent (extent + 1) event physical) ≈
      anchorEventNumerator (extent + 1)
        (canonicalSlabRestrictedEvent extent event) := by
  rw [← cutoffOneLiftedSlabRestrictedEvent_eq_physical extent event]
  exact anchorParametricKEventNumerator_one_eqv_anchorEventNumerator
    (extent + 1) (canonicalSlabRestrictedEvent extent event)

#print axioms canonicalFamilySlabSupportedB_true_iff
#print axioms physicalCanonicalAmbientFamily_slabSupported_iff
#print axioms cutoffOneLiftedSlabEvent_eq_physical
#print axioms cutoffOneLiftedSlabRestrictedEvent_eq_physical
#print axioms anchorPhysicalSlabSupportNumerator_eqv_canonical
#print axioms anchorPhysicalSlabRestrictedNumerator_eqv_canonical

end YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
