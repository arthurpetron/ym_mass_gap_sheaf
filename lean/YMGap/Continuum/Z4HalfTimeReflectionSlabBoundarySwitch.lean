/-
# Recoverable marked switching across the corrected-slab boundary

This module specializes the finite recoverable marked-component switch to
the anisotropic support event defining the corrected reflection slab.  The
separated branch preserves the boundary/supported cells, swaps every marked
cylinder fingerprint, preserves the exact product weight, and remains
injective.  The connected branch exposes a marked disagreement path ending
at a polymer that hits an omitted top face.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalLaw
import YMGap.Continuum.Z4CanonicalMarkedRootSeparation
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

abbrev PolymerFamily := List (List Nat)

/-! ## 1. Polymerwise form of the slab support event -/

def canonicalPolymerSlabSupportedB
    (extent : Nat) (polymer : List Nat) : Bool :=
  polymer.all fun face =>
    decide (boxPlaquetteAt (extent + 1) face ∈
      boundaryCompleteSlabPlaquettes extent)

theorem canonicalFamilySlabSupportedB_eq_polymerAll
    (extent : Nat) (family : PolymerFamily) :
    canonicalFamilySlabSupportedB extent family =
      family.all (canonicalPolymerSlabSupportedB extent) := by
  unfold canonicalFamilySlabSupportedB canonicalPolymerSlabSupportedB
  rfl

theorem canonicalPolymerSlabSupportedB_false_iff_hit
    (extent : Nat) (polymer : List Nat) :
    canonicalPolymerSlabSupportedB extent polymer = false ↔
      canonicalPolymerHitsSlabComplementB extent polymer = true := by
  constructor
  · intro houtside
    let witness := allFalseWitness
      (fun face => decide (boxPlaquetteAt (extent + 1) face ∈
        boundaryCompleteSlabPlaquettes extent)) polymer houtside
    let face := witness.1
    have hface : face ∈ polymer := witness.2.1
    have htest : decide (boxPlaquetteAt (extent + 1) face ∈
        boundaryCompleteSlabPlaquettes extent) = false := witness.2.2
    unfold canonicalPolymerHitsSlabComplementB geometricPolymer
    apply List.any_eq_true.mpr
    refine ⟨boxPlaquetteAt (extent + 1) face,
      List.mem_map.mpr ⟨face, hface, rfl⟩, ?_⟩
    exact decide_eq_true (of_decide_eq_false htest)
  · intro hhit
    unfold canonicalPolymerHitsSlabComplementB geometricPolymer at hhit
    obtain ⟨q, hq, hqOutside⟩ := List.any_eq_true.mp hhit
    obtain ⟨face, hface, hqEq⟩ := List.mem_map.mp hq
    subst q
    cases hsupported : canonicalPolymerSlabSupportedB extent polymer with
    | false => rfl
    | true =>
        have hinsideDecision := List.all_eq_true.mp hsupported face hface
        exact False.elim
          ((of_decide_eq_true hqOutside)
            (of_decide_eq_true hinsideDecision))

/-! ## 2. Literal supported and boundary family lists -/

def canonicalSlabSupportedFamilies (extent : Nat) :
    List PolymerFamily :=
  (canonicalCompatibleAmbientFamilies (extent + 1)).filter
    (canonicalFamilySlabSupportedB extent)

def canonicalSlabBoundaryFamilies (extent : Nat) :
    List PolymerFamily :=
  (canonicalCompatibleAmbientFamilies (extent + 1)).filter
    (fun family => !(canonicalFamilySlabSupportedB extent family))

theorem mem_canonicalSlabSupportedFamilies_iff
    {extent : Nat} {family : PolymerFamily} :
    family ∈ canonicalSlabSupportedFamilies extent ↔
      family ∈ canonicalCompatibleAmbientFamilies (extent + 1) ∧
        canonicalFamilySlabSupportedB extent family = true := by
  unfold canonicalSlabSupportedFamilies
  exact List.mem_filter

theorem mem_canonicalSlabBoundaryFamilies_iff
    {extent : Nat} {family : PolymerFamily} :
    family ∈ canonicalSlabBoundaryFamilies extent ↔
      family ∈ canonicalCompatibleAmbientFamilies (extent + 1) ∧
        canonicalFamilySlabSupportedB extent family = false := by
  unfold canonicalSlabBoundaryFamilies
  rw [List.mem_filter]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    cases hsupported : canonicalFamilySlabSupportedB extent family <;>
      simp_all
  · intro h
    exact ⟨h.1, by simp [h.2]⟩

theorem canonicalSlabSupportedFamilies_nodup (extent : Nat) :
    (canonicalSlabSupportedFamilies extent).Nodup := by
  unfold canonicalSlabSupportedFamilies
  exact List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup (extent + 1))

theorem canonicalSlabBoundaryFamilies_nodup (extent : Nat) :
    (canonicalSlabBoundaryFamilies extent).Nodup := by
  unfold canonicalSlabBoundaryFamilies
  exact List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup (extent + 1))

def canonicalSlabBoundaryNumerator (extent : Nat) : Q' :=
  listQSum
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (canonicalSlabBoundaryFamilies extent)

/-- Exact canonical full = supported + boundary decomposition. -/
theorem anchorCanonicalPartition_eqv_slabSupport_add_boundary
    (extent : Nat) :
    anchorCanonicalPartition (extent + 1) ≈
      anchorEventNumerator (extent + 1)
          (canonicalFamilySlabSupportedB extent) +
        canonicalSlabBoundaryNumerator extent := by
  unfold anchorCanonicalPartition
    parametricCanonicalCompatibleAmbientPartition
    anchorEventNumerator canonicalSlabBoundaryNumerator
    canonicalSlabBoundaryFamilies
  exact listQSum_filter_partition
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (canonicalFamilySlabSupportedB extent)
    (canonicalCompatibleAmbientFamilies (extent + 1))

/-! ## 3. Slab-specific connected/separated marked reach -/

def slabBoundaryOutsideMarkedReachB
    {extent : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (roots : List (CanonicalAtom (extent + 1))) : Bool :=
  (canonicalFamilyAtoms hleft).any (fun atom =>
    (!(canonicalPolymerSlabSupportedB extent atom.val)) &&
      canonicalMarkedCut hleft hright roots atom)

theorem slabBoundaryOutsideMarkedReachB_false_separated
    {extent : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (roots : List (CanonicalAtom (extent + 1)))
    (hreach : slabBoundaryOutsideMarkedReachB
      hleft hright roots = false) :
    ∀ atom : CanonicalAtom (extent + 1), atom.val ∈ left →
      canonicalPolymerSlabSupportedB extent atom.val = false →
        canonicalMarkedCut hleft hright roots atom = false := by
  intro atom hatom houtside
  cases hcut : canonicalMarkedCut hleft hright roots atom with
  | false => rfl
  | true =>
      have hatomList : atom ∈ canonicalFamilyAtoms hleft :=
        (canonicalFamilyAtom_mem_iff hleft atom).2 hatom
      have hterm :
          ((!(canonicalPolymerSlabSupportedB extent atom.val)) &&
            canonicalMarkedCut hleft hright roots atom) = true := by
        simp [houtside, hcut]
      have hany : (canonicalFamilyAtoms hleft).any (fun found =>
          (!(canonicalPolymerSlabSupportedB extent found.val)) &&
            canonicalMarkedCut hleft hright roots found) = true :=
        List.any_eq_true.mpr ⟨atom, hatomList, hterm⟩
      unfold slabBoundaryOutsideMarkedReachB at hreach
      rw [hreach] at hany
      exact False.elim (Bool.false_ne_true hany)

theorem slabBoundaryOutsideMarkedReachB_true_root_witness
    {extent : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (roots : List (CanonicalAtom (extent + 1)))
    (hreach : slabBoundaryOutsideMarkedReachB
      hleft hright roots = true) :
    ∃ root outside : CanonicalAtom (extent + 1),
      root ∈ roots ∧ outside.val ∈ left ∧
        canonicalPolymerHitsSlabComplementB extent outside.val = true ∧
          canonicalDisagreementCut hleft hright root outside = true := by
  unfold slabBoundaryOutsideMarkedReachB at hreach
  obtain ⟨outside, houtsideAtoms, hterm⟩ := List.any_eq_true.mp hreach
  have hparts := (Bool.and_eq_true _ _).mp hterm
  have houtside : canonicalPolymerSlabSupportedB
      extent outside.val = false := by
    cases hsupported : canonicalPolymerSlabSupportedB
      extent outside.val <;> simp_all
  obtain ⟨root, hroot, hrootReach⟩ :=
    canonicalMarkedCut_true_has_root hleft hright roots outside hparts.2
  exact ⟨root, outside, hroot,
    (canonicalFamilyAtom_mem_iff hleft outside).1 houtsideAtoms,
    (canonicalPolymerSlabSupportedB_false_iff_hit
      extent outside.val).1 houtside,
    hrootReach⟩

/-! ## 4. The separated switch preserves the two slab cells -/

theorem recoverableMarkedSwitchedRightFamily_mem_slabSupported_of_separated
    {extent : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (hrightSupported : right ∈ canonicalSlabSupportedFamilies extent)
    (roots : List (CanonicalAtom (extent + 1)))
    (hseparated : ∀ atom : CanonicalAtom (extent + 1),
      atom.val ∈ left →
        canonicalPolymerSlabSupportedB extent atom.val = false →
          canonicalMarkedCut hleft
            (mem_canonicalSlabSupportedFamilies_iff.mp
              hrightSupported).1 roots atom = false) :
    recoverableMarkedSwitchedRightFamily hleft
        (mem_canonicalSlabSupportedFamilies_iff.mp hrightSupported).1
        roots ∈ canonicalSlabSupportedFamilies extent := by
  let hright :=
    (mem_canonicalSlabSupportedFamilies_iff.mp hrightSupported).1
  have houtCompat :=
    (recoverableMarkedSwitchedFamilies_mem_compatible
      hleft hright roots).2
  apply mem_canonicalSlabSupportedFamilies_iff.mpr
  refine ⟨houtCompat, ?_⟩
  rw [canonicalFamilySlabSupportedB_eq_polymerAll]
  apply List.all_eq_true.mpr
  intro support hsupport
  unfold recoverableMarkedSwitchedRightFamily at hsupport
  obtain ⟨atom, hatom, hatomValue⟩ := List.mem_map.mp hsupport
  subst support
  have htest := (mem_recoverableMarkedSwitchedRightAtoms_iff
    hleft hright roots atom).1 hatom
  cases hcut : canonicalMarkedCut hleft hright roots atom with
  | false =>
      have hrightAtom : atom ∈ canonicalFamilyAtoms hright := by
        have hmemberB : memberB (canonicalFamilyAtoms hright) atom = true := by
          simpa [switchedRightB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      have hrightRaw : atom.val ∈ right :=
        (canonicalFamilyAtom_mem_iff hright atom).1 hrightAtom
      have hrightAll : right.all
          (canonicalPolymerSlabSupportedB extent) = true := by
        rw [← canonicalFamilySlabSupportedB_eq_polymerAll]
        exact (mem_canonicalSlabSupportedFamilies_iff.mp
          hrightSupported).2
      exact List.all_eq_true.mp
        hrightAll atom.val hrightRaw
  | true =>
      have hleftAtom : atom ∈ canonicalFamilyAtoms hleft := by
        have hmemberB : memberB (canonicalFamilyAtoms hleft) atom = true := by
          simpa [switchedRightB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      have hleftRaw : atom.val ∈ left :=
        (canonicalFamilyAtom_mem_iff hleft atom).1 hleftAtom
      cases hinside : canonicalPolymerSlabSupportedB extent atom.val with
      | true => rfl
      | false =>
          have hnotReach := hseparated atom hleftRaw hinside
          rw [hnotReach] at hcut
          exact False.elim (Bool.false_ne_true hcut)

theorem outside_support_mem_recoverableMarkedSwitchedLeft_of_slabSeparated
    {extent : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (roots : List (CanonicalAtom (extent + 1)))
    {outside : List Nat} (houtside : outside ∈ left)
    (houtsideRegion : canonicalPolymerSlabSupportedB
      extent outside = false)
    (hseparated : ∀ atom : CanonicalAtom (extent + 1),
      atom.val ∈ left →
        canonicalPolymerSlabSupportedB extent atom.val = false →
          canonicalMarkedCut hleft hright roots atom = false) :
    outside ∈ recoverableMarkedSwitchedLeftFamily
      hleft hright roots := by
  let outsideAtom : CanonicalAtom (extent + 1) :=
    ⟨outside, compatibleAmbientFamily_member_ambient hleft houtside⟩
  have houtsideAtom : outsideAtom ∈ canonicalFamilyAtoms hleft :=
    (canonicalFamilyAtom_mem_iff hleft outsideAtom).2 houtside
  have hcut : canonicalMarkedCut hleft hright roots outsideAtom = false :=
    hseparated outsideAtom houtside houtsideRegion
  have hleftB : memberB (canonicalFamilyAtoms hleft) outsideAtom = true :=
    (memberB_eq_true_iff _ _).2 houtsideAtom
  have houtAtoms : outsideAtom ∈
      recoverableMarkedSwitchedLeftAtoms hleft hright roots := by
    apply (mem_recoverableMarkedSwitchedLeftAtoms_iff
      hleft hright roots outsideAtom).2
    simp [switchedLeftB, hcut, hleftB]
  unfold recoverableMarkedSwitchedLeftFamily
  exact (canonicalAtom_value_mem_values_iff _ outsideAtom).2 houtAtoms

theorem recoverableMarkedSwitchedLeftFamily_mem_slabBoundary_of_separated
    {extent : Nat} {left right : PolymerFamily}
    (hleftBoundary : left ∈ canonicalSlabBoundaryFamilies extent)
    (hright : right ∈ canonicalCompatibleAmbientFamilies (extent + 1))
    (roots : List (CanonicalAtom (extent + 1)))
    (hseparated : ∀ atom : CanonicalAtom (extent + 1),
      atom.val ∈ left →
        canonicalPolymerSlabSupportedB extent atom.val = false →
          canonicalMarkedCut
            (mem_canonicalSlabBoundaryFamilies_iff.mp hleftBoundary).1
            hright roots atom = false) :
    recoverableMarkedSwitchedLeftFamily
        (mem_canonicalSlabBoundaryFamilies_iff.mp hleftBoundary).1
        hright roots ∈ canonicalSlabBoundaryFamilies extent := by
  let hleft :=
    (mem_canonicalSlabBoundaryFamilies_iff.mp hleftBoundary).1
  have hleftFalse :=
    (mem_canonicalSlabBoundaryFamilies_iff.mp hleftBoundary).2
  rw [canonicalFamilySlabSupportedB_eq_polymerAll] at hleftFalse
  let witness := allFalseWitness
    (canonicalPolymerSlabSupportedB extent) left hleftFalse
  let outside := witness.1
  have houtside : outside ∈ left := witness.2.1
  have houtsideRegion : canonicalPolymerSlabSupportedB
      extent outside = false := witness.2.2
  have houtsideOutput : outside ∈
      recoverableMarkedSwitchedLeftFamily hleft hright roots :=
    outside_support_mem_recoverableMarkedSwitchedLeft_of_slabSeparated
      hleft hright roots houtside houtsideRegion hseparated
  have houtCompat :=
    (recoverableMarkedSwitchedFamilies_mem_compatible
      hleft hright roots).1
  apply mem_canonicalSlabBoundaryFamilies_iff.mpr
  refine ⟨houtCompat, ?_⟩
  rw [canonicalFamilySlabSupportedB_eq_polymerAll]
  cases houtAll : (recoverableMarkedSwitchedLeftFamily
      hleft hright roots).all (canonicalPolymerSlabSupportedB extent) with
  | false => rfl
  | true =>
      have hinside := List.all_eq_true.mp houtAll outside houtsideOutput
      rw [houtsideRegion] at hinside
      exact False.elim (Bool.false_ne_true hinside)

/-- Complete separated-branch package used by the finite four-cell
summation: cell preservation, marked-event swap, and exact weight
preservation. -/
theorem separated_recoverable_slab_switch
    (w : Q') {extent : Nat} {left right : PolymerFamily}
    (hleftBoundary : left ∈ canonicalSlabBoundaryFamilies extent)
    (hrightSupported : right ∈ canonicalSlabSupportedFamilies extent)
    (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool)
    (hseparated : ∀ atom : CanonicalAtom (extent + 1),
      atom.val ∈ left →
        canonicalPolymerSlabSupportedB extent atom.val = false →
          canonicalMarkedCut
            (mem_canonicalSlabBoundaryFamilies_iff.mp hleftBoundary).1
            (mem_canonicalSlabSupportedFamilies_iff.mp hrightSupported).1
            roots atom = false) :
    let hleft :=
      (mem_canonicalSlabBoundaryFamilies_iff.mp hleftBoundary).1
    let hright :=
      (mem_canonicalSlabSupportedFamilies_iff.mp hrightSupported).1
    recoverableMarkedSwitchedLeftFamily hleft hright roots ∈
        canonicalSlabBoundaryFamilies extent ∧
      recoverableMarkedSwitchedRightFamily hleft hright roots ∈
        canonicalSlabSupportedFamilies extent ∧
      cylinderEvent (roots.map Subtype.val) predicate
          (recoverableMarkedSwitchedLeftFamily hleft hright roots) =
        cylinderEvent (roots.map Subtype.val) predicate right ∧
      cylinderEvent (roots.map Subtype.val) predicate
          (recoverableMarkedSwitchedRightFamily hleft hright roots) =
        cylinderEvent (roots.map Subtype.val) predicate left ∧
      canonicalSurfaceFamilyActivity w (extent + 1)
          (recoverableMarkedSwitchedLeftFamily hleft hright roots) *
        canonicalSurfaceFamilyActivity w (extent + 1)
          (recoverableMarkedSwitchedRightFamily hleft hright roots) ≈
      canonicalSurfaceFamilyActivity w (extent + 1) left *
        canonicalSurfaceFamilyActivity w (extent + 1) right := by
  dsimp only
  let hleft :=
    (mem_canonicalSlabBoundaryFamilies_iff.mp hleftBoundary).1
  let hright :=
    (mem_canonicalSlabSupportedFamilies_iff.mp hrightSupported).1
  have hleftOut :=
    recoverableMarkedSwitchedLeftFamily_mem_slabBoundary_of_separated
      hleftBoundary hright roots hseparated
  have hrightOut :=
    recoverableMarkedSwitchedRightFamily_mem_slabSupported_of_separated
      hleft hrightSupported roots hseparated
  have hevents := recoverableMarkedSwitchedFamilies_cylinderEvent_swap
    hleft hright roots predicate
  have hweight := recoverableMarkedSwitchedFamilies_weight_preserved
    w hleft hright roots
  exact ⟨hleftOut, hrightOut, hevents.1, hevents.2, hweight⟩

#print axioms canonicalPolymerSlabSupportedB_false_iff_hit
#print axioms mem_canonicalSlabSupportedFamilies_iff
#print axioms mem_canonicalSlabBoundaryFamilies_iff
#print axioms anchorCanonicalPartition_eqv_slabSupport_add_boundary
#print axioms slabBoundaryOutsideMarkedReachB_false_separated
#print axioms slabBoundaryOutsideMarkedReachB_true_root_witness
#print axioms recoverableMarkedSwitchedRightFamily_mem_slabSupported_of_separated
#print axioms recoverableMarkedSwitchedLeftFamily_mem_slabBoundary_of_separated
#print axioms separated_recoverable_slab_switch

end YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
