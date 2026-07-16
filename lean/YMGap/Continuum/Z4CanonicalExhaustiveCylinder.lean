/-
# Exhaustive finite canonical cylinder fingerprints

At a fixed finite volume, the occurrence fingerprint against the complete
ordered canonical-polymer list remembers an entire compatible support family.
This module gives an explicit decoder and proves exact recovery.  Consequently
every Boolean event, and every exact rational observable, on finite compatible
support families factors through one finite cylinder fingerprint.

This is a finite support-carrier theorem.  It deliberately does not claim that
spin-sensitive edge-labelling observables factor through support occurrence
bits.
-/

import YMGap.Continuum.FiniteCompatibilitySwitching
import YMGap.Continuum.Z4CanonicalCylinderEventTransport

namespace YMGap.Continuum.Z4CanonicalExhaustiveCylinder

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection

/-! ## A total decoder for ordinary Boolean lists -/

/-- Select entries of an ambient list using an ordinary Boolean list.  A
length mismatch is totalized by stopping when either list ends. -/
def selectByBoolFingerprint {A : Type} : List A → List Bool → List A
  | [], _ => []
  | _, [] => []
  | item :: rest, bit :: bits =>
      if bit then item :: selectByBoolFingerprint rest bits
      else selectByBoolFingerprint rest bits

@[simp] theorem selectByBoolFingerprint_nil_left {A : Type}
    (bits : List Bool) :
    selectByBoolFingerprint ([] : List A) bits = [] := rfl

@[simp] theorem selectByBoolFingerprint_nil_right {A : Type}
    (ambient : List A) :
    selectByBoolFingerprint ambient [] = [] := by
  cases ambient <;> rfl

@[simp] theorem selectByBoolFingerprint_cons_false {A : Type}
    (item : A) (ambient : List A) (bits : List Bool) :
    selectByBoolFingerprint (item :: ambient) (false :: bits) =
      selectByBoolFingerprint ambient bits := rfl

@[simp] theorem selectByBoolFingerprint_cons_true {A : Type}
    (item : A) (ambient : List A) (bits : List Bool) :
    selectByBoolFingerprint (item :: ambient) (true :: bits) =
      item :: selectByBoolFingerprint ambient bits := rfl

/-! ## Exact recovery of compatible canonical support families -/

/-- Decoding an occurrence fingerprint is exactly filtering its root list by
membership in the family. -/
theorem selectByBoolFingerprint_occurrence_eq_filter :
    ∀ (roots family : List (List Nat)),
      selectByBoolFingerprint roots
          (familyOccurrenceFingerprint roots family) =
        roots.filter (fun root => familyContainsPolymerB root family)
  | [], family => rfl
  | root :: roots, family => by
      simp only [familyOccurrenceFingerprint, List.map_cons]
      cases hcontains : familyContainsPolymerB root family
      · simp only [selectByBoolFingerprint_cons_false, List.filter_cons,
          hcontains, Bool.false_eq_true, ↓reduceIte]
        exact selectByBoolFingerprint_occurrence_eq_filter roots family
      · simp only [selectByBoolFingerprint_cons_true, List.filter_cons,
          hcontains, ↓reduceIte, List.cons.injEq, true_and]
        exact selectByBoolFingerprint_occurrence_eq_filter roots family

/-- The exhaustive canonical fingerprint reconstructs every compatible
ambient family literally, including the canonical ambient ordering. -/
theorem exhaustiveOccurrenceFingerprint_recovers
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    selectByBoolFingerprint (canonicalSurfacePolymers n)
        (familyOccurrenceFingerprint (canonicalSurfacePolymers n) family) =
      family := by
  rw [selectByBoolFingerprint_occurrence_eq_filter]
  apply sublists_eq_of_mem_iff
    (canonicalSurfacePolymers n) _ family
    (canonicalSurfacePolymers_nodup n)
    (filter_mem_sublists _ _)
    (compatibleAmbientFamily_sublist hfamily)
  intro polymer
  constructor
  · intro hfiltered
    have htest := (List.mem_filter.mp hfiltered).2
    unfold familyContainsPolymerB at htest
    exact of_decide_eq_true htest
  · intro hpolymer
    apply List.mem_filter.mpr
    refine ⟨mem_of_mem_sublists
      (canonicalSurfacePolymers n) family
      (compatibleAmbientFamily_sublist hfamily) polymer hpolymer, ?_⟩
    unfold familyContainsPolymerB
    exact decide_eq_true hpolymer

/-! ## Every finite support observable is a cylinder observable -/

/-- Cylinder predicate obtained by decoding the complete finite fingerprint
and applying an arbitrary support-family event. -/
def exhaustiveCylinderPredicate (n : Nat)
    (event : List (List Nat) → Bool) (bits : List Bool) : Bool :=
  event (selectByBoolFingerprint (canonicalSurfacePolymers n) bits)

/-- On every compatible family, the exhaustive cylinder event is literally
the original arbitrary Boolean family event. -/
theorem exhaustiveCylinderEvent_eq
    {n : Nat} (event : List (List Nat) → Bool)
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    sourceCylinderEvent (canonicalSurfacePolymers n)
        (exhaustiveCylinderPredicate n event) family = event family := by
  unfold sourceCylinderEvent cylinderEvent exhaustiveCylinderPredicate
  rw [exhaustiveOccurrenceFingerprint_recovers hfamily]

/-- Rational-valued analogue of `exhaustiveCylinderPredicate`. -/
def exhaustiveCylinderValue (n : Nat)
    (value : List (List Nat) → Q') (bits : List Bool) : Q' :=
  value (selectByBoolFingerprint (canonicalSurfacePolymers n) bits)

/-- Every exact rational observable on compatible finite support families is
recovered from the exhaustive occurrence fingerprint. -/
theorem exhaustiveCylinderValue_eq
    {n : Nat} (value : List (List Nat) → Q')
    {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    exhaustiveCylinderValue n value
        (familyOccurrenceFingerprint (canonicalSurfacePolymers n) family) =
      value family := by
  unfold exhaustiveCylinderValue
  rw [exhaustiveOccurrenceFingerprint_recovers hfamily]

/-- Equality of exhaustive fingerprints is injective on compatible canonical
families. -/
theorem exhaustiveOccurrenceFingerprint_injective_on
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (heq : familyOccurrenceFingerprint (canonicalSurfacePolymers n) left =
      familyOccurrenceFingerprint (canonicalSurfacePolymers n) right) :
    left = right := by
  have hdecode := congrArg
    (selectByBoolFingerprint (canonicalSurfacePolymers n)) heq
  rw [exhaustiveOccurrenceFingerprint_recovers hleft,
    exhaustiveOccurrenceFingerprint_recovers hright] at hdecode
  exact hdecode

#print axioms selectByBoolFingerprint_occurrence_eq_filter
#print axioms exhaustiveOccurrenceFingerprint_recovers
#print axioms exhaustiveCylinderEvent_eq
#print axioms exhaustiveCylinderValue_eq
#print axioms exhaustiveOccurrenceFingerprint_injective_on

end YMGap.Continuum.Z4CanonicalExhaustiveCylinder
