/-
# Canonical finite-cylinder component switch

This module instantiates the simultaneous marked-root switch for the exact
cutoff-one canonical surface gas.  The output families remain canonical and
compatible, their pair activity is preserved exactly, the source-dependent
map is injective, and the full finite occurrence fingerprint is swapped.
-/

import YMGap.Continuum.FiniteMarkedRootSwitch
import YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
import YMGap.Continuum.Z4CanonicalCylinderEventTransport

namespace YMGap.Continuum.Z4CanonicalMarkedRootSwitch

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteMarkedRootSwitch
open YMGap.Continuum.FiniteRootedSwitchFingerprint
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection

local infix:50 " ≈ " => Q'.eqv

/-- Turn a finite list of certified canonical polymer values into the
corresponding proof-carrying atom list without choice. -/
def canonicalAtomsOfRoots {n : Nat} :
    (roots : List (List Nat)) →
      (∀ root, root ∈ roots → root ∈ canonicalSurfacePolymers n) →
        List (CanonicalAtom n)
  | [], _ => []
  | root :: roots, hroots =>
      ⟨root, hroots root List.mem_cons_self⟩ ::
        canonicalAtomsOfRoots roots
          (fun tailRoot htail =>
            hroots tailRoot (List.mem_cons_of_mem root htail))

theorem canonicalAtomsOfRoots_values {n : Nat} :
    ∀ (roots : List (List Nat))
      (hroots : ∀ root, root ∈ roots →
        root ∈ canonicalSurfacePolymers n),
      (canonicalAtomsOfRoots roots hroots).map Subtype.val = roots
  | [], _ => rfl
  | root :: roots, hroots => by
      simp only [canonicalAtomsOfRoots, List.map_cons]
      exact congrArg (List.cons root)
        (canonicalAtomsOfRoots_values roots
          (fun tailRoot htail =>
            hroots tailRoot (List.mem_cons_of_mem root htail)))

def canonicalMarkedCut
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) : CanonicalAtom n → Bool :=
  markedRootCut (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n) roots
    (memberB (canonicalFamilyAtoms hleft))
    (memberB (canonicalFamilyAtoms hright))

def recoverableMarkedSwitchedLeftAtoms
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) : List (CanonicalAtom n) :=
  markedRootComponentSwitchedLeft (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n) roots
    (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)

def recoverableMarkedSwitchedRightAtoms
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) : List (CanonicalAtom n) :=
  markedRootComponentSwitchedRight (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n) roots
    (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)

/-- The union cut is closed across every occupied cross-family
incompatibility. -/
theorem canonicalMarkedCut_closed
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n))
    {leftAtom rightAtom : CanonicalAtom n}
    (hleftAtom : leftAtom ∈ canonicalFamilyAtoms hleft)
    (hrightAtom : rightAtom ∈ canonicalFamilyAtoms hright)
    (hincompatible :
      canonicalAtomCompatibleB n leftAtom rightAtom = false) :
    canonicalMarkedCut hleft hright roots leftAtom =
      canonicalMarkedCut hleft hright roots rightAtom := by
  unfold canonicalMarkedCut markedRootCut
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hleftReach
    obtain ⟨root, hroot, hreach⟩ := List.any_eq_true.mp hleftReach
    apply List.any_eq_true.mpr
    refine ⟨root, hroot, ?_⟩
    have hclosed := canonicalDisagreementCut_closed
      hleft hright root hleftAtom hrightAtom hincompatible
    unfold canonicalDisagreementCut at hclosed
    rw [← hclosed]
    exact hreach
  · intro hrightReach
    obtain ⟨root, hroot, hreach⟩ := List.any_eq_true.mp hrightReach
    apply List.any_eq_true.mpr
    refine ⟨root, hroot, ?_⟩
    have hclosed := canonicalDisagreementCut_closed
      hleft hright root hleftAtom hrightAtom hincompatible
    unfold canonicalDisagreementCut at hclosed
    rw [hclosed]
    exact hreach

theorem recoverableMarkedSwitchedAtoms_compatible
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    familyCompatibleB (canonicalAtomCompatibleB n)
        (recoverableMarkedSwitchedLeftAtoms hleft hright roots) = true ∧
      familyCompatibleB (canonicalAtomCompatibleB n)
        (recoverableMarkedSwitchedRightAtoms hleft hright roots) = true := by
  exact switched_pair_compatible (canonicalAtomCompatibleB n)
    (canonicalAtomCompatibleB_symm n)
    (canonicalMarkedCut hleft hright roots)
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_compatible hleft)
    (canonicalFamilyAtoms_compatible hright)
    (fun leftAtom hleftAtom rightAtom hrightAtom hincompatible =>
      canonicalMarkedCut_closed hleft hright roots
        hleftAtom hrightAtom hincompatible)

theorem recoverableMarkedSwitchedAtoms_weight_preserved
    (w : Q') {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (recoverableMarkedSwitchedLeftAtoms hleft hright roots) *
      familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (recoverableMarkedSwitchedRightAtoms hleft hright roots) ≈
    familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (canonicalFamilyAtoms hleft) *
      familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (canonicalFamilyAtoms hright) := by
  unfold recoverableMarkedSwitchedLeftAtoms
    recoverableMarkedSwitchedRightAtoms
  exact markedRootComponentSwitched_pair_weight_preserved
    (fun atom : CanonicalAtom n => canonicalSurfaceActivity w n atom.val)
    (canonicalAtomCompatibleB n) roots
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_mem_sublists hleft)
    (canonicalFamilyAtoms_mem_sublists hright)

def recoverableMarkedSwitchedLeftFamily
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) : List (List Nat) :=
  (recoverableMarkedSwitchedLeftAtoms hleft hright roots).map Subtype.val

def recoverableMarkedSwitchedRightFamily
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) : List (List Nat) :=
  (recoverableMarkedSwitchedRightAtoms hleft hright roots).map Subtype.val

private theorem markedAtomList_all_values {n : Nat}
    (test : List Nat → Bool) :
    ∀ atoms : List (CanonicalAtom n),
      atoms.all (fun atom => test atom.val) =
        (atoms.map Subtype.val).all test
  | [] => rfl
  | _ :: rest => by
      simp only [List.all_cons, List.map]
      rw [markedAtomList_all_values test rest]

private theorem markedAtomList_compatible_eq {n : Nat} :
    ∀ atoms : List (CanonicalAtom n),
      familyCompatibleB (canonicalAtomCompatibleB n) atoms =
        familyCompatibleB (canonicalPolymerCompatibleB n)
          (atoms.map Subtype.val)
  | [] => rfl
  | head :: rest => by
      change
        (rest.all (fun atom =>
            canonicalPolymerCompatibleB n head.val atom.val) &&
          familyCompatibleB (canonicalAtomCompatibleB n) rest) =
        ((rest.map Subtype.val).all
            (canonicalPolymerCompatibleB n head.val) &&
          familyCompatibleB (canonicalPolymerCompatibleB n)
            (rest.map Subtype.val))
      rw [markedAtomList_all_values
        (canonicalPolymerCompatibleB n head.val) rest]
      rw [markedAtomList_compatible_eq rest]

private theorem markedAtomList_weight_eq (w : Q') (n : Nat) :
    ∀ atoms : List (CanonicalAtom n),
      familyWeight (fun atom : CanonicalAtom n =>
          canonicalSurfaceActivity w n atom.val) atoms =
        canonicalSurfaceFamilyActivity w n
          (atoms.map Subtype.val)
  | [] => rfl
  | _ :: rest => by
      simp only [familyWeight_cons, List.map,
        canonicalSurfaceFamilyActivity]
      rw [markedAtomList_weight_eq w n rest]

theorem recoverableMarkedSwitchedFamilies_mem_compatible
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    recoverableMarkedSwitchedLeftFamily hleft hright roots ∈
        canonicalCompatibleAmbientFamilies n ∧
      recoverableMarkedSwitchedRightFamily hleft hright roots ∈
        canonicalCompatibleAmbientFamilies n := by
  have hatomCompat :=
    recoverableMarkedSwitchedAtoms_compatible hleft hright roots
  constructor
  · unfold canonicalCompatibleAmbientFamilies
    apply List.mem_filter.mpr
    constructor
    · have hsub := map_mem_sublists Subtype.val
          (canonicalAmbientAtoms n)
          (recoverableMarkedSwitchedLeftAtoms hleft hright roots)
          (switchedLeft_mem_sublists (canonicalAmbientAtoms n)
            (canonicalMarkedCut hleft hright roots)
            (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright))
      rw [canonicalAmbientAtoms_values] at hsub
      exact hsub
    · have hgeneric : familyCompatibleB
          (canonicalPolymerCompatibleB n)
          (recoverableMarkedSwitchedLeftFamily hleft hright roots) = true := by
        unfold recoverableMarkedSwitchedLeftFamily
        rw [← markedAtomList_compatible_eq]
        exact hatomCompat.1
      rw [genericFamilyCompatibleB_eq_canonical n] at hgeneric
      exact hgeneric
  · unfold canonicalCompatibleAmbientFamilies
    apply List.mem_filter.mpr
    constructor
    · have hsub := map_mem_sublists Subtype.val
          (canonicalAmbientAtoms n)
          (recoverableMarkedSwitchedRightAtoms hleft hright roots)
          (switchedRight_mem_sublists (canonicalAmbientAtoms n)
            (canonicalMarkedCut hleft hright roots)
            (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright))
      rw [canonicalAmbientAtoms_values] at hsub
      exact hsub
    · have hgeneric : familyCompatibleB
          (canonicalPolymerCompatibleB n)
          (recoverableMarkedSwitchedRightFamily hleft hright roots) = true := by
        unfold recoverableMarkedSwitchedRightFamily
        rw [← markedAtomList_compatible_eq]
        exact hatomCompat.2
      rw [genericFamilyCompatibleB_eq_canonical n] at hgeneric
      exact hgeneric

theorem recoverableMarkedSwitchedFamilies_weight_preserved
    (w : Q') {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    canonicalSurfaceFamilyActivity w n
        (recoverableMarkedSwitchedLeftFamily hleft hright roots) *
      canonicalSurfaceFamilyActivity w n
        (recoverableMarkedSwitchedRightFamily hleft hright roots) ≈
    canonicalSurfaceFamilyActivity w n left *
      canonicalSurfaceFamilyActivity w n right := by
  have hweight := recoverableMarkedSwitchedAtoms_weight_preserved
    w hleft hright roots
  rw [markedAtomList_weight_eq w n] at hweight
  rw [markedAtomList_weight_eq w n] at hweight
  rw [markedAtomList_weight_eq w n] at hweight
  rw [markedAtomList_weight_eq w n] at hweight
  rw [canonicalFamilyAtoms_values hleft] at hweight
  rw [canonicalFamilyAtoms_values hright] at hweight
  exact hweight

/-- Occurrence fingerprints of atom lists and their literal value lists agree. -/
theorem familyOccurrenceFingerprint_atomValues {n : Nat} :
    ∀ (roots atoms : List (CanonicalAtom n)),
      familyOccurrenceFingerprint (roots.map Subtype.val)
          (atoms.map Subtype.val) =
        familyMembershipFingerprint roots atoms
  | [], _ => rfl
  | root :: roots, atoms => by
      have hbit : familyContainsPolymerB root.val
          (atoms.map Subtype.val) = memberB atoms root := by
        apply Bool.eq_iff_iff.mpr
        simp only [familyContainsPolymerB, memberB,
          decide_eq_true_eq]
        exact canonicalAtom_value_mem_values_iff atoms root
      simp only [familyOccurrenceFingerprint,
        familyMembershipFingerprint, List.map_cons]
      rw [hbit]
      exact congrArg (List.cons (memberB atoms root))
        (familyOccurrenceFingerprint_atomValues roots atoms)

/-- The complete marked occurrence fingerprint of the left output is the
original right fingerprint. -/
theorem recoverableMarkedSwitchedLeftFamily_fingerprint
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    familyOccurrenceFingerprint (roots.map Subtype.val)
        (recoverableMarkedSwitchedLeftFamily hleft hright roots) =
      familyOccurrenceFingerprint (roots.map Subtype.val) right := by
  unfold recoverableMarkedSwitchedLeftFamily
  rw [familyOccurrenceFingerprint_atomValues]
  unfold recoverableMarkedSwitchedLeftAtoms
  rw [familyMembershipFingerprint_markedRootSwitchedLeft_self
    (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n) roots
    (canonicalFamilyAtoms_mem_sublists hleft)
    (canonicalFamilyAtoms_mem_sublists hright)]
  rw [← familyOccurrenceFingerprint_atomValues roots
    (canonicalFamilyAtoms hright)]
  rw [canonicalFamilyAtoms_values hright]

theorem recoverableMarkedSwitchedRightFamily_fingerprint
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    familyOccurrenceFingerprint (roots.map Subtype.val)
        (recoverableMarkedSwitchedRightFamily hleft hright roots) =
      familyOccurrenceFingerprint (roots.map Subtype.val) left := by
  unfold recoverableMarkedSwitchedRightFamily
  rw [familyOccurrenceFingerprint_atomValues]
  unfold recoverableMarkedSwitchedRightAtoms
  rw [familyMembershipFingerprint_markedRootSwitchedRight_self
    (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n) roots
    (canonicalFamilyAtoms_mem_sublists hleft)
    (canonicalFamilyAtoms_mem_sublists hright)]
  rw [← familyOccurrenceFingerprint_atomValues roots
    (canonicalFamilyAtoms hleft)]
  rw [canonicalFamilyAtoms_values hleft]

theorem recoverableMarkedSwitchedFamilies_cylinderEvent_swap
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    cylinderEvent (roots.map Subtype.val) predicate
        (recoverableMarkedSwitchedLeftFamily hleft hright roots) =
        cylinderEvent (roots.map Subtype.val) predicate right ∧
      cylinderEvent (roots.map Subtype.val) predicate
        (recoverableMarkedSwitchedRightFamily hleft hright roots) =
        cylinderEvent (roots.map Subtype.val) predicate left := by
  unfold cylinderEvent
  exact ⟨congrArg predicate
      (recoverableMarkedSwitchedLeftFamily_fingerprint hleft hright roots),
    congrArg predicate
      (recoverableMarkedSwitchedRightFamily_fingerprint hleft hright roots)⟩

/-- Raw-root wrapper used by the finite-cylinder transport layer. -/
theorem recoverableMarkedSwitchedFamilies_cylinderEvent_swap_raw
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (rawRoots : List (List Nat))
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers n)
    (predicate : List Bool → Bool) :
    let roots := canonicalAtomsOfRoots rawRoots hroots
    cylinderEvent rawRoots predicate
        (recoverableMarkedSwitchedLeftFamily hleft hright roots) =
        cylinderEvent rawRoots predicate right ∧
      cylinderEvent rawRoots predicate
        (recoverableMarkedSwitchedRightFamily hleft hright roots) =
        cylinderEvent rawRoots predicate left := by
  intro roots
  have hswap := recoverableMarkedSwitchedFamilies_cylinderEvent_swap
    hleft hright roots predicate
  rw [canonicalAtomsOfRoots_values rawRoots hroots] at hswap
  exact hswap

private theorem canonicalAtomList_eq_of_values_eq {n : Nat} :
    ∀ {first second : List (CanonicalAtom n)},
      first.map Subtype.val = second.map Subtype.val → first = second
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | firstHead :: firstTail, secondHead :: secondTail, h => by
      have hhead : firstHead.val = secondHead.val :=
        List.cons.inj h |>.1
      have htail : firstTail.map Subtype.val =
          secondTail.map Subtype.val := List.cons.inj h |>.2
      have hatom : firstHead = secondHead := Subtype.ext hhead
      subst secondHead
      exact congrArg (List.cons firstHead)
        (canonicalAtomList_eq_of_values_eq htail)

/-- Equality of both switched output families recovers the two source
families, even though the union cut depends on those sources. -/
theorem recoverableMarkedSwitchedFamilies_injective
    {n : Nat} (roots : List (CanonicalAtom n))
    {left₁ right₁ left₂ right₂ : List (List Nat)}
    (hleft₁ : left₁ ∈ canonicalCompatibleAmbientFamilies n)
    (hright₁ : right₁ ∈ canonicalCompatibleAmbientFamilies n)
    (hleft₂ : left₂ ∈ canonicalCompatibleAmbientFamilies n)
    (hright₂ : right₂ ∈ canonicalCompatibleAmbientFamilies n)
    (hleftOutput :
      recoverableMarkedSwitchedLeftFamily hleft₁ hright₁ roots =
        recoverableMarkedSwitchedLeftFamily hleft₂ hright₂ roots)
    (hrightOutput :
      recoverableMarkedSwitchedRightFamily hleft₁ hright₁ roots =
        recoverableMarkedSwitchedRightFamily hleft₂ hright₂ roots) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hleftAtoms :
      recoverableMarkedSwitchedLeftAtoms hleft₁ hright₁ roots =
        recoverableMarkedSwitchedLeftAtoms hleft₂ hright₂ roots := by
    apply canonicalAtomList_eq_of_values_eq
    exact hleftOutput
  have hrightAtoms :
      recoverableMarkedSwitchedRightAtoms hleft₁ hright₁ roots =
        recoverableMarkedSwitchedRightAtoms hleft₂ hright₂ roots := by
    apply canonicalAtomList_eq_of_values_eq
    exact hrightOutput
  have hatoms := marked_root_switched_families_injective
    (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n)
    (canonicalAtomCompatibleB_symm n) roots
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_mem_sublists hleft₁)
    (canonicalFamilyAtoms_mem_sublists hright₁)
    (canonicalFamilyAtoms_mem_sublists hleft₂)
    (canonicalFamilyAtoms_mem_sublists hright₂)
    (canonicalFamilyAtoms_compatible hleft₁)
    (canonicalFamilyAtoms_compatible hright₁)
    (canonicalFamilyAtoms_compatible hleft₂)
    (canonicalFamilyAtoms_compatible hright₂)
    hleftAtoms hrightAtoms
  constructor
  · rw [← canonicalFamilyAtoms_values hleft₁,
      ← canonicalFamilyAtoms_values hleft₂, hatoms.1]
  · rw [← canonicalFamilyAtoms_values hright₁,
      ← canonicalFamilyAtoms_values hright₂, hatoms.2]

end YMGap.Continuum.Z4CanonicalMarkedRootSwitch

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSwitch.canonicalMarkedCut_closed
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSwitch.canonicalAtomsOfRoots_values
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSwitch.recoverableMarkedSwitchedFamilies_mem_compatible
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSwitch.recoverableMarkedSwitchedFamilies_weight_preserved
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSwitch.recoverableMarkedSwitchedLeftFamily_fingerprint
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSwitch.recoverableMarkedSwitchedFamilies_cylinderEvent_swap
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSwitch.recoverableMarkedSwitchedFamilies_cylinderEvent_swap_raw
#print axioms YMGap.Continuum.Z4CanonicalMarkedRootSwitch.recoverableMarkedSwitchedFamilies_injective
