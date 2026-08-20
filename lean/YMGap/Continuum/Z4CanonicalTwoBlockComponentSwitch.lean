/-
# Two-block disagreement-component switching

The existing canonical marked switch exchanges every disagreement component
meeting a chosen root block.  For a two-block connected correlation, the
relevant dichotomy is whether one of those components also meets the second
root block.  On the separated branch the switch exchanges the complete first
fingerprint while leaving the complete second fingerprint unchanged.  On the
connected branch it constructively selects a first-block root and a
second-block root joined in the disagreement graph.

This is the exact finite cancellation mechanism needed before applying a
temporal carrier-size floor.  It is independent of a box boundary and makes no
probability or decay estimate.
-/

import YMGap.Continuum.Z4CanonicalMarkedRootSeparation

namespace YMGap.Continuum.Z4CanonicalTwoBlockComponentSwitch

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteMarkedRootSwitch
open YMGap.Continuum.FiniteRootedSwitchFingerprint
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerUniverse

/-! ## 1. The exact two-block connectivity classifier -/

/-- Does a disagreement component rooted in the first marked block meet an
atom of the second marked block? -/
def twoBlockMarkedReachB
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (firstRoots secondRoots : List (CanonicalAtom n)) : Bool :=
  secondRoots.any (canonicalMarkedCut hleft hright firstRoots)

theorem twoBlockMarkedReachB_false_cut
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (firstRoots secondRoots : List (CanonicalAtom n))
    (hseparated : twoBlockMarkedReachB hleft hright
      firstRoots secondRoots = false) :
    ∀ atom, atom ∈ secondRoots →
      canonicalMarkedCut hleft hright firstRoots atom = false := by
  intro atom hatom
  cases hcut : canonicalMarkedCut hleft hright firstRoots atom with
  | false => rfl
  | true =>
      have hany : secondRoots.any
          (canonicalMarkedCut hleft hright firstRoots) = true :=
        List.any_eq_true.mpr ⟨atom, hatom, hcut⟩
      unfold twoBlockMarkedReachB at hseparated
      rw [hseparated] at hany
      exact False.elim (Bool.false_ne_true hany)

/-- The connected branch supplies literal endpoints in the two marked blocks
and exact disagreement reachability between them. -/
theorem twoBlockMarkedReachB_true_witness
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (firstRoots secondRoots : List (CanonicalAtom n))
    (hconnected : twoBlockMarkedReachB hleft hright
      firstRoots secondRoots = true) :
    ∃ first second : CanonicalAtom n,
      first ∈ firstRoots ∧ second ∈ secondRoots ∧
        canonicalDisagreementCut hleft hright first second = true := by
  unfold twoBlockMarkedReachB at hconnected
  obtain ⟨second, hsecond, hcut⟩ := List.any_eq_true.mp hconnected
  obtain ⟨first, hfirst, hreach⟩ :=
    canonicalMarkedCut_true_has_root
      hleft hright firstRoots second hcut
  exact ⟨first, second, hfirst, hsecond, hreach⟩

/-! ## 2. The separated switch leaves the second block fixed -/

private theorem secondFingerprint_switchedLeft
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (firstRoots : List (CanonicalAtom n)) :
    ∀ (secondRoots : List (CanonicalAtom n)),
      (∀ atom, atom ∈ secondRoots →
        canonicalMarkedCut hleft hright firstRoots atom = false) →
      familyMembershipFingerprint secondRoots
          (recoverableMarkedSwitchedLeftAtoms
            hleft hright firstRoots) =
        familyMembershipFingerprint secondRoots
          (canonicalFamilyAtoms hleft)
  | [], _ => rfl
  | atom :: rest, hcut => by
      have hatomCut := hcut atom List.mem_cons_self
      unfold canonicalMarkedCut at hatomCut
      have hrestCut : ∀ found, found ∈ rest →
          canonicalMarkedCut hleft hright firstRoots found = false :=
        fun found hfound =>
          hcut found (List.mem_cons_of_mem atom hfound)
      have hmask := congrFun
        (markedRootComponentSwitchedLeft_mask
          (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n)
          firstRoots
          (canonicalFamilyAtoms_mem_sublists hleft)
          (canonicalFamilyAtoms_mem_sublists hright)) atom
      have hhead : memberB
          (recoverableMarkedSwitchedLeftAtoms hleft hright firstRoots) atom =
        memberB (canonicalFamilyAtoms hleft) atom := by
        simpa only [recoverableMarkedSwitchedLeftAtoms,
          markedRootSwitchedLeft, swapLeftMask,
          hatomCut, Bool.false_eq_true, ↓reduceIte] using hmask
      simp only [familyMembershipFingerprint, List.map_cons]
      rw [hhead]
      exact congrArg (List.cons (memberB (canonicalFamilyAtoms hleft) atom))
        (secondFingerprint_switchedLeft hleft hright firstRoots
          rest hrestCut)

private theorem secondFingerprint_switchedRight
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (firstRoots : List (CanonicalAtom n)) :
    ∀ (secondRoots : List (CanonicalAtom n)),
      (∀ atom, atom ∈ secondRoots →
        canonicalMarkedCut hleft hright firstRoots atom = false) →
      familyMembershipFingerprint secondRoots
          (recoverableMarkedSwitchedRightAtoms
            hleft hright firstRoots) =
        familyMembershipFingerprint secondRoots
          (canonicalFamilyAtoms hright)
  | [], _ => rfl
  | atom :: rest, hcut => by
      have hatomCut := hcut atom List.mem_cons_self
      unfold canonicalMarkedCut at hatomCut
      have hrestCut : ∀ found, found ∈ rest →
          canonicalMarkedCut hleft hright firstRoots found = false :=
        fun found hfound =>
          hcut found (List.mem_cons_of_mem atom hfound)
      have hmask := congrFun
        (markedRootComponentSwitchedRight_mask
          (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n)
          firstRoots
          (canonicalFamilyAtoms_mem_sublists hleft)
          (canonicalFamilyAtoms_mem_sublists hright)) atom
      have hhead : memberB
          (recoverableMarkedSwitchedRightAtoms hleft hright firstRoots) atom =
        memberB (canonicalFamilyAtoms hright) atom := by
        simpa only [recoverableMarkedSwitchedRightAtoms,
          markedRootSwitchedRight, swapRightMask,
          hatomCut, Bool.false_eq_true, ↓reduceIte] using hmask
      simp only [familyMembershipFingerprint, List.map_cons]
      rw [hhead]
      exact congrArg (List.cons (memberB (canonicalFamilyAtoms hright) atom))
        (secondFingerprint_switchedRight hleft hright firstRoots
          rest hrestCut)

theorem separatedTwoBlockSwitch_secondFingerprint
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (firstRoots secondRoots : List (CanonicalAtom n))
    (hseparated : twoBlockMarkedReachB hleft hright
      firstRoots secondRoots = false) :
    familyOccurrenceFingerprint (secondRoots.map Subtype.val)
        (recoverableMarkedSwitchedLeftFamily hleft hright firstRoots) =
          familyOccurrenceFingerprint (secondRoots.map Subtype.val) left ∧
      familyOccurrenceFingerprint (secondRoots.map Subtype.val)
        (recoverableMarkedSwitchedRightFamily hleft hright firstRoots) =
          familyOccurrenceFingerprint (secondRoots.map Subtype.val) right := by
  have hcut := twoBlockMarkedReachB_false_cut
    hleft hright firstRoots secondRoots hseparated
  constructor
  · unfold recoverableMarkedSwitchedLeftFamily
    rw [familyOccurrenceFingerprint_atomValues]
    rw [secondFingerprint_switchedLeft
      hleft hright firstRoots secondRoots hcut]
    rw [← familyOccurrenceFingerprint_atomValues
      secondRoots (canonicalFamilyAtoms hleft)]
    rw [canonicalFamilyAtoms_values hleft]
  · unfold recoverableMarkedSwitchedRightFamily
    rw [familyOccurrenceFingerprint_atomValues]
    rw [secondFingerprint_switchedRight
      hleft hright firstRoots secondRoots hcut]
    rw [← familyOccurrenceFingerprint_atomValues
      secondRoots (canonicalFamilyAtoms hright)]
    rw [canonicalFamilyAtoms_values hright]

/-- Complete separated-branch behavior: the first fingerprint is exchanged
between replicas while the second fingerprint remains in its original
replica.  This is the four-cell cancellation pattern for a connected
two-block correlation. -/
theorem separatedTwoBlockSwitch_fingerprints
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (firstRoots secondRoots : List (CanonicalAtom n))
    (hseparated : twoBlockMarkedReachB hleft hright
      firstRoots secondRoots = false) :
    (familyOccurrenceFingerprint (firstRoots.map Subtype.val)
        (recoverableMarkedSwitchedLeftFamily hleft hright firstRoots) =
          familyOccurrenceFingerprint (firstRoots.map Subtype.val) right ∧
      familyOccurrenceFingerprint (firstRoots.map Subtype.val)
        (recoverableMarkedSwitchedRightFamily hleft hright firstRoots) =
          familyOccurrenceFingerprint (firstRoots.map Subtype.val) left) ∧
    (familyOccurrenceFingerprint (secondRoots.map Subtype.val)
        (recoverableMarkedSwitchedLeftFamily hleft hright firstRoots) =
          familyOccurrenceFingerprint (secondRoots.map Subtype.val) left ∧
      familyOccurrenceFingerprint (secondRoots.map Subtype.val)
        (recoverableMarkedSwitchedRightFamily hleft hright firstRoots) =
          familyOccurrenceFingerprint (secondRoots.map Subtype.val) right) := by
  exact ⟨
    ⟨recoverableMarkedSwitchedLeftFamily_fingerprint
        hleft hright firstRoots,
      recoverableMarkedSwitchedRightFamily_fingerprint
        hleft hright firstRoots⟩,
    separatedTwoBlockSwitch_secondFingerprint
      hleft hright firstRoots secondRoots hseparated⟩

#print axioms twoBlockMarkedReachB_false_cut
#print axioms twoBlockMarkedReachB_true_witness
#print axioms separatedTwoBlockSwitch_secondFingerprint
#print axioms separatedTwoBlockSwitch_fingerprints

end YMGap.Continuum.Z4CanonicalTwoBlockComponentSwitch
