/-
# Finite fingerprints under a rooted disagreement-component switch

This module connects the recoverable rooted family switch to arbitrary finite
membership fingerprints.  Every marked bit is shown literally to be swapped
iff its atom lies in the rooted disagreement component.  This is the exact
interface needed to replace an artificial Boolean-coordinate path by a path
of realizable, weight-preserving component switches.
-/

import YMGap.Continuum.FiniteBooleanEventPivot
import YMGap.Continuum.FiniteDisagreementReverseRecovery

namespace YMGap.Continuum.FiniteRootedSwitchFingerprint

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalBipartitePath

variable {A : Type} [DecidableEq A]

def familyMembershipFingerprint (roots : List A) (family : List A) :
    List Bool :=
  roots.map (memberB family)

@[simp] theorem familyMembershipFingerprint_length
    (roots family : List A) :
    (familyMembershipFingerprint roots family).length = roots.length := by
  simp only [familyMembershipFingerprint, List.length_map]

def rootedSwitchLeftFingerprint (ambient : List A)
    (compat : A → A → Bool) (root : A)
    (left right roots : List A) : List Bool :=
  roots.map (fun atom =>
    if rootedComponent ambient compat (memberB left) (memberB right)
        root atom
    then memberB right atom
    else memberB left atom)

def rootedSwitchRightFingerprint (ambient : List A)
    (compat : A → A → Bool) (root : A)
    (left right roots : List A) : List Bool :=
  roots.map (fun atom =>
    if rootedComponent ambient compat (memberB left) (memberB right)
        root atom
    then memberB left atom
    else memberB right atom)

/-- Literal left-output fingerprint formula for the rooted component switch. -/
theorem familyMembershipFingerprint_rootedSwitchedLeft
    (ambient : List A) (compat : A → A → Bool) (root : A)
    {left right : List A}
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    ∀ roots : List A,
      familyMembershipFingerprint roots
          (rootedComponentSwitchedLeft ambient compat root left right) =
        rootedSwitchLeftFingerprint ambient compat root left right roots
  | [] => rfl
  | atom :: roots => by
      have hmask := congrFun
        (rootedComponentSwitchedLeft_mask ambient compat root hleft hright)
        atom
      have hbit :
          memberB
              (rootedComponentSwitchedLeft ambient compat root left right)
              atom =
            (if rootedComponent ambient compat (memberB left) (memberB right)
                  root atom
              then memberB right atom
              else memberB left atom) := by
        simpa only [rootedSwitchedLeft, swapLeftMask] using hmask
      simp only [familyMembershipFingerprint, rootedSwitchLeftFingerprint,
        List.map_cons]
      rw [hbit]
      exact congrArg
        (List.cons
          (if rootedComponent ambient compat (memberB left) (memberB right)
                root atom
            then memberB right atom
            else memberB left atom))
        (familyMembershipFingerprint_rootedSwitchedLeft ambient compat root
          hleft hright roots)

/-- Literal right-output fingerprint formula for the rooted component switch. -/
theorem familyMembershipFingerprint_rootedSwitchedRight
    (ambient : List A) (compat : A → A → Bool) (root : A)
    {left right : List A}
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    ∀ roots : List A,
      familyMembershipFingerprint roots
          (rootedComponentSwitchedRight ambient compat root left right) =
        rootedSwitchRightFingerprint ambient compat root left right roots
  | [] => rfl
  | atom :: roots => by
      have hmask := congrFun
        (rootedComponentSwitchedRight_mask ambient compat root hleft hright)
        atom
      have hbit :
          memberB
              (rootedComponentSwitchedRight ambient compat root left right)
              atom =
            (if rootedComponent ambient compat (memberB left) (memberB right)
                  root atom
              then memberB left atom
              else memberB right atom) := by
        simpa only [rootedSwitchedRight, swapRightMask] using hmask
      simp only [familyMembershipFingerprint, rootedSwitchRightFingerprint,
        List.map_cons]
      rw [hbit]
      exact congrArg
        (List.cons
          (if rootedComponent ambient compat (memberB left) (memberB right)
                root atom
            then memberB left atom
            else memberB right atom))
        (familyMembershipFingerprint_rootedSwitchedRight ambient compat root
          hleft hright roots)

theorem rootedSwitchLeftFingerprint_eq_right_of_all_reached
    (ambient : List A) (compat : A → A → Bool) (root : A)
    (left right : List A) :
    ∀ roots : List A,
      (∀ atom, atom ∈ roots →
        rootedComponent ambient compat (memberB left) (memberB right)
          root atom = true) →
      rootedSwitchLeftFingerprint ambient compat root left right roots =
        familyMembershipFingerprint roots right
  | [], _ => rfl
  | atom :: roots, hreached => by
      have hatom := hreached atom List.mem_cons_self
      have htail : ∀ tailAtom, tailAtom ∈ roots →
          rootedComponent ambient compat (memberB left) (memberB right)
            root tailAtom = true :=
        fun tailAtom htailAtom =>
          hreached tailAtom (List.mem_cons_of_mem atom htailAtom)
      simp only [rootedSwitchLeftFingerprint, familyMembershipFingerprint,
        List.map_cons, hatom, ↓reduceIte]
      exact congrArg (List.cons (memberB right atom))
        (rootedSwitchLeftFingerprint_eq_right_of_all_reached
          ambient compat root left right roots htail)

theorem rootedSwitchLeftFingerprint_eq_left_of_all_unreached
    (ambient : List A) (compat : A → A → Bool) (root : A)
    (left right : List A) :
    ∀ roots : List A,
      (∀ atom, atom ∈ roots →
        rootedComponent ambient compat (memberB left) (memberB right)
          root atom = false) →
      rootedSwitchLeftFingerprint ambient compat root left right roots =
        familyMembershipFingerprint roots left
  | [], _ => rfl
  | atom :: roots, hunreached => by
      have hatom := hunreached atom List.mem_cons_self
      have htail : ∀ tailAtom, tailAtom ∈ roots →
          rootedComponent ambient compat (memberB left) (memberB right)
            root tailAtom = false :=
        fun tailAtom htailAtom =>
          hunreached tailAtom (List.mem_cons_of_mem atom htailAtom)
      simp only [rootedSwitchLeftFingerprint, familyMembershipFingerprint,
        List.map_cons, hatom, Bool.false_eq_true, ↓reduceIte]
      exact congrArg (List.cons (memberB left atom))
        (rootedSwitchLeftFingerprint_eq_left_of_all_unreached
          ambient compat root left right roots htail)

/-- The root coordinate is always swapped; reflexive Warshall reachability is
the constructive reason. -/
theorem rootedComponentSwitchedLeft_root_bit
    (ambient : List A) (compat : A → A → Bool) (root : A)
    {left right : List A}
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient) :
    memberB (rootedComponentSwitchedLeft ambient compat root left right) root =
      memberB right root := by
  have hmask := congrFun
    (rootedComponentSwitchedLeft_mask ambient compat root hleft hright) root
  simpa only [rootedSwitchedLeft, swapLeftMask, rootedComponent,
    warshall_refl, ↓reduceIte] using hmask

/-- Event evaluation after a realizable rooted component switch factors
through the explicit switched fingerprint. -/
theorem event_rootedComponentSwitchedLeft
    (ambient : List A) (compat : A → A → Bool) (root : A)
    {left right : List A}
    (hleft : left ∈ sublists ambient)
    (hright : right ∈ sublists ambient)
    (roots : List A) (event : List Bool → Bool) :
    event (familyMembershipFingerprint roots
        (rootedComponentSwitchedLeft ambient compat root left right)) =
      event (rootedSwitchLeftFingerprint ambient compat root left right roots) := by
  rw [familyMembershipFingerprint_rootedSwitchedLeft
    ambient compat root hleft hright roots]

end YMGap.Continuum.FiniteRootedSwitchFingerprint

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteRootedSwitchFingerprint.familyMembershipFingerprint_rootedSwitchedLeft
#print axioms YMGap.Continuum.FiniteRootedSwitchFingerprint.familyMembershipFingerprint_rootedSwitchedRight
#print axioms YMGap.Continuum.FiniteRootedSwitchFingerprint.rootedComponentSwitchedLeft_root_bit
#print axioms YMGap.Continuum.FiniteRootedSwitchFingerprint.event_rootedComponentSwitchedLeft
