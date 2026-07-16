/-
# Recoverable canonical boundary-component switching

The earlier side-tagged canonical switch proves the exact per-pair algebra and
geometry.  This module supplies the missing global ingredient: a component cut
that is reconstructed from the switched output itself.  It instantiates the
generic exclusive-occurrence disagreement graph with the corrected canonical
surface-polymer compatibility relation.

The resulting source-dependent switch is injective on literal canonical
families.  No fixed-cut hypothesis is used.
-/

import YMGap.Continuum.FiniteDisagreementReverseRecovery
import YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch

namespace YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4FiniteBoxExhaustion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The canonical recoverable cut -/

def canonicalRootBad {n : Nat} (root : CanonicalAtom n) :
    CanonicalAtom n → Bool :=
  fun atom => decide (atom = root)

def canonicalDisagreementCut
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) : CanonicalAtom n → Bool :=
  rootedComponent (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n)
    (memberB (canonicalFamilyAtoms hleft))
    (memberB (canonicalFamilyAtoms hright))
    root

def recoverableSwitchedLeftAtoms
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) : List (CanonicalAtom n) :=
  rootedComponentSwitchedLeft (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n) root
    (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)

def recoverableSwitchedRightAtoms
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) : List (CanonicalAtom n) :=
  rootedComponentSwitchedRight (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n) root
    (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)

theorem canonicalAtomCompatibleB_symm (n : Nat)
    (first second : CanonicalAtom n) :
    canonicalAtomCompatibleB n first second =
      canonicalAtomCompatibleB n second first := by
  exact canonicalPolymerCompatibleB_symm n first.val second.val

theorem canonicalFamilyMask_pairwise
    {n : Nat} {family : List (List Nat)}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n) :
    ∀ first second : CanonicalAtom n, first ≠ second →
      memberB (canonicalFamilyAtoms hfamily) first = true →
      memberB (canonicalFamilyAtoms hfamily) second = true →
      canonicalAtomCompatibleB n first second = true := by
  intro first second hne hfirst hsecond
  exact familyCompatibleB_pairwise (canonicalAtomCompatibleB n)
    (canonicalAtomCompatibleB_symm n)
    (canonicalFamilyAtoms_compatible hfamily)
    ((memberB_eq_true_iff _ _).1 hfirst)
    ((memberB_eq_true_iff _ _).1 hsecond) hne

theorem canonicalRootBad_false_of_right_absent
    {n : Nat} {right : List (List Nat)}
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    (hrootRight : root ∉ canonicalFamilyAtoms hright) :
    ∀ atom, memberB (canonicalFamilyAtoms hright) atom = true →
      canonicalRootBad root atom = false := by
  intro atom hatom
  unfold canonicalRootBad
  cases heq : decide (atom = root) with
  | false => rfl
  | true =>
      have hsame : atom = root := of_decide_eq_true heq
      subst atom
      exact False.elim
        (hrootRight ((memberB_eq_true_iff _ _).1 hatom))

/-- Reverse reachability on the switched canonical masks recovers the complete
source-dependent cut exactly. -/
theorem canonical_reverse_component_recovers
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    (atom : CanonicalAtom n) :
    rootedComponent (canonicalAmbientAtoms n)
        (canonicalAtomCompatibleB n)
        (rootedSwitchedLeft (canonicalAmbientAtoms n)
          (canonicalAtomCompatibleB n)
          root
          (memberB (canonicalFamilyAtoms hleft))
          (memberB (canonicalFamilyAtoms hright)))
        (rootedSwitchedRight (canonicalAmbientAtoms n)
          (canonicalAtomCompatibleB n)
          root
          (memberB (canonicalFamilyAtoms hleft))
          (memberB (canonicalFamilyAtoms hright)))
        root atom =
      canonicalDisagreementCut hleft hright root atom := by
  exact rooted_component_recovers
    (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n)
    (canonicalAtomCompatibleB_symm n)
    root
    (memberB (canonicalFamilyAtoms hleft))
    (memberB (canonicalFamilyAtoms hright))
    (canonicalFamilyMask_pairwise hleft)
    (canonicalFamilyMask_pairwise hright)
    atom

/-! ## 2. Closedness, exact algebra, and source-dependent injectivity -/

theorem canonicalDisagreementCut_closed
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    {leftAtom rightAtom : CanonicalAtom n}
    (hleftAtom : leftAtom ∈ canonicalFamilyAtoms hleft)
    (hrightAtom : rightAtom ∈ canonicalFamilyAtoms hright)
    (hincompatible :
      canonicalAtomCompatibleB n leftAtom rightAtom = false) :
    canonicalDisagreementCut hleft hright root leftAtom =
      canonicalDisagreementCut hleft hright root rightAtom := by
  cases heq : decide (leftAtom = rightAtom) with
  | true =>
      have hsame : leftAtom = rightAtom := of_decide_eq_true heq
      subst rightAtom
      rfl
  | false =>
      have hne : leftAtom ≠ rightAtom := of_decide_eq_false heq
      have hleftB : memberB (canonicalFamilyAtoms hleft) leftAtom = true :=
        (memberB_eq_true_iff _ _).2 hleftAtom
      have hrightB : memberB (canonicalFamilyAtoms hright) rightAtom = true :=
        (memberB_eq_true_iff _ _).2 hrightAtom
      have hleftNotRight :
          memberB (canonicalFamilyAtoms hright) leftAtom = false := by
        cases hbit : memberB (canonicalFamilyAtoms hright) leftAtom with
        | false => rfl
        | true =>
            have hcompat := canonicalFamilyMask_pairwise hright
              leftAtom rightAtom hne hbit hrightB
            rw [hincompatible] at hcompat
            exact False.elim (Bool.false_ne_true hcompat)
      have hrightNotLeft :
          memberB (canonicalFamilyAtoms hleft) rightAtom = false := by
        cases hbit : memberB (canonicalFamilyAtoms hleft) rightAtom with
        | false => rfl
        | true =>
            have hcompat := canonicalFamilyMask_pairwise hleft
              leftAtom rightAtom hne hleftB hbit
            rw [hincompatible] at hcompat
            exact False.elim (Bool.false_ne_true hcompat)
      have hedge : disagreementEdge (canonicalAmbientAtoms n)
          (canonicalAtomCompatibleB n)
          (memberB (canonicalFamilyAtoms hleft))
          (memberB (canonicalFamilyAtoms hright))
          leftAtom rightAtom = true := by
        unfold disagreementEdge disagreementBits leftOnly rightOnly
        have hleftAmbient : memberB (canonicalAmbientAtoms n) leftAtom = true :=
          (memberB_eq_true_iff _ _).2
            (canonicalAtom_mem_ambientAtoms leftAtom)
        have hrightAmbient : memberB (canonicalAmbientAtoms n) rightAtom = true :=
          (memberB_eq_true_iff _ _).2
            (canonicalAtom_mem_ambientAtoms rightAtom)
        simp [hleftAmbient, hrightAmbient, hleftB, hrightB,
          hleftNotRight, hrightNotLeft, hincompatible]
      exact rootedComponent_cut_closed (canonicalAmbientAtoms n)
        (canonicalAtomCompatibleB n) (canonicalAtomCompatibleB_symm n)
        (memberB (canonicalFamilyAtoms hleft))
        (memberB (canonicalFamilyAtoms hright))
        root hedge

theorem recoverableSwitchedAtoms_compatible
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) :
    familyCompatibleB (canonicalAtomCompatibleB n)
        (recoverableSwitchedLeftAtoms hleft hright root) = true ∧
      familyCompatibleB (canonicalAtomCompatibleB n)
        (recoverableSwitchedRightAtoms hleft hright root) = true := by
  exact switched_pair_compatible (canonicalAtomCompatibleB n)
    (canonicalAtomCompatibleB_symm n)
    (canonicalDisagreementCut hleft hright root)
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_compatible hleft)
    (canonicalFamilyAtoms_compatible hright)
    (fun leftAtom hleftAtom rightAtom hrightAtom hincompatible =>
      canonicalDisagreementCut_closed hleft hright root
        hleftAtom hrightAtom hincompatible)

theorem recoverableSwitchedAtoms_weight_preserved
    (w : Q') {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) :
    familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (recoverableSwitchedLeftAtoms hleft hright root) *
      familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (recoverableSwitchedRightAtoms hleft hright root) ≈
    familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (canonicalFamilyAtoms hleft) *
      familyWeight (fun atom : CanonicalAtom n =>
        canonicalSurfaceActivity w n atom.val)
        (canonicalFamilyAtoms hright) := by
  unfold recoverableSwitchedLeftAtoms recoverableSwitchedRightAtoms
    rootedComponentSwitchedLeft rootedComponentSwitchedRight
  exact switched_pair_weight_preserved
    (fun atom : CanonicalAtom n => canonicalSurfaceActivity w n atom.val)
    (canonicalDisagreementCut hleft hright root)
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_mem_sublists hleft)
    (canonicalFamilyAtoms_mem_sublists hright)

/-! ### Return to literal canonical families -/

def recoverableSwitchedLeftFamily
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) : List (List Nat) :=
  (recoverableSwitchedLeftAtoms hleft hright root).map Subtype.val

def recoverableSwitchedRightFamily
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) : List (List Nat) :=
  (recoverableSwitchedRightAtoms hleft hright root).map Subtype.val

private theorem atomList_all_values {n : Nat}
    (test : List Nat → Bool) :
    ∀ atoms : List (CanonicalAtom n),
      atoms.all (fun atom => test atom.val) =
        (atoms.map Subtype.val).all test
  | [] => rfl
  | _ :: rest => by
      simp only [List.all_cons, List.map]
      rw [atomList_all_values test rest]

private theorem atomList_compatible_eq {n : Nat} :
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
      rw [atomList_all_values
        (canonicalPolymerCompatibleB n head.val) rest]
      rw [atomList_compatible_eq rest]

private theorem atomList_weight_eq (w : Q') (n : Nat) :
    ∀ atoms : List (CanonicalAtom n),
      familyWeight (fun atom : CanonicalAtom n =>
          canonicalSurfaceActivity w n atom.val) atoms =
        canonicalSurfaceFamilyActivity w n
          (atoms.map Subtype.val)
  | [] => rfl
  | _ :: rest => by
      simp only [familyWeight_cons, List.map,
        canonicalSurfaceFamilyActivity]
      rw [atomList_weight_eq w n rest]

theorem recoverableSwitchedFamilies_mem_compatible
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) :
    recoverableSwitchedLeftFamily hleft hright root ∈
        canonicalCompatibleAmbientFamilies n ∧
      recoverableSwitchedRightFamily hleft hright root ∈
        canonicalCompatibleAmbientFamilies n := by
  have hatomCompat := recoverableSwitchedAtoms_compatible hleft hright root
  constructor
  · unfold canonicalCompatibleAmbientFamilies
    apply List.mem_filter.mpr
    constructor
    · have hsub := map_mem_sublists Subtype.val
          (canonicalAmbientAtoms n)
          (recoverableSwitchedLeftAtoms hleft hright root)
          (switchedLeft_mem_sublists (canonicalAmbientAtoms n)
            (canonicalDisagreementCut hleft hright root)
            (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright))
      rw [canonicalAmbientAtoms_values] at hsub
      exact hsub
    · have hgeneric : familyCompatibleB
          (canonicalPolymerCompatibleB n)
          (recoverableSwitchedLeftFamily hleft hright root) = true := by
        unfold recoverableSwitchedLeftFamily
        rw [← atomList_compatible_eq]
        exact hatomCompat.1
      rw [genericFamilyCompatibleB_eq_canonical n] at hgeneric
      exact hgeneric
  · unfold canonicalCompatibleAmbientFamilies
    apply List.mem_filter.mpr
    constructor
    · have hsub := map_mem_sublists Subtype.val
          (canonicalAmbientAtoms n)
          (recoverableSwitchedRightAtoms hleft hright root)
          (switchedRight_mem_sublists (canonicalAmbientAtoms n)
            (canonicalDisagreementCut hleft hright root)
            (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright))
      rw [canonicalAmbientAtoms_values] at hsub
      exact hsub
    · have hgeneric : familyCompatibleB
          (canonicalPolymerCompatibleB n)
          (recoverableSwitchedRightFamily hleft hright root) = true := by
        unfold recoverableSwitchedRightFamily
        rw [← atomList_compatible_eq]
        exact hatomCompat.2
      rw [genericFamilyCompatibleB_eq_canonical n] at hgeneric
      exact hgeneric

theorem recoverableSwitchedFamilies_weight_preserved
    (w : Q') {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) :
    canonicalSurfaceFamilyActivity w n
        (recoverableSwitchedLeftFamily hleft hright root) *
      canonicalSurfaceFamilyActivity w n
        (recoverableSwitchedRightFamily hleft hright root) ≈
    canonicalSurfaceFamilyActivity w n left *
      canonicalSurfaceFamilyActivity w n right := by
  have hweight := recoverableSwitchedAtoms_weight_preserved
    w hleft hright root
  rw [atomList_weight_eq w n] at hweight
  rw [atomList_weight_eq w n] at hweight
  rw [atomList_weight_eq w n] at hweight
  rw [atomList_weight_eq w n] at hweight
  rw [canonicalFamilyAtoms_values hleft] at hweight
  rw [canonicalFamilyAtoms_values hright] at hweight
  exact hweight

/-! ### Local event and box cells -/

theorem mem_recoverableSwitchedLeftAtoms_iff
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root atom : CanonicalAtom n) :
    atom ∈ recoverableSwitchedLeftAtoms hleft hright root ↔
      switchedLeftB (canonicalDisagreementCut hleft hright root)
        (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)
        atom = true := by
  unfold recoverableSwitchedLeftAtoms rootedComponentSwitchedLeft
    FiniteCompatibilitySwitching.switchedLeft
  constructor
  · exact fun hatom => (List.mem_filter.mp hatom).2
  · intro htest
    exact List.mem_filter.mpr
      ⟨canonicalAtom_mem_ambientAtoms atom, htest⟩

theorem mem_recoverableSwitchedRightAtoms_iff
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root atom : CanonicalAtom n) :
    atom ∈ recoverableSwitchedRightAtoms hleft hright root ↔
      switchedRightB (canonicalDisagreementCut hleft hright root)
        (canonicalFamilyAtoms hleft) (canonicalFamilyAtoms hright)
        atom = true := by
  unfold recoverableSwitchedRightAtoms rootedComponentSwitchedRight
    FiniteCompatibilitySwitching.switchedRight
  constructor
  · exact fun hatom => (List.mem_filter.mp hatom).2
  · intro htest
    exact List.mem_filter.mpr
      ⟨canonicalAtom_mem_ambientAtoms atom, htest⟩

theorem canonicalDisagreementCut_root_true
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) :
    canonicalDisagreementCut hleft hright root root = true := by
  unfold canonicalDisagreementCut rootedComponent
  exact warshall_refl _ _ root

theorem recoverableSwitchedFamilies_root_cells
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {rootPolymer : List Nat} (hroot : rootPolymer ∈ left)
    (hrootRight : rootPolymer ∉ right) :
    familyContainsPolymerB rootPolymer
        (recoverableSwitchedLeftFamily hleft hright
          (leftCanonicalAtomOfMember hleft hroot)) = false ∧
      familyContainsPolymerB rootPolymer
        (recoverableSwitchedRightFamily hleft hright
          (leftCanonicalAtomOfMember hleft hroot)) = true := by
  let root := leftCanonicalAtomOfMember hleft hroot
  have hrootLeftAtom : root ∈ canonicalFamilyAtoms hleft :=
    (canonicalFamilyAtom_mem_iff hleft root).2 hroot
  have hrootRightAtom : root ∉ canonicalFamilyAtoms hright := by
    intro hmem
    exact hrootRight ((canonicalFamilyAtom_mem_iff hright root).1 hmem)
  have hcut : canonicalDisagreementCut hleft hright root root = true :=
    canonicalDisagreementCut_root_true hleft hright root
  have hleftOut : root ∉ recoverableSwitchedLeftAtoms hleft hright root := by
    intro hmem
    have htest := (mem_recoverableSwitchedLeftAtoms_iff
      hleft hright root root).1 hmem
    have hrightB : memberB (canonicalFamilyAtoms hright) root = false :=
      (memberB_eq_false_iff _ _).2 hrootRightAtom
    simp [switchedLeftB, hcut, hrightB] at htest
  have hrightOut : root ∈
      recoverableSwitchedRightAtoms hleft hright root := by
    apply (mem_recoverableSwitchedRightAtoms_iff
      hleft hright root root).2
    have hleftB : memberB (canonicalFamilyAtoms hleft) root = true :=
      (memberB_eq_true_iff _ _).2 hrootLeftAtom
    simp [switchedRightB, hcut, hleftB]
  constructor
  · unfold familyContainsPolymerB recoverableSwitchedLeftFamily
    have hnot : rootPolymer ∉
        (recoverableSwitchedLeftAtoms hleft hright root).map Subtype.val := by
      intro hvalue
      exact hleftOut
        ((canonicalAtom_value_mem_values_iff _ root).1 hvalue)
    simpa using hnot
  · unfold familyContainsPolymerB recoverableSwitchedRightFamily
    have hvalue : rootPolymer ∈
        (recoverableSwitchedRightAtoms hleft hright root).map Subtype.val :=
      (canonicalAtom_value_mem_values_iff _ root).2 hrightOut
    simpa using hvalue

theorem recoverableSwitchedRightFamily_inside_of_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    (hrightInside : FamilyInsideBox small n right)
    (hseparated : ∀ outside : CanonicalAtom n,
      outside.val ∈ left →
        polymerInsideBoxB small n outside.val = false →
          canonicalDisagreementCut hleft hright root outside = false) :
    FamilyInsideBox small n
      (recoverableSwitchedRightFamily hleft hright root) := by
  intro support hsupport
  unfold recoverableSwitchedRightFamily at hsupport
  obtain ⟨atom, hatom, hatomValue⟩ := List.mem_map.mp hsupport
  subst support
  have htest := (mem_recoverableSwitchedRightAtoms_iff
    hleft hright root atom).1 hatom
  cases hcut : canonicalDisagreementCut hleft hright root atom with
  | false =>
      have hrightAtom : atom ∈ canonicalFamilyAtoms hright := by
        have hmemberB : memberB (canonicalFamilyAtoms hright) atom = true := by
          simpa [switchedRightB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      exact hrightInside atom.val
        ((canonicalFamilyAtom_mem_iff hright atom).1 hrightAtom)
  | true =>
      have hleftAtom : atom ∈ canonicalFamilyAtoms hleft := by
        have hmemberB : memberB (canonicalFamilyAtoms hleft) atom = true := by
          simpa [switchedRightB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      have hleftRaw : atom.val ∈ left :=
        (canonicalFamilyAtom_mem_iff hleft atom).1 hleftAtom
      cases hinside : polymerInsideBoxB small n atom.val with
      | true =>
          exact (polymerInsideBoxB_true_iff small n atom.val).1 hinside
      | false =>
          have hnotReach := hseparated atom hleftRaw hinside
          rw [hnotReach] at hcut
          exact False.elim (Bool.false_ne_true hcut)

theorem outside_support_mem_recoverableSwitchedLeft_of_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    {outside : List Nat} (houtside : outside ∈ left)
    (houtsideBox : polymerInsideBoxB small n outside = false)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          canonicalDisagreementCut hleft hright root atom = false) :
    outside ∈ recoverableSwitchedLeftFamily hleft hright root := by
  let outsideAtom : CanonicalAtom n :=
    ⟨outside, compatibleAmbientFamily_member_ambient hleft houtside⟩
  have houtsideAtom : outsideAtom ∈ canonicalFamilyAtoms hleft :=
    (canonicalFamilyAtom_mem_iff hleft outsideAtom).2 houtside
  have hcut : canonicalDisagreementCut hleft hright root outsideAtom = false :=
    hseparated outsideAtom houtside houtsideBox
  have hleftB : memberB (canonicalFamilyAtoms hleft) outsideAtom = true :=
    (memberB_eq_true_iff _ _).2 houtsideAtom
  have houtAtoms : outsideAtom ∈
      recoverableSwitchedLeftAtoms hleft hright root := by
    apply (mem_recoverableSwitchedLeftAtoms_iff
      hleft hright root outsideAtom).2
    simp [switchedLeftB, hcut, hleftB]
  unfold recoverableSwitchedLeftFamily
  exact (canonicalAtom_value_mem_values_iff _ outsideAtom).2 houtAtoms

theorem recoverableSwitchedLeftFamily_mem_boundary_of_separated
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          canonicalDisagreementCut (List.mem_filter.mp hleftBoundary).1
            hright root atom = false) :
    recoverableSwitchedLeftFamily
        (List.mem_filter.mp hleftBoundary).1 hright root ∈
      boundaryTargetFamilies small n := by
  let hleft := (List.mem_filter.mp hleftBoundary).1
  obtain ⟨outside, houtside, plaquette, hplaquette,
      hplaquetteOutside⟩ :=
    boundaryTargetFamily_has_outside_witness hsmall hleftBoundary
  have houtsideBox : polymerInsideBoxB small n outside = false := by
    cases hinside : polymerInsideBoxB small n outside with
    | false => rfl
    | true =>
        have hin := (polymerInsideBoxB_true_iff small n outside).1
          hinside plaquette hplaquette
        exact False.elim (hplaquetteOutside hin)
  have houtsideOutput : outside ∈
      recoverableSwitchedLeftFamily hleft hright root :=
    outside_support_mem_recoverableSwitchedLeft_of_separated
      hleft hright root houtside houtsideBox hseparated
  have houtCompat :=
    (recoverableSwitchedFamilies_mem_compatible hleft hright root).1
  have hnotEmbedded : recoverableSwitchedLeftFamily hleft hright root ∉
      embeddedCompatibleFamilies small n := by
    intro hembedded
    have hinside := familyInsideBox_of_mem_embeddedCompatibleFamilies
      hsmall hembedded
    exact hplaquetteOutside
      (hinside outside houtsideOutput plaquette hplaquette)
  unfold boundaryTargetFamilies
  apply List.mem_filter.mpr
  exact ⟨houtCompat, by
    unfold embeddedFamilyB
    simp [hnotEmbedded]⟩

theorem recoverableSwitchedRightFamily_mem_embedded_of_separated
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hrightEmbedded : right ∈ embeddedCompatibleFamilies small n)
    (root : CanonicalAtom n)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          canonicalDisagreementCut hleft
            (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
            root atom = false) :
    recoverableSwitchedRightFamily hleft
        (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
        root ∈ embeddedCompatibleFamilies small n := by
  let hright := embeddedCompatibleFamilies_member_target
    hsmall hrightEmbedded
  have hrightInside := familyInsideBox_of_mem_embeddedCompatibleFamilies
    hsmall hrightEmbedded
  have houtInside := recoverableSwitchedRightFamily_inside_of_separated
    hleft hright root hrightInside hseparated
  have houtCompat :=
    (recoverableSwitchedFamilies_mem_compatible hleft hright root).2
  exact family_mem_embeddedCompatibleFamilies_of_inside
    hsmall houtCompat houtInside

/-- Complete recoverable separated-branch switch.  This strengthens the
earlier per-pair result by using the cut that is reconstructible from the
output, so the same map is also globally injective. -/
theorem separated_recoverable_boundary_event_pair_switch
    (w : Q') {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hrightEmbedded : right ∈ embeddedCompatibleFamilies small n)
    {rootPolymer : List Nat} (hroot : rootPolymer ∈ left)
    (hrootRight : rootPolymer ∉ right)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ left →
        polymerInsideBoxB small n atom.val = false →
          canonicalDisagreementCut
            (List.mem_filter.mp hleftBoundary).1
            (embeddedCompatibleFamilies_member_target
              hsmall hrightEmbedded)
            (leftCanonicalAtomOfMember
              (List.mem_filter.mp hleftBoundary).1 hroot) atom = false) :
    recoverableSwitchedLeftFamily
        (List.mem_filter.mp hleftBoundary).1
        (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
        (leftCanonicalAtomOfMember
          (List.mem_filter.mp hleftBoundary).1 hroot) ∈
        boundaryTargetFamilies small n ∧
      familyContainsPolymerB rootPolymer
        (recoverableSwitchedLeftFamily
          (List.mem_filter.mp hleftBoundary).1
          (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
          (leftCanonicalAtomOfMember
            (List.mem_filter.mp hleftBoundary).1 hroot)) = false ∧
      recoverableSwitchedRightFamily
        (List.mem_filter.mp hleftBoundary).1
        (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
        (leftCanonicalAtomOfMember
          (List.mem_filter.mp hleftBoundary).1 hroot) ∈
        embeddedCompatibleFamilies small n ∧
      familyContainsPolymerB rootPolymer
        (recoverableSwitchedRightFamily
          (List.mem_filter.mp hleftBoundary).1
          (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
          (leftCanonicalAtomOfMember
            (List.mem_filter.mp hleftBoundary).1 hroot)) = true ∧
      canonicalSurfaceFamilyActivity w n
          (recoverableSwitchedLeftFamily
            (List.mem_filter.mp hleftBoundary).1
            (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
            (leftCanonicalAtomOfMember
              (List.mem_filter.mp hleftBoundary).1 hroot)) *
        canonicalSurfaceFamilyActivity w n
          (recoverableSwitchedRightFamily
            (List.mem_filter.mp hleftBoundary).1
            (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
            (leftCanonicalAtomOfMember
              (List.mem_filter.mp hleftBoundary).1 hroot)) ≈
      canonicalSurfaceFamilyActivity w n left *
        canonicalSurfaceFamilyActivity w n right := by
  let hleft := (List.mem_filter.mp hleftBoundary).1
  let hright := embeddedCompatibleFamilies_member_target
    hsmall hrightEmbedded
  let root := leftCanonicalAtomOfMember hleft hroot
  have hboundary := recoverableSwitchedLeftFamily_mem_boundary_of_separated
    hsmall hleftBoundary hright root hseparated
  have hembedded := recoverableSwitchedRightFamily_mem_embedded_of_separated
    hsmall hleft hrightEmbedded root hseparated
  have hrootCells := recoverableSwitchedFamilies_root_cells
    hleft hright hroot hrootRight
  have hweight := recoverableSwitchedFamilies_weight_preserved
    w hleft hright root
  exact ⟨hboundary, hrootCells.1, hembedded,
    hrootCells.2, hweight⟩

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
      rw [canonicalAtomList_eq_of_values_eq htail]

/-- The raw-family recoverable switch is injective for a fixed marked
polymer, even though the proof-carrying root atoms arise from different source
membership proofs. -/
theorem recoverableBoundarySwitch_injective
    {n : Nat}
    {left₁ right₁ left₂ right₂ : List (List Nat)}
    (hleft₁ : left₁ ∈ canonicalCompatibleAmbientFamilies n)
    (hright₁ : right₁ ∈ canonicalCompatibleAmbientFamilies n)
    (hleft₂ : left₂ ∈ canonicalCompatibleAmbientFamilies n)
    (hright₂ : right₂ ∈ canonicalCompatibleAmbientFamilies n)
    {rootPolymer : List Nat}
    (hroot₁ : rootPolymer ∈ left₁)
    (hroot₂ : rootPolymer ∈ left₂)
    (hleftOutput :
      recoverableSwitchedLeftFamily hleft₁ hright₁
          (leftCanonicalAtomOfMember hleft₁ hroot₁) =
        recoverableSwitchedLeftFamily hleft₂ hright₂
          (leftCanonicalAtomOfMember hleft₂ hroot₂))
    (hrightOutput :
      recoverableSwitchedRightFamily hleft₁ hright₁
          (leftCanonicalAtomOfMember hleft₁ hroot₁) =
        recoverableSwitchedRightFamily hleft₂ hright₂
          (leftCanonicalAtomOfMember hleft₂ hroot₂)) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  let root₁ := leftCanonicalAtomOfMember hleft₁ hroot₁
  let root₂ := leftCanonicalAtomOfMember hleft₂ hroot₂
  have hrootAtoms : root₁ = root₂ := Subtype.ext rfl
  have hleftAtoms :
      recoverableSwitchedLeftAtoms hleft₁ hright₁ root₁ =
        recoverableSwitchedLeftAtoms hleft₂ hright₂ root₂ :=
    canonicalAtomList_eq_of_values_eq hleftOutput
  have hrightAtoms :
      recoverableSwitchedRightAtoms hleft₁ hright₁ root₁ =
        recoverableSwitchedRightAtoms hleft₂ hright₂ root₂ :=
    canonicalAtomList_eq_of_values_eq hrightOutput
  rw [hrootAtoms] at hleftAtoms hrightAtoms
  have hatoms := rooted_component_switched_families_injective
    (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n)
    (canonicalAtomCompatibleB_symm n) root₂
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

/-! ### Constructive connected-versus-separated split -/

def boundaryOutsideDisagreementReachB
    {n : Nat} {left right : List (List Nat)}
    (small : Nat)
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) : Bool :=
  (canonicalFamilyAtoms hleft).any (fun outside =>
    (!(polymerInsideBoxB small n outside.val)) &&
      canonicalDisagreementCut hleft hright root outside)

theorem boundaryDisagreementReachDichotomy
    {small n : Nat} {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {rootPolymer : List Nat} (hroot : rootPolymer ∈ left) :
    (∃ outside : CanonicalAtom n,
      outside.val ∈ left ∧
        polymerInsideBoxB small n outside.val = false ∧
          canonicalDisagreementCut
            (List.mem_filter.mp hleftBoundary).1 hright
            (leftCanonicalAtomOfMember
              (List.mem_filter.mp hleftBoundary).1 hroot) outside = true) ∨
      (∀ outside : CanonicalAtom n,
        outside.val ∈ left →
          polymerInsideBoxB small n outside.val = false →
            canonicalDisagreementCut
              (List.mem_filter.mp hleftBoundary).1 hright
              (leftCanonicalAtomOfMember
                (List.mem_filter.mp hleftBoundary).1 hroot) outside = false) := by
  let hleft := (List.mem_filter.mp hleftBoundary).1
  let root := leftCanonicalAtomOfMember hleft hroot
  cases hdecision : boundaryOutsideDisagreementReachB
      small hleft hright root with
  | true =>
      left
      obtain ⟨outside, houtsideAtoms, hterm⟩ :=
        List.any_eq_true.mp hdecision
      have hparts := (Bool.and_eq_true _ _).mp hterm
      have houtside : polymerInsideBoxB small n outside.val = false := by
        cases hinside : polymerInsideBoxB small n outside.val <;>
          simp_all
      exact ⟨outside,
        (canonicalFamilyAtom_mem_iff hleft outside).1 houtsideAtoms,
        houtside, hparts.2⟩
  | false =>
      right
      intro outside houtsideFamily houtside
      cases hreach : canonicalDisagreementCut hleft hright root outside with
      | false => rfl
      | true =>
          have houtsideAtoms : outside ∈ canonicalFamilyAtoms hleft :=
            (canonicalFamilyAtom_mem_iff hleft outside).2 houtsideFamily
          have hany : boundaryOutsideDisagreementReachB
              small hleft hright root = true := by
            apply List.any_eq_true.mpr
            exact ⟨outside, houtsideAtoms,
              by simp [houtside, hreach]⟩
          rw [hdecision] at hany
          exact False.elim (Bool.false_ne_true hany)

/-- The recoverable switch is globally injective on canonical compatible
family pairs whose right replica avoids the fixed root atom. -/
theorem recoverableSwitchedAtoms_injective
    {n : Nat}
    {left₁ right₁ left₂ right₂ : List (List Nat)}
    (hleft₁ : left₁ ∈ canonicalCompatibleAmbientFamilies n)
    (hright₁ : right₁ ∈ canonicalCompatibleAmbientFamilies n)
    (hleft₂ : left₂ ∈ canonicalCompatibleAmbientFamilies n)
    (hright₂ : right₂ ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    (hleftOutput :
      recoverableSwitchedLeftAtoms hleft₁ hright₁ root =
        recoverableSwitchedLeftAtoms hleft₂ hright₂ root)
    (hrightOutput :
      recoverableSwitchedRightAtoms hleft₁ hright₁ root =
        recoverableSwitchedRightAtoms hleft₂ hright₂ root) :
    canonicalFamilyAtoms hleft₁ = canonicalFamilyAtoms hleft₂ ∧
      canonicalFamilyAtoms hright₁ = canonicalFamilyAtoms hright₂ := by
  exact rooted_component_switched_families_injective
    (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n)
    (canonicalAtomCompatibleB_symm n) root
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_mem_sublists hleft₁)
    (canonicalFamilyAtoms_mem_sublists hright₁)
    (canonicalFamilyAtoms_mem_sublists hleft₂)
    (canonicalFamilyAtoms_mem_sublists hright₂)
    (canonicalFamilyAtoms_compatible hleft₁)
    (canonicalFamilyAtoms_compatible hright₁)
    (canonicalFamilyAtoms_compatible hleft₂)
    (canonicalFamilyAtoms_compatible hright₂)
    hleftOutput hrightOutput

/-- Value-level form: equality of switched proof-carrying atom lists recovers
the two original literal polymer families. -/
theorem recoverableSwitchedFamilies_injective
    {n : Nat}
    {left₁ right₁ left₂ right₂ : List (List Nat)}
    (hleft₁ : left₁ ∈ canonicalCompatibleAmbientFamilies n)
    (hright₁ : right₁ ∈ canonicalCompatibleAmbientFamilies n)
    (hleft₂ : left₂ ∈ canonicalCompatibleAmbientFamilies n)
    (hright₂ : right₂ ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    (hleftOutput :
      recoverableSwitchedLeftAtoms hleft₁ hright₁ root =
        recoverableSwitchedLeftAtoms hleft₂ hright₂ root)
    (hrightOutput :
      recoverableSwitchedRightAtoms hleft₁ hright₁ root =
        recoverableSwitchedRightAtoms hleft₂ hright₂ root) :
    left₁ = left₂ ∧ right₁ = right₂ := by
  have hatoms := recoverableSwitchedAtoms_injective
    hleft₁ hright₁ hleft₂ hright₂ root
    hleftOutput hrightOutput
  constructor
  · rw [← canonicalFamilyAtoms_values hleft₁,
      ← canonicalFamilyAtoms_values hleft₂, hatoms.1]
  · rw [← canonicalFamilyAtoms_values hright₁,
      ← canonicalFamilyAtoms_values hright₂, hatoms.2]

/-! ## 3. The recovered component carries a canonical geometric path -/

theorem canonicalDisagreementEdge_incompatible
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    {first second : CanonicalAtom n}
    (hedge : disagreementEdge (canonicalAmbientAtoms n)
      (canonicalAtomCompatibleB n)
      (memberB (canonicalFamilyAtoms hleft))
      (memberB (canonicalFamilyAtoms hright)) first second = true) :
    canonicalPolymerCompatibleB n first.val second.val = false := by
  have hdisagreement := (Bool.and_eq_true _ _).mp hedge |>.2
  have hconflict := (Bool.and_eq_true _ _).mp hdisagreement |>.2
  change canonicalAtomCompatibleB n first second = false
  cases hcompat : canonicalAtomCompatibleB n first second <;>
    simp_all

def disagreementDWalkToCanonicalPath
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n) :
    {first second : CanonicalAtom n} →
      DWalk (disagreementEdge (canonicalAmbientAtoms n)
        (canonicalAtomCompatibleB n)
        (memberB (canonicalFamilyAtoms hleft))
        (memberB (canonicalFamilyAtoms hright))) first second →
      CanonicalIncompatibilityPath n first second
  | _, _, .refl atom => .refl atom
  | _, _, .edge hedge =>
      .edge (canonicalDisagreementEdge_incompatible hleft hright hedge)
  | _, _, .trans first second =>
      .trans (disagreementDWalkToCanonicalPath hleft hright first)
        (disagreementDWalkToCanonicalPath hleft hright second)

def canonicalDisagreementPath
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root atom : CanonicalAtom n)
    (hreaches : canonicalDisagreementCut hleft hright root atom = true) :
    CanonicalIncompatibilityPath n root atom :=
  disagreementDWalkToCanonicalPath hleft hright
    (warshallSound
      (disagreementEdge (canonicalAmbientAtoms n)
        (canonicalAtomCompatibleB n)
        (memberB (canonicalFamilyAtoms hleft))
        (memberB (canonicalFamilyAtoms hright)))
      (canonicalAmbientAtoms n) root atom hreaches)

/-- If the recoverable component reaches a polymer leaving the smaller box,
the extracted incompatibility path pays the full root-to-boundary distance. -/
theorem connectedCanonicalDisagreement_path_cost_floor
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root outside : CanonicalAtom n)
    {start inner distance : Nat}
    (houtside : polymerInsideBoxB small n outside.val = false)
    (hstart : start ∈ root.val)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small)
    (hconnected : canonicalDisagreementCut hleft hright root outside = true) :
    distance + 2 ≤
      (canonicalDisagreementPath hleft hright root outside hconnected).cost := by
  obtain ⟨outsidePlaquette, houtsidePlaquette, houtsideSmall⟩ :=
    polymerInsideBoxB_false_witness houtside
  obtain ⟨finish, hfinish, hfinishEq⟩ :=
    List.mem_map.mp houtsidePlaquette
  have hfinishOutside :
      boxPlaquetteAt n finish ∉ boxPlaquettes small := by
    rw [hfinishEq]
    exact houtsideSmall
  have houtSmall : outsideBoxB small
      (boxPlaquetteAt n finish) = true :=
    (outsideBoxB_true_iff_not_mem small
      (boxPlaquetteAt n finish)).2 hfinishOutside
  have houtExpanded : outsideBoxB (inner + distance)
      (boxPlaquetteAt n finish) = true := by
    rw [hbox]
    exact houtSmall
  have hsep := outside_expanded_box_linf_floor hstartInner houtExpanded
  have hcost := canonicalIncompatibilityPath_cost_floor
    (canonicalDisagreementPath hleft hright root outside hconnected)
    hstart hfinish
  omega

end YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.canonical_reverse_component_recovers
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.canonicalDisagreementCut_closed
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.recoverableSwitchedAtoms_compatible
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.recoverableSwitchedAtoms_weight_preserved
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.recoverableSwitchedFamilies_mem_compatible
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.recoverableSwitchedFamilies_weight_preserved
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.recoverableSwitchedFamilies_root_cells
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.separated_recoverable_boundary_event_pair_switch
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.recoverableBoundarySwitch_injective
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.boundaryDisagreementReachDichotomy
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.recoverableSwitchedAtoms_injective
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.recoverableSwitchedFamilies_injective
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.canonicalDisagreementEdge_incompatible
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.disagreementDWalkToCanonicalPath
#print axioms YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery.connectedCanonicalDisagreement_path_cost_floor
