/-
# Marked-component switching for spin-summed support activities

The canonical disagreement-component switch is purely combinatorial: it moves
whole connected supports between two replicas.  Its generic finite theorem
preserves the product for any single-polymer weight.  This module instantiates
that theorem with the exact arbitrary-cutoff spin-summed support activity.
-/

import YMGap.Continuum.Z4SpinSummedCompatibleGas
import YMGap.Continuum.Z4CanonicalMarkedRootSwitch

namespace YMGap.Continuum.Z4SpinSummedMarkedRootSwitch

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper

local infix:50 " ≈ " => Q'.eqv

theorem markedAtomList_spinSummedWeight_eq (cutoff n : Nat) :
    ∀ atoms : List (CanonicalAtom n),
      familyWeight (fun atom : CanonicalAtom n =>
          parametricKSupportActivity cutoff n atom.val) atoms =
        parametricKSupportFamilyActivity cutoff n
          (atoms.map Subtype.val)
  | [] => rfl
  | _ :: rest => by
      simp only [familyWeight_cons, List.map,
        parametricKSupportFamilyActivity]
      rw [markedAtomList_spinSummedWeight_eq cutoff n rest]

theorem recoverableMarkedSwitchedAtoms_spinSummed_weight_preserved
    (cutoff : Nat) {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    familyWeight (fun atom : CanonicalAtom n =>
        parametricKSupportActivity cutoff n atom.val)
        (recoverableMarkedSwitchedLeftAtoms hleft hright roots) *
      familyWeight (fun atom : CanonicalAtom n =>
        parametricKSupportActivity cutoff n atom.val)
        (recoverableMarkedSwitchedRightAtoms hleft hright roots) ≈
    familyWeight (fun atom : CanonicalAtom n =>
        parametricKSupportActivity cutoff n atom.val)
        (canonicalFamilyAtoms hleft) *
      familyWeight (fun atom : CanonicalAtom n =>
        parametricKSupportActivity cutoff n atom.val)
        (canonicalFamilyAtoms hright) := by
  unfold recoverableMarkedSwitchedLeftAtoms
    recoverableMarkedSwitchedRightAtoms
  exact markedRootComponentSwitched_pair_weight_preserved
    (fun atom : CanonicalAtom n =>
      parametricKSupportActivity cutoff n atom.val)
    (canonicalAtomCompatibleB n) roots
    (canonicalAmbientAtoms_nodup n)
    (canonicalFamilyAtoms_mem_sublists hleft)
    (canonicalFamilyAtoms_mem_sublists hright)

theorem recoverableMarkedSwitchedFamilies_spinSummed_weight_preserved
    (cutoff : Nat) {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n)) :
    parametricKSupportFamilyActivity cutoff n
        (recoverableMarkedSwitchedLeftFamily hleft hright roots) *
      parametricKSupportFamilyActivity cutoff n
        (recoverableMarkedSwitchedRightFamily hleft hright roots) ≈
    parametricKSupportFamilyActivity cutoff n left *
      parametricKSupportFamilyActivity cutoff n right := by
  have hweight :=
    recoverableMarkedSwitchedAtoms_spinSummed_weight_preserved
      cutoff hleft hright roots
  rw [markedAtomList_spinSummedWeight_eq cutoff n] at hweight
  rw [markedAtomList_spinSummedWeight_eq cutoff n] at hweight
  rw [markedAtomList_spinSummedWeight_eq cutoff n] at hweight
  rw [markedAtomList_spinSummedWeight_eq cutoff n] at hweight
  rw [canonicalFamilyAtoms_values hleft] at hweight
  rw [canonicalFamilyAtoms_values hright] at hweight
  exact hweight

end YMGap.Continuum.Z4SpinSummedMarkedRootSwitch

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedMarkedRootSwitch.markedAtomList_spinSummedWeight_eq
#print axioms YMGap.Continuum.Z4SpinSummedMarkedRootSwitch.recoverableMarkedSwitchedFamilies_spinSummed_weight_preserved
