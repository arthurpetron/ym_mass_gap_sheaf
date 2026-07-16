/-
# Marked switching for an affine time-shifted embedded cell

The translated source gas is now treated as a literal restricted target gas.
This file performs the finite marked-component switch against its complement
inside the full target compatible-family list.  No convergence statement is
assumed: the four cylinder cells cancel by an explicit weight-preserving
injection, leaving exactly the connected shifted-boundary residue.
-/

import YMGap.Continuum.Z4CouplingParametricCylinderWeights
import YMGap.Continuum.Z4TimeShiftedEmbeddedRegion

namespace YMGap.Continuum.Z4TimeShiftedCylinderSwitchSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
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
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedEmbeddedRegion

local infix:50 " ≈ " => Q'.eqv

abbrev PolymerFamily := List (List Nat)
abbrev RawFamilyPair := PolymerFamily × PolymerFamily

def timeShiftMarkedCylinderEvent
    {shift base : Nat} (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) : PolymerFamily → Bool :=
  cylinderEvent (roots.map Subtype.val) predicate

/-! ## 1. The shifted embedded cell and its literal boundary complement -/

def timeShiftBoundaryTargetFamilies (shift base : Nat) :
    List PolymerFamily :=
  (canonicalCompatibleAmbientFamilies (base + shift)).filter
    (fun family =>
      !(family.all (targetRootInsideTimeShiftB shift base)))

theorem mem_timeShiftBoundaryTargetFamilies_iff
    {shift base : Nat} {family : PolymerFamily} :
    family ∈ timeShiftBoundaryTargetFamilies shift base ↔
      family ∈ canonicalCompatibleAmbientFamilies (base + shift) ∧
        family.all (targetRootInsideTimeShiftB shift base) = false := by
  unfold timeShiftBoundaryTargetFamilies
  rw [List.mem_filter]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    cases hall : family.all (targetRootInsideTimeShiftB shift base) <;>
      simp_all
  · intro h
    exact ⟨h.1, by simp [h.2]⟩

theorem timeShiftBoundaryTargetFamilies_nodup (shift base : Nat) :
    (timeShiftBoundaryTargetFamilies shift base).Nodup := by
  unfold timeShiftBoundaryTargetFamilies
  exact List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup (base + shift))

theorem timeShiftEmbeddedTargetFamilies_nodup (shift base : Nat) :
    (timeShiftEmbeddedTargetFamilies shift base).Nodup := by
  unfold timeShiftEmbeddedTargetFamilies
  exact List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup (base + shift))

theorem timeShiftEmbeddedTargetFamilies_member_target
    {shift base : Nat} {family : PolymerFamily}
    (hfamily : family ∈ timeShiftEmbeddedTargetFamilies shift base) :
    family ∈ canonicalCompatibleAmbientFamilies (base + shift) :=
  (mem_timeShiftEmbeddedTargetFamilies_iff.mp hfamily).1

/-! ## 2. Shifted separation and the two switched cells -/

def timeShiftBoundaryOutsideMarkedReachB
    {shift base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (roots : List (CanonicalAtom (base + shift))) : Bool :=
  (canonicalFamilyAtoms hleft).any (fun atom =>
    (!(targetRootInsideTimeShiftB shift base atom.val)) &&
      canonicalMarkedCut hleft hright roots atom)

theorem timeShiftBoundaryOutsideMarkedReachB_false_separated
    {shift base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (roots : List (CanonicalAtom (base + shift)))
    (hreach : timeShiftBoundaryOutsideMarkedReachB
      hleft hright roots = false) :
    ∀ atom : CanonicalAtom (base + shift), atom.val ∈ left →
      targetRootInsideTimeShiftB shift base atom.val = false →
        canonicalMarkedCut hleft hright roots atom = false := by
  intro atom hatom houtside
  cases hcut : canonicalMarkedCut hleft hright roots atom with
  | false => rfl
  | true =>
      have hatomList : atom ∈ canonicalFamilyAtoms hleft :=
        (canonicalFamilyAtom_mem_iff hleft atom).2 hatom
      have hterm :
          ((!(targetRootInsideTimeShiftB shift base atom.val)) &&
            canonicalMarkedCut hleft hright roots atom) = true := by
        simp [houtside, hcut]
      have hany : (canonicalFamilyAtoms hleft).any (fun found =>
          (!(targetRootInsideTimeShiftB shift base found.val)) &&
            canonicalMarkedCut hleft hright roots found) = true :=
        List.any_eq_true.mpr ⟨atom, hatomList, hterm⟩
      unfold timeShiftBoundaryOutsideMarkedReachB at hreach
      rw [hreach] at hany
      exact False.elim (Bool.false_ne_true hany)

theorem timeShiftBoundaryOutsideMarkedReachB_true_root_witness
    {shift base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (roots : List (CanonicalAtom (base + shift)))
    (hreach : timeShiftBoundaryOutsideMarkedReachB
      hleft hright roots = true) :
    ∃ root outside : CanonicalAtom (base + shift),
      root ∈ roots ∧ outside.val ∈ left ∧
        targetRootInsideTimeShiftB shift base outside.val = false ∧
          canonicalDisagreementCut hleft hright root outside = true := by
  unfold timeShiftBoundaryOutsideMarkedReachB at hreach
  obtain ⟨outside, houtsideAtoms, hterm⟩ := List.any_eq_true.mp hreach
  have hparts := (Bool.and_eq_true _ _).mp hterm
  have houtside : targetRootInsideTimeShiftB
      shift base outside.val = false := by
    cases hinside : targetRootInsideTimeShiftB shift base outside.val <;>
      simp_all
  obtain ⟨root, hroot, hrootReach⟩ :=
    canonicalMarkedCut_true_has_root hleft hright roots outside hparts.2
  exact ⟨root, outside, hroot,
    (canonicalFamilyAtom_mem_iff hleft outside).1 houtsideAtoms,
    houtside, hrootReach⟩

theorem recoverableMarkedSwitchedRightFamily_mem_timeShiftEmbedded_of_separated
    {shift base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (hrightEmbedded : right ∈
      timeShiftEmbeddedTargetFamilies shift base)
    (roots : List (CanonicalAtom (base + shift)))
    (hseparated : ∀ atom : CanonicalAtom (base + shift),
      atom.val ∈ left →
        targetRootInsideTimeShiftB shift base atom.val = false →
          canonicalMarkedCut hleft
            (timeShiftEmbeddedTargetFamilies_member_target hrightEmbedded)
            roots atom = false) :
    recoverableMarkedSwitchedRightFamily hleft
        (timeShiftEmbeddedTargetFamilies_member_target hrightEmbedded)
        roots ∈ timeShiftEmbeddedTargetFamilies shift base := by
  let hright := timeShiftEmbeddedTargetFamilies_member_target hrightEmbedded
  have houtCompat :=
    (recoverableMarkedSwitchedFamilies_mem_compatible
      hleft hright roots).2
  apply mem_timeShiftEmbeddedTargetFamilies_iff.mpr
  refine ⟨houtCompat, ?_⟩
  rw [List.all_eq_true]
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
      exact List.all_eq_true.mp
        (mem_timeShiftEmbeddedTargetFamilies_iff.mp hrightEmbedded).2
        atom.val hrightRaw
  | true =>
      have hleftAtom : atom ∈ canonicalFamilyAtoms hleft := by
        have hmemberB : memberB (canonicalFamilyAtoms hleft) atom = true := by
          simpa [switchedRightB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      have hleftRaw : atom.val ∈ left :=
        (canonicalFamilyAtom_mem_iff hleft atom).1 hleftAtom
      cases hinside : targetRootInsideTimeShiftB shift base atom.val with
      | true => rfl
      | false =>
          have hnotReach := hseparated atom hleftRaw hinside
          rw [hnotReach] at hcut
          exact False.elim (Bool.false_ne_true hcut)

theorem outside_support_mem_recoverableMarkedSwitchedLeft_of_timeShiftSeparated
    {shift base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (roots : List (CanonicalAtom (base + shift)))
    {outside : List Nat} (houtside : outside ∈ left)
    (houtsideRegion : targetRootInsideTimeShiftB
      shift base outside = false)
    (hseparated : ∀ atom : CanonicalAtom (base + shift),
      atom.val ∈ left →
        targetRootInsideTimeShiftB shift base atom.val = false →
          canonicalMarkedCut hleft hright roots atom = false) :
    outside ∈ recoverableMarkedSwitchedLeftFamily
      hleft hright roots := by
  let outsideAtom : CanonicalAtom (base + shift) :=
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

theorem recoverableMarkedSwitchedLeftFamily_mem_timeShiftBoundary_of_separated
    {shift base : Nat} {left right : PolymerFamily}
    (hleftBoundary : left ∈ timeShiftBoundaryTargetFamilies shift base)
    (hright : right ∈ canonicalCompatibleAmbientFamilies (base + shift))
    (roots : List (CanonicalAtom (base + shift)))
    (hseparated : ∀ atom : CanonicalAtom (base + shift),
      atom.val ∈ left →
        targetRootInsideTimeShiftB shift base atom.val = false →
          canonicalMarkedCut
            (mem_timeShiftBoundaryTargetFamilies_iff.mp hleftBoundary).1
            hright roots atom = false) :
    recoverableMarkedSwitchedLeftFamily
        (mem_timeShiftBoundaryTargetFamilies_iff.mp hleftBoundary).1
        hright roots ∈ timeShiftBoundaryTargetFamilies shift base := by
  let hleft := (mem_timeShiftBoundaryTargetFamilies_iff.mp hleftBoundary).1
  have hleftAllFalse :=
    (mem_timeShiftBoundaryTargetFamilies_iff.mp hleftBoundary).2
  let witness := allFalseWitness
    (targetRootInsideTimeShiftB shift base) left hleftAllFalse
  let outside := witness.1
  have houtside : outside ∈ left := witness.2.1
  have houtsideRegion : targetRootInsideTimeShiftB
      shift base outside = false := witness.2.2
  have houtsideOutput : outside ∈
      recoverableMarkedSwitchedLeftFamily hleft hright roots :=
    outside_support_mem_recoverableMarkedSwitchedLeft_of_timeShiftSeparated
      hleft hright roots houtside houtsideRegion hseparated
  have houtCompat :=
    (recoverableMarkedSwitchedFamilies_mem_compatible
      hleft hright roots).1
  apply mem_timeShiftBoundaryTargetFamilies_iff.mpr
  refine ⟨houtCompat, ?_⟩
  cases houtAll : (recoverableMarkedSwitchedLeftFamily
      hleft hright roots).all
        (targetRootInsideTimeShiftB shift base) with
  | false => rfl
  | true =>
      have hinside := List.all_eq_true.mp houtAll
        outside houtsideOutput
      rw [houtsideRegion] at hinside
      exact False.elim (Bool.false_ne_true hinside)

/-! ## 3. The four finite cylinder cells -/

def timeShiftBoundaryCylinderEventFamilyList
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (timeShiftBoundaryTargetFamilies shift base).filter
    (timeShiftMarkedCylinderEvent roots predicate)

def timeShiftEmbeddedCylinderComplementFamilyList
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (timeShiftEmbeddedTargetFamilies shift base).filter
    (fun family => !(timeShiftMarkedCylinderEvent roots predicate family))

def timeShiftBoundaryCylinderComplementFamilyList
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (timeShiftBoundaryTargetFamilies shift base).filter
    (fun family => !(timeShiftMarkedCylinderEvent roots predicate family))

def timeShiftEmbeddedCylinderEventFamilyList
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (timeShiftEmbeddedTargetFamilies shift base).filter
    (timeShiftMarkedCylinderEvent roots predicate)

abbrev TimeShiftBoundaryCylinderEventEntry
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :=
  {family : PolymerFamily // family ∈
    timeShiftBoundaryCylinderEventFamilyList shift base roots predicate}

abbrev TimeShiftEmbeddedCylinderComplementEntry
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :=
  {family : PolymerFamily // family ∈
    timeShiftEmbeddedCylinderComplementFamilyList shift base roots predicate}

abbrev TimeShiftCylinderSourcePair
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :=
  TimeShiftBoundaryCylinderEventEntry shift base roots predicate ×
    TimeShiftEmbeddedCylinderComplementEntry shift base roots predicate

def timeShiftBoundaryCylinderEventEntries
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    List (TimeShiftBoundaryCylinderEventEntry
      shift base roots predicate) :=
  (timeShiftBoundaryCylinderEventFamilyList
    shift base roots predicate).attach

def timeShiftEmbeddedCylinderComplementEntries
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    List (TimeShiftEmbeddedCylinderComplementEntry
      shift base roots predicate) :=
  (timeShiftEmbeddedCylinderComplementFamilyList
    shift base roots predicate).attach

def timeShiftCylinderSourcePairList
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    List (TimeShiftCylinderSourcePair shift base roots predicate) :=
  cartesian
    (timeShiftBoundaryCylinderEventEntries shift base roots predicate)
    (timeShiftEmbeddedCylinderComplementEntries
      shift base roots predicate)

def timeShiftCylinderTargetPairList
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) : List RawFamilyPair :=
  cartesian
    (timeShiftBoundaryCylinderComplementFamilyList
      shift base roots predicate)
    (timeShiftEmbeddedCylinderEventFamilyList
      shift base roots predicate)

def timeShiftCylinderSourceLeftBoundary
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    pair.1.val ∈ timeShiftBoundaryTargetFamilies shift base :=
  (List.mem_filter.mp pair.1.property).1

def timeShiftCylinderSourceRightEmbedded
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    pair.2.val ∈ timeShiftEmbeddedTargetFamilies shift base :=
  (List.mem_filter.mp pair.2.property).1

def timeShiftCylinderSourceLeftCompatible
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    pair.1.val ∈ canonicalCompatibleAmbientFamilies (base + shift) :=
  (mem_timeShiftBoundaryTargetFamilies_iff.mp
    (timeShiftCylinderSourceLeftBoundary pair)).1

def timeShiftCylinderSourceRightCompatible
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    pair.2.val ∈ canonicalCompatibleAmbientFamilies (base + shift) :=
  timeShiftEmbeddedTargetFamilies_member_target
    (timeShiftCylinderSourceRightEmbedded pair)

def timeShiftCylinderSourceSeparatedB
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) : Bool :=
  !(timeShiftBoundaryOutsideMarkedReachB
    (timeShiftCylinderSourceLeftCompatible pair)
    (timeShiftCylinderSourceRightCompatible pair) roots)

def separatedTimeShiftCylinderSourcePairs
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool} :
    List (TimeShiftCylinderSourcePair shift base roots predicate) :=
  (timeShiftCylinderSourcePairList shift base roots predicate).filter
    timeShiftCylinderSourceSeparatedB

def connectedTimeShiftCylinderSourcePairs
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool} :
    List (TimeShiftCylinderSourcePair shift base roots predicate) :=
  (timeShiftCylinderSourcePairList shift base roots predicate).filter
    (fun pair => !(timeShiftCylinderSourceSeparatedB pair))

def timeShiftSeparatedCylinderSwitchEncode
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    RawFamilyPair :=
  (recoverableMarkedSwitchedLeftFamily
      (timeShiftCylinderSourceLeftCompatible pair)
      (timeShiftCylinderSourceRightCompatible pair) roots,
    recoverableMarkedSwitchedRightFamily
      (timeShiftCylinderSourceLeftCompatible pair)
      (timeShiftCylinderSourceRightCompatible pair) roots)

theorem timeShiftSeparatedCylinderSwitchEncode_mem_target
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate)
    (hpair : pair ∈ separatedTimeShiftCylinderSourcePairs) :
    timeShiftSeparatedCylinderSwitchEncode pair ∈
      timeShiftCylinderTargetPairList shift base roots predicate := by
  have htest := (List.mem_filter.mp hpair).2
  have hdecision : timeShiftBoundaryOutsideMarkedReachB
      (timeShiftCylinderSourceLeftCompatible pair)
      (timeShiftCylinderSourceRightCompatible pair) roots = false := by
    unfold timeShiftCylinderSourceSeparatedB at htest
    cases hvalue : timeShiftBoundaryOutsideMarkedReachB
        (timeShiftCylinderSourceLeftCompatible pair)
        (timeShiftCylinderSourceRightCompatible pair) roots <;> simp_all
  have hseparated :=
    timeShiftBoundaryOutsideMarkedReachB_false_separated
      (timeShiftCylinderSourceLeftCompatible pair)
      (timeShiftCylinderSourceRightCompatible pair) roots hdecision
  have hleftOut :=
    recoverableMarkedSwitchedLeftFamily_mem_timeShiftBoundary_of_separated
      (timeShiftCylinderSourceLeftBoundary pair)
      (timeShiftCylinderSourceRightCompatible pair) roots hseparated
  have hrightOut :=
    recoverableMarkedSwitchedRightFamily_mem_timeShiftEmbedded_of_separated
      (timeShiftCylinderSourceLeftCompatible pair)
      (timeShiftCylinderSourceRightEmbedded pair) roots hseparated
  have hevents := recoverableMarkedSwitchedFamilies_cylinderEvent_swap
    (timeShiftCylinderSourceLeftCompatible pair)
    (timeShiftCylinderSourceRightCompatible pair) roots predicate
  apply (mem_cartesian_iff
    (timeShiftBoundaryCylinderComplementFamilyList
      shift base roots predicate)
    (timeShiftEmbeddedCylinderEventFamilyList
      shift base roots predicate)
    (timeShiftSeparatedCylinderSwitchEncode pair)).2
  constructor
  · apply List.mem_filter.mpr
    refine ⟨hleftOut, ?_⟩
    have hrightEventFalse : timeShiftMarkedCylinderEvent roots predicate
        pair.2.val = false := by
      have hraw := (List.mem_filter.mp pair.2.property).2
      cases hvalue : timeShiftMarkedCylinderEvent roots predicate
          pair.2.val <;> simp_all
    unfold timeShiftMarkedCylinderEvent at hrightEventFalse
    change (!(timeShiftMarkedCylinderEvent roots predicate
      (recoverableMarkedSwitchedLeftFamily
        (timeShiftCylinderSourceLeftCompatible pair)
        (timeShiftCylinderSourceRightCompatible pair) roots))) = true
    unfold timeShiftMarkedCylinderEvent
    rw [hevents.1, hrightEventFalse]
    rfl
  · apply List.mem_filter.mpr
    refine ⟨hrightOut, ?_⟩
    have hleftEvent : timeShiftMarkedCylinderEvent roots predicate
        pair.1.val = true :=
      (List.mem_filter.mp pair.1.property).2
    change timeShiftMarkedCylinderEvent roots predicate
      (recoverableMarkedSwitchedRightFamily
        (timeShiftCylinderSourceLeftCompatible pair)
        (timeShiftCylinderSourceRightCompatible pair) roots) = true
    unfold timeShiftMarkedCylinderEvent
    rw [hevents.2]
    exact hleftEvent

theorem timeShiftSeparatedCylinderSwitchEncode_injective
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (first second : TimeShiftCylinderSourcePair
      shift base roots predicate)
    (_hfirst : first ∈ separatedTimeShiftCylinderSourcePairs)
    (_hsecond : second ∈ separatedTimeShiftCylinderSourcePairs)
    (heq : timeShiftSeparatedCylinderSwitchEncode first =
      timeShiftSeparatedCylinderSwitchEncode second) : first = second := by
  have hleftOutput := congrArg Prod.fst heq
  have hrightOutput := congrArg Prod.snd heq
  have hsources := recoverableMarkedSwitchedFamilies_injective roots
    (timeShiftCylinderSourceLeftCompatible first)
    (timeShiftCylinderSourceRightCompatible first)
    (timeShiftCylinderSourceLeftCompatible second)
    (timeShiftCylinderSourceRightCompatible second)
    hleftOutput hrightOutput
  apply Prod.ext
  · exact Subtype.ext hsources.1
  · exact Subtype.ext hsources.2

/-! ## 4. Coupling-parametric exact cancellation -/

def couplingSpinSummedTimeShiftCylinderSourcePairWeight
    (coupling : Q') (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift) pair.1.val *
    couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift) pair.2.val

def couplingSpinSummedTimeShiftCylinderRawPairWeight
    (coupling : Q') (cutoff shift base : Nat)
    (pair : RawFamilyPair) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift) pair.1 *
    couplingParametricKSupportFamilyActivity coupling cutoff
      (base + shift) pair.2

theorem couplingSpinSummedTimeShiftSeparatedSwitchEncode_weight
    (coupling : Q') (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    couplingSpinSummedTimeShiftCylinderRawPairWeight
        coupling cutoff shift base
        (timeShiftSeparatedCylinderSwitchEncode pair) ≈
      couplingSpinSummedTimeShiftCylinderSourcePairWeight
        coupling cutoff pair := by
  exact
    recoverableMarkedSwitchedFamilies_couplingSpinSummed_weight_preserved
      coupling cutoff
      (timeShiftCylinderSourceLeftCompatible pair)
      (timeShiftCylinderSourceRightCompatible pair) roots

theorem timeShiftBoundaryCylinderEventFamilyList_nodup
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    (timeShiftBoundaryCylinderEventFamilyList
      shift base roots predicate).Nodup :=
  List.filter_sublist.nodup
    (timeShiftBoundaryTargetFamilies_nodup shift base)

theorem timeShiftEmbeddedCylinderComplementFamilyList_nodup
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    (timeShiftEmbeddedCylinderComplementFamilyList
      shift base roots predicate).Nodup :=
  List.filter_sublist.nodup
    (timeShiftEmbeddedTargetFamilies_nodup shift base)

theorem timeShiftBoundaryCylinderComplementFamilyList_nodup
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    (timeShiftBoundaryCylinderComplementFamilyList
      shift base roots predicate).Nodup :=
  List.filter_sublist.nodup
    (timeShiftBoundaryTargetFamilies_nodup shift base)

theorem timeShiftEmbeddedCylinderEventFamilyList_nodup
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    (timeShiftEmbeddedCylinderEventFamilyList
      shift base roots predicate).Nodup :=
  List.filter_sublist.nodup
    (timeShiftEmbeddedTargetFamilies_nodup shift base)

theorem timeShiftCylinderSourcePairList_nodup
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    (timeShiftCylinderSourcePairList shift base roots predicate).Nodup := by
  exact cartesian_nodup _ _
    (attach_nodup_of_nodup _
      (timeShiftBoundaryCylinderEventFamilyList_nodup
        shift base roots predicate))
    (attach_nodup_of_nodup _
      (timeShiftEmbeddedCylinderComplementFamilyList_nodup
        shift base roots predicate))

theorem separatedTimeShiftCylinderSourcePairs_nodup
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    (separatedTimeShiftCylinderSourcePairs
      (shift := shift) (base := base)
      (roots := roots) (predicate := predicate)).Nodup :=
  List.filter_sublist.nodup
    (timeShiftCylinderSourcePairList_nodup
      shift base roots predicate)

theorem timeShiftCylinderTargetPairList_nodup
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    (timeShiftCylinderTargetPairList
      shift base roots predicate).Nodup :=
  cartesian_nodup _ _
    (timeShiftBoundaryCylinderComplementFamilyList_nodup
      shift base roots predicate)
    (timeShiftEmbeddedCylinderEventFamilyList_nodup
      shift base roots predicate)

theorem couplingSpinSummedSeparatedTimeShiftCylinderPairSum_le_target
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat)
    (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTimeShiftCylinderSourcePairWeight
          coupling cutoff)
        (separatedTimeShiftCylinderSourcePairs
          (shift := shift) (base := base)
          (roots := roots) (predicate := predicate)) ≤
      listQSum
        (couplingSpinSummedTimeShiftCylinderRawPairWeight
          coupling cutoff shift base)
        (timeShiftCylinderTargetPairList
          shift base roots predicate) := by
  apply listQSum_le_of_injective
    (separatedTimeShiftCylinderSourcePairs
      (shift := shift) (base := base)
      (roots := roots) (predicate := predicate))
    (timeShiftCylinderTargetPairList shift base roots predicate)
    (couplingSpinSummedTimeShiftCylinderSourcePairWeight
      coupling cutoff)
    (couplingSpinSummedTimeShiftCylinderRawPairWeight
      coupling cutoff shift base)
    timeShiftSeparatedCylinderSwitchEncode
    (separatedTimeShiftCylinderSourcePairs_nodup
      shift base roots predicate)
  · exact timeShiftSeparatedCylinderSwitchEncode_mem_target
  · intro first hfirst second hsecond heq
    exact timeShiftSeparatedCylinderSwitchEncode_injective
      first second hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (couplingSpinSummedTimeShiftSeparatedSwitchEncode_weight
          coupling cutoff pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (base + shift) pair.1)
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (base + shift) pair.2)

theorem couplingSpinSummedTimeShiftCylinderSourcePairList_sum_eqv_product
    (coupling : Q') (cutoff shift base : Nat)
    (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTimeShiftCylinderSourcePairWeight
          coupling cutoff)
        (timeShiftCylinderSourcePairList shift base roots predicate) ≈
      listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (base + shift))
          (timeShiftBoundaryCylinderEventFamilyList
            shift base roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (base + shift))
          (timeShiftEmbeddedCylinderComplementFamilyList
            shift base roots predicate) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : TimeShiftBoundaryCylinderEventEntry
        shift base roots predicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff (base + shift) entry.val)
    (fun entry : TimeShiftEmbeddedCylinderComplementEntry
        shift base roots predicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff (base + shift) entry.val)
    (timeShiftBoundaryCylinderEventEntries
      shift base roots predicate)
    (timeShiftEmbeddedCylinderComplementEntries
      shift base roots predicate)
  unfold timeShiftCylinderSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold timeShiftBoundaryCylinderEventEntries
    timeShiftEmbeddedCylinderComplementEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem couplingSpinSummedTimeShiftCylinderTargetPairList_sum_eqv_product
    (coupling : Q') (cutoff shift base : Nat)
    (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTimeShiftCylinderRawPairWeight
          coupling cutoff shift base)
        (timeShiftCylinderTargetPairList shift base roots predicate) ≈
      listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (base + shift))
          (timeShiftBoundaryCylinderComplementFamilyList
            shift base roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (base + shift))
          (timeShiftEmbeddedCylinderEventFamilyList
            shift base roots predicate) := by
  exact listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (base + shift))
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (base + shift))
    (timeShiftBoundaryCylinderComplementFamilyList
      shift base roots predicate)
    (timeShiftEmbeddedCylinderEventFamilyList
      shift base roots predicate)

theorem couplingSpinSummedTimeShiftCylinderSourcePairList_partition
    (coupling : Q') (cutoff shift base : Nat)
    (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTimeShiftCylinderSourcePairWeight
          coupling cutoff)
        (timeShiftCylinderSourcePairList shift base roots predicate) ≈
      listQSum
          (couplingSpinSummedTimeShiftCylinderSourcePairWeight
            coupling cutoff)
          (separatedTimeShiftCylinderSourcePairs
            (shift := shift) (base := base)
            (roots := roots) (predicate := predicate)) +
        listQSum
          (couplingSpinSummedTimeShiftCylinderSourcePairWeight
            coupling cutoff)
          (connectedTimeShiftCylinderSourcePairs
            (shift := shift) (base := base)
            (roots := roots) (predicate := predicate)) := by
  exact listQSum_filter_partition
    (couplingSpinSummedTimeShiftCylinderSourcePairWeight coupling cutoff)
    timeShiftCylinderSourceSeparatedB
    (timeShiftCylinderSourcePairList shift base roots predicate)

theorem couplingSpinSummedTimeShiftBoundaryEvent_embeddedComplement_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat)
    (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :
    listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (base + shift))
          (timeShiftBoundaryCylinderEventFamilyList
            shift base roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (base + shift))
          (timeShiftEmbeddedCylinderComplementFamilyList
            shift base roots predicate) ≤
      listQSum
            (couplingParametricKSupportFamilyActivity
              coupling cutoff (base + shift))
            (timeShiftBoundaryCylinderComplementFamilyList
              shift base roots predicate) *
          listQSum
            (couplingParametricKSupportFamilyActivity
              coupling cutoff (base + shift))
            (timeShiftEmbeddedCylinderEventFamilyList
              shift base roots predicate) +
        listQSum
          (couplingSpinSummedTimeShiftCylinderSourcePairWeight
            coupling cutoff)
          (connectedTimeShiftCylinderSourcePairs
            (shift := shift) (base := base)
            (roots := roots) (predicate := predicate)) := by
  have hsource :=
    couplingSpinSummedTimeShiftCylinderSourcePairList_sum_eqv_product
      coupling cutoff shift base roots predicate
  have htarget :=
    couplingSpinSummedTimeShiftCylinderTargetPairList_sum_eqv_product
      coupling cutoff shift base roots predicate
  have hpartition :=
    couplingSpinSummedTimeShiftCylinderSourcePairList_partition
      coupling cutoff shift base roots predicate
  have hinjection :=
    couplingSpinSummedSeparatedTimeShiftCylinderPairSum_le_target
      hcoupling cutoff shift base roots predicate
  have hsepAdd := Q'.add_le_add hinjection (Q'.le_refl'
    (listQSum
      (couplingSpinSummedTimeShiftCylinderSourcePairWeight
        coupling cutoff)
      (connectedTimeShiftCylinderSourcePairs
        (shift := shift) (base := base)
        (roots := roots) (predicate := predicate))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

#print axioms mem_timeShiftBoundaryTargetFamilies_iff
#print axioms timeShiftBoundaryOutsideMarkedReachB_true_root_witness
#print axioms recoverableMarkedSwitchedRightFamily_mem_timeShiftEmbedded_of_separated
#print axioms recoverableMarkedSwitchedLeftFamily_mem_timeShiftBoundary_of_separated
#print axioms timeShiftSeparatedCylinderSwitchEncode_mem_target
#print axioms timeShiftSeparatedCylinderSwitchEncode_injective
#print axioms couplingSpinSummedSeparatedTimeShiftCylinderPairSum_le_target
#print axioms couplingSpinSummedTimeShiftBoundaryEvent_embeddedComplement_le

end YMGap.Continuum.Z4TimeShiftedCylinderSwitchSummation
