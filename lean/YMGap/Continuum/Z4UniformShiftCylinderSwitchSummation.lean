/-
# Marked switching for an affine uniformly shifted embedded cell

The translated source gas is now treated as a literal restricted target gas.
This file performs the finite marked-component switch against its complement
inside the full target compatible-family list.  No convergence statement is
assumed: the four cylinder cells cancel by an explicit weight-preserving
injection, leaving exactly the connected shifted-boundary residue.
-/

import YMGap.Continuum.Z4CouplingParametricCylinderWeights
import YMGap.Continuum.Z4UniformShiftEmbeddedRegion

namespace YMGap.Continuum.Z4UniformShiftCylinderSwitchSummation

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
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftEmbeddedRegion
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

abbrev PolymerFamily := List (List Nat)
abbrev RawFamilyPair := PolymerFamily × PolymerFamily

def uniformShiftMarkedCylinderEvent
    {padding base : Nat} (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) : PolymerFamily → Bool :=
  cylinderEvent (roots.map Subtype.val) predicate

/-! ## 1. The shifted embedded cell and its literal boundary complement -/

def uniformShiftBoundaryTargetFamilies (padding base : Nat) :
    List PolymerFamily :=
  (canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base)).filter
    (fun family =>
      !(family.all (targetRootInsideUniformShiftB padding base)))

theorem mem_uniformShiftBoundaryTargetFamilies_iff
    {padding base : Nat} {family : PolymerFamily} :
    family ∈ uniformShiftBoundaryTargetFamilies padding base ↔
      family ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) ∧
        family.all (targetRootInsideUniformShiftB padding base) = false := by
  unfold uniformShiftBoundaryTargetFamilies
  rw [List.mem_filter]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    cases hall : family.all (targetRootInsideUniformShiftB padding base) <;>
      simp_all
  · intro h
    exact ⟨h.1, by simp [h.2]⟩

theorem uniformShiftBoundaryTargetFamilies_nodup (padding base : Nat) :
    (uniformShiftBoundaryTargetFamilies padding base).Nodup := by
  unfold uniformShiftBoundaryTargetFamilies
  exact List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup (uniformPaddedBase padding base))

theorem uniformShiftEmbeddedTargetFamilies_nodup (padding base : Nat) :
    (uniformShiftEmbeddedTargetFamilies padding base).Nodup := by
  unfold uniformShiftEmbeddedTargetFamilies
  exact List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup (uniformPaddedBase padding base))

theorem uniformShiftEmbeddedTargetFamilies_member_target
    {padding base : Nat} {family : PolymerFamily}
    (hfamily : family ∈ uniformShiftEmbeddedTargetFamilies padding base) :
    family ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) :=
  (mem_uniformShiftEmbeddedTargetFamilies_iff.mp hfamily).1

/-! ## 2. Shifted separation and the two switched cells -/

def uniformShiftBoundaryOutsideMarkedReachB
    {padding base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (roots : List (CanonicalAtom (uniformPaddedBase padding base))) : Bool :=
  (canonicalFamilyAtoms hleft).any (fun atom =>
    (!(targetRootInsideUniformShiftB padding base atom.val)) &&
      canonicalMarkedCut hleft hright roots atom)

theorem uniformShiftBoundaryOutsideMarkedReachB_false_separated
    {padding base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (hreach : uniformShiftBoundaryOutsideMarkedReachB
      hleft hright roots = false) :
    ∀ atom : CanonicalAtom (uniformPaddedBase padding base), atom.val ∈ left →
      targetRootInsideUniformShiftB padding base atom.val = false →
        canonicalMarkedCut hleft hright roots atom = false := by
  intro atom hatom houtside
  cases hcut : canonicalMarkedCut hleft hright roots atom with
  | false => rfl
  | true =>
      have hatomList : atom ∈ canonicalFamilyAtoms hleft :=
        (canonicalFamilyAtom_mem_iff hleft atom).2 hatom
      have hterm :
          ((!(targetRootInsideUniformShiftB padding base atom.val)) &&
            canonicalMarkedCut hleft hright roots atom) = true := by
        simp [houtside, hcut]
      have hany : (canonicalFamilyAtoms hleft).any (fun found =>
          (!(targetRootInsideUniformShiftB padding base found.val)) &&
            canonicalMarkedCut hleft hright roots found) = true :=
        List.any_eq_true.mpr ⟨atom, hatomList, hterm⟩
      unfold uniformShiftBoundaryOutsideMarkedReachB at hreach
      rw [hreach] at hany
      exact False.elim (Bool.false_ne_true hany)

theorem uniformShiftBoundaryOutsideMarkedReachB_true_root_witness
    {padding base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (hreach : uniformShiftBoundaryOutsideMarkedReachB
      hleft hright roots = true) :
    ∃ root outside : CanonicalAtom (uniformPaddedBase padding base),
      root ∈ roots ∧ outside.val ∈ left ∧
        targetRootInsideUniformShiftB padding base outside.val = false ∧
          canonicalDisagreementCut hleft hright root outside = true := by
  unfold uniformShiftBoundaryOutsideMarkedReachB at hreach
  obtain ⟨outside, houtsideAtoms, hterm⟩ := List.any_eq_true.mp hreach
  have hparts := (Bool.and_eq_true _ _).mp hterm
  have houtside : targetRootInsideUniformShiftB
      padding base outside.val = false := by
    cases hinside : targetRootInsideUniformShiftB padding base outside.val <;>
      simp_all
  obtain ⟨root, hroot, hrootReach⟩ :=
    canonicalMarkedCut_true_has_root hleft hright roots outside hparts.2
  exact ⟨root, outside, hroot,
    (canonicalFamilyAtom_mem_iff hleft outside).1 houtsideAtoms,
    houtside, hrootReach⟩

theorem recoverableMarkedSwitchedRightFamily_mem_uniformShiftEmbedded_of_separated
    {padding base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (hrightEmbedded : right ∈
      uniformShiftEmbeddedTargetFamilies padding base)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (hseparated : ∀ atom : CanonicalAtom (uniformPaddedBase padding base),
      atom.val ∈ left →
        targetRootInsideUniformShiftB padding base atom.val = false →
          canonicalMarkedCut hleft
            (uniformShiftEmbeddedTargetFamilies_member_target hrightEmbedded)
            roots atom = false) :
    recoverableMarkedSwitchedRightFamily hleft
        (uniformShiftEmbeddedTargetFamilies_member_target hrightEmbedded)
        roots ∈ uniformShiftEmbeddedTargetFamilies padding base := by
  let hright := uniformShiftEmbeddedTargetFamilies_member_target hrightEmbedded
  have houtCompat :=
    (recoverableMarkedSwitchedFamilies_mem_compatible
      hleft hright roots).2
  apply mem_uniformShiftEmbeddedTargetFamilies_iff.mpr
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
        (mem_uniformShiftEmbeddedTargetFamilies_iff.mp hrightEmbedded).2
        atom.val hrightRaw
  | true =>
      have hleftAtom : atom ∈ canonicalFamilyAtoms hleft := by
        have hmemberB : memberB (canonicalFamilyAtoms hleft) atom = true := by
          simpa [switchedRightB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      have hleftRaw : atom.val ∈ left :=
        (canonicalFamilyAtom_mem_iff hleft atom).1 hleftAtom
      cases hinside : targetRootInsideUniformShiftB padding base atom.val with
      | true => rfl
      | false =>
          have hnotReach := hseparated atom hleftRaw hinside
          rw [hnotReach] at hcut
          exact False.elim (Bool.false_ne_true hcut)

theorem outside_support_mem_recoverableMarkedSwitchedLeft_of_uniformShiftSeparated
    {padding base : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (hright : right ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    {outside : List Nat} (houtside : outside ∈ left)
    (houtsideRegion : targetRootInsideUniformShiftB
      padding base outside = false)
    (hseparated : ∀ atom : CanonicalAtom (uniformPaddedBase padding base),
      atom.val ∈ left →
        targetRootInsideUniformShiftB padding base atom.val = false →
          canonicalMarkedCut hleft hright roots atom = false) :
    outside ∈ recoverableMarkedSwitchedLeftFamily
      hleft hright roots := by
  let outsideAtom : CanonicalAtom (uniformPaddedBase padding base) :=
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

theorem recoverableMarkedSwitchedLeftFamily_mem_uniformShiftBoundary_of_separated
    {padding base : Nat} {left right : PolymerFamily}
    (hleftBoundary : left ∈ uniformShiftBoundaryTargetFamilies padding base)
    (hright : right ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (hseparated : ∀ atom : CanonicalAtom (uniformPaddedBase padding base),
      atom.val ∈ left →
        targetRootInsideUniformShiftB padding base atom.val = false →
          canonicalMarkedCut
            (mem_uniformShiftBoundaryTargetFamilies_iff.mp hleftBoundary).1
            hright roots atom = false) :
    recoverableMarkedSwitchedLeftFamily
        (mem_uniformShiftBoundaryTargetFamilies_iff.mp hleftBoundary).1
        hright roots ∈ uniformShiftBoundaryTargetFamilies padding base := by
  let hleft := (mem_uniformShiftBoundaryTargetFamilies_iff.mp hleftBoundary).1
  have hleftAllFalse :=
    (mem_uniformShiftBoundaryTargetFamilies_iff.mp hleftBoundary).2
  let witness := allFalseWitness
    (targetRootInsideUniformShiftB padding base) left hleftAllFalse
  let outside := witness.1
  have houtside : outside ∈ left := witness.2.1
  have houtsideRegion : targetRootInsideUniformShiftB
      padding base outside = false := witness.2.2
  have houtsideOutput : outside ∈
      recoverableMarkedSwitchedLeftFamily hleft hright roots :=
    outside_support_mem_recoverableMarkedSwitchedLeft_of_uniformShiftSeparated
      hleft hright roots houtside houtsideRegion hseparated
  have houtCompat :=
    (recoverableMarkedSwitchedFamilies_mem_compatible
      hleft hright roots).1
  apply mem_uniformShiftBoundaryTargetFamilies_iff.mpr
  refine ⟨houtCompat, ?_⟩
  cases houtAll : (recoverableMarkedSwitchedLeftFamily
      hleft hright roots).all
        (targetRootInsideUniformShiftB padding base) with
  | false => rfl
  | true =>
      have hinside := List.all_eq_true.mp houtAll
        outside houtsideOutput
      rw [houtsideRegion] at hinside
      exact False.elim (Bool.false_ne_true hinside)

/-! ## 3. The four finite cylinder cells -/

def uniformShiftBoundaryCylinderEventFamilyList
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (uniformShiftBoundaryTargetFamilies padding base).filter
    (uniformShiftMarkedCylinderEvent roots predicate)

def uniformShiftEmbeddedCylinderComplementFamilyList
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (uniformShiftEmbeddedTargetFamilies padding base).filter
    (fun family => !(uniformShiftMarkedCylinderEvent roots predicate family))

def uniformShiftBoundaryCylinderComplementFamilyList
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (uniformShiftBoundaryTargetFamilies padding base).filter
    (fun family => !(uniformShiftMarkedCylinderEvent roots predicate family))

def uniformShiftEmbeddedCylinderEventFamilyList
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (uniformShiftEmbeddedTargetFamilies padding base).filter
    (uniformShiftMarkedCylinderEvent roots predicate)

abbrev UniformShiftBoundaryCylinderEventEntry
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :=
  {family : PolymerFamily // family ∈
    uniformShiftBoundaryCylinderEventFamilyList padding base roots predicate}

abbrev UniformShiftEmbeddedCylinderComplementEntry
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :=
  {family : PolymerFamily // family ∈
    uniformShiftEmbeddedCylinderComplementFamilyList padding base roots predicate}

abbrev UniformShiftCylinderSourcePair
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :=
  UniformShiftBoundaryCylinderEventEntry padding base roots predicate ×
    UniformShiftEmbeddedCylinderComplementEntry padding base roots predicate

def uniformShiftBoundaryCylinderEventEntries
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    List (UniformShiftBoundaryCylinderEventEntry
      padding base roots predicate) :=
  (uniformShiftBoundaryCylinderEventFamilyList
    padding base roots predicate).attach

def uniformShiftEmbeddedCylinderComplementEntries
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    List (UniformShiftEmbeddedCylinderComplementEntry
      padding base roots predicate) :=
  (uniformShiftEmbeddedCylinderComplementFamilyList
    padding base roots predicate).attach

def uniformShiftCylinderSourcePairList
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    List (UniformShiftCylinderSourcePair padding base roots predicate) :=
  cartesian
    (uniformShiftBoundaryCylinderEventEntries padding base roots predicate)
    (uniformShiftEmbeddedCylinderComplementEntries
      padding base roots predicate)

def uniformShiftCylinderTargetPairList
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) : List RawFamilyPair :=
  cartesian
    (uniformShiftBoundaryCylinderComplementFamilyList
      padding base roots predicate)
    (uniformShiftEmbeddedCylinderEventFamilyList
      padding base roots predicate)

def uniformShiftCylinderSourceLeftBoundary
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    pair.1.val ∈ uniformShiftBoundaryTargetFamilies padding base :=
  (List.mem_filter.mp pair.1.property).1

def uniformShiftCylinderSourceRightEmbedded
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    pair.2.val ∈ uniformShiftEmbeddedTargetFamilies padding base :=
  (List.mem_filter.mp pair.2.property).1

def uniformShiftCylinderSourceLeftCompatible
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    pair.1.val ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) :=
  (mem_uniformShiftBoundaryTargetFamilies_iff.mp
    (uniformShiftCylinderSourceLeftBoundary pair)).1

def uniformShiftCylinderSourceRightCompatible
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    pair.2.val ∈ canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) :=
  uniformShiftEmbeddedTargetFamilies_member_target
    (uniformShiftCylinderSourceRightEmbedded pair)

def uniformShiftCylinderSourceSeparatedB
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) : Bool :=
  !(uniformShiftBoundaryOutsideMarkedReachB
    (uniformShiftCylinderSourceLeftCompatible pair)
    (uniformShiftCylinderSourceRightCompatible pair) roots)

def separatedUniformShiftCylinderSourcePairs
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool} :
    List (UniformShiftCylinderSourcePair padding base roots predicate) :=
  (uniformShiftCylinderSourcePairList padding base roots predicate).filter
    uniformShiftCylinderSourceSeparatedB

def connectedUniformShiftCylinderSourcePairs
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool} :
    List (UniformShiftCylinderSourcePair padding base roots predicate) :=
  (uniformShiftCylinderSourcePairList padding base roots predicate).filter
    (fun pair => !(uniformShiftCylinderSourceSeparatedB pair))

def uniformShiftSeparatedCylinderSwitchEncode
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    RawFamilyPair :=
  (recoverableMarkedSwitchedLeftFamily
      (uniformShiftCylinderSourceLeftCompatible pair)
      (uniformShiftCylinderSourceRightCompatible pair) roots,
    recoverableMarkedSwitchedRightFamily
      (uniformShiftCylinderSourceLeftCompatible pair)
      (uniformShiftCylinderSourceRightCompatible pair) roots)

theorem uniformShiftSeparatedCylinderSwitchEncode_mem_target
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate)
    (hpair : pair ∈ separatedUniformShiftCylinderSourcePairs) :
    uniformShiftSeparatedCylinderSwitchEncode pair ∈
      uniformShiftCylinderTargetPairList padding base roots predicate := by
  have htest := (List.mem_filter.mp hpair).2
  have hdecision : uniformShiftBoundaryOutsideMarkedReachB
      (uniformShiftCylinderSourceLeftCompatible pair)
      (uniformShiftCylinderSourceRightCompatible pair) roots = false := by
    unfold uniformShiftCylinderSourceSeparatedB at htest
    cases hvalue : uniformShiftBoundaryOutsideMarkedReachB
        (uniformShiftCylinderSourceLeftCompatible pair)
        (uniformShiftCylinderSourceRightCompatible pair) roots <;> simp_all
  have hseparated :=
    uniformShiftBoundaryOutsideMarkedReachB_false_separated
      (uniformShiftCylinderSourceLeftCompatible pair)
      (uniformShiftCylinderSourceRightCompatible pair) roots hdecision
  have hleftOut :=
    recoverableMarkedSwitchedLeftFamily_mem_uniformShiftBoundary_of_separated
      (uniformShiftCylinderSourceLeftBoundary pair)
      (uniformShiftCylinderSourceRightCompatible pair) roots hseparated
  have hrightOut :=
    recoverableMarkedSwitchedRightFamily_mem_uniformShiftEmbedded_of_separated
      (uniformShiftCylinderSourceLeftCompatible pair)
      (uniformShiftCylinderSourceRightEmbedded pair) roots hseparated
  have hevents := recoverableMarkedSwitchedFamilies_cylinderEvent_swap
    (uniformShiftCylinderSourceLeftCompatible pair)
    (uniformShiftCylinderSourceRightCompatible pair) roots predicate
  apply (mem_cartesian_iff
    (uniformShiftBoundaryCylinderComplementFamilyList
      padding base roots predicate)
    (uniformShiftEmbeddedCylinderEventFamilyList
      padding base roots predicate)
    (uniformShiftSeparatedCylinderSwitchEncode pair)).2
  constructor
  · apply List.mem_filter.mpr
    refine ⟨hleftOut, ?_⟩
    have hrightEventFalse : uniformShiftMarkedCylinderEvent roots predicate
        pair.2.val = false := by
      have hraw := (List.mem_filter.mp pair.2.property).2
      cases hvalue : uniformShiftMarkedCylinderEvent roots predicate
          pair.2.val <;> simp_all
    unfold uniformShiftMarkedCylinderEvent at hrightEventFalse
    change (!(uniformShiftMarkedCylinderEvent roots predicate
      (recoverableMarkedSwitchedLeftFamily
        (uniformShiftCylinderSourceLeftCompatible pair)
        (uniformShiftCylinderSourceRightCompatible pair) roots))) = true
    unfold uniformShiftMarkedCylinderEvent
    rw [hevents.1, hrightEventFalse]
    rfl
  · apply List.mem_filter.mpr
    refine ⟨hrightOut, ?_⟩
    have hleftEvent : uniformShiftMarkedCylinderEvent roots predicate
        pair.1.val = true :=
      (List.mem_filter.mp pair.1.property).2
    change uniformShiftMarkedCylinderEvent roots predicate
      (recoverableMarkedSwitchedRightFamily
        (uniformShiftCylinderSourceLeftCompatible pair)
        (uniformShiftCylinderSourceRightCompatible pair) roots) = true
    unfold uniformShiftMarkedCylinderEvent
    rw [hevents.2]
    exact hleftEvent

theorem uniformShiftSeparatedCylinderSwitchEncode_injective
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (first second : UniformShiftCylinderSourcePair
      padding base roots predicate)
    (_hfirst : first ∈ separatedUniformShiftCylinderSourcePairs)
    (_hsecond : second ∈ separatedUniformShiftCylinderSourcePairs)
    (heq : uniformShiftSeparatedCylinderSwitchEncode first =
      uniformShiftSeparatedCylinderSwitchEncode second) : first = second := by
  have hleftOutput := congrArg Prod.fst heq
  have hrightOutput := congrArg Prod.snd heq
  have hsources := recoverableMarkedSwitchedFamilies_injective roots
    (uniformShiftCylinderSourceLeftCompatible first)
    (uniformShiftCylinderSourceRightCompatible first)
    (uniformShiftCylinderSourceLeftCompatible second)
    (uniformShiftCylinderSourceRightCompatible second)
    hleftOutput hrightOutput
  apply Prod.ext
  · exact Subtype.ext hsources.1
  · exact Subtype.ext hsources.2

/-! ## 4. Coupling-parametric exact cancellation -/

def couplingSpinSummedUniformShiftCylinderSourcePairWeight
    (coupling : Q') (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base) pair.1.val *
    couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base) pair.2.val

def couplingSpinSummedUniformShiftCylinderRawPairWeight
    (coupling : Q') (cutoff padding base : Nat)
    (pair : RawFamilyPair) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base) pair.1 *
    couplingParametricKSupportFamilyActivity coupling cutoff
      (uniformPaddedBase padding base) pair.2

theorem couplingSpinSummedUniformShiftSeparatedSwitchEncode_weight
    (coupling : Q') (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    couplingSpinSummedUniformShiftCylinderRawPairWeight
        coupling cutoff padding base
        (uniformShiftSeparatedCylinderSwitchEncode pair) ≈
      couplingSpinSummedUniformShiftCylinderSourcePairWeight
        coupling cutoff pair := by
  exact
    recoverableMarkedSwitchedFamilies_couplingSpinSummed_weight_preserved
      coupling cutoff
      (uniformShiftCylinderSourceLeftCompatible pair)
      (uniformShiftCylinderSourceRightCompatible pair) roots

theorem uniformShiftBoundaryCylinderEventFamilyList_nodup
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    (uniformShiftBoundaryCylinderEventFamilyList
      padding base roots predicate).Nodup :=
  List.filter_sublist.nodup
    (uniformShiftBoundaryTargetFamilies_nodup padding base)

theorem uniformShiftEmbeddedCylinderComplementFamilyList_nodup
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    (uniformShiftEmbeddedCylinderComplementFamilyList
      padding base roots predicate).Nodup :=
  List.filter_sublist.nodup
    (uniformShiftEmbeddedTargetFamilies_nodup padding base)

theorem uniformShiftBoundaryCylinderComplementFamilyList_nodup
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    (uniformShiftBoundaryCylinderComplementFamilyList
      padding base roots predicate).Nodup :=
  List.filter_sublist.nodup
    (uniformShiftBoundaryTargetFamilies_nodup padding base)

theorem uniformShiftEmbeddedCylinderEventFamilyList_nodup
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    (uniformShiftEmbeddedCylinderEventFamilyList
      padding base roots predicate).Nodup :=
  List.filter_sublist.nodup
    (uniformShiftEmbeddedTargetFamilies_nodup padding base)

theorem uniformShiftCylinderSourcePairList_nodup
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    (uniformShiftCylinderSourcePairList padding base roots predicate).Nodup := by
  exact cartesian_nodup _ _
    (attach_nodup_of_nodup _
      (uniformShiftBoundaryCylinderEventFamilyList_nodup
        padding base roots predicate))
    (attach_nodup_of_nodup _
      (uniformShiftEmbeddedCylinderComplementFamilyList_nodup
        padding base roots predicate))

theorem separatedUniformShiftCylinderSourcePairs_nodup
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    (separatedUniformShiftCylinderSourcePairs
      (padding := padding) (base := base)
      (roots := roots) (predicate := predicate)).Nodup :=
  List.filter_sublist.nodup
    (uniformShiftCylinderSourcePairList_nodup
      padding base roots predicate)

theorem uniformShiftCylinderTargetPairList_nodup
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    (uniformShiftCylinderTargetPairList
      padding base roots predicate).Nodup :=
  cartesian_nodup _ _
    (uniformShiftBoundaryCylinderComplementFamilyList_nodup
      padding base roots predicate)
    (uniformShiftEmbeddedCylinderEventFamilyList_nodup
      padding base roots predicate)

theorem couplingSpinSummedSeparatedUniformShiftCylinderPairSum_le_target
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedUniformShiftCylinderSourcePairWeight
          coupling cutoff)
        (separatedUniformShiftCylinderSourcePairs
          (padding := padding) (base := base)
          (roots := roots) (predicate := predicate)) ≤
      listQSum
        (couplingSpinSummedUniformShiftCylinderRawPairWeight
          coupling cutoff padding base)
        (uniformShiftCylinderTargetPairList
          padding base roots predicate) := by
  apply listQSum_le_of_injective
    (separatedUniformShiftCylinderSourcePairs
      (padding := padding) (base := base)
      (roots := roots) (predicate := predicate))
    (uniformShiftCylinderTargetPairList padding base roots predicate)
    (couplingSpinSummedUniformShiftCylinderSourcePairWeight
      coupling cutoff)
    (couplingSpinSummedUniformShiftCylinderRawPairWeight
      coupling cutoff padding base)
    uniformShiftSeparatedCylinderSwitchEncode
    (separatedUniformShiftCylinderSourcePairs_nodup
      padding base roots predicate)
  · exact uniformShiftSeparatedCylinderSwitchEncode_mem_target
  · intro first hfirst second hsecond heq
    exact uniformShiftSeparatedCylinderSwitchEncode_injective
      first second hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (couplingSpinSummedUniformShiftSeparatedSwitchEncode_weight
          coupling cutoff pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (uniformPaddedBase padding base) pair.1)
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (uniformPaddedBase padding base) pair.2)

theorem couplingSpinSummedUniformShiftCylinderSourcePairList_sum_eqv_product
    (coupling : Q') (cutoff padding base : Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedUniformShiftCylinderSourcePairWeight
          coupling cutoff)
        (uniformShiftCylinderSourcePairList padding base roots predicate) ≈
      listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (uniformPaddedBase padding base))
          (uniformShiftBoundaryCylinderEventFamilyList
            padding base roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (uniformPaddedBase padding base))
          (uniformShiftEmbeddedCylinderComplementFamilyList
            padding base roots predicate) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : UniformShiftBoundaryCylinderEventEntry
        padding base roots predicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff (uniformPaddedBase padding base) entry.val)
    (fun entry : UniformShiftEmbeddedCylinderComplementEntry
        padding base roots predicate =>
      couplingParametricKSupportFamilyActivity
        coupling cutoff (uniformPaddedBase padding base) entry.val)
    (uniformShiftBoundaryCylinderEventEntries
      padding base roots predicate)
    (uniformShiftEmbeddedCylinderComplementEntries
      padding base roots predicate)
  unfold uniformShiftCylinderSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold uniformShiftBoundaryCylinderEventEntries
    uniformShiftEmbeddedCylinderComplementEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem couplingSpinSummedUniformShiftCylinderTargetPairList_sum_eqv_product
    (coupling : Q') (cutoff padding base : Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedUniformShiftCylinderRawPairWeight
          coupling cutoff padding base)
        (uniformShiftCylinderTargetPairList padding base roots predicate) ≈
      listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (uniformPaddedBase padding base))
          (uniformShiftBoundaryCylinderComplementFamilyList
            padding base roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (uniformPaddedBase padding base))
          (uniformShiftEmbeddedCylinderEventFamilyList
            padding base roots predicate) := by
  exact listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (uniformPaddedBase padding base))
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (uniformPaddedBase padding base))
    (uniformShiftBoundaryCylinderComplementFamilyList
      padding base roots predicate)
    (uniformShiftEmbeddedCylinderEventFamilyList
      padding base roots predicate)

theorem couplingSpinSummedUniformShiftCylinderSourcePairList_partition
    (coupling : Q') (cutoff padding base : Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedUniformShiftCylinderSourcePairWeight
          coupling cutoff)
        (uniformShiftCylinderSourcePairList padding base roots predicate) ≈
      listQSum
          (couplingSpinSummedUniformShiftCylinderSourcePairWeight
            coupling cutoff)
          (separatedUniformShiftCylinderSourcePairs
            (padding := padding) (base := base)
            (roots := roots) (predicate := predicate)) +
        listQSum
          (couplingSpinSummedUniformShiftCylinderSourcePairWeight
            coupling cutoff)
          (connectedUniformShiftCylinderSourcePairs
            (padding := padding) (base := base)
            (roots := roots) (predicate := predicate)) := by
  exact listQSum_filter_partition
    (couplingSpinSummedUniformShiftCylinderSourcePairWeight coupling cutoff)
    uniformShiftCylinderSourceSeparatedB
    (uniformShiftCylinderSourcePairList padding base roots predicate)

theorem couplingSpinSummedUniformShiftBoundaryEvent_embeddedComplement_le
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :
    listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (uniformPaddedBase padding base))
          (uniformShiftBoundaryCylinderEventFamilyList
            padding base roots predicate) *
        listQSum
          (couplingParametricKSupportFamilyActivity
            coupling cutoff (uniformPaddedBase padding base))
          (uniformShiftEmbeddedCylinderComplementFamilyList
            padding base roots predicate) ≤
      listQSum
            (couplingParametricKSupportFamilyActivity
              coupling cutoff (uniformPaddedBase padding base))
            (uniformShiftBoundaryCylinderComplementFamilyList
              padding base roots predicate) *
          listQSum
            (couplingParametricKSupportFamilyActivity
              coupling cutoff (uniformPaddedBase padding base))
            (uniformShiftEmbeddedCylinderEventFamilyList
              padding base roots predicate) +
        listQSum
          (couplingSpinSummedUniformShiftCylinderSourcePairWeight
            coupling cutoff)
          (connectedUniformShiftCylinderSourcePairs
            (padding := padding) (base := base)
            (roots := roots) (predicate := predicate)) := by
  have hsource :=
    couplingSpinSummedUniformShiftCylinderSourcePairList_sum_eqv_product
      coupling cutoff padding base roots predicate
  have htarget :=
    couplingSpinSummedUniformShiftCylinderTargetPairList_sum_eqv_product
      coupling cutoff padding base roots predicate
  have hpartition :=
    couplingSpinSummedUniformShiftCylinderSourcePairList_partition
      coupling cutoff padding base roots predicate
  have hinjection :=
    couplingSpinSummedSeparatedUniformShiftCylinderPairSum_le_target
      hcoupling cutoff padding base roots predicate
  have hsepAdd := Q'.add_le_add hinjection (Q'.le_refl'
    (listQSum
      (couplingSpinSummedUniformShiftCylinderSourcePairWeight
        coupling cutoff)
      (connectedUniformShiftCylinderSourcePairs
        (padding := padding) (base := base)
        (roots := roots) (predicate := predicate))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

#print axioms mem_uniformShiftBoundaryTargetFamilies_iff
#print axioms uniformShiftBoundaryOutsideMarkedReachB_true_root_witness
#print axioms recoverableMarkedSwitchedRightFamily_mem_uniformShiftEmbedded_of_separated
#print axioms recoverableMarkedSwitchedLeftFamily_mem_uniformShiftBoundary_of_separated
#print axioms uniformShiftSeparatedCylinderSwitchEncode_mem_target
#print axioms uniformShiftSeparatedCylinderSwitchEncode_injective
#print axioms couplingSpinSummedSeparatedUniformShiftCylinderPairSum_le_target
#print axioms couplingSpinSummedUniformShiftBoundaryEvent_embeddedComplement_le

end YMGap.Continuum.Z4UniformShiftCylinderSwitchSummation
