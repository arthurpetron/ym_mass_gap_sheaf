/-
# Right-boundary orientation of the recoverable component switch

For the reverse local-occurrence determinant the marked polymer belongs to
the embedded replica, while the other replica is a boundary family avoiding
it.  The same recoverable disagreement component applies, but the geometric
preservation argument is mirrored: no exterior atom of the right boundary
family may lie in the switched component.
-/

import YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery

namespace YMGap.Continuum.Z4CanonicalBoundaryRightRootSwitch

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Mirrored geometric preservation -/

theorem recoverableSwitchedLeftFamily_inside_of_right_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    (hleftInside : FamilyInsideBox small n left)
    (hseparated : ∀ outside : CanonicalAtom n,
      outside.val ∈ right →
        polymerInsideBoxB small n outside.val = false →
          canonicalDisagreementCut hleft hright root outside = false) :
    FamilyInsideBox small n
      (recoverableSwitchedLeftFamily hleft hright root) := by
  intro support hsupport
  unfold recoverableSwitchedLeftFamily at hsupport
  obtain ⟨atom, hatom, hatomValue⟩ := List.mem_map.mp hsupport
  subst support
  have htest := (mem_recoverableSwitchedLeftAtoms_iff
    hleft hright root atom).1 hatom
  cases hcut : canonicalDisagreementCut hleft hright root atom with
  | false =>
      have hleftAtom : atom ∈ canonicalFamilyAtoms hleft := by
        have hmemberB : memberB (canonicalFamilyAtoms hleft) atom = true := by
          simpa [switchedLeftB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      exact hleftInside atom.val
        ((canonicalFamilyAtom_mem_iff hleft atom).1 hleftAtom)
  | true =>
      have hrightAtom : atom ∈ canonicalFamilyAtoms hright := by
        have hmemberB : memberB (canonicalFamilyAtoms hright) atom = true := by
          simpa [switchedLeftB, hcut] using htest
        exact (memberB_eq_true_iff _ _).1 hmemberB
      have hrightRaw : atom.val ∈ right :=
        (canonicalFamilyAtom_mem_iff hright atom).1 hrightAtom
      cases hinside : polymerInsideBoxB small n atom.val with
      | true =>
          exact (polymerInsideBoxB_true_iff small n atom.val).1 hinside
      | false =>
          have hnotReach := hseparated atom hrightRaw hinside
          rw [hnotReach] at hcut
          exact False.elim (Bool.false_ne_true hcut)

theorem recoverableSwitchedLeftFamily_mem_embedded_of_right_separated
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftEmbedded : left ∈ embeddedCompatibleFamilies small n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ right →
        polymerInsideBoxB small n atom.val = false →
          canonicalDisagreementCut
            (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
            hright root atom = false) :
    recoverableSwitchedLeftFamily
        (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
        hright root ∈ embeddedCompatibleFamilies small n := by
  let hleft := embeddedCompatibleFamilies_member_target
    hsmall hleftEmbedded
  have hleftInside := familyInsideBox_of_mem_embeddedCompatibleFamilies
    hsmall hleftEmbedded
  have houtInside := recoverableSwitchedLeftFamily_inside_of_right_separated
    hleft hright root hleftInside hseparated
  have houtCompat :=
    (recoverableSwitchedFamilies_mem_compatible hleft hright root).1
  exact family_mem_embeddedCompatibleFamilies_of_inside
    hsmall houtCompat houtInside

theorem outside_support_mem_recoverableSwitchedRight_of_right_separated
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n)
    {outside : List Nat} (houtside : outside ∈ right)
    (houtsideBox : polymerInsideBoxB small n outside = false)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ right →
        polymerInsideBoxB small n atom.val = false →
          canonicalDisagreementCut hleft hright root atom = false) :
    outside ∈ recoverableSwitchedRightFamily hleft hright root := by
  let outsideAtom : CanonicalAtom n :=
    ⟨outside, compatibleAmbientFamily_member_ambient hright houtside⟩
  have houtsideAtom : outsideAtom ∈ canonicalFamilyAtoms hright :=
    (canonicalFamilyAtom_mem_iff hright outsideAtom).2 houtside
  have hcut : canonicalDisagreementCut hleft hright root outsideAtom = false :=
    hseparated outsideAtom houtside houtsideBox
  have hrightB : memberB (canonicalFamilyAtoms hright) outsideAtom = true :=
    (memberB_eq_true_iff _ _).2 houtsideAtom
  have houtAtoms : outsideAtom ∈
      recoverableSwitchedRightAtoms hleft hright root := by
    apply (mem_recoverableSwitchedRightAtoms_iff
      hleft hright root outsideAtom).2
    simp [switchedRightB, hcut, hrightB]
  unfold recoverableSwitchedRightFamily
  exact (canonicalAtom_value_mem_values_iff _ outsideAtom).2 houtAtoms

theorem recoverableSwitchedRightFamily_mem_boundary_of_right_separated
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hrightBoundary : right ∈ boundaryTargetFamilies small n)
    (root : CanonicalAtom n)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ right →
        polymerInsideBoxB small n atom.val = false →
          canonicalDisagreementCut hleft
            (List.mem_filter.mp hrightBoundary).1 root atom = false) :
    recoverableSwitchedRightFamily hleft
        (List.mem_filter.mp hrightBoundary).1 root ∈
      boundaryTargetFamilies small n := by
  let hright := (List.mem_filter.mp hrightBoundary).1
  obtain ⟨outside, houtside, plaquette, hplaquette,
      hplaquetteOutside⟩ :=
    boundaryTargetFamily_has_outside_witness hsmall hrightBoundary
  have houtsideBox : polymerInsideBoxB small n outside = false := by
    cases hinside : polymerInsideBoxB small n outside with
    | false => rfl
    | true =>
        have hin := (polymerInsideBoxB_true_iff small n outside).1
          hinside plaquette hplaquette
        exact False.elim (hplaquetteOutside hin)
  have houtsideOutput : outside ∈
      recoverableSwitchedRightFamily hleft hright root :=
    outside_support_mem_recoverableSwitchedRight_of_right_separated
      hleft hright root houtside houtsideBox hseparated
  have houtCompat :=
    (recoverableSwitchedFamilies_mem_compatible hleft hright root).2
  have hnotEmbedded : recoverableSwitchedRightFamily hleft hright root ∉
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

/-! ## 2. Complete reverse-orientation separated switch -/

/-- An embedded event family and a boundary complement family are sent to an
embedded complement family and a boundary event family, preserving the exact
pair activity. -/
theorem separated_recoverable_embedded_event_pair_switch
    (w : Q') {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftEmbedded : left ∈ embeddedCompatibleFamilies small n)
    (hrightBoundary : right ∈ boundaryTargetFamilies small n)
    {rootPolymer : List Nat} (hroot : rootPolymer ∈ left)
    (hrootRight : rootPolymer ∉ right)
    (hseparated : ∀ atom : CanonicalAtom n,
      atom.val ∈ right →
        polymerInsideBoxB small n atom.val = false →
          canonicalDisagreementCut
            (embeddedCompatibleFamilies_member_target
              hsmall hleftEmbedded)
            (List.mem_filter.mp hrightBoundary).1
            (leftCanonicalAtomOfMember
              (embeddedCompatibleFamilies_member_target
                hsmall hleftEmbedded) hroot) atom = false) :
    recoverableSwitchedLeftFamily
        (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
        (List.mem_filter.mp hrightBoundary).1
        (leftCanonicalAtomOfMember
          (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
          hroot) ∈ embeddedCompatibleFamilies small n ∧
      familyContainsPolymerB rootPolymer
        (recoverableSwitchedLeftFamily
          (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
          (List.mem_filter.mp hrightBoundary).1
          (leftCanonicalAtomOfMember
            (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
            hroot)) = false ∧
      recoverableSwitchedRightFamily
        (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
        (List.mem_filter.mp hrightBoundary).1
        (leftCanonicalAtomOfMember
          (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
          hroot) ∈ boundaryTargetFamilies small n ∧
      familyContainsPolymerB rootPolymer
        (recoverableSwitchedRightFamily
          (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
          (List.mem_filter.mp hrightBoundary).1
          (leftCanonicalAtomOfMember
            (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
            hroot)) = true ∧
      canonicalSurfaceFamilyActivity w n
          (recoverableSwitchedLeftFamily
            (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
            (List.mem_filter.mp hrightBoundary).1
            (leftCanonicalAtomOfMember
              (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
              hroot)) *
        canonicalSurfaceFamilyActivity w n
          (recoverableSwitchedRightFamily
            (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
            (List.mem_filter.mp hrightBoundary).1
            (leftCanonicalAtomOfMember
              (embeddedCompatibleFamilies_member_target hsmall hleftEmbedded)
              hroot)) ≈
      canonicalSurfaceFamilyActivity w n left *
        canonicalSurfaceFamilyActivity w n right := by
  let hleft := embeddedCompatibleFamilies_member_target
    hsmall hleftEmbedded
  let hright := (List.mem_filter.mp hrightBoundary).1
  let root := leftCanonicalAtomOfMember hleft hroot
  have hembedded :=
    recoverableSwitchedLeftFamily_mem_embedded_of_right_separated
      hsmall hleftEmbedded hright root hseparated
  have hboundary :=
    recoverableSwitchedRightFamily_mem_boundary_of_right_separated
      hsmall hleft hrightBoundary root hseparated
  have hrootCells := recoverableSwitchedFamilies_root_cells
    hleft hright hroot hrootRight
  have hweight := recoverableSwitchedFamilies_weight_preserved
    w hleft hright root
  exact ⟨hembedded, hrootCells.1, hboundary,
    hrootCells.2, hweight⟩

end YMGap.Continuum.Z4CanonicalBoundaryRightRootSwitch

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSwitch.recoverableSwitchedLeftFamily_inside_of_right_separated
#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSwitch.recoverableSwitchedRightFamily_mem_boundary_of_right_separated
#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSwitch.separated_recoverable_embedded_event_pair_switch
