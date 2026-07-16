/-
# Classification of the finite-cylinder connected residue

When a marked union component reaches the boundary, an inside marked root is
exclusive to one replica.  The source pair is therefore an entry in one of
the already-certified singleton connected lists: the forward list for a
left-only root, or the mirrored list (with replicas exchanged) for a
right-only root.
-/

import YMGap.Continuum.Z4CanonicalMarkedRootSeparation
import YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
import YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation

namespace YMGap.Continuum.Z4CanonicalCylinderConnectedClassification

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse

theorem disagreementBits_swap_sides
    (leftI rightI leftJ rightJ conflict : Bool) :
    disagreementBits rightI leftI rightJ leftJ conflict =
      disagreementBits leftI rightI leftJ rightJ conflict := by
  cases leftI <;> cases rightI <;> cases leftJ <;>
    cases rightJ <;> cases conflict <;>
    rfl

theorem disagreementEdge_swap_sides
    {A : Type} [DecidableEq A] (ambient : List A)
    (compat : A → A → Bool) (left right : A → Bool)
    (first second : A) :
    disagreementEdge ambient compat right left first second =
      disagreementEdge ambient compat left right first second := by
  unfold disagreementEdge
  rw [disagreementBits_swap_sides]

theorem canonicalDisagreementCut_swap_sides
    {n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root atom : CanonicalAtom n) :
    canonicalDisagreementCut hright hleft root atom =
      canonicalDisagreementCut hleft hright root atom := by
  unfold canonicalDisagreementCut rootedComponent
  have hedge : disagreementEdge (canonicalAmbientAtoms n)
      (canonicalAtomCompatibleB n)
      (memberB (canonicalFamilyAtoms hright))
      (memberB (canonicalFamilyAtoms hleft)) =
    disagreementEdge (canonicalAmbientAtoms n)
      (canonicalAtomCompatibleB n)
      (memberB (canonicalFamilyAtoms hleft))
      (memberB (canonicalFamilyAtoms hright)) := by
    funext first second
    exact disagreementEdge_swap_sides _ _ _ _ first second
  rw [hedge]

/-- The marked connected branch selects an inside exclusive root, including
its orientation. -/
theorem boundaryOutsideMarkedReachB_true_oriented_root
    {small n : Nat} {left right : List (List Nat)}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (roots : List (CanonicalAtom n))
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hreach : boundaryOutsideMarkedReachB small hleft hright roots = true) :
    ∃ root outside : CanonicalAtom n,
      root ∈ roots ∧ outside.val ∈ left ∧
        polymerInsideBoxB small n outside.val = false ∧
          canonicalDisagreementCut hleft hright root outside = true ∧
            ((root.val ∈ left ∧ root.val ∉ right) ∨
              (root.val ∉ left ∧ root.val ∈ right)) := by
  obtain ⟨root, outside, hroot, houtside, houtsideBox, hrootReach⟩ :=
    boundaryOutsideMarkedReachB_true_root_witness
      hleft hright roots hreach
  have horientation := canonicalRoot_exclusive_of_reaches_outside
    hleft hright root outside (hrootsInside root hroot)
      houtsideBox hrootReach
  exact ⟨root, outside, hroot, houtside, houtsideBox,
    hrootReach, horientation⟩

theorem leftOnly_reach_mem_connectedSourcePairs
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hrightEmbedded : right ∈ embeddedCompatibleFamilies small n)
    (root outside : CanonicalAtom n)
    (hrootLeft : root.val ∈ left) (hrootRight : root.val ∉ right)
    (houtsideLeft : outside.val ∈ left)
    (houtsideBox : polymerInsideBoxB small n outside.val = false)
    (hreaches : canonicalDisagreementCut
      (List.mem_filter.mp hleftBoundary).1
      (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
      root outside = true) :
    ∃ pair : SourcePair small n root.val,
      pair.1.val = left ∧ pair.2.val = right ∧
        pair ∈ connectedSourcePairs hsmall := by
  have hleftEvent : left ∈ boundaryEventFamilyList small n root.val := by
    unfold boundaryEventFamilyList
    apply List.mem_filter.mpr
    exact ⟨hleftBoundary, by
      unfold familyContainsPolymerB
      exact decide_eq_true hrootLeft⟩
  have hrightComplement :
      right ∈ embeddedComplementFamilyList small n root.val := by
    unfold embeddedComplementFamilyList
    apply List.mem_filter.mpr
    constructor
    · exact hrightEmbedded
    · have hfalse : familyContainsPolymerB root.val right = false := by
        unfold familyContainsPolymerB
        exact decide_eq_false hrootRight
      simp [hfalse]
  let leftEntry : BoundaryEventEntry small n root.val :=
    ⟨left, hleftEvent⟩
  let rightEntry : EmbeddedComplementEntry small n root.val :=
    ⟨right, hrightComplement⟩
  let pair : SourcePair small n root.val := (leftEntry, rightEntry)
  have hpairList : pair ∈ sourcePairList small n root.val := by
    unfold sourcePairList
    apply (mem_cartesian_iff _ _ pair).2
    constructor <;> simp [boundaryEventEntries,
      embeddedComplementEntries, pair, leftEntry, rightEntry]
  have hleftCompat : sourceLeftCompatible pair =
      (List.mem_filter.mp hleftBoundary).1 := Subsingleton.elim _ _
  have hrightCompat : sourceRightCompatible hsmall pair =
      embeddedCompatibleFamilies_member_target hsmall hrightEmbedded :=
    Subsingleton.elim _ _
  have hrootAtom : sourceRootAtom pair = root := Subtype.ext rfl
  have hreachB : boundaryOutsideDisagreementReachB small
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) = true := by
    unfold boundaryOutsideDisagreementReachB
    apply List.any_eq_true.mpr
    refine ⟨outside, ?_, ?_⟩
    · exact (canonicalFamilyAtom_mem_iff
        (sourceLeftCompatible pair) outside).2 (by
          simpa [pair, leftEntry] using houtsideLeft)
    · have hreach' : canonicalDisagreementCut
          (sourceLeftCompatible pair)
          (sourceRightCompatible hsmall pair)
          (sourceRootAtom pair) outside = true := by
        rw [hleftCompat, hrightCompat, hrootAtom]
        exact hreaches
      simp [houtsideBox, hreach']
  refine ⟨pair, rfl, rfl, ?_⟩
  unfold connectedSourcePairs
  apply List.mem_filter.mpr
  refine ⟨hpairList, ?_⟩
  unfold sourceSeparatedB
  simp [hreachB]

theorem rightOnly_reach_mem_connectedReverseSourcePairs
    {small n : Nat} (hsmall : small ≤ n)
    {left right : List (List Nat)}
    (hleftBoundary : left ∈ boundaryTargetFamilies small n)
    (hrightEmbedded : right ∈ embeddedCompatibleFamilies small n)
    (root outside : CanonicalAtom n)
    (hrootLeft : root.val ∉ left) (hrootRight : root.val ∈ right)
    (houtsideLeft : outside.val ∈ left)
    (houtsideBox : polymerInsideBoxB small n outside.val = false)
    (hreaches : canonicalDisagreementCut
      (List.mem_filter.mp hleftBoundary).1
      (embeddedCompatibleFamilies_member_target hsmall hrightEmbedded)
      root outside = true) :
    ∃ pair : ReverseSourcePair small n root.val,
      pair.1.val = right ∧ pair.2.val = left ∧
        pair ∈ connectedReverseSourcePairs hsmall := by
  have hrightEvent : right ∈ embeddedEventFamilyList small n root.val := by
    unfold embeddedEventFamilyList
    apply List.mem_filter.mpr
    exact ⟨hrightEmbedded, by
      unfold familyContainsPolymerB
      exact decide_eq_true hrootRight⟩
  have hleftComplement :
      left ∈ boundaryComplementFamilyList small n root.val := by
    unfold boundaryComplementFamilyList
    apply List.mem_filter.mpr
    constructor
    · exact hleftBoundary
    · have hfalse : familyContainsPolymerB root.val left = false := by
        unfold familyContainsPolymerB
        exact decide_eq_false hrootLeft
      simp [hfalse]
  let leftEntry : ReverseEmbeddedEventEntry small n root.val :=
    ⟨right, hrightEvent⟩
  let rightEntry : ReverseBoundaryComplementEntry small n root.val :=
    ⟨left, hleftComplement⟩
  let pair : ReverseSourcePair small n root.val := (leftEntry, rightEntry)
  have hpairList : pair ∈ reverseSourcePairList small n root.val := by
    unfold reverseSourcePairList
    apply (mem_cartesian_iff _ _ pair).2
    constructor <;> simp [reverseEmbeddedEventEntries,
      reverseBoundaryComplementEntries, pair, leftEntry, rightEntry]
  have hleftCompat : reverseSourceLeftCompatible hsmall pair =
      embeddedCompatibleFamilies_member_target hsmall hrightEmbedded :=
    Subsingleton.elim _ _
  have hrightCompat : reverseSourceRightCompatible pair =
      (List.mem_filter.mp hleftBoundary).1 := Subsingleton.elim _ _
  have hrootAtom : reverseSourceRootAtom hsmall pair = root := Subtype.ext rfl
  have hreachB : rightBoundaryOutsideDisagreementReachB small
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair) = true := by
    unfold rightBoundaryOutsideDisagreementReachB
    apply List.any_eq_true.mpr
    refine ⟨outside, ?_, ?_⟩
    · exact (canonicalFamilyAtom_mem_iff
        (reverseSourceRightCompatible pair) outside).2 (by
          simpa [pair, rightEntry] using houtsideLeft)
    · have hreach' : canonicalDisagreementCut
          (reverseSourceLeftCompatible hsmall pair)
          (reverseSourceRightCompatible pair)
          (reverseSourceRootAtom hsmall pair) outside = true := by
        rw [hleftCompat, hrightCompat, hrootAtom]
        rw [canonicalDisagreementCut_swap_sides]
        exact hreaches
      simp [houtsideBox, hreach']
  refine ⟨pair, rfl, rfl, ?_⟩
  unfold connectedReverseSourcePairs
  apply List.mem_filter.mpr
  refine ⟨hpairList, ?_⟩
  unfold reverseSourceSeparatedB
  simp [hreachB]

end YMGap.Continuum.Z4CanonicalCylinderConnectedClassification

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalCylinderConnectedClassification.canonicalDisagreementCut_swap_sides
#print axioms YMGap.Continuum.Z4CanonicalCylinderConnectedClassification.boundaryOutsideMarkedReachB_true_oriented_root
#print axioms YMGap.Continuum.Z4CanonicalCylinderConnectedClassification.leftOnly_reach_mem_connectedSourcePairs
#print axioms YMGap.Continuum.Z4CanonicalCylinderConnectedClassification.rightOnly_reach_mem_connectedReverseSourcePairs
