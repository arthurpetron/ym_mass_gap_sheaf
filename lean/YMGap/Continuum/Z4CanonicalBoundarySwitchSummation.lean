/-
# Finite summation of the recoverable boundary switch

This module enumerates the boundary-event / embedded-complement Cartesian
cell with proof-carrying entries.  The separated part is injected into the
opposite boundary-complement / embedded-event cell by the recoverable
component switch.  Exact pair activity is preserved, so only the connected
source pairs remain in the subtraction-free cell bound.
-/

import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
import YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance

namespace YMGap.Continuum.Z4CanonicalBoundarySwitchSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerLocalOccurrence
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

abbrev PolymerFamily := List (List Nat)
abbrev RawFamilyPair := PolymerFamily × PolymerFamily

/-! ## 1. Proof-carrying source entries and literal target entries -/

def boundaryEventFamilyList (small n : Nat) (root : List Nat) :
    List PolymerFamily :=
  (boundaryTargetFamilies small n).filter
    (familyContainsPolymerB root)

def embeddedComplementFamilyList (small n : Nat) (root : List Nat) :
    List PolymerFamily :=
  (embeddedCompatibleFamilies small n).filter
    (fun family => !(familyContainsPolymerB root family))

def boundaryComplementFamilyList (small n : Nat) (root : List Nat) :
    List PolymerFamily :=
  (boundaryTargetFamilies small n).filter
    (fun family => !(familyContainsPolymerB root family))

def embeddedEventFamilyList (small n : Nat) (root : List Nat) :
    List PolymerFamily :=
  (embeddedCompatibleFamilies small n).filter
    (familyContainsPolymerB root)

abbrev BoundaryEventEntry (small n : Nat) (root : List Nat) :=
  {family : PolymerFamily //
    family ∈ boundaryEventFamilyList small n root}

abbrev EmbeddedComplementEntry (small n : Nat) (root : List Nat) :=
  {family : PolymerFamily //
    family ∈ embeddedComplementFamilyList small n root}

abbrev SourcePair (small n : Nat) (root : List Nat) :=
  BoundaryEventEntry small n root ×
    EmbeddedComplementEntry small n root

def boundaryEventEntries (small n : Nat) (root : List Nat) :
    List (BoundaryEventEntry small n root) :=
  (boundaryEventFamilyList small n root).attach

def embeddedComplementEntries (small n : Nat) (root : List Nat) :
    List (EmbeddedComplementEntry small n root) :=
  (embeddedComplementFamilyList small n root).attach

def sourcePairList (small n : Nat) (root : List Nat) :
    List (SourcePair small n root) :=
  cartesian (boundaryEventEntries small n root)
    (embeddedComplementEntries small n root)

def targetPairList (small n : Nat) (root : List Nat) :
    List RawFamilyPair :=
  cartesian (boundaryComplementFamilyList small n root)
    (embeddedEventFamilyList small n root)

/-! ## 2. Canonical source proofs recovered from the entry subtype -/

def sourceLeftBoundary {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) :
    pair.1.val ∈ boundaryTargetFamilies small n :=
  (List.mem_filter.mp pair.1.property).1

def sourceRootMem {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) : root ∈ pair.1.val := by
  have htest := (List.mem_filter.mp pair.1.property).2
  unfold familyContainsPolymerB at htest
  exact of_decide_eq_true htest

def sourceRightEmbedded {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) :
    pair.2.val ∈ embeddedCompatibleFamilies small n :=
  (List.mem_filter.mp pair.2.property).1

def sourceRootNotMem {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) : root ∉ pair.2.val := by
  have htest := (List.mem_filter.mp pair.2.property).2
  have hfalse : familyContainsPolymerB root pair.2.val = false := by
    cases hvalue : familyContainsPolymerB root pair.2.val <;>
      simp_all
  unfold familyContainsPolymerB at hfalse
  exact of_decide_eq_false hfalse

def sourceLeftCompatible {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) :
    pair.1.val ∈ canonicalCompatibleAmbientFamilies n :=
  (List.mem_filter.mp (sourceLeftBoundary pair)).1

def sourceRightCompatible {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : SourcePair small n root) :
    pair.2.val ∈ canonicalCompatibleAmbientFamilies n :=
  embeddedCompatibleFamilies_member_target hsmall
    (sourceRightEmbedded pair)

def sourceRootAtom {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) : CanonicalAtom n :=
  leftCanonicalAtomOfMember (sourceLeftCompatible pair)
    (sourceRootMem pair)

def sourceSeparatedB {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : SourcePair small n root) : Bool :=
  !(boundaryOutsideDisagreementReachB small
    (sourceLeftCompatible pair)
    (sourceRightCompatible hsmall pair)
    (sourceRootAtom pair))

def separatedSourcePairs {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) : List (SourcePair small n root) :=
  (sourcePairList small n root).filter (sourceSeparatedB hsmall)

def connectedSourcePairs {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) : List (SourcePair small n root) :=
  (sourcePairList small n root).filter
    (fun pair => !(sourceSeparatedB hsmall pair))

theorem sourceSeparatedB_all_outside_false
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hseparated : sourceSeparatedB hsmall pair = true) :
    ∀ outside : CanonicalAtom n,
      outside.val ∈ pair.1.val →
        polymerInsideBoxB small n outside.val = false →
          canonicalDisagreementCut
            (sourceLeftCompatible pair)
            (sourceRightCompatible hsmall pair)
            (sourceRootAtom pair) outside = false := by
  have hdecision : boundaryOutsideDisagreementReachB small
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) = false := by
    unfold sourceSeparatedB at hseparated
    cases hvalue : boundaryOutsideDisagreementReachB small
        (sourceLeftCompatible pair)
        (sourceRightCompatible hsmall pair)
        (sourceRootAtom pair) <;> simp_all
  have hdichotomy := boundaryDisagreementReachDichotomy
    (sourceLeftBoundary pair) (sourceRightCompatible hsmall pair)
    (sourceRootMem pair)
  rcases hdichotomy with hconnected | hseparate
  · obtain ⟨outside, houtside, houtsideBox, hreach⟩ := hconnected
    have hreach' : canonicalDisagreementCut
        (sourceLeftCompatible pair)
        (sourceRightCompatible hsmall pair)
        (sourceRootAtom pair) outside = true := by
      simpa [sourceLeftCompatible, sourceRootAtom] using hreach
    have hany : boundaryOutsideDisagreementReachB small
        (sourceLeftCompatible pair)
        (sourceRightCompatible hsmall pair)
        (sourceRootAtom pair) = true := by
      unfold boundaryOutsideDisagreementReachB
      apply List.any_eq_true.mpr
      exact ⟨outside,
        (canonicalFamilyAtom_mem_iff
          (sourceLeftCompatible pair) outside).2 houtside,
        by simp [houtsideBox, hreach']⟩
    rw [hdecision] at hany
    exact False.elim (Bool.false_ne_true hany)
  · intro outside houtside houtsideBox
    simpa [sourceLeftCompatible, sourceRootAtom] using
      hseparate outside houtside houtsideBox

/-! ## 3. The pure switch encoder -/

def separatedSwitchEncode {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : SourcePair small n root) :
    RawFamilyPair :=
  (recoverableSwitchedLeftFamily
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair),
    recoverableSwitchedRightFamily
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair))

theorem separatedSwitchEncode_mem_target
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hpair : pair ∈ separatedSourcePairs hsmall) :
    separatedSwitchEncode hsmall pair ∈ targetPairList small n root := by
  have htest := (List.mem_filter.mp hpair).2
  have hseparated := sourceSeparatedB_all_outside_false
    hsmall pair htest
  have hswitch := separated_recoverable_boundary_event_pair_switch
    anchorCoupling hsmall (sourceLeftBoundary pair)
    (sourceRightEmbedded pair) (sourceRootMem pair)
    (sourceRootNotMem pair) hseparated
  apply (mem_cartesian_iff
    (boundaryComplementFamilyList small n root)
    (embeddedEventFamilyList small n root)
    (separatedSwitchEncode hsmall pair)).2
  constructor
  · unfold boundaryComplementFamilyList
    apply List.mem_filter.mpr
    constructor
    · exact hswitch.1
    · change (!(familyContainsPolymerB root
          (recoverableSwitchedLeftFamily
            (sourceLeftCompatible pair)
            (sourceRightCompatible hsmall pair)
            (sourceRootAtom pair)))) = true
      have hfalse : familyContainsPolymerB root
          (recoverableSwitchedLeftFamily
            (sourceLeftCompatible pair)
            (sourceRightCompatible hsmall pair)
            (sourceRootAtom pair)) = false := by
        simpa [sourceLeftCompatible, sourceRootAtom] using hswitch.2.1
      rw [hfalse]
      rfl
  · unfold embeddedEventFamilyList
    apply List.mem_filter.mpr
    constructor
    · exact hswitch.2.2.1
    · simpa [separatedSwitchEncode, sourceLeftCompatible,
        sourceRootAtom] using hswitch.2.2.2.1

theorem separatedSwitchEncode_injective
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (first second : SourcePair small n root)
    (_hfirst : first ∈ separatedSourcePairs hsmall)
    (_hsecond : second ∈ separatedSourcePairs hsmall)
    (heq : separatedSwitchEncode hsmall first =
      separatedSwitchEncode hsmall second) :
    first = second := by
  have hleftOutput :
      recoverableSwitchedLeftFamily
          (sourceLeftCompatible first)
          (sourceRightCompatible hsmall first)
          (sourceRootAtom first) =
        recoverableSwitchedLeftFamily
          (sourceLeftCompatible second)
          (sourceRightCompatible hsmall second)
          (sourceRootAtom second) :=
    congrArg Prod.fst heq
  have hrightOutput :
      recoverableSwitchedRightFamily
          (sourceLeftCompatible first)
          (sourceRightCompatible hsmall first)
          (sourceRootAtom first) =
        recoverableSwitchedRightFamily
          (sourceLeftCompatible second)
          (sourceRightCompatible hsmall second)
          (sourceRootAtom second) :=
    congrArg Prod.snd heq
  have hsources := recoverableBoundarySwitch_injective
    (sourceLeftCompatible first) (sourceRightCompatible hsmall first)
    (sourceLeftCompatible second) (sourceRightCompatible hsmall second)
    (sourceRootMem first) (sourceRootMem second)
    hleftOutput hrightOutput
  apply Prod.ext
  · exact Subtype.ext hsources.1
  · exact Subtype.ext hsources.2

/-! ## 4. Exact weights and duplicate-free enumerations -/

def sourcePairWeight {small n : Nat} {root : List Nat}
    (pair : SourcePair small n root) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n pair.1.val *
    canonicalSurfaceFamilyActivity anchorCoupling n pair.2.val

def rawPairWeight (n : Nat) (pair : RawFamilyPair) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n pair.1 *
    canonicalSurfaceFamilyActivity anchorCoupling n pair.2

theorem separatedSwitchEncode_weight
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root) :
    rawPairWeight n (separatedSwitchEncode hsmall pair) ≈
      sourcePairWeight pair := by
  exact recoverableSwitchedFamilies_weight_preserved anchorCoupling
    (sourceLeftCompatible pair) (sourceRightCompatible hsmall pair)
    (sourceRootAtom pair)

theorem boundaryEventFamilyList_nodup
    (small n : Nat) (root : List Nat) :
    (boundaryEventFamilyList small n root).Nodup := by
  unfold boundaryEventFamilyList boundaryTargetFamilies
  exact List.filter_sublist.nodup
    (List.filter_sublist.nodup
      (canonicalCompatibleAmbientFamilies_nodup n))

theorem embeddedComplementFamilyList_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (embeddedComplementFamilyList small n root).Nodup := by
  unfold embeddedComplementFamilyList
  exact List.filter_sublist.nodup
    (embeddedCompatibleFamilies_nodup hsmall)

theorem boundaryComplementFamilyList_nodup
    (small n : Nat) (root : List Nat) :
    (boundaryComplementFamilyList small n root).Nodup := by
  unfold boundaryComplementFamilyList boundaryTargetFamilies
  exact List.filter_sublist.nodup
    (List.filter_sublist.nodup
      (canonicalCompatibleAmbientFamilies_nodup n))

theorem embeddedEventFamilyList_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (embeddedEventFamilyList small n root).Nodup := by
  unfold embeddedEventFamilyList
  exact List.filter_sublist.nodup
    (embeddedCompatibleFamilies_nodup hsmall)

theorem sourcePairList_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (sourcePairList small n root).Nodup := by
  exact cartesian_nodup _ _
    (attach_nodup_of_nodup _
      (boundaryEventFamilyList_nodup small n root))
    (attach_nodup_of_nodup _
      (embeddedComplementFamilyList_nodup hsmall root))

theorem separatedSourcePairs_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (separatedSourcePairs (root := root) hsmall).Nodup :=
  List.filter_sublist.nodup (sourcePairList_nodup hsmall root)

theorem targetPairList_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (targetPairList small n root).Nodup :=
  cartesian_nodup _ _
    (boundaryComplementFamilyList_nodup small n root)
    (embeddedEventFamilyList_nodup hsmall root)

/-! ## 5. Global separated cancellation and the connected residual -/

theorem separatedPairSum_le_targetPairSum
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    listQSum sourcePairWeight
        (separatedSourcePairs (root := root) hsmall) ≤
      listQSum (rawPairWeight n) (targetPairList small n root) := by
  apply listQSum_le_of_injective
    (separatedSourcePairs (root := root) hsmall)
    (targetPairList small n root)
    sourcePairWeight (rawPairWeight n)
    (separatedSwitchEncode hsmall)
    (separatedSourcePairs_nodup hsmall root)
  · exact separatedSwitchEncode_mem_target hsmall
  · intro first hfirst second hsecond heq
    exact separatedSwitchEncode_injective hsmall first second
      hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm (separatedSwitchEncode_weight hsmall pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (canonicalSurfaceFamilyActivity_nonnegative n pair.1)
      (canonicalSurfaceFamilyActivity_nonnegative n pair.2)

theorem sourcePairList_sum_eqv_cellProduct
    {small n : Nat} (_hsmall : small ≤ n) (root : List Nat) :
    listQSum sourcePairWeight (sourcePairList small n root) ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryEventFamilyList small n root) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedComplementFamilyList small n root) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : BoundaryEventEntry small n root =>
      canonicalSurfaceFamilyActivity anchorCoupling n entry.val)
    (fun entry : EmbeddedComplementEntry small n root =>
      canonicalSurfaceFamilyActivity anchorCoupling n entry.val)
    (boundaryEventEntries small n root)
    (embeddedComplementEntries small n root)
  unfold sourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold boundaryEventEntries embeddedComplementEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem targetPairList_sum_eqv_cellProduct
    (small n : Nat) (root : List Nat) :
    listQSum (rawPairWeight n) (targetPairList small n root) ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryComplementFamilyList small n root) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedEventFamilyList small n root) := by
  exact listQSum_cartesian_product
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (boundaryComplementFamilyList small n root)
    (embeddedEventFamilyList small n root)

/-! ## 5. Named four-cell observables -/

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem boundaryEventFamilySum_eqv_targetEventNumerator
    (small n : Nat) (root : List Nat) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (boundaryEventFamilyList small n root) ≈
      boundaryTargetEventNumerator small n
        (familyContainsPolymerB root) := by
  unfold boundaryEventFamilyList
  exact Q'.eqv_symm
    (boundaryTargetEventNumerator_eqv_filter small n
      (familyContainsPolymerB root))

theorem boundaryComplementFamilySum_eqv_targetComplementNumerator
    (small n : Nat) (root : List Nat) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (boundaryComplementFamilyList small n root) ≈
      boundaryTargetEventComplementNumerator small n
        (familyContainsPolymerB root) := by
  unfold boundaryComplementFamilyList
    boundaryTargetEventComplementNumerator
  exact Q'.eqv_refl _

theorem embeddedEventFamilySum_eqv_targetEventNumerator
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (embeddedEventFamilyList small n root) ≈
      embeddedTargetEventNumerator small n
        (familyContainsPolymerB root) := by
  have hperm := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    ((embeddedCompatibleFamilies_perm_target hsmall).filter
      (familyContainsPolymerB root))
  unfold embeddedEventFamilyList at hperm ⊢
  exact Q'.eqv_trans _ _ _ hperm
    (Q'.eqv_symm
      (embeddedTargetEventNumerator_eqv_filter small n
        (familyContainsPolymerB root)))

theorem embeddedComplementFamilySum_eqv_targetComplementNumerator
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (embeddedComplementFamilyList small n root) ≈
      embeddedTargetEventComplementNumerator small n
        (familyContainsPolymerB root) := by
  have hperm := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    ((embeddedCompatibleFamilies_perm_target hsmall).filter
      (fun family => !(familyContainsPolymerB root family)))
  unfold embeddedComplementFamilyList
  exact hperm

/-! ## 6. Global separated cancellation and the connected residual -/

theorem sourcePairList_partition
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    listQSum sourcePairWeight (sourcePairList small n root) ≈
      listQSum sourcePairWeight
          (separatedSourcePairs (root := root) hsmall) +
        listQSum sourcePairWeight
          (connectedSourcePairs (root := root) hsmall) := by
  exact listQSum_filter_partition sourcePairWeight
    (sourceSeparatedB hsmall) (sourcePairList small n root)

/-- Subtraction-free global cancellation: the entire source opposite cell is
bounded by the target opposite cell plus exactly the connected source pairs. -/
theorem boundaryEvent_embeddedComplement_le_opposite_add_connected
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryEventFamilyList small n root) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedComplementFamilyList small n root) ≤
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
            (boundaryComplementFamilyList small n root) *
          listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
            (embeddedEventFamilyList small n root) +
        listQSum sourcePairWeight
          (connectedSourcePairs (root := root) hsmall) := by
  have hsource := sourcePairList_sum_eqv_cellProduct hsmall root
  have htarget := targetPairList_sum_eqv_cellProduct small n root
  have hpartition := sourcePairList_partition hsmall root
  have hinjection := separatedPairSum_le_targetPairSum hsmall root
  have hsepAdd :
      listQSum sourcePairWeight
            (separatedSourcePairs (root := root) hsmall) +
          listQSum sourcePairWeight
            (connectedSourcePairs (root := root) hsmall) ≤
        listQSum (rawPairWeight n) (targetPairList small n root) +
          listQSum sourcePairWeight
            (connectedSourcePairs (root := root) hsmall) :=
    Q'.add_le_add hinjection (Q'.le_refl' _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

/-- The raw-list cancellation expressed in the named four-cell observables. -/
theorem boundaryTargetEvent_embeddedTargetComplement_le_opposite_add_connected
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    boundaryTargetEventNumerator small n
          (familyContainsPolymerB root) *
        embeddedTargetEventComplementNumerator small n
          (familyContainsPolymerB root) ≤
      boundaryTargetEventComplementNumerator small n
            (familyContainsPolymerB root) *
          embeddedTargetEventNumerator small n
            (familyContainsPolymerB root) +
        listQSum sourcePairWeight
          (connectedSourcePairs (root := root) hsmall) := by
  have hraw := boundaryEvent_embeddedComplement_le_opposite_add_connected
    hsmall root
  have hboundaryEvent :=
    boundaryEventFamilySum_eqv_targetEventNumerator small n root
  have hembeddedComplement :=
    embeddedComplementFamilySum_eqv_targetComplementNumerator hsmall root
  have hboundaryComplement :=
    boundaryComplementFamilySum_eqv_targetComplementNumerator small n root
  have hembeddedEvent :=
    embeddedEventFamilySum_eqv_targetEventNumerator hsmall root
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (mul_eqv_both (Q'.eqv_symm hboundaryEvent)
        (Q'.eqv_symm hembeddedComplement)))
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv
        (Q'.add_eqv_congr'
          (mul_eqv_both hboundaryComplement hembeddedEvent)
          (Q'.eqv_refl _))))

/-- The named opposite-cell determinant is bounded by exactly the connected
source-pair residue. -/
theorem boundaryTargetEventComplementCrossDifference_le_connected
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    boundaryTargetEventNumerator small n
          (familyContainsPolymerB root) *
        embeddedTargetEventComplementNumerator small n
          (familyContainsPolymerB root) -
      embeddedTargetEventNumerator small n
          (familyContainsPolymerB root) *
        boundaryTargetEventComplementNumerator small n
          (familyContainsPolymerB root) ≤
      listQSum sourcePairWeight
        (connectedSourcePairs (root := root) hsmall) := by
  have hcells :=
    boundaryTargetEvent_embeddedTargetComplement_le_opposite_add_connected
      hsmall root
  have hreordered :
      boundaryTargetEventNumerator small n
            (familyContainsPolymerB root) *
          embeddedTargetEventComplementNumerator small n
            (familyContainsPolymerB root) ≤
        embeddedTargetEventNumerator small n
              (familyContainsPolymerB root) *
            boundaryTargetEventComplementNumerator small n
              (familyContainsPolymerB root) +
          listQSum sourcePairWeight
            (connectedSourcePairs (root := root) hsmall) :=
    Q'.le_trans' _ _ _ hcells
      (Q'.le_of_eqv
        (Q'.add_eqv_congr'
          (Q'.mul_comm_eqv
            (boundaryTargetEventComplementNumerator small n
              (familyContainsPolymerB root))
            (embeddedTargetEventNumerator small n
              (familyContainsPolymerB root)))
          (Q'.eqv_refl _)))
  exact Q'.sub_le_of_le_add hreordered

/-- The exact larger-minus-smaller local-occurrence cross numerator is reduced
to the explicit connected source-pair sum. -/
theorem anchorOccurrenceCrossDifference_le_connected
    {small n : Nat} (hsmall : small ≤ n) {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers small) :
    anchorEventNumerator n (targetOccurrenceEvent small n polymer) *
          anchorCanonicalPartition small -
        anchorEventNumerator small (sourceOccurrenceEvent polymer) *
          anchorCanonicalPartition n ≤
      listQSum sourcePairWeight
        (connectedSourcePairs
          (root := transportPolymer small n polymer) hsmall) := by
  have hcross := anchorOccurrenceCrossDifference_eqv_eventComplementCells
    hsmall hpolymer
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcross)
    (boundaryTargetEventComplementCrossDifference_le_connected hsmall
      (transportPolymer small n polymer))

end YMGap.Continuum.Z4CanonicalBoundarySwitchSummation

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.sourceSeparatedB_all_outside_false
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.separatedSwitchEncode_mem_target
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.separatedSwitchEncode_injective
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.separatedPairSum_le_targetPairSum
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.sourcePairList_sum_eqv_cellProduct
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.boundaryEvent_embeddedComplement_le_opposite_add_connected
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.embeddedEventFamilySum_eqv_targetEventNumerator
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.boundaryTargetEvent_embeddedTargetComplement_le_opposite_add_connected
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.boundaryTargetEventComplementCrossDifference_le_connected
#print axioms YMGap.Continuum.Z4CanonicalBoundarySwitchSummation.anchorOccurrenceCrossDifference_le_connected
