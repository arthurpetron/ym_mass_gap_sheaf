/-
# Finite summation of the right-rooted boundary switch

This is the reverse orientation of the canonical four-cell cancellation.  Its
source is embedded-event times boundary-complement.  Separated disagreement
components inject into embedded-complement times boundary-event; the remaining
entries are exactly those whose marked embedded polymer connects to an
exterior polymer in the boundary replica.
-/

import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4CanonicalBoundaryRightRootSwitch
import YMGap.Continuum.Z4CanonicalBoundarySwitchSummation

namespace YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSwitch
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
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

/-! ## 1. Reverse source and target enumerations -/

abbrev ReverseEmbeddedEventEntry (small n : Nat) (root : List Nat) :=
  {family : PolymerFamily //
    family ∈ embeddedEventFamilyList small n root}

abbrev ReverseBoundaryComplementEntry
    (small n : Nat) (root : List Nat) :=
  {family : PolymerFamily //
    family ∈ boundaryComplementFamilyList small n root}

abbrev ReverseSourcePair (small n : Nat) (root : List Nat) :=
  ReverseEmbeddedEventEntry small n root ×
    ReverseBoundaryComplementEntry small n root

def reverseEmbeddedEventEntries (small n : Nat) (root : List Nat) :
    List (ReverseEmbeddedEventEntry small n root) :=
  (embeddedEventFamilyList small n root).attach

def reverseBoundaryComplementEntries (small n : Nat) (root : List Nat) :
    List (ReverseBoundaryComplementEntry small n root) :=
  (boundaryComplementFamilyList small n root).attach

def reverseSourcePairList (small n : Nat) (root : List Nat) :
    List (ReverseSourcePair small n root) :=
  cartesian (reverseEmbeddedEventEntries small n root)
    (reverseBoundaryComplementEntries small n root)

def reverseTargetPairList (small n : Nat) (root : List Nat) :
    List RawFamilyPair :=
  cartesian (embeddedComplementFamilyList small n root)
    (boundaryEventFamilyList small n root)

/-! ## 2. Source facts and the right-boundary reach decision -/

def reverseSourceLeftEmbedded {small n : Nat} {root : List Nat}
    (pair : ReverseSourcePair small n root) :
    pair.1.val ∈ embeddedCompatibleFamilies small n :=
  (List.mem_filter.mp pair.1.property).1

def reverseSourceRootMem {small n : Nat} {root : List Nat}
    (pair : ReverseSourcePair small n root) : root ∈ pair.1.val := by
  have htest := (List.mem_filter.mp pair.1.property).2
  unfold familyContainsPolymerB at htest
  exact of_decide_eq_true htest

def reverseSourceRightBoundary {small n : Nat} {root : List Nat}
    (pair : ReverseSourcePair small n root) :
    pair.2.val ∈ boundaryTargetFamilies small n :=
  (List.mem_filter.mp pair.2.property).1

def reverseSourceRootNotMem {small n : Nat} {root : List Nat}
    (pair : ReverseSourcePair small n root) : root ∉ pair.2.val := by
  have htest := (List.mem_filter.mp pair.2.property).2
  have hfalse : familyContainsPolymerB root pair.2.val = false := by
    cases hvalue : familyContainsPolymerB root pair.2.val <;> simp_all
  unfold familyContainsPolymerB at hfalse
  exact of_decide_eq_false hfalse

def reverseSourceLeftCompatible {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : ReverseSourcePair small n root) :
    pair.1.val ∈ canonicalCompatibleAmbientFamilies n :=
  embeddedCompatibleFamilies_member_target hsmall
    (reverseSourceLeftEmbedded pair)

def reverseSourceRightCompatible {small n : Nat} {root : List Nat}
    (pair : ReverseSourcePair small n root) :
    pair.2.val ∈ canonicalCompatibleAmbientFamilies n :=
  (List.mem_filter.mp (reverseSourceRightBoundary pair)).1

def reverseSourceRootAtom {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : ReverseSourcePair small n root) :
    CanonicalAtom n :=
  leftCanonicalAtomOfMember (reverseSourceLeftCompatible hsmall pair)
    (reverseSourceRootMem pair)

def rightBoundaryOutsideDisagreementReachB
    {n : Nat} {left right : List (List Nat)}
    (small : Nat)
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n)
    (root : CanonicalAtom n) : Bool :=
  (canonicalFamilyAtoms hright).any (fun outside =>
    (!(polymerInsideBoxB small n outside.val)) &&
      canonicalDisagreementCut hleft hright root outside)

def reverseSourceSeparatedB
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root) : Bool :=
  !(rightBoundaryOutsideDisagreementReachB small
    (reverseSourceLeftCompatible hsmall pair)
    (reverseSourceRightCompatible pair)
    (reverseSourceRootAtom hsmall pair))

def separatedReverseSourcePairs
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n) :
    List (ReverseSourcePair small n root) :=
  (reverseSourcePairList small n root).filter
    (reverseSourceSeparatedB hsmall)

def connectedReverseSourcePairs
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n) :
    List (ReverseSourcePair small n root) :=
  (reverseSourcePairList small n root).filter
    (fun pair => !(reverseSourceSeparatedB hsmall pair))

theorem reverseSourceSeparatedB_all_outside_false
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root)
    (hseparated : reverseSourceSeparatedB hsmall pair = true) :
    ∀ outside : CanonicalAtom n,
      outside.val ∈ pair.2.val →
        polymerInsideBoxB small n outside.val = false →
          canonicalDisagreementCut
            (reverseSourceLeftCompatible hsmall pair)
            (reverseSourceRightCompatible pair)
            (reverseSourceRootAtom hsmall pair) outside = false := by
  have hdecision : rightBoundaryOutsideDisagreementReachB small
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair) = false := by
    unfold reverseSourceSeparatedB at hseparated
    cases hvalue : rightBoundaryOutsideDisagreementReachB small
        (reverseSourceLeftCompatible hsmall pair)
        (reverseSourceRightCompatible pair)
        (reverseSourceRootAtom hsmall pair) <;> simp_all
  intro outside houtside houtsideBox
  cases hreach : canonicalDisagreementCut
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair) outside with
  | false => rfl
  | true =>
      have houtsideAtoms : outside ∈
          canonicalFamilyAtoms (reverseSourceRightCompatible pair) :=
        (canonicalFamilyAtom_mem_iff
          (reverseSourceRightCompatible pair) outside).2 houtside
      have hany : rightBoundaryOutsideDisagreementReachB small
          (reverseSourceLeftCompatible hsmall pair)
          (reverseSourceRightCompatible pair)
          (reverseSourceRootAtom hsmall pair) = true := by
        unfold rightBoundaryOutsideDisagreementReachB
        apply List.any_eq_true.mpr
        exact ⟨outside, houtsideAtoms, by simp [houtsideBox, hreach]⟩
      rw [hdecision] at hany
      exact False.elim (Bool.false_ne_true hany)

/-! ## 3. The separated injection -/

def separatedReverseSwitchEncode
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root) : RawFamilyPair :=
  (recoverableSwitchedLeftFamily
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair),
    recoverableSwitchedRightFamily
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair))

theorem separatedReverseSwitchEncode_mem_target
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root)
    (hpair : pair ∈ separatedReverseSourcePairs hsmall) :
    separatedReverseSwitchEncode hsmall pair ∈
      reverseTargetPairList small n root := by
  have htest := (List.mem_filter.mp hpair).2
  have hseparated := reverseSourceSeparatedB_all_outside_false
    hsmall pair htest
  have hswitch := separated_recoverable_embedded_event_pair_switch
    anchorCoupling hsmall (reverseSourceLeftEmbedded pair)
    (reverseSourceRightBoundary pair) (reverseSourceRootMem pair)
    (reverseSourceRootNotMem pair) hseparated
  apply (mem_cartesian_iff
    (embeddedComplementFamilyList small n root)
    (boundaryEventFamilyList small n root)
    (separatedReverseSwitchEncode hsmall pair)).2
  constructor
  · unfold embeddedComplementFamilyList
    apply List.mem_filter.mpr
    exact ⟨hswitch.1, by
      have hfalse : familyContainsPolymerB root
          (recoverableSwitchedLeftFamily
            (reverseSourceLeftCompatible hsmall pair)
            (reverseSourceRightCompatible pair)
            (reverseSourceRootAtom hsmall pair)) = false := by
        simpa [reverseSourceLeftCompatible, reverseSourceRightCompatible,
          reverseSourceRootAtom] using hswitch.2.1
      simp [separatedReverseSwitchEncode, hfalse]⟩
  · unfold boundaryEventFamilyList
    apply List.mem_filter.mpr
    exact ⟨hswitch.2.2.1, by
      simpa [separatedReverseSwitchEncode, reverseSourceLeftCompatible,
        reverseSourceRightCompatible, reverseSourceRootAtom] using
        hswitch.2.2.2.1⟩

theorem separatedReverseSwitchEncode_injective
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (first second : ReverseSourcePair small n root)
    (_hfirst : first ∈ separatedReverseSourcePairs hsmall)
    (_hsecond : second ∈ separatedReverseSourcePairs hsmall)
    (heq : separatedReverseSwitchEncode hsmall first =
      separatedReverseSwitchEncode hsmall second) :
    first = second := by
  have hleftOutput := congrArg Prod.fst heq
  have hrightOutput := congrArg Prod.snd heq
  have hsources := recoverableBoundarySwitch_injective
    (reverseSourceLeftCompatible hsmall first)
    (reverseSourceRightCompatible first)
    (reverseSourceLeftCompatible hsmall second)
    (reverseSourceRightCompatible second)
    (reverseSourceRootMem first) (reverseSourceRootMem second)
    hleftOutput hrightOutput
  apply Prod.ext
  · exact Subtype.ext hsources.1
  · exact Subtype.ext hsources.2

def reverseSourcePairWeight
    {small n : Nat} {root : List Nat}
    (pair : ReverseSourcePair small n root) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n pair.1.val *
    canonicalSurfaceFamilyActivity anchorCoupling n pair.2.val

def reverseRawPairWeight (n : Nat) (pair : RawFamilyPair) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n pair.1 *
    canonicalSurfaceFamilyActivity anchorCoupling n pair.2

theorem separatedReverseSwitchEncode_weight
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root) :
    reverseRawPairWeight n (separatedReverseSwitchEncode hsmall pair) ≈
      reverseSourcePairWeight pair := by
  exact recoverableSwitchedFamilies_weight_preserved anchorCoupling
    (reverseSourceLeftCompatible hsmall pair)
    (reverseSourceRightCompatible pair)
    (reverseSourceRootAtom hsmall pair)

theorem reverseSourcePairList_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (reverseSourcePairList small n root).Nodup := by
  exact cartesian_nodup _ _
    (attach_nodup_of_nodup _
      (embeddedEventFamilyList_nodup hsmall root))
    (attach_nodup_of_nodup _
      (boundaryComplementFamilyList_nodup small n root))

theorem separatedReverseSourcePairs_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (separatedReverseSourcePairs (root := root) hsmall).Nodup :=
  List.filter_sublist.nodup (reverseSourcePairList_nodup hsmall root)

theorem reverseTargetPairList_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (reverseTargetPairList small n root).Nodup :=
  cartesian_nodup _ _
    (embeddedComplementFamilyList_nodup hsmall root)
    (boundaryEventFamilyList_nodup small n root)

theorem separatedReversePairSum_le_targetPairSum
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    listQSum reverseSourcePairWeight
        (separatedReverseSourcePairs (root := root) hsmall) ≤
      listQSum (reverseRawPairWeight n)
        (reverseTargetPairList small n root) := by
  apply listQSum_le_of_injective
    (separatedReverseSourcePairs (root := root) hsmall)
    (reverseTargetPairList small n root)
    reverseSourcePairWeight (reverseRawPairWeight n)
    (separatedReverseSwitchEncode hsmall)
    (separatedReverseSourcePairs_nodup hsmall root)
  · exact separatedReverseSwitchEncode_mem_target hsmall
  · intro first hfirst second hsecond heq
    exact separatedReverseSwitchEncode_injective hsmall first second
      hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm (separatedReverseSwitchEncode_weight hsmall pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (canonicalSurfaceFamilyActivity_nonnegative n pair.1)
      (canonicalSurfaceFamilyActivity_nonnegative n pair.2)

/-! ## 4. Four-cell summation and reverse cross numerator -/

theorem reverseSourcePairList_sum_eqv_cellProduct
    {small n : Nat} (_hsmall : small ≤ n) (root : List Nat) :
    listQSum reverseSourcePairWeight
        (reverseSourcePairList small n root) ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedEventFamilyList small n root) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryComplementFamilyList small n root) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : ReverseEmbeddedEventEntry small n root =>
      canonicalSurfaceFamilyActivity anchorCoupling n entry.val)
    (fun entry : ReverseBoundaryComplementEntry small n root =>
      canonicalSurfaceFamilyActivity anchorCoupling n entry.val)
    (reverseEmbeddedEventEntries small n root)
    (reverseBoundaryComplementEntries small n root)
  unfold reverseSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold reverseEmbeddedEventEntries reverseBoundaryComplementEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem reverseTargetPairList_sum_eqv_cellProduct
    (small n : Nat) (root : List Nat) :
    listQSum (reverseRawPairWeight n)
        (reverseTargetPairList small n root) ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedComplementFamilyList small n root) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryEventFamilyList small n root) := by
  exact listQSum_cartesian_product
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (embeddedComplementFamilyList small n root)
    (boundaryEventFamilyList small n root)

theorem reverseSourcePairList_partition
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    listQSum reverseSourcePairWeight
        (reverseSourcePairList small n root) ≈
      listQSum reverseSourcePairWeight
          (separatedReverseSourcePairs (root := root) hsmall) +
        listQSum reverseSourcePairWeight
          (connectedReverseSourcePairs (root := root) hsmall) := by
  exact listQSum_filter_partition reverseSourcePairWeight
    (reverseSourceSeparatedB hsmall) (reverseSourcePairList small n root)

theorem embeddedEvent_boundaryComplement_le_opposite_add_connected
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedEventFamilyList small n root) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryComplementFamilyList small n root) ≤
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
            (embeddedComplementFamilyList small n root) *
          listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
            (boundaryEventFamilyList small n root) +
        listQSum reverseSourcePairWeight
          (connectedReverseSourcePairs (root := root) hsmall) := by
  have hsource := reverseSourcePairList_sum_eqv_cellProduct hsmall root
  have htarget := reverseTargetPairList_sum_eqv_cellProduct small n root
  have hpartition := reverseSourcePairList_partition hsmall root
  have hinjection := separatedReversePairSum_le_targetPairSum hsmall root
  have hsepAdd := Q'.add_le_add hinjection
    (Q'.le_refl' (listQSum reverseSourcePairWeight
      (connectedReverseSourcePairs (root := root) hsmall)))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem embeddedTargetEvent_boundaryTargetComplement_le_opposite_add_connected
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    embeddedTargetEventNumerator small n
          (familyContainsPolymerB root) *
        boundaryTargetEventComplementNumerator small n
          (familyContainsPolymerB root) ≤
      boundaryTargetEventNumerator small n
            (familyContainsPolymerB root) *
          embeddedTargetEventComplementNumerator small n
            (familyContainsPolymerB root) +
        listQSum reverseSourcePairWeight
          (connectedReverseSourcePairs (root := root) hsmall) := by
  have hraw := embeddedEvent_boundaryComplement_le_opposite_add_connected
    hsmall root
  have hembeddedEvent :=
    embeddedEventFamilySum_eqv_targetEventNumerator hsmall root
  have hboundaryComplement :=
    boundaryComplementFamilySum_eqv_targetComplementNumerator small n root
  have hembeddedComplement :=
    embeddedComplementFamilySum_eqv_targetComplementNumerator hsmall root
  have hboundaryEvent :=
    boundaryEventFamilySum_eqv_targetEventNumerator small n root
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (mul_eqv_both (Q'.eqv_symm hembeddedEvent)
        (Q'.eqv_symm hboundaryComplement)))
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (mul_eqv_both hembeddedComplement hboundaryEvent)
            (Q'.mul_comm_eqv _ _))
          (Q'.eqv_refl _))))

theorem embeddedTargetEventBoundaryComplementCrossDifference_le_connected
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    embeddedTargetEventNumerator small n
          (familyContainsPolymerB root) *
        boundaryTargetEventComplementNumerator small n
          (familyContainsPolymerB root) -
      boundaryTargetEventNumerator small n
          (familyContainsPolymerB root) *
        embeddedTargetEventComplementNumerator small n
          (familyContainsPolymerB root) ≤
      listQSum reverseSourcePairWeight
        (connectedReverseSourcePairs (root := root) hsmall) := by
  exact Q'.sub_le_of_le_add
    (embeddedTargetEvent_boundaryTargetComplement_le_opposite_add_connected
      hsmall root)

private theorem sub_swap_eqv_neg (a b : Q') :
    b - a ≈ -(a - b) := by
  change (b + -a).eqv (-(a + -b))
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv b (-a)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (-a) b (-(-b))
      (Q'.eqv_symm (Q'.neg_neg_eqv b))) ?_
  exact Q'.eqv_symm (Q'.neg_add_eqv a (-b))

/-- The smaller-minus-larger occurrence cross numerator is reduced to the
right-rooted connected residue. -/
theorem anchorReverseOccurrenceCrossDifference_le_connected
    {small n : Nat} (hsmall : small ≤ n) {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalSurfacePolymers small) :
    anchorEventNumerator small (sourceOccurrenceEvent polymer) *
          anchorCanonicalPartition n -
        anchorEventNumerator n (targetOccurrenceEvent small n polymer) *
          anchorCanonicalPartition small ≤
      listQSum reverseSourcePairWeight
        (connectedReverseSourcePairs
          (root := transportPolymer small n polymer) hsmall) := by
  have hforward := anchorOccurrenceCrossDifference_eqv_eventComplementCells
    hsmall hpolymer
  have hreverse :
      anchorEventNumerator small (sourceOccurrenceEvent polymer) *
            anchorCanonicalPartition n -
          anchorEventNumerator n (targetOccurrenceEvent small n polymer) *
            anchorCanonicalPartition small ≈
        embeddedTargetEventNumerator small n
              (targetOccurrenceEvent small n polymer) *
            boundaryTargetEventComplementNumerator small n
              (targetOccurrenceEvent small n polymer) -
          boundaryTargetEventNumerator small n
              (targetOccurrenceEvent small n polymer) *
            embeddedTargetEventComplementNumerator small n
              (targetOccurrenceEvent small n polymer) := by
    refine Q'.eqv_trans _ _ _
      (sub_swap_eqv_neg
        (anchorEventNumerator n (targetOccurrenceEvent small n polymer) *
          anchorCanonicalPartition small)
        (anchorEventNumerator small (sourceOccurrenceEvent polymer) *
          anchorCanonicalPartition n)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ hforward) ?_
    exact Q'.eqv_symm
      (sub_swap_eqv_neg
        (boundaryTargetEventNumerator small n
            (targetOccurrenceEvent small n polymer) *
          embeddedTargetEventComplementNumerator small n
            (targetOccurrenceEvent small n polymer))
        (embeddedTargetEventNumerator small n
            (targetOccurrenceEvent small n polymer) *
          boundaryTargetEventComplementNumerator small n
            (targetOccurrenceEvent small n polymer)))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreverse)
    (embeddedTargetEventBoundaryComplementCrossDifference_le_connected
      hsmall (transportPolymer small n polymer))

end YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation.reverseSourceSeparatedB_all_outside_false
#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation.separatedReverseSwitchEncode_mem_target
#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation.separatedReverseSwitchEncode_injective
#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation.separatedReversePairSum_le_targetPairSum
#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation.embeddedEvent_boundaryComplement_le_opposite_add_connected
#print axioms YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation.anchorReverseOccurrenceCrossDifference_le_connected
