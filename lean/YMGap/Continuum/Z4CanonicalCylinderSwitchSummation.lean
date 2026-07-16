/-
# Finite summation of the marked cylinder switch

This module repeats the exact four-cell cancellation for an arbitrary Boolean
function of a finite occurrence fingerprint.  The separated source pairs are
injected into the opposite cell by the simultaneous marked-component switch;
only the marked connected residue remains.
-/

import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4CanonicalCylinderConnectedClassification
import YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance

namespace YMGap.Continuum.Z4CanonicalCylinderSwitchSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

abbrev PolymerFamily := List (List Nat)
abbrev RawFamilyPair := PolymerFamily × PolymerFamily

def markedCylinderEvent (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) : PolymerFamily → Bool :=
  cylinderEvent (roots.map Subtype.val) predicate

def boundaryCylinderEventFamilyList (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    List PolymerFamily :=
  (boundaryTargetFamilies small n).filter
    (markedCylinderEvent roots predicate)

def embeddedCylinderComplementFamilyList (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    List PolymerFamily :=
  (embeddedCompatibleFamilies small n).filter
    (fun family => !(markedCylinderEvent roots predicate family))

def boundaryCylinderComplementFamilyList (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    List PolymerFamily :=
  (boundaryTargetFamilies small n).filter
    (fun family => !(markedCylinderEvent roots predicate family))

def embeddedCylinderEventFamilyList (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    List PolymerFamily :=
  (embeddedCompatibleFamilies small n).filter
    (markedCylinderEvent roots predicate)

abbrev BoundaryCylinderEventEntry (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :=
  {family : PolymerFamily //
    family ∈ boundaryCylinderEventFamilyList small n roots predicate}

abbrev EmbeddedCylinderComplementEntry (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :=
  {family : PolymerFamily //
    family ∈ embeddedCylinderComplementFamilyList small n roots predicate}

abbrev CylinderSourcePair (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :=
  BoundaryCylinderEventEntry small n roots predicate ×
    EmbeddedCylinderComplementEntry small n roots predicate

def boundaryCylinderEventEntries (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    List (BoundaryCylinderEventEntry small n roots predicate) :=
  (boundaryCylinderEventFamilyList small n roots predicate).attach

def embeddedCylinderComplementEntries (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    List (EmbeddedCylinderComplementEntry small n roots predicate) :=
  (embeddedCylinderComplementFamilyList small n roots predicate).attach

def cylinderSourcePairList (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    List (CylinderSourcePair small n roots predicate) :=
  cartesian (boundaryCylinderEventEntries small n roots predicate)
    (embeddedCylinderComplementEntries small n roots predicate)

def cylinderTargetPairList (small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    List RawFamilyPair :=
  cartesian (boundaryCylinderComplementFamilyList small n roots predicate)
    (embeddedCylinderEventFamilyList small n roots predicate)

def cylinderSourceLeftBoundary
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) :
    pair.1.val ∈ boundaryTargetFamilies small n :=
  (List.mem_filter.mp pair.1.property).1

def cylinderSourceLeftEvent
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) :
    markedCylinderEvent roots predicate pair.1.val = true :=
  (List.mem_filter.mp pair.1.property).2

def cylinderSourceRightEmbedded
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) :
    pair.2.val ∈ embeddedCompatibleFamilies small n :=
  (List.mem_filter.mp pair.2.property).1

def cylinderSourceRightEventFalse
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) :
    markedCylinderEvent roots predicate pair.2.val = false := by
  have htest := (List.mem_filter.mp pair.2.property).2
  cases hvalue : markedCylinderEvent roots predicate pair.2.val <;>
    simp_all

def cylinderSourceLeftCompatible
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) :
    pair.1.val ∈ canonicalCompatibleAmbientFamilies n :=
  (List.mem_filter.mp (cylinderSourceLeftBoundary pair)).1

def cylinderSourceRightCompatible
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (pair : CylinderSourcePair small n roots predicate) :
    pair.2.val ∈ canonicalCompatibleAmbientFamilies n :=
  embeddedCompatibleFamilies_member_target hsmall
    (cylinderSourceRightEmbedded pair)

def cylinderSourceSeparatedB
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (pair : CylinderSourcePair small n roots predicate) : Bool :=
  !(boundaryOutsideMarkedReachB small
    (cylinderSourceLeftCompatible pair)
    (cylinderSourceRightCompatible hsmall pair) roots)

def separatedCylinderSourcePairs
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n) :
    List (CylinderSourcePair small n roots predicate) :=
  (cylinderSourcePairList small n roots predicate).filter
    (cylinderSourceSeparatedB hsmall)

def connectedCylinderSourcePairs
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n) :
    List (CylinderSourcePair small n roots predicate) :=
  (cylinderSourcePairList small n roots predicate).filter
    (fun pair => !(cylinderSourceSeparatedB hsmall pair))

theorem cylinderSourceSeparatedB_all_outside_false
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (pair : CylinderSourcePair small n roots predicate)
    (hseparated : cylinderSourceSeparatedB hsmall pair = true) :
    ∀ outside : CanonicalAtom n, outside.val ∈ pair.1.val →
      polymerInsideBoxB small n outside.val = false →
        canonicalMarkedCut
          (cylinderSourceLeftCompatible pair)
          (cylinderSourceRightCompatible hsmall pair)
          roots outside = false := by
  have hdecision : boundaryOutsideMarkedReachB small
      (cylinderSourceLeftCompatible pair)
      (cylinderSourceRightCompatible hsmall pair) roots = false := by
    unfold cylinderSourceSeparatedB at hseparated
    cases hvalue : boundaryOutsideMarkedReachB small
        (cylinderSourceLeftCompatible pair)
        (cylinderSourceRightCompatible hsmall pair) roots <;> simp_all
  exact boundaryOutsideMarkedReachB_false_separated
    (cylinderSourceLeftCompatible pair)
    (cylinderSourceRightCompatible hsmall pair) roots hdecision

def separatedCylinderSwitchEncode
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (pair : CylinderSourcePair small n roots predicate) : RawFamilyPair :=
  (recoverableMarkedSwitchedLeftFamily
      (cylinderSourceLeftCompatible pair)
      (cylinderSourceRightCompatible hsmall pair) roots,
    recoverableMarkedSwitchedRightFamily
      (cylinderSourceLeftCompatible pair)
      (cylinderSourceRightCompatible hsmall pair) roots)

theorem separatedCylinderSwitchEncode_mem_target
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (pair : CylinderSourcePair small n roots predicate)
    (hpair : pair ∈ separatedCylinderSourcePairs hsmall) :
    separatedCylinderSwitchEncode hsmall pair ∈
      cylinderTargetPairList small n roots predicate := by
  have htest := (List.mem_filter.mp hpair).2
  have hseparated := cylinderSourceSeparatedB_all_outside_false
    hsmall pair htest
  have hswitch := separated_marked_boundary_cylinder_pair_switch
    anchorCoupling hsmall (cylinderSourceLeftBoundary pair)
    (cylinderSourceRightEmbedded pair) roots predicate hseparated
  apply (mem_cartesian_iff
    (boundaryCylinderComplementFamilyList small n roots predicate)
    (embeddedCylinderEventFamilyList small n roots predicate)
    (separatedCylinderSwitchEncode hsmall pair)).2
  constructor
  · unfold boundaryCylinderComplementFamilyList
    apply List.mem_filter.mpr
    constructor
    · exact hswitch.1
    · have hevent : markedCylinderEvent roots predicate
          (recoverableMarkedSwitchedLeftFamily
            (cylinderSourceLeftCompatible pair)
            (cylinderSourceRightCompatible hsmall pair) roots) = false := by
        unfold markedCylinderEvent
        rw [hswitch.2.2.1]
        exact cylinderSourceRightEventFalse pair
      change (!(markedCylinderEvent roots predicate
        (recoverableMarkedSwitchedLeftFamily
          (cylinderSourceLeftCompatible pair)
          (cylinderSourceRightCompatible hsmall pair) roots))) = true
      rw [hevent]
      rfl
  · unfold embeddedCylinderEventFamilyList
    apply List.mem_filter.mpr
    constructor
    · exact hswitch.2.1
    · change markedCylinderEvent roots predicate
          (recoverableMarkedSwitchedRightFamily
            (cylinderSourceLeftCompatible pair)
            (cylinderSourceRightCompatible hsmall pair) roots) = true
      unfold markedCylinderEvent
      rw [hswitch.2.2.2.1]
      exact cylinderSourceLeftEvent pair

theorem separatedCylinderSwitchEncode_injective
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (first second : CylinderSourcePair small n roots predicate)
    (_hfirst : first ∈ separatedCylinderSourcePairs hsmall)
    (_hsecond : second ∈ separatedCylinderSourcePairs hsmall)
    (heq : separatedCylinderSwitchEncode hsmall first =
      separatedCylinderSwitchEncode hsmall second) : first = second := by
  have hleftOutput :
      recoverableMarkedSwitchedLeftFamily
          (cylinderSourceLeftCompatible first)
          (cylinderSourceRightCompatible hsmall first) roots =
        recoverableMarkedSwitchedLeftFamily
          (cylinderSourceLeftCompatible second)
          (cylinderSourceRightCompatible hsmall second) roots :=
    congrArg Prod.fst heq
  have hrightOutput :
      recoverableMarkedSwitchedRightFamily
          (cylinderSourceLeftCompatible first)
          (cylinderSourceRightCompatible hsmall first) roots =
        recoverableMarkedSwitchedRightFamily
          (cylinderSourceLeftCompatible second)
          (cylinderSourceRightCompatible hsmall second) roots :=
    congrArg Prod.snd heq
  have hsources := recoverableMarkedSwitchedFamilies_injective roots
    (cylinderSourceLeftCompatible first)
    (cylinderSourceRightCompatible hsmall first)
    (cylinderSourceLeftCompatible second)
    (cylinderSourceRightCompatible hsmall second)
    hleftOutput hrightOutput
  apply Prod.ext
  · exact Subtype.ext hsources.1
  · exact Subtype.ext hsources.2

def cylinderSourcePairWeight
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n pair.1.val *
    canonicalSurfaceFamilyActivity anchorCoupling n pair.2.val

def cylinderRawPairWeight (n : Nat) (pair : RawFamilyPair) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n pair.1 *
    canonicalSurfaceFamilyActivity anchorCoupling n pair.2

theorem separatedCylinderSwitchEncode_weight
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool} (hsmall : small ≤ n)
    (pair : CylinderSourcePair small n roots predicate) :
    cylinderRawPairWeight n (separatedCylinderSwitchEncode hsmall pair) ≈
      cylinderSourcePairWeight pair := by
  exact recoverableMarkedSwitchedFamilies_weight_preserved anchorCoupling
    (cylinderSourceLeftCompatible pair)
    (cylinderSourceRightCompatible hsmall pair) roots

theorem boundaryCylinderEventFamilyList_nodup
    (small n : Nat) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    (boundaryCylinderEventFamilyList small n roots predicate).Nodup := by
  unfold boundaryCylinderEventFamilyList boundaryTargetFamilies
  exact List.filter_sublist.nodup
    (List.filter_sublist.nodup
      (canonicalCompatibleAmbientFamilies_nodup n))

theorem embeddedCylinderComplementFamilyList_nodup
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    (embeddedCylinderComplementFamilyList small n roots predicate).Nodup := by
  unfold embeddedCylinderComplementFamilyList
  exact List.filter_sublist.nodup
    (embeddedCompatibleFamilies_nodup hsmall)

theorem boundaryCylinderComplementFamilyList_nodup
    (small n : Nat) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    (boundaryCylinderComplementFamilyList small n roots predicate).Nodup := by
  unfold boundaryCylinderComplementFamilyList boundaryTargetFamilies
  exact List.filter_sublist.nodup
    (List.filter_sublist.nodup
      (canonicalCompatibleAmbientFamilies_nodup n))

theorem embeddedCylinderEventFamilyList_nodup
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    (embeddedCylinderEventFamilyList small n roots predicate).Nodup := by
  unfold embeddedCylinderEventFamilyList
  exact List.filter_sublist.nodup
    (embeddedCompatibleFamilies_nodup hsmall)

theorem cylinderSourcePairList_nodup
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    (cylinderSourcePairList small n roots predicate).Nodup := by
  exact cartesian_nodup _ _
    (attach_nodup_of_nodup _
      (boundaryCylinderEventFamilyList_nodup
        small n roots predicate))
    (attach_nodup_of_nodup _
      (embeddedCylinderComplementFamilyList_nodup
        hsmall roots predicate))

theorem separatedCylinderSourcePairs_nodup
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    (separatedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall).Nodup :=
  List.filter_sublist.nodup
    (cylinderSourcePairList_nodup hsmall roots predicate)

theorem cylinderTargetPairList_nodup
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    (cylinderTargetPairList small n roots predicate).Nodup :=
  cartesian_nodup _ _
    (boundaryCylinderComplementFamilyList_nodup
      small n roots predicate)
    (embeddedCylinderEventFamilyList_nodup hsmall roots predicate)

theorem separatedCylinderPairSum_le_targetPairSum
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum cylinderSourcePairWeight
        (separatedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) ≤
      listQSum (cylinderRawPairWeight n)
        (cylinderTargetPairList small n roots predicate) := by
  apply listQSum_le_of_injective
    (separatedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall)
    (cylinderTargetPairList small n roots predicate)
    cylinderSourcePairWeight (cylinderRawPairWeight n)
    (separatedCylinderSwitchEncode hsmall)
    (separatedCylinderSourcePairs_nodup hsmall roots predicate)
  · exact separatedCylinderSwitchEncode_mem_target hsmall
  · intro first hfirst second hsecond heq
    exact separatedCylinderSwitchEncode_injective hsmall first second
      hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm (separatedCylinderSwitchEncode_weight hsmall pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (canonicalSurfaceFamilyActivity_nonnegative n pair.1)
      (canonicalSurfaceFamilyActivity_nonnegative n pair.2)

theorem cylinderSourcePairList_sum_eqv_cellProduct
    {small n : Nat} (_hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum cylinderSourcePairWeight
        (cylinderSourcePairList small n roots predicate) ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryCylinderEventFamilyList small n roots predicate) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedCylinderComplementFamilyList small n roots predicate) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : BoundaryCylinderEventEntry small n roots predicate =>
      canonicalSurfaceFamilyActivity anchorCoupling n entry.val)
    (fun entry : EmbeddedCylinderComplementEntry small n roots predicate =>
      canonicalSurfaceFamilyActivity anchorCoupling n entry.val)
    (boundaryCylinderEventEntries small n roots predicate)
    (embeddedCylinderComplementEntries small n roots predicate)
  unfold cylinderSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold boundaryCylinderEventEntries embeddedCylinderComplementEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem cylinderTargetPairList_sum_eqv_cellProduct
    (small n : Nat) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    listQSum (cylinderRawPairWeight n)
        (cylinderTargetPairList small n roots predicate) ≈
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryCylinderComplementFamilyList small n roots predicate) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedCylinderEventFamilyList small n roots predicate) := by
  exact listQSum_cartesian_product
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    (boundaryCylinderComplementFamilyList small n roots predicate)
    (embeddedCylinderEventFamilyList small n roots predicate)

theorem cylinderSourcePairList_partition
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum cylinderSourcePairWeight
        (cylinderSourcePairList small n roots predicate) ≈
      listQSum cylinderSourcePairWeight
          (separatedCylinderSourcePairs
            (roots := roots) (predicate := predicate) hsmall) +
        listQSum cylinderSourcePairWeight
          (connectedCylinderSourcePairs
            (roots := roots) (predicate := predicate) hsmall) := by
  exact listQSum_filter_partition cylinderSourcePairWeight
    (cylinderSourceSeparatedB hsmall)
    (cylinderSourcePairList small n roots predicate)

theorem boundaryCylinderEvent_embeddedComplement_le_opposite_add_connected
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (boundaryCylinderEventFamilyList small n roots predicate) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
          (embeddedCylinderComplementFamilyList small n roots predicate) ≤
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
            (boundaryCylinderComplementFamilyList small n roots predicate) *
          listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
            (embeddedCylinderEventFamilyList small n roots predicate) +
        listQSum cylinderSourcePairWeight
          (connectedCylinderSourcePairs
            (roots := roots) (predicate := predicate) hsmall) := by
  have hsource := cylinderSourcePairList_sum_eqv_cellProduct
    hsmall roots predicate
  have htarget := cylinderTargetPairList_sum_eqv_cellProduct
    small n roots predicate
  have hpartition := cylinderSourcePairList_partition
    hsmall roots predicate
  have hinjection := separatedCylinderPairSum_le_targetPairSum
    hsmall roots predicate
  have hsepAdd :
      listQSum cylinderSourcePairWeight
            (separatedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) +
          listQSum cylinderSourcePairWeight
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) ≤
        listQSum (cylinderRawPairWeight n)
              (cylinderTargetPairList small n roots predicate) +
          listQSum cylinderSourcePairWeight
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) :=
    Q'.add_le_add hinjection (Q'.le_refl' _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem boundaryCylinderEventFamilySum_eqv_numerator
    (small n : Nat) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (boundaryCylinderEventFamilyList small n roots predicate) ≈
      boundaryTargetEventNumerator small n
        (markedCylinderEvent roots predicate) := by
  unfold boundaryCylinderEventFamilyList
  exact Q'.eqv_symm
    (boundaryTargetEventNumerator_eqv_filter small n
      (markedCylinderEvent roots predicate))

theorem boundaryCylinderComplementFamilySum_eqv_numerator
    (small n : Nat) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (boundaryCylinderComplementFamilyList small n roots predicate) ≈
      boundaryTargetEventComplementNumerator small n
        (markedCylinderEvent roots predicate) := by
  unfold boundaryCylinderComplementFamilyList
    boundaryTargetEventComplementNumerator
  exact Q'.eqv_refl _

theorem embeddedCylinderEventFamilySum_eqv_numerator
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (embeddedCylinderEventFamilyList small n roots predicate) ≈
      embeddedTargetEventNumerator small n
        (markedCylinderEvent roots predicate) := by
  have hperm := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    ((embeddedCompatibleFamilies_perm_target hsmall).filter
      (markedCylinderEvent roots predicate))
  unfold embeddedCylinderEventFamilyList at hperm ⊢
  exact Q'.eqv_trans _ _ _ hperm
    (Q'.eqv_symm
      (embeddedTargetEventNumerator_eqv_filter small n
        (markedCylinderEvent roots predicate)))

theorem embeddedCylinderComplementFamilySum_eqv_numerator
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling n)
        (embeddedCylinderComplementFamilyList small n roots predicate) ≈
      embeddedTargetEventComplementNumerator small n
        (markedCylinderEvent roots predicate) := by
  have hperm := listQSum_perm
    (canonicalSurfaceFamilyActivity anchorCoupling n)
    ((embeddedCompatibleFamilies_perm_target hsmall).filter
      (fun family => !(markedCylinderEvent roots predicate family)))
  unfold embeddedCylinderComplementFamilyList
  exact hperm

theorem boundaryCylinderEventComplementCrossDifference_le_connected
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    boundaryTargetEventNumerator small n
          (markedCylinderEvent roots predicate) *
        embeddedTargetEventComplementNumerator small n
          (markedCylinderEvent roots predicate) -
      embeddedTargetEventNumerator small n
          (markedCylinderEvent roots predicate) *
        boundaryTargetEventComplementNumerator small n
          (markedCylinderEvent roots predicate) ≤
      listQSum cylinderSourcePairWeight
        (connectedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) := by
  have hraw :=
    boundaryCylinderEvent_embeddedComplement_le_opposite_add_connected
      hsmall roots predicate
  have hboundaryEvent :=
    boundaryCylinderEventFamilySum_eqv_numerator small n roots predicate
  have hembeddedComplement :=
    embeddedCylinderComplementFamilySum_eqv_numerator
      hsmall roots predicate
  have hboundaryComplement :=
    boundaryCylinderComplementFamilySum_eqv_numerator
      small n roots predicate
  have hembeddedEvent :=
    embeddedCylinderEventFamilySum_eqv_numerator
      hsmall roots predicate
  have hcells :
      boundaryTargetEventNumerator small n
            (markedCylinderEvent roots predicate) *
          embeddedTargetEventComplementNumerator small n
            (markedCylinderEvent roots predicate) ≤
        boundaryTargetEventComplementNumerator small n
              (markedCylinderEvent roots predicate) *
            embeddedTargetEventNumerator small n
              (markedCylinderEvent roots predicate) +
          listQSum cylinderSourcePairWeight
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (mul_eqv_both (Q'.eqv_symm hboundaryEvent)
          (Q'.eqv_symm hembeddedComplement)))
      (Q'.le_trans' _ _ _ hraw
        (Q'.le_of_eqv
          (Q'.add_eqv_congr'
            (mul_eqv_both hboundaryComplement hembeddedEvent)
            (Q'.eqv_refl _))))
  have hreordered :
      boundaryTargetEventNumerator small n
            (markedCylinderEvent roots predicate) *
          embeddedTargetEventComplementNumerator small n
            (markedCylinderEvent roots predicate) ≤
        embeddedTargetEventNumerator small n
              (markedCylinderEvent roots predicate) *
            boundaryTargetEventComplementNumerator small n
              (markedCylinderEvent roots predicate) +
          listQSum cylinderSourcePairWeight
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) :=
    Q'.le_trans' _ _ _ hcells
      (Q'.le_of_eqv
        (Q'.add_eqv_congr'
          (Q'.mul_comm_eqv
            (boundaryTargetEventComplementNumerator small n
              (markedCylinderEvent roots predicate))
            (embeddedTargetEventNumerator small n
              (markedCylinderEvent roots predicate)))
          (Q'.eqv_refl _)))
  exact Q'.sub_le_of_le_add hreordered

/-- The exact finite-cylinder cross numerator is reduced to the explicit
marked connected residue. -/
theorem anchorCylinderCrossDifference_le_connected
    {small n : Nat} (hsmall : small ≤ n)
    {rawRoots : List (List Nat)}
    (hroots : ∀ root, root ∈ rawRoots →
      root ∈ canonicalSurfacePolymers small)
    (predicate : List Bool → Bool) :
    let roots := canonicalAtomsOfRoots
      (transportedCylinderRoots small n rawRoots)
      (fun root hroot => by
        obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hroot
        subst root
        exact transportPolymer_mem_canonicalSurfacePolymers
          hsmall (hroots source hsource))
    anchorEventNumerator n
          (targetCylinderEvent small n rawRoots predicate) *
        anchorCanonicalPartition small -
      anchorEventNumerator small
          (sourceCylinderEvent rawRoots predicate) *
        anchorCanonicalPartition n ≤
      listQSum cylinderSourcePairWeight
        (connectedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) := by
  intro roots
  have hcross := anchorCylinderCrossDifference_eqv_eventComplementCells
    hsmall hroots predicate
  have hvalues : roots.map Subtype.val =
      transportedCylinderRoots small n rawRoots :=
    canonicalAtomsOfRoots_values _ _
  have hevent : markedCylinderEvent roots predicate =
      targetCylinderEvent small n rawRoots predicate := by
    funext family
    unfold markedCylinderEvent targetCylinderEvent
    rw [hvalues]
  rw [← hevent] at hcross
  rw [← hevent]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcross)
    (boundaryCylinderEventComplementCrossDifference_le_connected
      hsmall roots predicate)

end YMGap.Continuum.Z4CanonicalCylinderSwitchSummation

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalCylinderSwitchSummation.cylinderSourceSeparatedB_all_outside_false
#print axioms YMGap.Continuum.Z4CanonicalCylinderSwitchSummation.separatedCylinderSwitchEncode_mem_target
#print axioms YMGap.Continuum.Z4CanonicalCylinderSwitchSummation.separatedCylinderSwitchEncode_injective
#print axioms YMGap.Continuum.Z4CanonicalCylinderSwitchSummation.separatedCylinderPairSum_le_targetPairSum
#print axioms YMGap.Continuum.Z4CanonicalCylinderSwitchSummation.boundaryCylinderEvent_embeddedComplement_le_opposite_add_connected
#print axioms YMGap.Continuum.Z4CanonicalCylinderSwitchSummation.boundaryCylinderEventComplementCrossDifference_le_connected
#print axioms YMGap.Continuum.Z4CanonicalCylinderSwitchSummation.anchorCylinderCrossDifference_le_connected
