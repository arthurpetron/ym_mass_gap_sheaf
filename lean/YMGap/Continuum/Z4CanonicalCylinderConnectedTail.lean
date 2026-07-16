/-
# Uniform tail for the finite-cylinder connected residue

Every connected marked-cylinder source pair selects an exclusive marked root.
According to its orientation, the unchanged raw pair belongs either to the
forward singleton connected list or to the mirrored singleton connected list
with the two replicas restored to boundary/embedded order.  A single
constructive injection into the union over all marked roots therefore reduces
the entire cylinder residue to the two already-certified carrier tails.
-/

import YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
import YMGap.Continuum.Z4CanonicalConnectedCarrierTail
import YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail

namespace YMGap.Continuum.Z4CanonicalCylinderConnectedTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedCarrierTail
open YMGap.Continuum.Z4CanonicalCylinderConnectedClassification
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

abbrev CylinderRawFamilyPair :=
  Z4CanonicalCylinderSwitchSummation.RawFamilyPair

/-! ## 1. A non-dependent raw target over all marked roots -/

def cylinderConnectedRawEncode
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (pair : CylinderSourcePair small n roots predicate) :
    CylinderRawFamilyPair :=
  (pair.1.val, pair.2.val)

def forwardConnectedRawPairs
    {small n : Nat} (hsmall : small ≤ n) (root : CanonicalAtom n) :
    List CylinderRawFamilyPair :=
  (connectedSourcePairs (root := root.val) hsmall).map
    (fun pair => (pair.1.val, pair.2.val))

def reverseConnectedRawPairs
    {small n : Nat} (hsmall : small ≤ n) (root : CanonicalAtom n) :
    List CylinderRawFamilyPair :=
  (connectedReverseSourcePairs (root := root.val) hsmall).map
    (fun pair => (pair.2.val, pair.1.val))

def rootedCylinderConnectedRawPairs
    {small n : Nat} (hsmall : small ≤ n) (root : CanonicalAtom n) :
    List CylinderRawFamilyPair :=
  forwardConnectedRawPairs hsmall root ++
    reverseConnectedRawPairs hsmall root

def allCylinderConnectedRawPairs
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) : List CylinderRawFamilyPair :=
  roots.flatMap (rootedCylinderConnectedRawPairs hsmall)

theorem connectedCylinderSourcePairs_nodup
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    (connectedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall).Nodup :=
  List.filter_sublist.nodup
    (cylinderSourcePairList_nodup hsmall roots predicate)

theorem cylinderConnectedRawEncode_injective
    {small n : Nat} {roots : List (CanonicalAtom n)}
    {predicate : List Bool → Bool}
    (first second : CylinderSourcePair small n roots predicate)
    (heq : cylinderConnectedRawEncode first =
      cylinderConnectedRawEncode second) : first = second := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst heq
  · apply Subtype.ext
    exact congrArg Prod.snd heq

theorem cylinderConnectedRawEncode_mem_all
    {small n : Nat} (hsmall : small ≤ n)
    {roots : List (CanonicalAtom n)} {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (pair : CylinderSourcePair small n roots predicate)
    (hpair : pair ∈ connectedCylinderSourcePairs hsmall) :
    cylinderConnectedRawEncode pair ∈
      allCylinderConnectedRawPairs hsmall roots := by
  have htest := (List.mem_filter.mp hpair).2
  have hreach : boundaryOutsideMarkedReachB small
      (cylinderSourceLeftCompatible pair)
      (cylinderSourceRightCompatible hsmall pair) roots = true := by
    unfold cylinderSourceSeparatedB at htest
    cases hvalue : boundaryOutsideMarkedReachB small
        (cylinderSourceLeftCompatible pair)
        (cylinderSourceRightCompatible hsmall pair) roots <;>
      simp_all
  obtain ⟨root, outside, hroot, houtside, houtsideBox,
      hreaches, horientation⟩ :=
    boundaryOutsideMarkedReachB_true_oriented_root
      (cylinderSourceLeftCompatible pair)
      (cylinderSourceRightCompatible hsmall pair)
      roots hrootsInside hreach
  apply List.mem_flatMap.mpr
  refine ⟨root, hroot, ?_⟩
  unfold rootedCylinderConnectedRawPairs
  rcases horientation with hleftOnly | hrightOnly
  · obtain ⟨single, hsingleLeft, hsingleRight, hsingle⟩ :=
      leftOnly_reach_mem_connectedSourcePairs hsmall
        (cylinderSourceLeftBoundary pair)
        (cylinderSourceRightEmbedded pair) root outside
        hleftOnly.1 hleftOnly.2 houtside houtsideBox hreaches
    apply List.mem_append.mpr
    apply Or.inl
    unfold forwardConnectedRawPairs
    apply List.mem_map.mpr
    refine ⟨single, hsingle, ?_⟩
    unfold cylinderConnectedRawEncode
    rw [hsingleLeft, hsingleRight]
  · obtain ⟨single, hsingleRight, hsingleLeft, hsingle⟩ :=
      rightOnly_reach_mem_connectedReverseSourcePairs hsmall
        (cylinderSourceLeftBoundary pair)
        (cylinderSourceRightEmbedded pair) root outside
        hrightOnly.1 hrightOnly.2 houtside houtsideBox hreaches
    apply List.mem_append.mpr
    apply Or.inr
    unfold reverseConnectedRawPairs
    apply List.mem_map.mpr
    refine ⟨single, hsingle, ?_⟩
    unfold cylinderConnectedRawEncode
    rw [hsingleLeft, hsingleRight]

theorem connectedCylinderPairSum_le_allRootRawPairSum
    {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true) :
    listQSum cylinderSourcePairWeight
        (connectedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) ≤
      listQSum (cylinderRawPairWeight n)
        (allCylinderConnectedRawPairs hsmall roots) := by
  apply listQSum_le_of_injective
    (connectedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall)
    (allCylinderConnectedRawPairs hsmall roots)
    cylinderSourcePairWeight (cylinderRawPairWeight n)
    cylinderConnectedRawEncode
    (connectedCylinderSourcePairs_nodup hsmall roots predicate)
  · exact cylinderConnectedRawEncode_mem_all hsmall hrootsInside
  · intro first _ second _ heq
    exact cylinderConnectedRawEncode_injective first second heq
  · intro pair _
    exact Q'.le_refl' _
  · intro pair _
    exact Q'.mul_nonneg _ _
      (canonicalSurfaceFamilyActivity_nonnegative n pair.1)
      (canonicalSurfaceFamilyActivity_nonnegative n pair.2)

/-! ## 2. Exact reduction to the two oriented singleton sums -/

private theorem listQSum_pointwise_eqv {A : Type}
    (f g : A → Q') (hfg : ∀ x, f x ≈ g x) :
    ∀ xs : List A, listQSum f xs ≈ listQSum g xs
  | [] => Q'.eqv_refl 0
  | head :: tail =>
      Q'.add_eqv_congr' (hfg head)
        (listQSum_pointwise_eqv f g hfg tail)

theorem forwardConnectedRawPairSum_eqv
    {small n : Nat} (hsmall : small ≤ n) (root : CanonicalAtom n) :
    listQSum (cylinderRawPairWeight n)
        (forwardConnectedRawPairs hsmall root) ≈
      listQSum sourcePairWeight
        (connectedSourcePairs (root := root.val) hsmall) := by
  unfold forwardConnectedRawPairs
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem reverseConnectedRawPairSum_eqv
    {small n : Nat} (hsmall : small ≤ n) (root : CanonicalAtom n) :
    listQSum (cylinderRawPairWeight n)
        (reverseConnectedRawPairs hsmall root) ≈
      listQSum reverseSourcePairWeight
        (connectedReverseSourcePairs (root := root.val) hsmall) := by
  unfold reverseConnectedRawPairs
  rw [listQSum_map]
  apply listQSum_pointwise_eqv
  intro pair
  unfold cylinderRawPairWeight reverseSourcePairWeight
  exact Q'.mul_comm_eqv _ _

theorem rootedCylinderConnectedRawPairSum_eqv
    {small n : Nat} (hsmall : small ≤ n) (root : CanonicalAtom n) :
    listQSum (cylinderRawPairWeight n)
        (rootedCylinderConnectedRawPairs hsmall root) ≈
      listQSum sourcePairWeight
          (connectedSourcePairs (root := root.val) hsmall) +
        listQSum reverseSourcePairWeight
          (connectedReverseSourcePairs (root := root.val) hsmall) := by
  unfold rootedCylinderConnectedRawPairs
  exact Q'.eqv_trans _ _ _
    (listQSum_append (cylinderRawPairWeight n)
      (forwardConnectedRawPairs hsmall root)
      (reverseConnectedRawPairs hsmall root))
    (Q'.add_eqv_congr'
      (forwardConnectedRawPairSum_eqv hsmall root)
      (reverseConnectedRawPairSum_eqv hsmall root))

/-! ## 3. Uniform summation over the finite marked family -/

def cylinderSingleRootBoundaryTail (small n distance : Nat) : Q' :=
  (anchorCanonicalPartition n * anchorCanonicalPartition small) *
    (anchorEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)

def cylinderSingleRootTwoSidedTail (small n distance : Nat) : Q' :=
  cylinderSingleRootBoundaryTail small n distance +
    cylinderSingleRootBoundaryTail small n distance

theorem cylinderSingleRootBoundaryTail_nonnegative
    (small n distance : Nat) :
    (0 : Q') ≤ cylinderSingleRootBoundaryTail small n distance := by
  unfold cylinderSingleRootBoundaryTail
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (anchorCanonicalPartition_nonnegative n)
      (anchorCanonicalPartition_nonnegative small))
    (Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorEffectiveRatio
        anchorEffectiveRatio_nonnegative (distance + 2))
      (by decide))

theorem cylinderSingleRootTwoSidedTail_nonnegative
    (small n distance : Nat) :
    (0 : Q') ≤ cylinderSingleRootTwoSidedTail small n distance := by
  unfold cylinderSingleRootTwoSidedTail
  exact Q'.zero_le_add _ _
    (cylinderSingleRootBoundaryTail_nonnegative small n distance)
    (cylinderSingleRootBoundaryTail_nonnegative small n distance)

theorem rootedCylinderConnectedRawPairSum_le_boundaryTail
    {small n inner distance start : Nat} (hsmall : small ≤ n)
    (root : CanonicalAtom n)
    (hstart : start ∈ root.val)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (cylinderRawPairWeight n)
        (rootedCylinderConnectedRawPairs hsmall root) ≤
      cylinderSingleRootTwoSidedTail small n distance := by
  have hforward := connectedSourcePairSum_le_boundaryTail
    hsmall hstart hstartInner hbox
  have hreverse := connectedReverseSourcePairSum_le_boundaryTail
    hsmall hstart hstartInner hbox
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (rootedCylinderConnectedRawPairSum_eqv hsmall root))
    (Q'.add_le_add hforward hreverse)

theorem allCylinderConnectedRawPairSum_le_boundaryTail
    {small n inner distance : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n))
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (cylinderRawPairWeight n)
        (allCylinderConnectedRawPairs hsmall roots) ≤
      Q'.ofNat roots.length *
        cylinderSingleRootTwoSidedTail small n distance := by
  have hflat := listQSum_flatMap (cylinderRawPairWeight n)
    (rootedCylinderConnectedRawPairs hsmall) roots
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv hflat)
  apply listQSum_le_length_mul
    (fun root => listQSum (cylinderRawPairWeight n)
      (rootedCylinderConnectedRawPairs hsmall root))
    (cylinderSingleRootTwoSidedTail_nonnegative small n distance)
    roots
  intro root hroot
  obtain ⟨start, hstart, hstartInner⟩ := hgeometry root hroot
  exact rootedCylinderConnectedRawPairSum_le_boundaryTail
    hsmall root hstart hstartInner hbox

theorem connectedCylinderPairSum_le_boundaryTail
    {small n inner distance : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum cylinderSourcePairWeight
        (connectedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) ≤
      Q'.ofNat roots.length *
        cylinderSingleRootTwoSidedTail small n distance := by
  exact Q'.le_trans' _ _ _
    (connectedCylinderPairSum_le_allRootRawPairSum
      hsmall roots predicate hrootsInside)
    (allCylinderConnectedRawPairSum_le_boundaryTail
      hsmall roots hgeometry hbox)

end YMGap.Continuum.Z4CanonicalCylinderConnectedTail

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalCylinderConnectedTail.cylinderConnectedRawEncode_mem_all
#print axioms YMGap.Continuum.Z4CanonicalCylinderConnectedTail.connectedCylinderPairSum_le_allRootRawPairSum
#print axioms YMGap.Continuum.Z4CanonicalCylinderConnectedTail.rootedCylinderConnectedRawPairSum_le_boundaryTail
#print axioms YMGap.Continuum.Z4CanonicalCylinderConnectedTail.connectedCylinderPairSum_le_boundaryTail
