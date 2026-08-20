/-
# Finite four-cell summation for the two-block switch

For two Boolean cylinder events `A` and `B`, pair one replica in the `A ∩ B`
cell with one replica in the `Aᶜ ∩ Bᶜ` cell.  On the branch where no
first-block disagreement component meets the second block, the recoverable
component switch injects this pair into the opposite cells
`Aᶜ ∩ B` and `A ∩ Bᶜ`, preserving the exact product activity.
Only pairs with a disagreement connection between the two blocks remain.

This proves the finite connected-covariance cancellation inequality for the
literal canonical polymer gas.  It does not yet bound the connected residue.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockConnectedCarrier
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockComponentSwitch
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

abbrev TwoBlockPolymerFamily := List (List Nat)
abbrev TwoBlockRawFamilyPair := TwoBlockPolymerFamily × TwoBlockPolymerFamily

def blockCylinderEvent
    {n : Nat} (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) : TwoBlockPolymerFamily → Bool :=
  fun family =>
    predicate (familyOccurrenceFingerprint (roots.map Subtype.val) family)

def twoBlockTTFamilyList
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    List TwoBlockPolymerFamily :=
  (canonicalCompatibleAmbientFamilies n).filter (fun family =>
    blockCylinderEvent firstRoots firstPredicate family &&
      blockCylinderEvent secondRoots secondPredicate family)

def twoBlockFFFamilyList
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    List TwoBlockPolymerFamily :=
  (canonicalCompatibleAmbientFamilies n).filter (fun family =>
    (!(blockCylinderEvent firstRoots firstPredicate family)) &&
      (!(blockCylinderEvent secondRoots secondPredicate family)))

def twoBlockFTFamilyList
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    List TwoBlockPolymerFamily :=
  (canonicalCompatibleAmbientFamilies n).filter (fun family =>
    (!(blockCylinderEvent firstRoots firstPredicate family)) &&
      blockCylinderEvent secondRoots secondPredicate family)

def twoBlockTFFamilyList
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    List TwoBlockPolymerFamily :=
  (canonicalCompatibleAmbientFamilies n).filter (fun family =>
    blockCylinderEvent firstRoots firstPredicate family &&
      (!(blockCylinderEvent secondRoots secondPredicate family)))

abbrev TwoBlockTTEntry
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :=
  {family : TwoBlockPolymerFamily // family ∈
    twoBlockTTFamilyList firstRoots secondRoots
      firstPredicate secondPredicate}

abbrev TwoBlockFFEntry
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :=
  {family : TwoBlockPolymerFamily // family ∈
    twoBlockFFFamilyList firstRoots secondRoots
      firstPredicate secondPredicate}

abbrev TwoBlockSourcePair
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :=
  TwoBlockTTEntry firstRoots secondRoots firstPredicate secondPredicate ×
    TwoBlockFFEntry firstRoots secondRoots firstPredicate secondPredicate

def twoBlockTTEntries
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    List (TwoBlockTTEntry firstRoots secondRoots
      firstPredicate secondPredicate) :=
  (twoBlockTTFamilyList firstRoots secondRoots
    firstPredicate secondPredicate).attach

def twoBlockFFEntries
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    List (TwoBlockFFEntry firstRoots secondRoots
      firstPredicate secondPredicate) :=
  (twoBlockFFFamilyList firstRoots secondRoots
    firstPredicate secondPredicate).attach

def twoBlockSourcePairList
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    List (TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :=
  cartesian
    (twoBlockTTEntries firstRoots secondRoots
      firstPredicate secondPredicate)
    (twoBlockFFEntries firstRoots secondRoots
      firstPredicate secondPredicate)

def twoBlockTargetPairList
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    List TwoBlockRawFamilyPair :=
  cartesian
    (twoBlockFTFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)
    (twoBlockTFFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

def twoBlockSourceLeftCompatible
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :
    pair.1.val ∈ canonicalCompatibleAmbientFamilies n :=
  (List.mem_filter.mp pair.1.property).1

def twoBlockSourceRightCompatible
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :
    pair.2.val ∈ canonicalCompatibleAmbientFamilies n :=
  (List.mem_filter.mp pair.2.property).1

theorem twoBlockSourceLeft_events_true
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :
    blockCylinderEvent firstRoots firstPredicate pair.1.val = true ∧
      blockCylinderEvent secondRoots secondPredicate pair.1.val = true :=
  Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp pair.1.property).2

theorem twoBlockSourceRight_events_false
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :
    blockCylinderEvent firstRoots firstPredicate pair.2.val = false ∧
      blockCylinderEvent secondRoots secondPredicate pair.2.val = false := by
  have hboth := Bool.and_eq_true _ _ |>.mp
    (List.mem_filter.mp pair.2.property).2
  constructor
  · cases hvalue : blockCylinderEvent firstRoots firstPredicate pair.2.val <;>
      simp_all
  · cases hvalue : blockCylinderEvent secondRoots secondPredicate pair.2.val <;>
      simp_all

def twoBlockSourceSeparatedB
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) : Bool :=
  !(twoBlockMarkedReachB
    (twoBlockSourceLeftCompatible pair)
    (twoBlockSourceRightCompatible pair) firstRoots secondRoots)

def separatedTwoBlockSourcePairs
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool} :
    List (TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :=
  (twoBlockSourcePairList firstRoots secondRoots
    firstPredicate secondPredicate).filter twoBlockSourceSeparatedB

def connectedTwoBlockSourcePairs
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool} :
    List (TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :=
  (twoBlockSourcePairList firstRoots secondRoots
    firstPredicate secondPredicate).filter
      (fun pair => !(twoBlockSourceSeparatedB pair))

theorem twoBlockSourceSeparatedB_reach_false
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate)
    (hseparated : twoBlockSourceSeparatedB pair = true) :
    twoBlockMarkedReachB
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair)
      firstRoots secondRoots = false := by
  unfold twoBlockSourceSeparatedB at hseparated
  cases hreach : twoBlockMarkedReachB
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair)
      firstRoots secondRoots <;> simp_all

def separatedTwoBlockSwitchEncode
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) : TwoBlockRawFamilyPair :=
  (recoverableMarkedSwitchedLeftFamily
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair) firstRoots,
    recoverableMarkedSwitchedRightFamily
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair) firstRoots)

theorem separatedTwoBlockSwitchEncode_mem_target
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate)
    (hpair : pair ∈ separatedTwoBlockSourcePairs) :
    separatedTwoBlockSwitchEncode pair ∈
      twoBlockTargetPairList firstRoots secondRoots
        firstPredicate secondPredicate := by
  have hreach := twoBlockSourceSeparatedB_reach_false pair
    (List.mem_filter.mp hpair).2
  have hfingerprints := separatedTwoBlockSwitch_fingerprints
    (twoBlockSourceLeftCompatible pair)
    (twoBlockSourceRightCompatible pair)
    firstRoots secondRoots hreach
  have hcompatible := recoverableMarkedSwitchedFamilies_mem_compatible
    (twoBlockSourceLeftCompatible pair)
    (twoBlockSourceRightCompatible pair) firstRoots
  apply (mem_cartesian_iff _ _ _).2
  constructor
  · unfold twoBlockFTFamilyList
    apply List.mem_filter.mpr
    refine ⟨hcompatible.1, ?_⟩
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · have hfalse := (twoBlockSourceRight_events_false pair).1
      unfold blockCylinderEvent at hfalse ⊢
      simp only [separatedTwoBlockSwitchEncode]
      rw [hfingerprints.1.1]
      rw [hfalse]
      rfl
    · have htrue := (twoBlockSourceLeft_events_true pair).2
      unfold blockCylinderEvent at htrue ⊢
      simp only [separatedTwoBlockSwitchEncode]
      rw [hfingerprints.2.1]
      exact htrue
  · unfold twoBlockTFFamilyList
    apply List.mem_filter.mpr
    refine ⟨hcompatible.2, ?_⟩
    apply (Bool.and_eq_true _ _).mpr
    constructor
    · have htrue := (twoBlockSourceLeft_events_true pair).1
      unfold blockCylinderEvent at htrue ⊢
      simp only [separatedTwoBlockSwitchEncode]
      rw [hfingerprints.1.2]
      exact htrue
    · have hfalse := (twoBlockSourceRight_events_false pair).2
      unfold blockCylinderEvent at hfalse ⊢
      simp only [separatedTwoBlockSwitchEncode]
      rw [hfingerprints.2.2]
      rw [hfalse]
      rfl

theorem separatedTwoBlockSwitchEncode_injective
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (first second : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate)
    (_hfirst : first ∈ separatedTwoBlockSourcePairs)
    (_hsecond : second ∈ separatedTwoBlockSourcePairs)
    (heq : separatedTwoBlockSwitchEncode first =
      separatedTwoBlockSwitchEncode second) : first = second := by
  have hsources := recoverableMarkedSwitchedFamilies_injective firstRoots
    (twoBlockSourceLeftCompatible first)
    (twoBlockSourceRightCompatible first)
    (twoBlockSourceLeftCompatible second)
    (twoBlockSourceRightCompatible second)
    (congrArg Prod.fst heq) (congrArg Prod.snd heq)
  apply Prod.ext
  · exact Subtype.ext hsources.1
  · exact Subtype.ext hsources.2

def twoBlockSourcePairWeight
    (coupling : Q')
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) : Q' :=
  canonicalSurfaceFamilyActivity coupling n pair.1.val *
    canonicalSurfaceFamilyActivity coupling n pair.2.val

def twoBlockRawPairWeight
    (coupling : Q') (n : Nat) (pair : TwoBlockRawFamilyPair) : Q' :=
  canonicalSurfaceFamilyActivity coupling n pair.1 *
    canonicalSurfaceFamilyActivity coupling n pair.2

theorem separatedTwoBlockSwitchEncode_weight
    (coupling : Q')
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockRawPairWeight coupling n
        (separatedTwoBlockSwitchEncode pair) ≈
      twoBlockSourcePairWeight coupling pair :=
  recoverableMarkedSwitchedFamilies_weight_preserved coupling
    (twoBlockSourceLeftCompatible pair)
    (twoBlockSourceRightCompatible pair) firstRoots

private theorem canonicalSurfaceFamilyActivity_nonnegative_local
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling) (n : Nat) :
  ∀ family : List (List Nat),
      (0 : Q') ≤ canonicalSurfaceFamilyActivity coupling n family
  | [] => by
      change (0 : Q') ≤ 1
      decide
  | polymer :: rest => by
      change (0 : Q') ≤
        canonicalSurfaceActivity coupling n polymer *
          canonicalSurfaceFamilyActivity coupling n rest
      exact Q'.mul_nonneg _ _
        (canonicalSurfaceActivity_nonnegative hcoupling n polymer)
        (canonicalSurfaceFamilyActivity_nonnegative_local
          hcoupling n rest)

private theorem twoBlockCell_nodup
    {n : Nat} (test : TwoBlockPolymerFamily → Bool) :
    ((canonicalCompatibleAmbientFamilies n).filter test).Nodup :=
  List.filter_sublist.nodup
    (canonicalCompatibleAmbientFamilies_nodup n)

theorem twoBlockSourcePairList_nodup
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    (twoBlockSourcePairList firstRoots secondRoots
      firstPredicate secondPredicate).Nodup := by
  exact cartesian_nodup _ _
    (attach_nodup_of_nodup _ (twoBlockCell_nodup _))
    (attach_nodup_of_nodup _ (twoBlockCell_nodup _))

theorem separatedTwoBlockSourcePairs_nodup
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    (separatedTwoBlockSourcePairs
      (firstRoots := firstRoots) (secondRoots := secondRoots)
      (firstPredicate := firstPredicate)
      (secondPredicate := secondPredicate)).Nodup :=
  List.filter_sublist.nodup
    (twoBlockSourcePairList_nodup
      firstRoots secondRoots firstPredicate secondPredicate)

theorem twoBlockTargetPairList_nodup
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    (twoBlockTargetPairList firstRoots secondRoots
      firstPredicate secondPredicate).Nodup :=
  cartesian_nodup _ _ (twoBlockCell_nodup _) (twoBlockCell_nodup _)

theorem separatedTwoBlockPairSum_le_targetPairSum
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum (twoBlockSourcePairWeight coupling)
        (separatedTwoBlockSourcePairs
          (firstRoots := firstRoots) (secondRoots := secondRoots)
          (firstPredicate := firstPredicate)
          (secondPredicate := secondPredicate)) ≤
      listQSum (twoBlockRawPairWeight coupling n)
        (twoBlockTargetPairList firstRoots secondRoots
          firstPredicate secondPredicate) := by
  apply listQSum_le_of_injective
    (separatedTwoBlockSourcePairs
      (firstRoots := firstRoots) (secondRoots := secondRoots)
      (firstPredicate := firstPredicate)
      (secondPredicate := secondPredicate))
    (twoBlockTargetPairList firstRoots secondRoots
      firstPredicate secondPredicate)
    (twoBlockSourcePairWeight coupling)
    (twoBlockRawPairWeight coupling n)
    separatedTwoBlockSwitchEncode
    (separatedTwoBlockSourcePairs_nodup
      firstRoots secondRoots firstPredicate secondPredicate)
  · exact separatedTwoBlockSwitchEncode_mem_target
  · intro first hfirst second hsecond heq
    exact separatedTwoBlockSwitchEncode_injective
      first second hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm (separatedTwoBlockSwitchEncode_weight coupling pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (canonicalSurfaceFamilyActivity_nonnegative_local
        hcoupling n pair.1)
      (canonicalSurfaceFamilyActivity_nonnegative_local
        hcoupling n pair.2)

theorem twoBlockSourcePairList_sum_eqv_cellProduct
    (coupling : Q') {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum (twoBlockSourcePairWeight coupling)
        (twoBlockSourcePairList firstRoots secondRoots
          firstPredicate secondPredicate) ≈
      listQSum (canonicalSurfaceFamilyActivity coupling n)
          (twoBlockTTFamilyList firstRoots secondRoots
            firstPredicate secondPredicate) *
        listQSum (canonicalSurfaceFamilyActivity coupling n)
          (twoBlockFFFamilyList firstRoots secondRoots
            firstPredicate secondPredicate) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : TwoBlockTTEntry firstRoots secondRoots
        firstPredicate secondPredicate =>
      canonicalSurfaceFamilyActivity coupling n entry.val)
    (fun entry : TwoBlockFFEntry firstRoots secondRoots
        firstPredicate secondPredicate =>
      canonicalSurfaceFamilyActivity coupling n entry.val)
    (twoBlockTTEntries firstRoots secondRoots
      firstPredicate secondPredicate)
    (twoBlockFFEntries firstRoots secondRoots
      firstPredicate secondPredicate)
  unfold twoBlockSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold twoBlockTTEntries twoBlockFFEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem twoBlockTargetPairList_sum_eqv_cellProduct
    (coupling : Q') {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum (twoBlockRawPairWeight coupling n)
        (twoBlockTargetPairList firstRoots secondRoots
          firstPredicate secondPredicate) ≈
      listQSum (canonicalSurfaceFamilyActivity coupling n)
          (twoBlockFTFamilyList firstRoots secondRoots
            firstPredicate secondPredicate) *
        listQSum (canonicalSurfaceFamilyActivity coupling n)
          (twoBlockTFFamilyList firstRoots secondRoots
            firstPredicate secondPredicate) :=
  listQSum_cartesian_product
    (canonicalSurfaceFamilyActivity coupling n)
    (canonicalSurfaceFamilyActivity coupling n)
    (twoBlockFTFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)
    (twoBlockTFFamilyList firstRoots secondRoots
      firstPredicate secondPredicate)

theorem twoBlockSourcePairList_partition
    (coupling : Q') {n : Nat}
    (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum (twoBlockSourcePairWeight coupling)
        (twoBlockSourcePairList firstRoots secondRoots
          firstPredicate secondPredicate) ≈
      listQSum (twoBlockSourcePairWeight coupling)
          (separatedTwoBlockSourcePairs
            (firstRoots := firstRoots) (secondRoots := secondRoots)
            (firstPredicate := firstPredicate)
            (secondPredicate := secondPredicate)) +
        listQSum (twoBlockSourcePairWeight coupling)
          (connectedTwoBlockSourcePairs
            (firstRoots := firstRoots) (secondRoots := secondRoots)
            (firstPredicate := firstPredicate)
            (secondPredicate := secondPredicate)) :=
  listQSum_filter_partition (twoBlockSourcePairWeight coupling)
    twoBlockSourceSeparatedB
    (twoBlockSourcePairList firstRoots secondRoots
      firstPredicate secondPredicate)

/-- Exact four-cell cancellation: the positive covariance cell determinant is
bounded by the literal connected two-replica residue. -/
theorem twoBlockFourCellCrossDifference_le_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum (canonicalSurfaceFamilyActivity coupling n)
          (twoBlockTTFamilyList firstRoots secondRoots
            firstPredicate secondPredicate) *
        listQSum (canonicalSurfaceFamilyActivity coupling n)
          (twoBlockFFFamilyList firstRoots secondRoots
            firstPredicate secondPredicate) -
      listQSum (canonicalSurfaceFamilyActivity coupling n)
          (twoBlockFTFamilyList firstRoots secondRoots
            firstPredicate secondPredicate) *
        listQSum (canonicalSurfaceFamilyActivity coupling n)
          (twoBlockTFFamilyList firstRoots secondRoots
            firstPredicate secondPredicate) ≤
      listQSum (twoBlockSourcePairWeight coupling)
        (connectedTwoBlockSourcePairs
          (firstRoots := firstRoots) (secondRoots := secondRoots)
          (firstPredicate := firstPredicate)
          (secondPredicate := secondPredicate)) := by
  have hsource := twoBlockSourcePairList_sum_eqv_cellProduct
    coupling firstRoots secondRoots firstPredicate secondPredicate
  have htarget := twoBlockTargetPairList_sum_eqv_cellProduct
    coupling firstRoots secondRoots firstPredicate secondPredicate
  have hpartition := twoBlockSourcePairList_partition
    coupling firstRoots secondRoots firstPredicate secondPredicate
  have hinjection := separatedTwoBlockPairSum_le_targetPairSum
    hcoupling firstRoots secondRoots firstPredicate secondPredicate
  have hsourceLe :
      listQSum (twoBlockSourcePairWeight coupling)
          (twoBlockSourcePairList firstRoots secondRoots
            firstPredicate secondPredicate) ≤
        listQSum (twoBlockRawPairWeight coupling n)
            (twoBlockTargetPairList firstRoots secondRoots
              firstPredicate secondPredicate) +
          listQSum (twoBlockSourcePairWeight coupling)
            (connectedTwoBlockSourcePairs
              (firstRoots := firstRoots) (secondRoots := secondRoots)
              (firstPredicate := firstPredicate)
              (secondPredicate := secondPredicate)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpartition)
      (Q'.add_le_add hinjection (Q'.le_refl' _))
  have hcells :
      listQSum (canonicalSurfaceFamilyActivity coupling n)
            (twoBlockTTFamilyList firstRoots secondRoots
              firstPredicate secondPredicate) *
          listQSum (canonicalSurfaceFamilyActivity coupling n)
            (twoBlockFFFamilyList firstRoots secondRoots
              firstPredicate secondPredicate) ≤
        listQSum (canonicalSurfaceFamilyActivity coupling n)
              (twoBlockFTFamilyList firstRoots secondRoots
                firstPredicate secondPredicate) *
            listQSum (canonicalSurfaceFamilyActivity coupling n)
              (twoBlockTFFamilyList firstRoots secondRoots
                firstPredicate secondPredicate) +
          listQSum (twoBlockSourcePairWeight coupling)
            (connectedTwoBlockSourcePairs
              (firstRoots := firstRoots) (secondRoots := secondRoots)
              (firstPredicate := firstPredicate)
              (secondPredicate := secondPredicate)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hsource))
      (Q'.le_trans' _ _ _ hsourceLe
        (Q'.le_of_eqv
          (Q'.add_eqv_congr' htarget (Q'.eqv_refl _))))
  exact Q'.sub_le_of_le_add hcells

#print axioms separatedTwoBlockSwitchEncode_mem_target
#print axioms separatedTwoBlockPairSum_le_targetPairSum
#print axioms twoBlockFourCellCrossDifference_le_connected

end YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
