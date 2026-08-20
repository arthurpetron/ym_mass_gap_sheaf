/-
# Recoverable colored paths for the two-block connected residue

Each connected two-block source pair has a canonical loop-erased disagreement
path.  Split its atoms according to the source replica in which they occur and
retain the two complementary backgrounds.  The resulting colored carrier
recovers the complete source pair and preserves an exact activity
factorization.

This module establishes recoverability and the termwise weight envelope.  A
following module identifies the colored union with the temporal carrier and
sums the fixed-size shells.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
import YMGap.Continuum.Z4CanonicalConnectedCarrierWeight

namespace YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockComponentSwitch
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev TwoBlockConnectedEntry
    {n : Nat} (firstRoots secondRoots : List (CanonicalAtom n))
    (firstPredicate secondPredicate : List Bool → Bool) :=
  {pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate //
    pair ∈ connectedTwoBlockSourcePairs}

def twoBlockConnectedEndpoints
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    Σ' first : CanonicalAtom n, Σ' second : CanonicalAtom n,
      (first ∈ firstRoots) ×' (second ∈ secondRoots) ×'
        (canonicalDisagreementCut
          (twoBlockSourceLeftCompatible entry.val)
          (twoBlockSourceRightCompatible entry.val)
          first second = true) :=
  twoBlockMarkedReachWitness
    (twoBlockSourceLeftCompatible entry.val)
    (twoBlockSourceRightCompatible entry.val)
    firstRoots secondRoots
    (twoBlockConnectedSourcePair_reach_true entry.val entry.property)

def twoBlockConnectedFirst
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : CanonicalAtom n :=
  (twoBlockConnectedEndpoints entry).1

def twoBlockConnectedSecond
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : CanonicalAtom n :=
  (twoBlockConnectedEndpoints entry).2.1

theorem twoBlockConnectedFirst_mem
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockConnectedFirst entry ∈ firstRoots :=
  (twoBlockConnectedEndpoints entry).2.2.1

theorem twoBlockConnectedSecond_mem
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockConnectedSecond entry ∈ secondRoots :=
  (twoBlockConnectedEndpoints entry).2.2.2.1

theorem twoBlockConnectedEndpoints_reach
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    canonicalDisagreementCut
      (twoBlockSourceLeftCompatible entry.val)
      (twoBlockSourceRightCompatible entry.val)
      (twoBlockConnectedFirst entry)
      (twoBlockConnectedSecond entry) = true :=
  (twoBlockConnectedEndpoints entry).2.2.2.2

def twoBlockConnectedSourcePath
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    CWalk.Simple
      (twoBlockDisagreementEdge
        (twoBlockSourceLeftCompatible entry.val)
        (twoBlockSourceRightCompatible entry.val))
      (twoBlockConnectedFirst entry)
      (twoBlockConnectedSecond entry) :=
  twoBlockConnectedPath
    (twoBlockSourceLeftCompatible entry.val)
    (twoBlockSourceRightCompatible entry.val)
    (twoBlockConnectedFirst entry)
    (twoBlockConnectedSecond entry)
    (twoBlockConnectedEndpoints_reach entry)

def twoBlockConnectedPathAtoms
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : List (CanonicalAtom n) :=
  (twoBlockConnectedSourcePath entry).walk.vertices

def twoBlockConnectedPathValues
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : List (List Nat) :=
  (twoBlockConnectedPathAtoms entry).map Subtype.val

def twoBlockSourceExclusive
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate) (atom : CanonicalAtom n) : Prop :=
  (memberB (canonicalFamilyAtoms
        (twoBlockSourceLeftCompatible pair)) atom = true ∧
      memberB (canonicalFamilyAtoms
        (twoBlockSourceRightCompatible pair)) atom = false) ∨
    (memberB (canonicalFamilyAtoms
        (twoBlockSourceLeftCompatible pair)) atom = false ∧
      memberB (canonicalFamilyAtoms
        (twoBlockSourceRightCompatible pair)) atom = true)

theorem twoBlockDisagreementEdge_target_exclusive
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (pair : TwoBlockSourcePair firstRoots secondRoots
      firstPredicate secondPredicate)
    {first second : CanonicalAtom n}
    (hedge : twoBlockDisagreementEdge
      (twoBlockSourceLeftCompatible pair)
      (twoBlockSourceRightCompatible pair) first second = true) :
    twoBlockSourceExclusive pair second := by
  have hbits := (Bool.and_eq_true _ _).mp hedge |>.2
  unfold twoBlockDisagreementEdge disagreementBits leftOnly rightOnly at hbits
  unfold twoBlockSourceExclusive
  cases hleftFirst : memberB (canonicalFamilyAtoms
      (twoBlockSourceLeftCompatible pair)) first <;>
    cases hrightFirst : memberB (canonicalFamilyAtoms
      (twoBlockSourceRightCompatible pair)) first <;>
    cases hleftSecond : memberB (canonicalFamilyAtoms
      (twoBlockSourceLeftCompatible pair)) second <;>
    cases hrightSecond : memberB (canonicalFamilyAtoms
      (twoBlockSourceRightCompatible pair)) second <;>
    simp_all

theorem twoBlockConnectedFirst_exclusive_of_ne
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (hne : twoBlockConnectedFirst entry ≠
      twoBlockConnectedSecond entry) :
    twoBlockSourceExclusive entry.val (twoBlockConnectedFirst entry) := by
  have hwalk := warshallSound
    (twoBlockDisagreementEdge
      (twoBlockSourceLeftCompatible entry.val)
      (twoBlockSourceRightCompatible entry.val))
    (canonicalAmbientAtoms n)
    (twoBlockConnectedFirst entry)
    (twoBlockConnectedSecond entry)
    (twoBlockConnectedEndpoints_reach entry)
  obtain ⟨next, hedge⟩ := dWalk_start_edge_of_ne _ hwalk hne
  exact disagreementEdge_source_exclusive
    (canonicalAmbientAtoms n) (canonicalAtomCompatibleB n)
    (memberB (canonicalFamilyAtoms
      (twoBlockSourceLeftCompatible entry.val)))
    (memberB (canonicalFamilyAtoms
      (twoBlockSourceRightCompatible entry.val))) hedge

theorem twoBlockConnectedPathAtoms_exclusive
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (hne : twoBlockConnectedFirst entry ≠
      twoBlockConnectedSecond entry) :
    ∀ atom, atom ∈ twoBlockConnectedPathAtoms entry →
      twoBlockSourceExclusive entry.val atom := by
  exact CWalk.all_vertices_of_start
    (twoBlockSourceExclusive entry.val)
    (fun _ _ hedge _ =>
      twoBlockDisagreementEdge_target_exclusive entry.val hedge)
    (twoBlockConnectedSourcePath entry).walk
    (twoBlockConnectedFirst_exclusive_of_ne entry hne)

def twoBlockConnectedPathTest
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : List Nat → Bool :=
  memberB (twoBlockConnectedPathValues entry)

def twoBlockConnectedPathLeftFamily
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : TwoBlockPolymerFamily :=
  entry.val.1.val.filter (twoBlockConnectedPathTest entry)

def twoBlockConnectedBackgroundLeftFamily
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : TwoBlockPolymerFamily :=
  entry.val.1.val.filter (fun polymer =>
    !(twoBlockConnectedPathTest entry polymer))

def twoBlockConnectedPathRightFamily
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : TwoBlockPolymerFamily :=
  entry.val.2.val.filter (twoBlockConnectedPathTest entry)

def twoBlockConnectedBackgroundRightFamily
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : TwoBlockPolymerFamily :=
  entry.val.2.val.filter (fun polymer =>
    !(twoBlockConnectedPathTest entry polymer))

theorem twoBlockConnectedPathLeftFamily_mem
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockConnectedPathLeftFamily entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem
    (twoBlockSourceLeftCompatible entry.val)
    (twoBlockConnectedPathTest entry)

theorem twoBlockConnectedPathRightFamily_mem
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockConnectedPathRightFamily entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem
    (twoBlockSourceRightCompatible entry.val)
    (twoBlockConnectedPathTest entry)

theorem twoBlockConnectedBackgroundLeftFamily_mem
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockConnectedBackgroundLeftFamily entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem
    (twoBlockSourceLeftCompatible entry.val)
    (fun polymer => !(twoBlockConnectedPathTest entry polymer))

theorem twoBlockConnectedBackgroundRightFamily_mem
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockConnectedBackgroundRightFamily entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem
    (twoBlockSourceRightCompatible entry.val)
    (fun polymer => !(twoBlockConnectedPathTest entry polymer))

def twoBlockConnectedPathPairWeight
    (coupling : Q')
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : Q' :=
  canonicalSurfaceFamilyActivity coupling n
      (twoBlockConnectedPathLeftFamily entry) *
    canonicalSurfaceFamilyActivity coupling n
      (twoBlockConnectedPathRightFamily entry)

def twoBlockConnectedBackgroundPairWeight
    (coupling : Q')
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : Q' :=
  canonicalSurfaceFamilyActivity coupling n
      (twoBlockConnectedBackgroundLeftFamily entry) *
    canonicalSurfaceFamilyActivity coupling n
      (twoBlockConnectedBackgroundRightFamily entry)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem twoBlockConnectedSourcePairWeight_factor
    (coupling : Q')
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    twoBlockSourcePairWeight coupling entry.val ≈
      twoBlockConnectedPathPairWeight coupling entry *
        twoBlockConnectedBackgroundPairWeight coupling entry := by
  have hleft := canonicalSurfaceFamilyActivity_filter_partition
    coupling n entry.val.1.val (twoBlockConnectedPathTest entry)
  have hright := canonicalSurfaceFamilyActivity_filter_partition
    coupling n entry.val.2.val (twoBlockConnectedPathTest entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold twoBlockConnectedPathPairWeight
    twoBlockConnectedBackgroundPairWeight
    twoBlockConnectedPathLeftFamily
    twoBlockConnectedBackgroundLeftFamily
    twoBlockConnectedPathRightFamily
    twoBlockConnectedBackgroundRightFamily
  ring_qeqv

def twoBlockConnectedLeftColorSupport
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : List Nat :=
  familyUnionSupport n (twoBlockConnectedPathLeftFamily entry)

def twoBlockConnectedRightColorSupport
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : List Nat :=
  familyUnionSupport n (twoBlockConnectedPathRightFamily entry)

def twoBlockConnectedColoredCarrier
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) : ConnectedCarrier :=
  ((twoBlockConnectedLeftColorSupport entry,
      twoBlockConnectedRightColorSupport entry),
    (twoBlockConnectedBackgroundLeftFamily entry,
      twoBlockConnectedBackgroundRightFamily entry))

theorem twoBlockConnectedColoredCarrier_injective
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (first second : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (heq : twoBlockConnectedColoredCarrier first =
      twoBlockConnectedColoredCarrier second) : first = second := by
  have hleftSupport : twoBlockConnectedLeftColorSupport first =
      twoBlockConnectedLeftColorSupport second :=
    congrArg (fun carrier => carrier.1.1) heq
  have hrightSupport : twoBlockConnectedRightColorSupport first =
      twoBlockConnectedRightColorSupport second :=
    congrArg (fun carrier => carrier.1.2) heq
  have hleftBackground : twoBlockConnectedBackgroundLeftFamily first =
      twoBlockConnectedBackgroundLeftFamily second :=
    congrArg (fun carrier => carrier.2.1) heq
  have hrightBackground : twoBlockConnectedBackgroundRightFamily first =
      twoBlockConnectedBackgroundRightFamily second :=
    congrArg (fun carrier => carrier.2.2) heq
  have hleftPath : twoBlockConnectedPathLeftFamily first =
      twoBlockConnectedPathLeftFamily second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (twoBlockConnectedPathLeftFamily_mem first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (twoBlockConnectedPathLeftFamily_mem second)
    exact hrecoverFirst.symm.trans
      ((congrArg (fun support => ambientOrderedFamily n
        (canonicalSurfaceFamily n support)) hleftSupport).trans
        hrecoverSecond)
  have hrightPath : twoBlockConnectedPathRightFamily first =
      twoBlockConnectedPathRightFamily second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (twoBlockConnectedPathRightFamily_mem first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (twoBlockConnectedPathRightFamily_mem second)
    exact hrecoverFirst.symm.trans
      ((congrArg (fun support => ambientOrderedFamily n
        (canonicalSurfaceFamily n support)) hrightSupport).trans
        hrecoverSecond)
  have hleftSource : first.val.1.val = second.val.1.val :=
    ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup n)
      (compatibleAmbientFamily_sublist
        (twoBlockSourceLeftCompatible first.val))
      (compatibleAmbientFamily_sublist
        (twoBlockSourceLeftCompatible second.val))
      (twoBlockConnectedPathTest first)
      (twoBlockConnectedPathTest second) hleftPath hleftBackground
  have hrightSource : first.val.2.val = second.val.2.val :=
    ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup n)
      (compatibleAmbientFamily_sublist
        (twoBlockSourceRightCompatible first.val))
      (compatibleAmbientFamily_sublist
        (twoBlockSourceRightCompatible second.val))
      (twoBlockConnectedPathTest first)
      (twoBlockConnectedPathTest second) hrightPath hrightBackground
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hleftSource
  · exact Subtype.ext hrightSource

#print axioms twoBlockConnectedPathAtoms_exclusive
#print axioms twoBlockConnectedSourcePairWeight_factor
#print axioms twoBlockConnectedColoredCarrier_injective

end YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier
