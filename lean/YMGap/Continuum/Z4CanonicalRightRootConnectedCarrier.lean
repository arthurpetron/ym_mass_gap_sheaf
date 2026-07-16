/-
# Colored connected carriers for the right-rooted residue

The reverse four-cell determinant has its marked polymer in the embedded
replica and its exterior witness in the boundary replica.  This module builds
the mirrored deterministic simple path, splits it into two source colors, and
stores the two backgrounds in large/embedded order.  The resulting carrier is
injective and uses the same pinned colored-support target as the forward
orientation.
-/

import YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
import YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize

namespace YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedResiduePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev PolymerFamily := List (List Nat)

/-! ## 1. Deterministic right-boundary simple path -/

def reverseSourceDisagreementEdge
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root) :
    CanonicalAtom n → CanonicalAtom n → Bool :=
  disagreementEdge (canonicalAmbientAtoms n)
    (canonicalAtomCompatibleB n)
    (memberB (canonicalFamilyAtoms
      (reverseSourceLeftCompatible hsmall pair)))
    (memberB (canonicalFamilyAtoms
      (reverseSourceRightCompatible pair)))

theorem connectedReverseSourcePair_reach_true
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root)
    (hpair : pair ∈ connectedReverseSourcePairs hsmall) :
    rightBoundaryOutsideDisagreementReachB small
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair) = true := by
  have htest := (List.mem_filter.mp hpair).2
  unfold reverseSourceSeparatedB at htest
  cases hreach : rightBoundaryOutsideDisagreementReachB small
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair) <;> simp_all

def reverseSourceOutsideTest
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root)
    (atom : CanonicalAtom n) : Bool :=
  (!(polymerInsideBoxB small n atom.val)) &&
    canonicalDisagreementCut
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair) atom

def reverseSourceOutsideAtom
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root) : CanonicalAtom n :=
  firstTrueOr (reverseSourceRootAtom hsmall pair)
    (reverseSourceOutsideTest hsmall pair)
    (canonicalFamilyAtoms (reverseSourceRightCompatible pair))

theorem reverseSourceOutsideAtom_spec
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root)
    (hpair : pair ∈ connectedReverseSourcePairs hsmall) :
    reverseSourceOutsideTest hsmall pair
          (reverseSourceOutsideAtom hsmall pair) = true ∧
      reverseSourceOutsideAtom hsmall pair ∈
        canonicalFamilyAtoms (reverseSourceRightCompatible pair) := by
  apply firstTrueOr_spec
  simpa [rightBoundaryOutsideDisagreementReachB,
    reverseSourceOutsideTest] using
      connectedReverseSourcePair_reach_true hsmall pair hpair

theorem reverseSourceOutsideAtom_outside
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root)
    (hpair : pair ∈ connectedReverseSourcePairs hsmall) :
    polymerInsideBoxB small n
      (reverseSourceOutsideAtom hsmall pair).val = false := by
  have htest := (Bool.and_eq_true _ _).mp
    (reverseSourceOutsideAtom_spec hsmall pair hpair).1 |>.1
  cases hinside : polymerInsideBoxB small n
      (reverseSourceOutsideAtom hsmall pair).val <;> simp_all

theorem reverseSourceOutsideAtom_reaches
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root)
    (hpair : pair ∈ connectedReverseSourcePairs hsmall) :
    canonicalDisagreementCut
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair)
      (reverseSourceOutsideAtom hsmall pair) = true :=
  (Bool.and_eq_true _ _).mp
    (reverseSourceOutsideAtom_spec hsmall pair hpair).1 |>.2

abbrev ReverseConnectedSourceEntry
    {small n : Nat} (root : List Nat) (hsmall : small ≤ n) :=
  {pair : ReverseSourcePair small n root //
    pair ∈ connectedReverseSourcePairs hsmall}

def reverseConnectedSourcePath
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    CWalk.Simple (reverseSourceDisagreementEdge hsmall entry.val)
      (reverseSourceRootAtom hsmall entry.val)
      (reverseSourceOutsideAtom hsmall entry.val) :=
  simpleWalkOfWarshall (reverseSourceDisagreementEdge hsmall entry.val)
    (canonicalAmbientAtoms n)
    (reverseSourceRootAtom hsmall entry.val)
    (reverseSourceOutsideAtom hsmall entry.val)
    (reverseSourceOutsideAtom_reaches hsmall entry.val entry.property)

def reverseConnectedPathAtoms
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    List (CanonicalAtom n) :=
  (reverseConnectedSourcePath hsmall entry).walk.vertices

def reverseConnectedPathValues
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : List (List Nat) :=
  (reverseConnectedPathAtoms hsmall entry).map Subtype.val

/-! ## 2. Source colors and exact path/background factorization -/

def reverseSourceExclusive
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root) (atom : CanonicalAtom n) : Prop :=
  (memberB (canonicalFamilyAtoms
        (reverseSourceLeftCompatible hsmall pair)) atom = true ∧
      memberB (canonicalFamilyAtoms
        (reverseSourceRightCompatible pair)) atom = false) ∨
    (memberB (canonicalFamilyAtoms
        (reverseSourceLeftCompatible hsmall pair)) atom = false ∧
      memberB (canonicalFamilyAtoms
        (reverseSourceRightCompatible pair)) atom = true)

theorem reverseSourceRootAtom_exclusive
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root) :
    reverseSourceExclusive hsmall pair
      (reverseSourceRootAtom hsmall pair) := by
  apply Or.inl
  constructor
  · apply (memberB_eq_true_iff _ _).2
    exact (canonicalFamilyAtom_mem_iff
      (reverseSourceLeftCompatible hsmall pair)
      (reverseSourceRootAtom hsmall pair)).2
      (reverseSourceRootMem pair)
  · apply (memberB_eq_false_iff _ _).2
    intro hright
    have hvalue := (canonicalFamilyAtom_mem_iff
      (reverseSourceRightCompatible pair)
      (reverseSourceRootAtom hsmall pair)).1 hright
    exact reverseSourceRootNotMem pair (by
      simpa [reverseSourceRootAtom, leftCanonicalAtomOfMember] using hvalue)

theorem reverseSourceDisagreementEdge_target_exclusive
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root)
    {first second : CanonicalAtom n}
    (hedge : reverseSourceDisagreementEdge hsmall pair first second = true) :
    reverseSourceExclusive hsmall pair second := by
  have hbits := (Bool.and_eq_true _ _).mp hedge |>.2
  unfold reverseSourceDisagreementEdge disagreementBits leftOnly rightOnly
    at hbits
  unfold reverseSourceExclusive
  cases hleftFirst : memberB (canonicalFamilyAtoms
      (reverseSourceLeftCompatible hsmall pair)) first <;>
    cases hrightFirst : memberB (canonicalFamilyAtoms
      (reverseSourceRightCompatible pair)) first <;>
    cases hleftSecond : memberB (canonicalFamilyAtoms
      (reverseSourceLeftCompatible hsmall pair)) second <;>
    cases hrightSecond : memberB (canonicalFamilyAtoms
      (reverseSourceRightCompatible pair)) second <;>
    simp_all

theorem reverseConnectedPathAtoms_exclusive
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    ∀ atom, atom ∈ reverseConnectedPathAtoms hsmall entry →
      reverseSourceExclusive hsmall entry.val atom := by
  exact CWalk.all_vertices_of_start
    (reverseSourceExclusive hsmall entry.val)
    (fun _ _ hedge _ =>
      reverseSourceDisagreementEdge_target_exclusive
        hsmall entry.val hedge)
    (reverseConnectedSourcePath hsmall entry).walk
    (reverseSourceRootAtom_exclusive hsmall entry.val)

def reverseConnectedPathTest
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : List Nat → Bool :=
  memberB (reverseConnectedPathValues hsmall entry)

def reverseConnectedPathLeftFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : PolymerFamily :=
  entry.val.1.val.filter (reverseConnectedPathTest hsmall entry)

def reverseConnectedBackgroundLeftFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : PolymerFamily :=
  entry.val.1.val.filter
    (fun polymer => !(reverseConnectedPathTest hsmall entry polymer))

def reverseConnectedPathRightFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : PolymerFamily :=
  entry.val.2.val.filter (reverseConnectedPathTest hsmall entry)

def reverseConnectedBackgroundRightFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : PolymerFamily :=
  entry.val.2.val.filter
    (fun polymer => !(reverseConnectedPathTest hsmall entry polymer))

theorem reverseConnectedPathLeftFamily_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseConnectedPathLeftFamily hsmall entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem
    (reverseSourceLeftCompatible hsmall entry.val)
    (reverseConnectedPathTest hsmall entry)

theorem reverseConnectedBackgroundLeftFamily_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseConnectedBackgroundLeftFamily hsmall entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem
    (reverseSourceLeftCompatible hsmall entry.val)
    (fun polymer => !(reverseConnectedPathTest hsmall entry polymer))

theorem reverseConnectedPathRightFamily_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseConnectedPathRightFamily hsmall entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem
    (reverseSourceRightCompatible entry.val)
    (reverseConnectedPathTest hsmall entry)

theorem reverseConnectedBackgroundRightFamily_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseConnectedBackgroundRightFamily hsmall entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem
    (reverseSourceRightCompatible entry.val)
    (fun polymer => !(reverseConnectedPathTest hsmall entry polymer))

def reverseConnectedPathPairWeight
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n
      (reverseConnectedPathLeftFamily hsmall entry) *
    canonicalSurfaceFamilyActivity anchorCoupling n
      (reverseConnectedPathRightFamily hsmall entry)

/-- Backgrounds are deliberately stored in large/embedded order: the right
boundary background first, then the left embedded background. -/
def reverseConnectedBackgroundPairWeight
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n
      (reverseConnectedBackgroundRightFamily hsmall entry) *
    canonicalSurfaceFamilyActivity anchorCoupling n
      (reverseConnectedBackgroundLeftFamily hsmall entry)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem reverseConnectedSourcePairWeight_factor
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseSourcePairWeight entry.val ≈
      reverseConnectedPathPairWeight hsmall entry *
        reverseConnectedBackgroundPairWeight hsmall entry := by
  have hleft := canonicalSurfaceFamilyActivity_filter_partition
    anchorCoupling n entry.val.1.val
    (reverseConnectedPathTest hsmall entry)
  have hright := canonicalSurfaceFamilyActivity_filter_partition
    anchorCoupling n entry.val.2.val
    (reverseConnectedPathTest hsmall entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold reverseConnectedPathPairWeight
    reverseConnectedBackgroundPairWeight
    reverseConnectedPathLeftFamily reverseConnectedBackgroundLeftFamily
    reverseConnectedPathRightFamily reverseConnectedBackgroundRightFamily
  ring_qeqv

/-! ## 3. Support/background recovery -/

def reverseConnectedLeftColorSupport
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : List Nat :=
  familyUnionSupport n (reverseConnectedPathLeftFamily hsmall entry)

def reverseConnectedRightColorSupport
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : List Nat :=
  familyUnionSupport n (reverseConnectedPathRightFamily hsmall entry)

def reverseConnectedCarrier
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : ConnectedCarrier :=
  ((reverseConnectedLeftColorSupport hsmall entry,
      reverseConnectedRightColorSupport hsmall entry),
    (reverseConnectedBackgroundRightFamily hsmall entry,
      reverseConnectedBackgroundLeftFamily hsmall entry))

theorem reverseConnectedCarrier_injective
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (first second : ReverseConnectedSourceEntry root hsmall)
    (heq : reverseConnectedCarrier hsmall first =
      reverseConnectedCarrier hsmall second) : first = second := by
  have hleftSupport : reverseConnectedLeftColorSupport hsmall first =
      reverseConnectedLeftColorSupport hsmall second :=
    congrArg (fun carrier => carrier.1.1) heq
  have hrightSupport : reverseConnectedRightColorSupport hsmall first =
      reverseConnectedRightColorSupport hsmall second :=
    congrArg (fun carrier => carrier.1.2) heq
  have hrightBackground :
      reverseConnectedBackgroundRightFamily hsmall first =
        reverseConnectedBackgroundRightFamily hsmall second :=
    congrArg (fun carrier => carrier.2.1) heq
  have hleftBackground :
      reverseConnectedBackgroundLeftFamily hsmall first =
        reverseConnectedBackgroundLeftFamily hsmall second :=
    congrArg (fun carrier => carrier.2.2) heq
  have hleftPath : reverseConnectedPathLeftFamily hsmall first =
      reverseConnectedPathLeftFamily hsmall second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (reverseConnectedPathLeftFamily_mem hsmall first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (reverseConnectedPathLeftFamily_mem hsmall second)
    exact hrecoverFirst.symm.trans
      ((congrArg (fun support => ambientOrderedFamily n
          (canonicalSurfaceFamily n support)) hleftSupport).trans
        hrecoverSecond)
  have hrightPath : reverseConnectedPathRightFamily hsmall first =
      reverseConnectedPathRightFamily hsmall second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (reverseConnectedPathRightFamily_mem hsmall first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (reverseConnectedPathRightFamily_mem hsmall second)
    exact hrecoverFirst.symm.trans
      ((congrArg (fun support => ambientOrderedFamily n
          (canonicalSurfaceFamily n support)) hrightSupport).trans
        hrecoverSecond)
  have hleftSource : first.val.1.val = second.val.1.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup n)
      (compatibleAmbientFamily_sublist
        (reverseSourceLeftCompatible hsmall first.val))
      (compatibleAmbientFamily_sublist
        (reverseSourceLeftCompatible hsmall second.val))
      (reverseConnectedPathTest hsmall first)
      (reverseConnectedPathTest hsmall second)
      hleftPath hleftBackground
  have hrightSource : first.val.2.val = second.val.2.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup n)
      (compatibleAmbientFamily_sublist
        (reverseSourceRightCompatible first.val))
      (compatibleAmbientFamily_sublist
        (reverseSourceRightCompatible second.val))
      (reverseConnectedPathTest hsmall first)
      (reverseConnectedPathTest hsmall second)
      hrightPath hrightBackground
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hleftSource
  · exact Subtype.ext hrightSource

/-! ## 4. The color union is a pinned boundary-reaching animal -/

def reverseConnectedCarrierSupport
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) : List Nat :=
  familyUnionSupport n
    (reverseConnectedPathLeftFamily hsmall entry ++
      reverseConnectedPathRightFamily hsmall entry)

theorem reverseConnectedPathAtom_mem_coloredFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {atom : CanonicalAtom n}
    (hatom : atom ∈ reverseConnectedPathAtoms hsmall entry) :
    atom.val ∈ reverseConnectedPathLeftFamily hsmall entry ∨
      atom.val ∈ reverseConnectedPathRightFamily hsmall entry := by
  have htest : reverseConnectedPathTest hsmall entry atom.val = true := by
    unfold reverseConnectedPathTest reverseConnectedPathValues
    apply (memberB_eq_true_iff _ _).2
    exact List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rcases reverseConnectedPathAtoms_exclusive hsmall entry atom hatom with
      hleft | hright
  · apply Or.inl
    unfold reverseConnectedPathLeftFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (reverseSourceLeftCompatible hsmall entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hleft.1), htest⟩
  · apply Or.inr
    unfold reverseConnectedPathRightFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (reverseSourceRightCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hright.2), htest⟩

theorem reverseConnectedPathAtom_face_mem_support
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {atom : CanonicalAtom n}
    (hatom : atom ∈ reverseConnectedPathAtoms hsmall entry)
    {face : Nat} (hface : face ∈ atom.val) :
    face ∈ reverseConnectedCarrierSupport hsmall entry := by
  unfold reverseConnectedCarrierSupport
  rw [mem_familyUnionSupport_iff]
  constructor
  · exact mem_of_mem_sublists (physicalFaceEdges n) atom.val
      (canonicalSurfacePolymer_mem_faceSupports atom.property) face hface
  · refine ⟨atom.val, ?_, hface⟩
    rcases reverseConnectedPathAtom_mem_coloredFamily
        hsmall entry hatom with hleft | hright
    · exact List.mem_append_left _ hleft
    · exact List.mem_append_right _ hright

theorem reverseConnectedColoredFamily_pathTest
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {polymer : List Nat}
    (hpolymer : polymer ∈
      reverseConnectedPathLeftFamily hsmall entry ++
        reverseConnectedPathRightFamily hsmall entry) :
    reverseConnectedPathTest hsmall entry polymer = true := by
  rcases List.mem_append.mp hpolymer with hleft | hright
  · exact (List.mem_filter.mp hleft).2
  · exact (List.mem_filter.mp hright).2

def reverseConnectedCarrierSupport_face_witness
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {face : Nat} (hface : face ∈ reverseConnectedCarrierSupport hsmall entry) :
    Σ' atom : CanonicalAtom n,
      (atom ∈ reverseConnectedPathAtoms hsmall entry) ×'
        (face ∈ atom.val) := by
  have hcontains : familyContainsFaceB face
      (reverseConnectedPathLeftFamily hsmall entry ++
        reverseConnectedPathRightFamily hsmall entry) = true :=
    (List.mem_filter.mp hface).2
  obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
    familyContainsFaceWitness face _ hcontains
  have hpathTest : reverseConnectedPathTest hsmall entry polymer = true :=
    reverseConnectedColoredFamily_pathTest hsmall entry hpolymer
  have hpathValue : polymer ∈ reverseConnectedPathValues hsmall entry :=
    (memberB_eq_true_iff _ _).1 hpathTest
  obtain ⟨atom, hatom, hatomValue⟩ :=
    decodeMapMember Subtype.val (reverseConnectedPathAtoms hsmall entry)
      polymer hpathValue
  refine ⟨atom, ?_, ?_⟩
  · simpa [reverseConnectedPathValues] using hatom
  · rw [hatomValue]
    exact hfacePolymer

theorem reverseConnectedCarrierSupport_mem_faceSupports
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseConnectedCarrierSupport hsmall entry ∈ cutoffOneFaceSupports n :=
  familyUnionSupport_mem_cutoffOneFaceSupports n _

def reverseDisagreementCWalk_faceChainFromStart
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : ReverseSourcePair small n root) :
    ∀ {first last : CanonicalAtom n}
      (walk : CWalk (reverseSourceDisagreementEdge hsmall pair) first last)
      (support : List Nat),
      (∀ atom, atom ∈ walk.vertices →
        ∀ face, face ∈ atom.val → face ∈ support) →
      ∀ {target : CanonicalAtom n}, target ∈ walk.vertices →
        ∀ {start finish : Nat}, start ∈ first.val → finish ∈ target.val →
          ChainIn (faceLinkAdjacentB n) support start finish
  | _, _, .single atom, support, hcover, target, htarget,
      start, finish, hstart, hfinish => by
      have htargetEq : target = atom := List.mem_singleton.mp htarget
      subst target
      exact ChainIn.mono
        (fun face hface => hcover atom List.mem_cons_self face hface)
        ((canonicalSurfacePolymers_allConnected n) atom atom.property
          start finish hstart hfinish)
  | first, last, .cons (middle := middle) hedge rest, support, hcover,
      target, htarget, start, finish, hstart, hfinish => by
      cases heqTarget : decide (target = first) with
      | true =>
        have htargetFirst : target = first := of_decide_eq_true heqTarget
        subst target
        exact ChainIn.mono
          (fun face hface => hcover first List.mem_cons_self face hface)
          ((canonicalSurfacePolymers_allConnected n) first first.property
            start finish hstart hfinish)
      | false =>
        have htargetFirst : target ≠ first := of_decide_eq_false heqTarget
        have htargetRest : target ∈ rest.vertices :=
          (List.mem_cons.mp htarget).resolve_left htargetFirst
        have hincompatible : canonicalPolymerCompatibleB n
            first.val middle.val = false :=
          canonicalDisagreementEdge_incompatible
            (reverseSourceLeftCompatible hsmall pair)
            (reverseSourceRightCompatible pair)
            (by simpa [reverseSourceDisagreementEdge] using hedge)
        obtain ⟨leftContact, hleftContact, rightContact,
            hrightContact, hcontact⟩ :=
          canonicalPolymerIncompatibleContact hincompatible
        have hhead : ChainIn (faceLinkAdjacentB n) support
            start leftContact :=
          ChainIn.mono
            (fun face hface => hcover first List.mem_cons_self face hface)
            ((canonicalSurfacePolymers_allConnected n) first first.property
              start leftContact hstart hleftContact)
        have htail : ChainIn (faceLinkAdjacentB n) support
            rightContact finish :=
          reverseDisagreementCWalk_faceChainFromStart hsmall pair rest support
            (fun atom hatom face hface =>
              hcover atom (List.mem_cons_of_mem first hatom) face hface)
            htargetRest hrightContact hfinish
        cases hcontact with
        | same heq =>
          subst rightContact
          exact ChainIn.trans hhead htail
        | adjacent hadj =>
          exact ChainIn.trans hhead
            (.step hadj
              (hcover middle
                (List.mem_cons_of_mem first
                  (CWalk.start_mem_vertices rest))
                rightContact hrightContact)
              htail)

def reverseConnectedCarrierSupport_chain_from_root
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {rootFace face : Nat} (hrootFace : rootFace ∈ root)
    (hface : face ∈ reverseConnectedCarrierSupport hsmall entry) :
    ChainIn (faceLinkAdjacentB n)
      (reverseConnectedCarrierSupport hsmall entry) rootFace face := by
  obtain ⟨target, htarget, hfaceTarget⟩ :=
    reverseConnectedCarrierSupport_face_witness hsmall entry hface
  exact reverseDisagreementCWalk_faceChainFromStart hsmall entry.val
    (reverseConnectedSourcePath hsmall entry).walk
    (reverseConnectedCarrierSupport hsmall entry)
    (fun atom hatom found hfound =>
      reverseConnectedPathAtom_face_mem_support
        hsmall entry hatom hfound)
    htarget hrootFace hfaceTarget

theorem reverseConnectedCarrierSupport_root_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {rootFace : Nat} (hrootFace : rootFace ∈ root) :
    rootFace ∈ reverseConnectedCarrierSupport hsmall entry :=
  reverseConnectedPathAtom_face_mem_support hsmall entry
    (by simpa [reverseConnectedPathAtoms] using
      CWalk.start_mem_vertices (reverseConnectedSourcePath hsmall entry).walk)
    hrootFace

def reverseConnectedCarrierSupport_internallyConnected
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {rootFace : Nat} (hrootFace : rootFace ∈ root) :
    InternallyConnected (faceLinkAdjacentB n)
      (reverseConnectedCarrierSupport hsmall entry) := by
  intro first last hfirst hlast
  have hrootFirst := reverseConnectedCarrierSupport_chain_from_root
    hsmall entry hrootFace hfirst
  have hrootLast := reverseConnectedCarrierSupport_chain_from_root
    hsmall entry hrootFace hlast
  exact ChainIn.trans
    (chainInReverse (faceLinkAdjacentB_symmetric n) hrootFirst
      (reverseConnectedCarrierSupport_root_mem
        hsmall entry hrootFace))
    hrootLast

theorem reverseConnectedCarrierSupport_boundary_floor
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {start inner distance : Nat}
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    distance + 2 ≤
      (reverseConnectedCarrierSupport hsmall entry).length := by
  have houtside := reverseSourceOutsideAtom_outside
    hsmall entry.val entry.property
  obtain ⟨outsidePlaquette, houtsidePlaquette, houtsideSmall⟩ :=
    polymerInsideBoxB_false_witness houtside
  obtain ⟨finish, hfinish, hfinishEq⟩ :=
    List.mem_map.mp houtsidePlaquette
  have hfinishSupport : finish ∈
      reverseConnectedCarrierSupport hsmall entry :=
    reverseConnectedPathAtom_face_mem_support hsmall entry
      (by simpa [reverseConnectedPathAtoms] using
        CWalk.end_mem_vertices (reverseConnectedSourcePath hsmall entry).walk)
      hfinish
  have hfinishOutside :
      boxPlaquetteAt n finish ∉ boxPlaquettes small := by
    rw [hfinishEq]
    exact houtsideSmall
  have houtSmall : outsideBoxB small (boxPlaquetteAt n finish) = true :=
    (outsideBoxB_true_iff_not_mem small (boxPlaquetteAt n finish)).2
      hfinishOutside
  have houtExpanded :
      outsideBoxB (inner + distance) (boxPlaquetteAt n finish) = true := by
    rw [hbox]
    exact houtSmall
  have hsep := outside_expanded_box_linf_floor hstartInner houtExpanded
  have hfloor := connectedFaceSupport_linf_size_floor
    (reverseConnectedCarrierSupport_mem_faceSupports hsmall entry)
    (reverseConnectedCarrierSupport_internallyConnected hsmall entry hstart)
    (reverseConnectedCarrierSupport_root_mem hsmall entry hstart)
    (List.mem_map.mpr ⟨finish, hfinishSupport, rfl⟩)
    hsep
  omega

theorem reverseConnectedCarrierSupport_mem_canonicalSurfacePolymers
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall)
    {rootFace : Nat} (hrootFace : rootFace ∈ root) :
    reverseConnectedCarrierSupport hsmall entry ∈
      canonicalSurfacePolymers n :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (reverseConnectedCarrierSupport_mem_faceSupports hsmall entry)
    ⟨rootFace,
      reverseConnectedCarrierSupport_root_mem hsmall entry hrootFace⟩
    (reverseConnectedCarrierSupport_internallyConnected
      hsmall entry hrootFace)

/-! ## 5. Exact activity envelope and embedded background -/

theorem reverseConnectedCarrierSupport_length_le_pathFaceCount
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    (reverseConnectedCarrierSupport hsmall entry).length ≤
      familyFaceCount (reverseConnectedPathLeftFamily hsmall entry) +
        familyFaceCount (reverseConnectedPathRightFamily hsmall entry) := by
  have hbound := familyUnionSupport_length_le_familyFaceCount n
    (reverseConnectedPathLeftFamily hsmall entry ++
      reverseConnectedPathRightFamily hsmall entry)
  rw [familyFaceCount_append] at hbound
  exact hbound

theorem reverseConnectedPathPairWeight_le_totalFacePow
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseConnectedPathPairWeight hsmall entry ≤
      anchorPerFaceEnvelope ^
        (familyFaceCount (reverseConnectedPathLeftFamily hsmall entry) +
          familyFaceCount
            (reverseConnectedPathRightFamily hsmall entry)) := by
  have hleft := compatibleFamily_activity_le_totalFacePow
    (reverseConnectedPathLeftFamily_mem hsmall entry)
  have hright := compatibleFamily_activity_le_totalFacePow
    (reverseConnectedPathRightFamily_mem hsmall entry)
  have hright0 := canonicalSurfaceFamilyActivity_nonnegative n
    (reverseConnectedPathRightFamily hsmall entry)
  have hleftPow0 : (0 : Q') ≤ anchorPerFaceEnvelope ^
      familyFaceCount (reverseConnectedPathLeftFamily hsmall entry) :=
    Q'.pow_nonneg anchorPerFaceEnvelope (by decide) _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  unfold reverseConnectedPathPairWeight
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.pow_add_eqv anchorPerFaceEnvelope
          (familyFaceCount (reverseConnectedPathLeftFamily hsmall entry))
          (familyFaceCount
            (reverseConnectedPathRightFamily hsmall entry))))))

theorem reverseConnectedPathPairWeight_le_supportPow
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseConnectedPathPairWeight hsmall entry ≤
      anchorPerFaceEnvelope ^
        (reverseConnectedCarrierSupport hsmall entry).length := by
  exact Q'.le_trans' _ _ _
    (reverseConnectedPathPairWeight_le_totalFacePow hsmall entry)
    (pow_base_antitone (r := anchorPerFaceEnvelope)
      (by decide) (by decide)
      (reverseConnectedCarrierSupport_length_le_pathFaceCount hsmall entry))

theorem reverseConnectedBackgroundPairWeight_nonnegative
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    (0 : Q') ≤ reverseConnectedBackgroundPairWeight hsmall entry := by
  unfold reverseConnectedBackgroundPairWeight
  exact Q'.mul_nonneg _ _
    (canonicalSurfaceFamilyActivity_nonnegative n _)
    (canonicalSurfaceFamilyActivity_nonnegative n _)

theorem reverseConnectedSourcePairWeight_le_support_background
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseSourcePairWeight entry.val ≤
      anchorPerFaceEnvelope ^
          (reverseConnectedCarrierSupport hsmall entry).length *
        reverseConnectedBackgroundPairWeight hsmall entry := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (reverseConnectedSourcePairWeight_factor hsmall entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (reverseConnectedPathPairWeight_le_supportPow hsmall entry)
      (reverseConnectedBackgroundPairWeight_nonnegative hsmall entry))

theorem reverseConnectedBackgroundLeftFamily_mem_embedded
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ReverseConnectedSourceEntry root hsmall) :
    reverseConnectedBackgroundLeftFamily hsmall entry ∈
      embeddedCompatibleFamilies small n := by
  apply family_mem_embeddedCompatibleFamilies_of_inside hsmall
    (reverseConnectedBackgroundLeftFamily_mem hsmall entry)
  have hinside := familyInsideBox_of_mem_embeddedCompatibleFamilies
    hsmall (reverseSourceLeftEmbedded entry.val)
  intro support hsupport
  exact hinside support (List.mem_filter.mp hsupport).1

end YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier.reverseSourceOutsideAtom_spec
#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier.reverseConnectedPathAtoms_exclusive
#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier.reverseConnectedSourcePairWeight_factor
#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier.reverseConnectedCarrier_injective
#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier.reverseConnectedCarrierSupport_boundary_floor
#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier.reverseConnectedCarrierSupport_mem_canonicalSurfacePolymers
#print axioms YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier.reverseConnectedSourcePairWeight_le_support_background
