/-
# Recoverable colored carriers for the canonical connected residue

A connected source pair has a deterministic first outside polymer and a
constructively loop-erased disagreement path to it.  The path polymers are
split by their source color.  Each color is stored only through its union
support; canonical component uniqueness recovers the corresponding polymer
family.  Together with the two compatible background families this gives an
injective code for connected source entries and an exact path/background
factorization of their rational activity.
-/

import YMGap.Continuum.FiniteFamilyWeightPartition
import YMGap.Continuum.Z4CanonicalConnectedResiduePath

namespace YMGap.Continuum.Z4CanonicalConnectedPathCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteFamilyWeightPartition
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryPairDichotomy
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalConnectedResiduePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4CutoffOneSupportBijection

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev PolymerFamily := List (List Nat)

/-! ## 1. Constructive deterministic selection -/

def firstTrueOr {A : Type} (default : A) (test : A → Bool) :
    List A → A
  | [] => default
  | head :: tail =>
      if test head then head else firstTrueOr default test tail

theorem firstTrueOr_spec {A : Type} (default : A) (test : A → Bool) :
    ∀ xs : List A, xs.any test = true →
      test (firstTrueOr default test xs) = true ∧
        firstTrueOr default test xs ∈ xs
  | [], h => by cases h
  | head :: tail, h => by
      cases hhead : test head with
      | true =>
          simp [firstTrueOr, hhead]
      | false =>
          have htail : tail.any test = true := by
            simpa [List.any_cons, hhead] using h
          have ih := firstTrueOr_spec default test tail htail
          simp only [firstTrueOr, hhead, Bool.false_eq_true, ↓reduceIte]
          exact ⟨ih.1, List.mem_cons_of_mem head ih.2⟩

def sourceOutsideTest {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : SourcePair small n root)
    (atom : CanonicalAtom n) : Bool :=
  (!(polymerInsideBoxB small n atom.val)) &&
    canonicalDisagreementCut
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) atom

def sourceOutsideAtom {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : SourcePair small n root) :
    CanonicalAtom n :=
  firstTrueOr (sourceRootAtom pair) (sourceOutsideTest hsmall pair)
    (canonicalFamilyAtoms (sourceLeftCompatible pair))

theorem sourceOutsideAtom_spec
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hpair : pair ∈ connectedSourcePairs hsmall) :
    sourceOutsideTest hsmall pair (sourceOutsideAtom hsmall pair) = true ∧
      sourceOutsideAtom hsmall pair ∈
        canonicalFamilyAtoms (sourceLeftCompatible pair) := by
  apply firstTrueOr_spec
  simpa [boundaryOutsideDisagreementReachB, sourceOutsideTest] using
    connectedSourcePair_reach_true hsmall pair hpair

theorem sourceOutsideAtom_outside
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hpair : pair ∈ connectedSourcePairs hsmall) :
    polymerInsideBoxB small n (sourceOutsideAtom hsmall pair).val = false := by
  have htest := (Bool.and_eq_true _ _).mp
    (sourceOutsideAtom_spec hsmall pair hpair).1 |>.1
  cases hinside : polymerInsideBoxB small n
      (sourceOutsideAtom hsmall pair).val <;> simp_all

theorem sourceOutsideAtom_reaches
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    (hpair : pair ∈ connectedSourcePairs hsmall) :
    canonicalDisagreementCut
      (sourceLeftCompatible pair)
      (sourceRightCompatible hsmall pair)
      (sourceRootAtom pair) (sourceOutsideAtom hsmall pair) = true :=
  (Bool.and_eq_true _ _).mp
    (sourceOutsideAtom_spec hsmall pair hpair).1 |>.2

abbrev ConnectedSourceEntry
    {small n : Nat} (root : List Nat) (hsmall : small ≤ n) :=
  {pair : SourcePair small n root // pair ∈ connectedSourcePairs hsmall}

def connectedSourcePath
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    CWalk.Simple (sourceDisagreementEdge hsmall entry.val)
      (sourceRootAtom entry.val) (sourceOutsideAtom hsmall entry.val) :=
  sourceSimpleDisagreementPath hsmall entry.val
    (sourceOutsideAtom hsmall entry.val)
    (sourceOutsideAtom_reaches hsmall entry.val entry.property)

def connectedPathAtoms
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : List (CanonicalAtom n) :=
  (connectedSourcePath hsmall entry).walk.vertices

def connectedPathValues
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : List (List Nat) :=
  (connectedPathAtoms hsmall entry).map Subtype.val

/-! ## 2. Every carrier vertex has exactly one source color -/

def sourceExclusive {small n : Nat} {root : List Nat}
    (hsmall : small ≤ n) (pair : SourcePair small n root)
    (atom : CanonicalAtom n) : Prop :=
  (memberB (canonicalFamilyAtoms (sourceLeftCompatible pair)) atom = true ∧
      memberB (canonicalFamilyAtoms
        (sourceRightCompatible hsmall pair)) atom = false) ∨
    (memberB (canonicalFamilyAtoms (sourceLeftCompatible pair)) atom = false ∧
      memberB (canonicalFamilyAtoms
        (sourceRightCompatible hsmall pair)) atom = true)

theorem sourceRootAtom_exclusive
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root) :
    sourceExclusive hsmall pair (sourceRootAtom pair) := by
  apply Or.inl
  constructor
  · apply (memberB_eq_true_iff _ _).2
    exact (canonicalFamilyAtom_mem_iff
      (sourceLeftCompatible pair) (sourceRootAtom pair)).2
      (sourceRootMem pair)
  · apply (memberB_eq_false_iff _ _).2
    intro hright
    have hvalue := (canonicalFamilyAtom_mem_iff
      (sourceRightCompatible hsmall pair) (sourceRootAtom pair)).1 hright
    exact sourceRootNotMem pair (by
      simpa [sourceRootAtom, leftCanonicalAtomOfMember] using hvalue)

theorem sourceDisagreementEdge_target_exclusive
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (pair : SourcePair small n root)
    {first second : CanonicalAtom n}
    (hedge : sourceDisagreementEdge hsmall pair first second = true) :
    sourceExclusive hsmall pair second := by
  have hbits := (Bool.and_eq_true _ _).mp hedge |>.2
  unfold sourceDisagreementEdge disagreementBits leftOnly rightOnly at hbits
  unfold sourceExclusive
  cases hleftFirst : memberB (canonicalFamilyAtoms
      (sourceLeftCompatible pair)) first <;>
    cases hrightFirst : memberB (canonicalFamilyAtoms
      (sourceRightCompatible hsmall pair)) first <;>
    cases hleftSecond : memberB (canonicalFamilyAtoms
      (sourceLeftCompatible pair)) second <;>
    cases hrightSecond : memberB (canonicalFamilyAtoms
      (sourceRightCompatible hsmall pair)) second <;>
    simp_all

theorem connectedPathAtoms_exclusive
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    ∀ atom, atom ∈ connectedPathAtoms hsmall entry →
      sourceExclusive hsmall entry.val atom := by
  exact CWalk.all_vertices_of_start
    (sourceExclusive hsmall entry.val)
    (fun _ _ hedge _ =>
      sourceDisagreementEdge_target_exclusive hsmall entry.val hedge)
    (connectedSourcePath hsmall entry).walk
    (sourceRootAtom_exclusive hsmall entry.val)

/-! ## 3. Literal path/background subfamilies -/

def connectedPathTest
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : List Nat → Bool :=
  memberB (connectedPathValues hsmall entry)

def connectedPathLeftFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : PolymerFamily :=
  entry.val.1.val.filter (connectedPathTest hsmall entry)

def connectedBackgroundLeftFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : PolymerFamily :=
  entry.val.1.val.filter
    (fun polymer => !(connectedPathTest hsmall entry polymer))

def connectedPathRightFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : PolymerFamily :=
  entry.val.2.val.filter (connectedPathTest hsmall entry)

def connectedBackgroundRightFamily
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : PolymerFamily :=
  entry.val.2.val.filter
    (fun polymer => !(connectedPathTest hsmall entry polymer))

theorem filter_mem_sublists_of_mem_sublists
    {A : Type} [DecidableEq A]
    {ambient family : List A} (hambient : ambient.Nodup)
    (hfamily : family ∈ sublists ambient) (test : A → Bool) :
    family.filter test ∈ sublists ambient := by
  let mask := fun atom => memberB family atom && test atom
  have hsub : ambient.filter mask ∈ sublists ambient :=
    filter_mem_sublists _ _
  have heq : ambient.filter mask = family.filter test := by
    unfold mask
    have hcomm : ambient.filter (fun atom => memberB family atom && test atom) =
        ambient.filter (fun atom => test atom && memberB family atom) := by
      apply List.filter_congr
      intro atom _
      exact Bool.and_comm _ _
    rw [hcomm]
    rw [← List.filter_filter]
    rw [filter_memberB_eq_of_mem_sublists hambient hfamily]
  rw [← heq]
  exact hsub

theorem familyCompatibleB_filter_of_true
    {A : Type} [DecidableEq A]
    (compat : A → A → Bool)
    (hsymm : ∀ left right, compat left right = compat right left)
    {family : List A} (hnodup : family.Nodup)
    (hfamily : familyCompatibleB compat family = true)
    (test : A → Bool) :
    familyCompatibleB compat (family.filter test) = true := by
  apply familyCompatibleB_of_pairwise compat
    (List.filter_sublist.nodup hnodup)
  intro left hleft right hright hne
  exact familyCompatibleB_pairwise compat hsymm hfamily
    (List.mem_filter.mp hleft).1 (List.mem_filter.mp hright).1 hne

theorem canonicalFilteredFamily_mem
    {n : Nat} {family : PolymerFamily}
    (hfamily : family ∈ canonicalCompatibleAmbientFamilies n)
    (test : List Nat → Bool) :
    family.filter test ∈ canonicalCompatibleAmbientFamilies n := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  constructor
  · exact filter_mem_sublists_of_mem_sublists
      (canonicalSurfacePolymers_nodup n)
      (compatibleAmbientFamily_sublist hfamily) test
  · rw [← genericFamilyCompatibleB_eq_canonical n]
    apply familyCompatibleB_filter_of_true
      (canonicalPolymerCompatibleB n)
      (canonicalPolymerCompatibleB_symm n)
      (compatibleAmbientFamily_nodup hfamily)
    · rw [genericFamilyCompatibleB_eq_canonical n]
      exact (List.mem_filter.mp hfamily).2

theorem connectedPathLeftFamily_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    connectedPathLeftFamily hsmall entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem (sourceLeftCompatible entry.val)
    (connectedPathTest hsmall entry)

theorem connectedBackgroundLeftFamily_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    connectedBackgroundLeftFamily hsmall entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem (sourceLeftCompatible entry.val)
    (fun polymer => !(connectedPathTest hsmall entry polymer))

theorem connectedPathRightFamily_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    connectedPathRightFamily hsmall entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem (sourceRightCompatible hsmall entry.val)
    (connectedPathTest hsmall entry)

theorem connectedBackgroundRightFamily_mem
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    connectedBackgroundRightFamily hsmall entry ∈
      canonicalCompatibleAmbientFamilies n :=
  canonicalFilteredFamily_mem (sourceRightCompatible hsmall entry.val)
    (fun polymer => !(connectedPathTest hsmall entry polymer))

/-! ## 4. Exact activity factorization -/

theorem canonicalSurfaceFamilyActivity_filter_partition
    (w : Q') (n : Nat) (family : PolymerFamily)
    (test : List Nat → Bool) :
    canonicalSurfaceFamilyActivity w n family ≈
      canonicalSurfaceFamilyActivity w n (family.filter test) *
        canonicalSurfaceFamilyActivity w n
          (family.filter (fun polymer => !(test polymer))) := by
  simpa only [genericFamilyWeight_eq_canonical] using
    familyWeight_filter_partition (canonicalSurfaceActivity w n) test family

def connectedPathPairWeight
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n
      (connectedPathLeftFamily hsmall entry) *
    canonicalSurfaceFamilyActivity anchorCoupling n
      (connectedPathRightFamily hsmall entry)

def connectedBackgroundPairWeight
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling n
      (connectedBackgroundLeftFamily hsmall entry) *
    canonicalSurfaceFamilyActivity anchorCoupling n
      (connectedBackgroundRightFamily hsmall entry)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem connectedSourcePairWeight_factor
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    sourcePairWeight entry.val ≈
      connectedPathPairWeight hsmall entry *
        connectedBackgroundPairWeight hsmall entry := by
  have hleft := canonicalSurfaceFamilyActivity_filter_partition
    anchorCoupling n entry.val.1.val (connectedPathTest hsmall entry)
  have hright := canonicalSurfaceFamilyActivity_filter_partition
    anchorCoupling n entry.val.2.val (connectedPathTest hsmall entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold connectedPathPairWeight connectedBackgroundPairWeight
    connectedPathLeftFamily connectedBackgroundLeftFamily
    connectedPathRightFamily connectedBackgroundRightFamily
  ring_qeqv

/-! ## 5. Support/background recovery and injectivity -/

def connectedLeftColorSupport
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : List Nat :=
  familyUnionSupport n (connectedPathLeftFamily hsmall entry)

def connectedRightColorSupport
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : List Nat :=
  familyUnionSupport n (connectedPathRightFamily hsmall entry)

abbrev ConnectedCarrier :=
  (List Nat × List Nat) × (PolymerFamily × PolymerFamily)

def connectedCarrier
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) : ConnectedCarrier :=
  ((connectedLeftColorSupport hsmall entry,
      connectedRightColorSupport hsmall entry),
    (connectedBackgroundLeftFamily hsmall entry,
      connectedBackgroundRightFamily hsmall entry))

theorem ambientSubfamilies_eq_of_partition
    {A : Type} [DecidableEq A]
    {ambient first second : List A} (hambient : ambient.Nodup)
    (hfirst : first ∈ sublists ambient)
    (hsecond : second ∈ sublists ambient)
    (firstTest secondTest : A → Bool)
    (hkeep : first.filter firstTest = second.filter secondTest)
    (hdrop : first.filter (fun item => !(firstTest item)) =
      second.filter (fun item => !(secondTest item))) :
    first = second := by
  apply sublists_eq_of_mem_iff ambient first second hambient hfirst hsecond
  intro item
  constructor
  · intro hitem
    cases htest : firstTest item with
    | true =>
        have hin : item ∈ first.filter firstTest :=
          List.mem_filter.mpr ⟨hitem, htest⟩
        have hout : item ∈ second.filter secondTest := hkeep ▸ hin
        exact (List.mem_filter.mp hout).1
    | false =>
        have hin : item ∈ first.filter (fun atom => !(firstTest atom)) := by
          apply List.mem_filter.mpr
          simp only [hitem, true_and, htest, Bool.not_false]
        have hout : item ∈
            second.filter (fun atom => !(secondTest atom)) := hdrop ▸ hin
        exact (List.mem_filter.mp hout).1
  · intro hitem
    cases htest : secondTest item with
    | true =>
        have hin : item ∈ second.filter secondTest :=
          List.mem_filter.mpr ⟨hitem, htest⟩
        have hout : item ∈ first.filter firstTest := hkeep.symm ▸ hin
        exact (List.mem_filter.mp hout).1
    | false =>
        have hin : item ∈ second.filter (fun atom => !(secondTest atom)) := by
          apply List.mem_filter.mpr
          simp only [hitem, true_and, htest, Bool.not_false]
        have hout : item ∈
            first.filter (fun atom => !(firstTest atom)) := hdrop.symm ▸ hin
        exact (List.mem_filter.mp hout).1

theorem connectedCarrier_injective
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (first second : ConnectedSourceEntry root hsmall)
    (heq : connectedCarrier hsmall first = connectedCarrier hsmall second) :
    first = second := by
  have hleftSupport : connectedLeftColorSupport hsmall first =
      connectedLeftColorSupport hsmall second :=
    congrArg (fun carrier => carrier.1.1) heq
  have hrightSupport : connectedRightColorSupport hsmall first =
      connectedRightColorSupport hsmall second :=
    congrArg (fun carrier => carrier.1.2) heq
  have hleftBackground : connectedBackgroundLeftFamily hsmall first =
      connectedBackgroundLeftFamily hsmall second :=
    congrArg (fun carrier => carrier.2.1) heq
  have hrightBackground : connectedBackgroundRightFamily hsmall first =
      connectedBackgroundRightFamily hsmall second :=
    congrArg (fun carrier => carrier.2.2) heq
  have hleftPath : connectedPathLeftFamily hsmall first =
      connectedPathLeftFamily hsmall second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (connectedPathLeftFamily_mem hsmall first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (connectedPathLeftFamily_mem hsmall second)
    exact hrecoverFirst.symm.trans
      ((congrArg
        (fun support => ambientOrderedFamily n
          (canonicalSurfaceFamily n support)) hleftSupport).trans
        hrecoverSecond)
  have hrightPath : connectedPathRightFamily hsmall first =
      connectedPathRightFamily hsmall second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (connectedPathRightFamily_mem hsmall first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (connectedPathRightFamily_mem hsmall second)
    exact hrecoverFirst.symm.trans
      ((congrArg
        (fun support => ambientOrderedFamily n
          (canonicalSurfaceFamily n support)) hrightSupport).trans
        hrecoverSecond)
  have hleftSource : first.val.1.val = second.val.1.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup n)
      (compatibleAmbientFamily_sublist (sourceLeftCompatible first.val))
      (compatibleAmbientFamily_sublist (sourceLeftCompatible second.val))
      (connectedPathTest hsmall first)
      (connectedPathTest hsmall second) hleftPath hleftBackground
  have hrightSource : first.val.2.val = second.val.2.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup n)
      (compatibleAmbientFamily_sublist
        (sourceRightCompatible hsmall first.val))
      (compatibleAmbientFamily_sublist
        (sourceRightCompatible hsmall second.val))
      (connectedPathTest hsmall first)
      (connectedPathTest hsmall second) hrightPath hrightBackground
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hleftSource
  · exact Subtype.ext hrightSource

end YMGap.Continuum.Z4CanonicalConnectedPathCarrier

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalConnectedPathCarrier.firstTrueOr_spec
#print axioms YMGap.Continuum.Z4CanonicalConnectedPathCarrier.sourceOutsideAtom_spec
#print axioms YMGap.Continuum.Z4CanonicalConnectedPathCarrier.connectedPathAtoms_exclusive
#print axioms YMGap.Continuum.Z4CanonicalConnectedPathCarrier.canonicalFilteredFamily_mem
#print axioms YMGap.Continuum.Z4CanonicalConnectedPathCarrier.connectedSourcePairWeight_factor
#print axioms YMGap.Continuum.Z4CanonicalConnectedPathCarrier.connectedCarrier_injective
