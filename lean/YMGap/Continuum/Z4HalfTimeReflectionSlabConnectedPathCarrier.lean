/-
# Recoverable colored carriers for the slab connected residue

The slab switch leaves a literal connected two-replica residue.  A connected
entry deterministically selects a complement-hitting polymer in the boundary
replica and then a marked root whose disagreement component reaches it.  The
resulting simple disagreement path is split by source color.  Its two union
supports, together with the two path-deleted backgrounds, recover the source
entry injectively and factor its exact rational activity.

The right background is proved to remain slab-supported.  This is the key
normalization feature needed later: summing carrier backgrounds produces the
actual ambient partition times the actual slab-supported partition, not the
square of the ambient partition.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
import YMGap.Continuum.Z4CanonicalConnectedPathCarrier
import YMGap.Continuum.Z4CanonicalMarkedRootSeparation

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteFamilyWeightPartition
open YMGap.Continuum.FiniteMarkedRootSwitch
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev SlabPolymerFamily := List (List Nat)

/-! ## 1. Deterministic outside endpoint and marked root -/

theorem connectedSlabCylinderSourcePair_reach_true
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate)
    (hpair : pair ∈ connectedSlabCylinderSourcePairs) :
    slabBoundaryOutsideMarkedReachB
      (slabCylinderSourceLeftCompatible pair)
      (slabCylinderSourceRightCompatible pair) roots = true := by
  have htest := (List.mem_filter.mp hpair).2
  unfold slabCylinderSourceSeparatedB at htest
  cases hreach : slabBoundaryOutsideMarkedReachB
      (slabCylinderSourceLeftCompatible pair)
      (slabCylinderSourceRightCompatible pair) roots <;> simp_all

def slabSourceOutsideTest
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate)
    (atom : CanonicalAtom (extent + 1)) : Bool :=
  (!(canonicalPolymerSlabSupportedB extent atom.val)) &&
    canonicalMarkedCut
      (slabCylinderSourceLeftCompatible pair)
      (slabCylinderSourceRightCompatible pair) roots atom

def slabSourceOutsideAtom
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (pair : SlabCylinderSourcePair extent roots predicate) :
    CanonicalAtom (extent + 1) :=
  firstTrueOr defaultRoot (slabSourceOutsideTest pair)
    (canonicalFamilyAtoms (slabCylinderSourceLeftCompatible pair))

theorem slabSourceOutsideAtom_spec
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (pair : SlabCylinderSourcePair extent roots predicate)
    (hpair : pair ∈ connectedSlabCylinderSourcePairs) :
    slabSourceOutsideTest pair
        (slabSourceOutsideAtom defaultRoot pair) = true ∧
      slabSourceOutsideAtom defaultRoot pair ∈
        canonicalFamilyAtoms (slabCylinderSourceLeftCompatible pair) := by
  apply firstTrueOr_spec
  simpa [slabBoundaryOutsideMarkedReachB, slabSourceOutsideTest] using
    connectedSlabCylinderSourcePair_reach_true pair hpair

theorem slabSourceOutsideAtom_not_supported
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (pair : SlabCylinderSourcePair extent roots predicate)
    (hpair : pair ∈ connectedSlabCylinderSourcePairs) :
    canonicalPolymerSlabSupportedB extent
      (slabSourceOutsideAtom defaultRoot pair).val = false := by
  have hnot := (Bool.and_eq_true _ _).mp
    (slabSourceOutsideAtom_spec defaultRoot pair hpair).1 |>.1
  cases hsupported : canonicalPolymerSlabSupportedB extent
      (slabSourceOutsideAtom defaultRoot pair).val <;> simp_all

theorem slabSourceOutsideAtom_hits_complement
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (pair : SlabCylinderSourcePair extent roots predicate)
    (hpair : pair ∈ connectedSlabCylinderSourcePairs) :
    canonicalPolymerHitsSlabComplementB extent
      (slabSourceOutsideAtom defaultRoot pair).val = true :=
  (canonicalPolymerSlabSupportedB_false_iff_hit extent _).1
    (slabSourceOutsideAtom_not_supported defaultRoot pair hpair)

theorem slabSourceOutsideAtom_markedCut
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (pair : SlabCylinderSourcePair extent roots predicate)
    (hpair : pair ∈ connectedSlabCylinderSourcePairs) :
    canonicalMarkedCut
      (slabCylinderSourceLeftCompatible pair)
      (slabCylinderSourceRightCompatible pair) roots
      (slabSourceOutsideAtom defaultRoot pair) = true :=
  (Bool.and_eq_true _ _).mp
    (slabSourceOutsideAtom_spec defaultRoot pair hpair).1 |>.2

def slabSourceRootTest
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (pair : SlabCylinderSourcePair extent roots predicate)
    (root : CanonicalAtom (extent + 1)) : Bool :=
  canonicalDisagreementCut
    (slabCylinderSourceLeftCompatible pair)
    (slabCylinderSourceRightCompatible pair) root
    (slabSourceOutsideAtom defaultRoot pair)

def slabSourceRootAtom
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (pair : SlabCylinderSourcePair extent roots predicate) :
    CanonicalAtom (extent + 1) :=
  firstTrueOr defaultRoot (slabSourceRootTest defaultRoot pair) roots

theorem slabSourceRootAtom_spec
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (pair : SlabCylinderSourcePair extent roots predicate)
    (hpair : pair ∈ connectedSlabCylinderSourcePairs) :
    slabSourceRootTest defaultRoot pair
        (slabSourceRootAtom defaultRoot pair) = true ∧
      slabSourceRootAtom defaultRoot pair ∈ roots := by
  apply firstTrueOr_spec
  have hcut := slabSourceOutsideAtom_markedCut defaultRoot pair hpair
  obtain ⟨root, hroot, hreach⟩ := canonicalMarkedCut_true_has_root
    (slabCylinderSourceLeftCompatible pair)
    (slabCylinderSourceRightCompatible pair) roots
    (slabSourceOutsideAtom defaultRoot pair) hcut
  exact List.any_eq_true.mpr ⟨root, hroot, by
    simpa [slabSourceRootTest] using hreach⟩

/-! ## 2. The deterministic simple disagreement path -/

def slabSourceDisagreementEdge
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    CanonicalAtom (extent + 1) → CanonicalAtom (extent + 1) → Bool :=
  disagreementEdge (canonicalAmbientAtoms (extent + 1))
    (canonicalAtomCompatibleB (extent + 1))
    (memberB (canonicalFamilyAtoms
      (slabCylinderSourceLeftCompatible pair)))
    (memberB (canonicalFamilyAtoms
      (slabCylinderSourceRightCompatible pair)))

abbrev SlabConnectedSourceEntry
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :=
  {pair : SlabCylinderSourcePair extent roots predicate //
    pair ∈ connectedSlabCylinderSourcePairs}

def slabConnectedSourcePath
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    CWalk.Simple (slabSourceDisagreementEdge entry.val)
      (slabSourceRootAtom defaultRoot entry.val)
      (slabSourceOutsideAtom defaultRoot entry.val) :=
  simpleWalkOfWarshall (slabSourceDisagreementEdge entry.val)
    (canonicalAmbientAtoms (extent + 1))
    (slabSourceRootAtom defaultRoot entry.val)
    (slabSourceOutsideAtom defaultRoot entry.val)
    (slabSourceRootAtom_spec defaultRoot entry.val entry.property).1

def slabConnectedPathAtoms
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    List (CanonicalAtom (extent + 1)) :=
  (slabConnectedSourcePath defaultRoot entry).walk.vertices

def slabConnectedPathValues
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    List (List Nat) :=
  (slabConnectedPathAtoms defaultRoot entry).map Subtype.val

def slabSourceExclusive
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate)
    (atom : CanonicalAtom (extent + 1)) : Prop :=
  (memberB (canonicalFamilyAtoms
        (slabCylinderSourceLeftCompatible pair)) atom = true ∧
      memberB (canonicalFamilyAtoms
        (slabCylinderSourceRightCompatible pair)) atom = false) ∨
    (memberB (canonicalFamilyAtoms
        (slabCylinderSourceLeftCompatible pair)) atom = false ∧
      memberB (canonicalFamilyAtoms
        (slabCylinderSourceRightCompatible pair)) atom = true)

theorem slabSourceRootAtom_exclusive
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabSourceExclusive entry.val
      (slabSourceRootAtom defaultRoot entry.val) := by
  let root := slabSourceRootAtom defaultRoot entry.val
  let outside := slabSourceOutsideAtom defaultRoot entry.val
  have hrootSupported : canonicalPolymerSlabSupportedB extent
      root.val = true :=
    hrootsSupported root
      (slabSourceRootAtom_spec defaultRoot entry.val entry.property).2
  have houtsideUnsupported : canonicalPolymerSlabSupportedB extent
      outside.val = false :=
    slabSourceOutsideAtom_not_supported defaultRoot entry.val entry.property
  have hne : root ≠ outside := by
    intro heq
    have heqVal : root.val = outside.val := congrArg Subtype.val heq
    rw [← heqVal, hrootSupported] at houtsideUnsupported
    cases houtsideUnsupported
  have hreach : canonicalDisagreementCut
      (slabCylinderSourceLeftCompatible entry.val)
      (slabCylinderSourceRightCompatible entry.val) root outside = true :=
    (slabSourceRootAtom_spec defaultRoot entry.val entry.property).1
  have hwalk := warshallSound
    (slabSourceDisagreementEdge entry.val)
    (canonicalAmbientAtoms (extent + 1)) root outside hreach
  obtain ⟨next, hedge⟩ := dWalk_start_edge_of_ne _ hwalk hne
  exact disagreementEdge_source_exclusive
    (canonicalAmbientAtoms (extent + 1))
    (canonicalAtomCompatibleB (extent + 1))
    (memberB (canonicalFamilyAtoms
      (slabCylinderSourceLeftCompatible entry.val)))
    (memberB (canonicalFamilyAtoms
      (slabCylinderSourceRightCompatible entry.val))) hedge

theorem slabSourceDisagreementEdge_target_exclusive
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate)
    {first second : CanonicalAtom (extent + 1)}
    (hedge : slabSourceDisagreementEdge pair first second = true) :
    slabSourceExclusive pair second := by
  have hbits := (Bool.and_eq_true _ _).mp hedge |>.2
  unfold slabSourceDisagreementEdge disagreementBits leftOnly rightOnly
    at hbits
  unfold slabSourceExclusive
  cases hleftFirst : memberB (canonicalFamilyAtoms
      (slabCylinderSourceLeftCompatible pair)) first <;>
    cases hrightFirst : memberB (canonicalFamilyAtoms
      (slabCylinderSourceRightCompatible pair)) first <;>
    cases hleftSecond : memberB (canonicalFamilyAtoms
      (slabCylinderSourceLeftCompatible pair)) second <;>
    cases hrightSecond : memberB (canonicalFamilyAtoms
      (slabCylinderSourceRightCompatible pair)) second <;>
    simp_all

theorem slabConnectedPathAtoms_exclusive
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    ∀ atom, atom ∈ slabConnectedPathAtoms defaultRoot entry →
      slabSourceExclusive entry.val atom := by
  exact CWalk.all_vertices_of_start
    (slabSourceExclusive entry.val)
    (fun _ _ hedge _ =>
      slabSourceDisagreementEdge_target_exclusive entry.val hedge)
    (slabConnectedSourcePath defaultRoot entry).walk
    (slabSourceRootAtom_exclusive defaultRoot hrootsSupported entry)

/-! ## 3. Literal path and background subfamilies -/

def slabConnectedPathTest
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    List Nat → Bool :=
  memberB (slabConnectedPathValues defaultRoot entry)

def slabConnectedPathLeftFamily
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    SlabPolymerFamily :=
  entry.val.1.val.filter (slabConnectedPathTest defaultRoot entry)

def slabConnectedBackgroundLeftFamily
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    SlabPolymerFamily :=
  entry.val.1.val.filter
    (fun polymer => !(slabConnectedPathTest defaultRoot entry polymer))

def slabConnectedPathRightFamily
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    SlabPolymerFamily :=
  entry.val.2.val.filter (slabConnectedPathTest defaultRoot entry)

def slabConnectedBackgroundRightFamily
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    SlabPolymerFamily :=
  entry.val.2.val.filter
    (fun polymer => !(slabConnectedPathTest defaultRoot entry polymer))

theorem slabConnectedPathLeftFamily_mem
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabConnectedPathLeftFamily defaultRoot entry ∈
      canonicalCompatibleAmbientFamilies (extent + 1) :=
  canonicalFilteredFamily_mem
    (slabCylinderSourceLeftCompatible entry.val)
    (slabConnectedPathTest defaultRoot entry)

theorem slabConnectedBackgroundLeftFamily_mem
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabConnectedBackgroundLeftFamily defaultRoot entry ∈
      canonicalCompatibleAmbientFamilies (extent + 1) :=
  canonicalFilteredFamily_mem
    (slabCylinderSourceLeftCompatible entry.val)
    (fun polymer => !(slabConnectedPathTest defaultRoot entry polymer))

theorem slabConnectedPathRightFamily_mem
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabConnectedPathRightFamily defaultRoot entry ∈
      canonicalCompatibleAmbientFamilies (extent + 1) :=
  canonicalFilteredFamily_mem
    (slabCylinderSourceRightCompatible entry.val)
    (slabConnectedPathTest defaultRoot entry)

theorem slabConnectedBackgroundRightFamily_mem
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabConnectedBackgroundRightFamily defaultRoot entry ∈
      canonicalCompatibleAmbientFamilies (extent + 1) :=
  canonicalFilteredFamily_mem
    (slabCylinderSourceRightCompatible entry.val)
    (fun polymer => !(slabConnectedPathTest defaultRoot entry polymer))

theorem slabConnectedBackgroundRightFamily_mem_supported
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabConnectedBackgroundRightFamily defaultRoot entry ∈
      canonicalSlabSupportedFamilies extent := by
  apply mem_canonicalSlabSupportedFamilies_iff.mpr
  constructor
  · exact slabConnectedBackgroundRightFamily_mem defaultRoot entry
  · rw [canonicalFamilySlabSupportedB_eq_polymerAll]
    apply List.all_eq_true.mpr
    intro polymer hpolymer
    have hsource := mem_canonicalSlabSupportedFamilies_iff.mp
      (slabCylinderSourceRightSupported entry.val) |>.2
    rw [canonicalFamilySlabSupportedB_eq_polymerAll] at hsource
    exact List.all_eq_true.mp hsource polymer
      (List.mem_filter.mp hpolymer).1

/-! ## 4. Exact activity factorization -/

def slabConnectedPathPairWeight
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
      (slabConnectedPathLeftFamily defaultRoot entry) *
    canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
      (slabConnectedPathRightFamily defaultRoot entry)

def slabConnectedBackgroundPairWeight
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
      (slabConnectedBackgroundLeftFamily defaultRoot entry) *
    canonicalSurfaceFamilyActivity anchorCoupling (extent + 1)
      (slabConnectedBackgroundRightFamily defaultRoot entry)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem slabConnectedSourcePairWeight_factor
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    slabCylinderSourcePairWeight entry.val ≈
      slabConnectedPathPairWeight defaultRoot entry *
        slabConnectedBackgroundPairWeight defaultRoot entry := by
  have hleft := canonicalSurfaceFamilyActivity_filter_partition
    anchorCoupling (extent + 1) entry.val.1.val
      (slabConnectedPathTest defaultRoot entry)
  have hright := canonicalSurfaceFamilyActivity_filter_partition
    anchorCoupling (extent + 1) entry.val.2.val
      (slabConnectedPathTest defaultRoot entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both hleft hright) ?_
  unfold slabConnectedPathPairWeight slabConnectedBackgroundPairWeight
    slabConnectedPathLeftFamily slabConnectedBackgroundLeftFamily
    slabConnectedPathRightFamily slabConnectedBackgroundRightFamily
  ring_qeqv

/-! ## 5. Support/background recovery and injectivity -/

def slabConnectedLeftColorSupport
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) : List Nat :=
  familyUnionSupport (extent + 1)
    (slabConnectedPathLeftFamily defaultRoot entry)

def slabConnectedRightColorSupport
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) : List Nat :=
  familyUnionSupport (extent + 1)
    (slabConnectedPathRightFamily defaultRoot entry)

abbrev SlabConnectedCarrier :=
  (List Nat × List Nat) × (SlabPolymerFamily × SlabPolymerFamily)

def slabConnectedCarrier
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    SlabConnectedCarrier :=
  ((slabConnectedLeftColorSupport defaultRoot entry,
      slabConnectedRightColorSupport defaultRoot entry),
    (slabConnectedBackgroundLeftFamily defaultRoot entry,
      slabConnectedBackgroundRightFamily defaultRoot entry))

theorem slabConnectedCarrier_injective
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (first second : SlabConnectedSourceEntry extent roots predicate)
    (heq : slabConnectedCarrier defaultRoot first =
      slabConnectedCarrier defaultRoot second) :
    first = second := by
  have hleftSupport : slabConnectedLeftColorSupport defaultRoot first =
      slabConnectedLeftColorSupport defaultRoot second :=
    congrArg (fun carrier => carrier.1.1) heq
  have hrightSupport : slabConnectedRightColorSupport defaultRoot first =
      slabConnectedRightColorSupport defaultRoot second :=
    congrArg (fun carrier => carrier.1.2) heq
  have hleftBackground :
      slabConnectedBackgroundLeftFamily defaultRoot first =
        slabConnectedBackgroundLeftFamily defaultRoot second :=
    congrArg (fun carrier => carrier.2.1) heq
  have hrightBackground :
      slabConnectedBackgroundRightFamily defaultRoot first =
        slabConnectedBackgroundRightFamily defaultRoot second :=
    congrArg (fun carrier => carrier.2.2) heq
  have hleftPath : slabConnectedPathLeftFamily defaultRoot first =
      slabConnectedPathLeftFamily defaultRoot second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (slabConnectedPathLeftFamily_mem defaultRoot first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (slabConnectedPathLeftFamily_mem defaultRoot second)
    exact hrecoverFirst.symm.trans
      ((congrArg
        (fun support => ambientOrderedFamily (extent + 1)
          (canonicalSurfaceFamily (extent + 1) support))
        hleftSupport).trans hrecoverSecond)
  have hrightPath : slabConnectedPathRightFamily defaultRoot first =
      slabConnectedPathRightFamily defaultRoot second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (slabConnectedPathRightFamily_mem defaultRoot first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (slabConnectedPathRightFamily_mem defaultRoot second)
    exact hrecoverFirst.symm.trans
      ((congrArg
        (fun support => ambientOrderedFamily (extent + 1)
          (canonicalSurfaceFamily (extent + 1) support))
        hrightSupport).trans hrecoverSecond)
  have hleftSource : first.val.1.val = second.val.1.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup (extent + 1))
      (compatibleAmbientFamily_sublist
        (slabCylinderSourceLeftCompatible first.val))
      (compatibleAmbientFamily_sublist
        (slabCylinderSourceLeftCompatible second.val))
      (slabConnectedPathTest defaultRoot first)
      (slabConnectedPathTest defaultRoot second)
      hleftPath hleftBackground
  have hrightSource : first.val.2.val = second.val.2.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup (extent + 1))
      (compatibleAmbientFamily_sublist
        (slabCylinderSourceRightCompatible first.val))
      (compatibleAmbientFamily_sublist
        (slabCylinderSourceRightCompatible second.val))
      (slabConnectedPathTest defaultRoot first)
      (slabConnectedPathTest defaultRoot second)
      hrightPath hrightBackground
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hleftSource
  · exact Subtype.ext hrightSource

#print axioms connectedSlabCylinderSourcePair_reach_true
#print axioms slabSourceOutsideAtom_spec
#print axioms slabSourceRootAtom_spec
#print axioms slabConnectedPathAtoms_exclusive
#print axioms slabConnectedBackgroundRightFamily_mem_supported
#print axioms slabConnectedSourcePairWeight_factor
#print axioms slabConnectedCarrier_injective

end YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
