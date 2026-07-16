/-
# Recoverable carriers for the affine shifted-boundary residue

For a connected shifted cylinder pair we choose, by finite Boolean search,
the first outside left atom and then the first marked root reaching it.  The
loop-erased disagreement path is split into its two source colors.  Its color
supports together with the two compatible backgrounds recover the original
pair, so the construction is an injection rather than a compactness step.

The final section proves the only new geometric fact needed by the tail: if
an explicit shifted outer subbox is contained in the affine embedded cell,
then the carrier selected above exits that subbox and has at least
`distance + 2` faces.
-/

import YMGap.Continuum.Z4TimeShiftedCylinderSwitchSummation
import YMGap.Continuum.Z4ShiftedSubboxCarrierTail
import YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize

namespace YMGap.Continuum.Z4TimeShiftedConnectedCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteDisagreementReverseRecovery
open YMGap.Continuum.FiniteMarkedRootSwitch
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryComponentSwitch
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4TimeShiftedCylinderSwitchSummation
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedEmbeddedRegion
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport
open Dir4

abbrev PolymerFamily := List (List Nat)

abbrev TimeShiftConnectedEntry
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) :=
  {pair : TimeShiftCylinderSourcePair shift base roots predicate //
    pair ∈ connectedTimeShiftCylinderSourcePairs}

/-! ## 1. Deterministic outside endpoint and marked root -/

theorem timeShiftConnectedReach_true
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftBoundaryOutsideMarkedReachB
      (timeShiftCylinderSourceLeftCompatible entry.val)
      (timeShiftCylinderSourceRightCompatible entry.val) roots = true := by
  have htest := (List.mem_filter.mp entry.property).2
  unfold timeShiftCylinderSourceSeparatedB at htest
  cases hreach : timeShiftBoundaryOutsideMarkedReachB
      (timeShiftCylinderSourceLeftCompatible entry.val)
      (timeShiftCylinderSourceRightCompatible entry.val) roots <;>
    simp_all

def timeShiftBoundaryDefaultAtom
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    CanonicalAtom (base + shift) :=
  let witness := allFalseWitness
    (targetRootInsideTimeShiftB shift base) pair.1.val
    (mem_timeShiftBoundaryTargetFamilies_iff.mp
      (timeShiftCylinderSourceLeftBoundary pair)).2
  ⟨witness.1, compatibleAmbientFamily_member_ambient
    (timeShiftCylinderSourceLeftCompatible pair) witness.2.1⟩

def timeShiftSourceOutsideTest
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate)
    (atom : CanonicalAtom (base + shift)) : Bool :=
  (!(targetRootInsideTimeShiftB shift base atom.val)) &&
    canonicalMarkedCut
      (timeShiftCylinderSourceLeftCompatible pair)
      (timeShiftCylinderSourceRightCompatible pair) roots atom

def timeShiftSourceOutsideAtom
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    CanonicalAtom (base + shift) :=
  firstTrueOr (timeShiftBoundaryDefaultAtom pair)
    (timeShiftSourceOutsideTest pair)
    (canonicalFamilyAtoms (timeShiftCylinderSourceLeftCompatible pair))

theorem timeShiftSourceOutsideAtom_spec
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftSourceOutsideTest entry.val
        (timeShiftSourceOutsideAtom entry.val) = true ∧
      timeShiftSourceOutsideAtom entry.val ∈
        canonicalFamilyAtoms
          (timeShiftCylinderSourceLeftCompatible entry.val) := by
  apply firstTrueOr_spec
  simpa [timeShiftBoundaryOutsideMarkedReachB,
    timeShiftSourceOutsideTest] using timeShiftConnectedReach_true entry

theorem timeShiftSourceOutsideAtom_outside
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    targetRootInsideTimeShiftB shift base
      (timeShiftSourceOutsideAtom entry.val).val = false := by
  have htest := (Bool.and_eq_true _ _).mp
    (timeShiftSourceOutsideAtom_spec entry).1 |>.1
  cases hinside : targetRootInsideTimeShiftB shift base
      (timeShiftSourceOutsideAtom entry.val).val <;> simp_all

theorem timeShiftSourceOutsideAtom_markedCut
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    canonicalMarkedCut
      (timeShiftCylinderSourceLeftCompatible entry.val)
      (timeShiftCylinderSourceRightCompatible entry.val) roots
      (timeShiftSourceOutsideAtom entry.val) = true :=
  (Bool.and_eq_true _ _).mp
    (timeShiftSourceOutsideAtom_spec entry).1 |>.2

def timeShiftSourceRootTest
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate)
    (root : CanonicalAtom (base + shift)) : Bool :=
  canonicalDisagreementCut
    (timeShiftCylinderSourceLeftCompatible pair)
    (timeShiftCylinderSourceRightCompatible pair) root
    (timeShiftSourceOutsideAtom pair)

def timeShiftSourceRootAtom
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    CanonicalAtom (base + shift) :=
  firstTrueOr (timeShiftSourceOutsideAtom pair)
    (timeShiftSourceRootTest pair) roots

theorem timeShiftSourceRootAtom_spec
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftSourceRootTest entry.val
        (timeShiftSourceRootAtom entry.val) = true ∧
      timeShiftSourceRootAtom entry.val ∈ roots := by
  apply firstTrueOr_spec
  have hmarked := timeShiftSourceOutsideAtom_markedCut entry
  simpa [canonicalMarkedCut, markedRootCut,
    timeShiftSourceRootTest] using hmarked

theorem timeShiftSourceRootAtom_reaches
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    canonicalDisagreementCut
      (timeShiftCylinderSourceLeftCompatible entry.val)
      (timeShiftCylinderSourceRightCompatible entry.val)
      (timeShiftSourceRootAtom entry.val)
      (timeShiftSourceOutsideAtom entry.val) = true :=
  (timeShiftSourceRootAtom_spec entry).1

/-! ## 2. The loop-erased disagreement path and its two colors -/

def timeShiftSourceDisagreementEdge
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate) :
    CanonicalAtom (base + shift) →
      CanonicalAtom (base + shift) → Bool :=
  disagreementEdge (canonicalAmbientAtoms (base + shift))
    (canonicalAtomCompatibleB (base + shift))
    (memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceLeftCompatible pair)))
    (memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceRightCompatible pair)))

def timeShiftConnectedPath
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    CWalk.Simple (timeShiftSourceDisagreementEdge entry.val)
      (timeShiftSourceRootAtom entry.val)
      (timeShiftSourceOutsideAtom entry.val) :=
  simpleWalkOfWarshall (timeShiftSourceDisagreementEdge entry.val)
    (canonicalAmbientAtoms (base + shift))
    (timeShiftSourceRootAtom entry.val)
    (timeShiftSourceOutsideAtom entry.val)
    (timeShiftSourceRootAtom_reaches entry)

def timeShiftConnectedPathAtoms
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    List (CanonicalAtom (base + shift)) :=
  (timeShiftConnectedPath entry).walk.vertices

def timeShiftConnectedPathValues
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    List (List Nat) :=
  (timeShiftConnectedPathAtoms entry).map Subtype.val

def timeShiftSourceExclusive
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate)
    (atom : CanonicalAtom (base + shift)) : Prop :=
  (memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceLeftCompatible pair)) atom = true ∧
    memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceRightCompatible pair)) atom = false) ∨
  (memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceLeftCompatible pair)) atom = false ∧
    memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceRightCompatible pair)) atom = true)

theorem timeShiftSourceRootAtom_exclusive
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftSourceExclusive entry.val
      (timeShiftSourceRootAtom entry.val) := by
  let root := timeShiftSourceRootAtom entry.val
  let outside := timeShiftSourceOutsideAtom entry.val
  have hrootInside : targetRootInsideTimeShiftB
      shift base root.val = true :=
    hrootsInside root (timeShiftSourceRootAtom_spec entry).2
  have houtside : targetRootInsideTimeShiftB
      shift base outside.val = false :=
    timeShiftSourceOutsideAtom_outside entry
  have hne : root ≠ outside := by
    intro heq
    have hrootAtOutside := hrootInside
    rw [heq] at hrootAtOutside
    rw [hrootAtOutside] at houtside
    exact Bool.false_ne_true houtside.symm
  have hwalk := warshallSound
    (timeShiftSourceDisagreementEdge entry.val)
    (canonicalAmbientAtoms (base + shift)) root outside
    (timeShiftSourceRootAtom_reaches entry)
  obtain ⟨next, hedge⟩ := dWalk_start_edge_of_ne _ hwalk hne
  rcases disagreementEdge_source_exclusive _ _ _ _ hedge with
    hleft | hright
  · exact Or.inl hleft
  · exact Or.inr hright

theorem timeShiftSourceDisagreementEdge_target_exclusive
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (pair : TimeShiftCylinderSourcePair shift base roots predicate)
    {first second : CanonicalAtom (base + shift)}
    (hedge : timeShiftSourceDisagreementEdge pair first second = true) :
    timeShiftSourceExclusive pair second := by
  have hbits := (Bool.and_eq_true _ _).mp hedge |>.2
  unfold timeShiftSourceDisagreementEdge disagreementBits
    leftOnly rightOnly at hbits
  unfold timeShiftSourceExclusive
  cases hleftFirst : memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceLeftCompatible pair)) first <;>
    cases hrightFirst : memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceRightCompatible pair)) first <;>
    cases hleftSecond : memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceLeftCompatible pair)) second <;>
    cases hrightSecond : memberB (canonicalFamilyAtoms
      (timeShiftCylinderSourceRightCompatible pair)) second <;>
    simp_all

theorem timeShiftConnectedPathAtoms_exclusive
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    ∀ atom, atom ∈ timeShiftConnectedPathAtoms entry →
      timeShiftSourceExclusive entry.val atom := by
  exact CWalk.all_vertices_of_start
    (timeShiftSourceExclusive entry.val)
    (fun _ _ hedge _ =>
      timeShiftSourceDisagreementEdge_target_exclusive entry.val hedge)
    (timeShiftConnectedPath entry).walk
    (timeShiftSourceRootAtom_exclusive hrootsInside entry)

def timeShiftConnectedPathTest
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    List Nat → Bool :=
  memberB (timeShiftConnectedPathValues entry)

def timeShiftConnectedPathLeftFamily
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    PolymerFamily :=
  entry.val.1.val.filter (timeShiftConnectedPathTest entry)

def timeShiftConnectedBackgroundLeftFamily
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    PolymerFamily :=
  entry.val.1.val.filter
    (fun polymer => !(timeShiftConnectedPathTest entry polymer))

def timeShiftConnectedPathRightFamily
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    PolymerFamily :=
  entry.val.2.val.filter (timeShiftConnectedPathTest entry)

def timeShiftConnectedBackgroundRightFamily
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    PolymerFamily :=
  entry.val.2.val.filter
    (fun polymer => !(timeShiftConnectedPathTest entry polymer))

theorem timeShiftConnectedPathLeftFamily_mem
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftConnectedPathLeftFamily entry ∈
      canonicalCompatibleAmbientFamilies (base + shift) :=
  canonicalFilteredFamily_mem
    (timeShiftCylinderSourceLeftCompatible entry.val)
    (timeShiftConnectedPathTest entry)

theorem timeShiftConnectedBackgroundLeftFamily_mem
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftConnectedBackgroundLeftFamily entry ∈
      canonicalCompatibleAmbientFamilies (base + shift) :=
  canonicalFilteredFamily_mem
    (timeShiftCylinderSourceLeftCompatible entry.val)
    (fun polymer => !(timeShiftConnectedPathTest entry polymer))

theorem timeShiftConnectedPathRightFamily_mem
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftConnectedPathRightFamily entry ∈
      canonicalCompatibleAmbientFamilies (base + shift) :=
  canonicalFilteredFamily_mem
    (timeShiftCylinderSourceRightCompatible entry.val)
    (timeShiftConnectedPathTest entry)

theorem timeShiftConnectedBackgroundRightFamily_mem
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftConnectedBackgroundRightFamily entry ∈
      canonicalCompatibleAmbientFamilies (base + shift) :=
  canonicalFilteredFamily_mem
    (timeShiftCylinderSourceRightCompatible entry.val)
    (fun polymer => !(timeShiftConnectedPathTest entry polymer))

theorem timeShiftConnectedBackgroundRightFamily_mem_embedded
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftConnectedBackgroundRightFamily entry ∈
      timeShiftEmbeddedTargetFamilies shift base := by
  apply mem_timeShiftEmbeddedTargetFamilies_iff.mpr
  refine ⟨timeShiftConnectedBackgroundRightFamily_mem entry, ?_⟩
  rw [List.all_eq_true]
  intro support hsupport
  have hsource : support ∈ entry.val.2.val :=
    (List.mem_filter.mp hsupport).1
  exact List.all_eq_true.mp
    (mem_timeShiftEmbeddedTargetFamilies_iff.mp
      (timeShiftCylinderSourceRightEmbedded entry.val)).2
    support hsource

/-! ## 3. Support/background recovery -/

def timeShiftConnectedLeftColorSupport
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) : List Nat :=
  familyUnionSupport (base + shift)
    (timeShiftConnectedPathLeftFamily entry)

def timeShiftConnectedRightColorSupport
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) : List Nat :=
  familyUnionSupport (base + shift)
    (timeShiftConnectedPathRightFamily entry)

def timeShiftConnectedCarrier
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    ConnectedCarrier :=
  ((timeShiftConnectedLeftColorSupport entry,
      timeShiftConnectedRightColorSupport entry),
    (timeShiftConnectedBackgroundLeftFamily entry,
      timeShiftConnectedBackgroundRightFamily entry))

theorem timeShiftConnectedCarrier_injective
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (first second : TimeShiftConnectedEntry shift base roots predicate)
    (heq : timeShiftConnectedCarrier first =
      timeShiftConnectedCarrier second) : first = second := by
  have hleftSupport : timeShiftConnectedLeftColorSupport first =
      timeShiftConnectedLeftColorSupport second :=
    congrArg (fun carrier => carrier.1.1) heq
  have hrightSupport : timeShiftConnectedRightColorSupport first =
      timeShiftConnectedRightColorSupport second :=
    congrArg (fun carrier => carrier.1.2) heq
  have hleftBackground : timeShiftConnectedBackgroundLeftFamily first =
      timeShiftConnectedBackgroundLeftFamily second :=
    congrArg (fun carrier => carrier.2.1) heq
  have hrightBackground : timeShiftConnectedBackgroundRightFamily first =
      timeShiftConnectedBackgroundRightFamily second :=
    congrArg (fun carrier => carrier.2.2) heq
  have hleftPath : timeShiftConnectedPathLeftFamily first =
      timeShiftConnectedPathLeftFamily second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (timeShiftConnectedPathLeftFamily_mem first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (timeShiftConnectedPathLeftFamily_mem second)
    exact hrecoverFirst.symm.trans
      ((congrArg
        (fun support => ambientOrderedFamily (base + shift)
          (canonicalSurfaceFamily (base + shift) support))
        hleftSupport).trans hrecoverSecond)
  have hrightPath : timeShiftConnectedPathRightFamily first =
      timeShiftConnectedPathRightFamily second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (timeShiftConnectedPathRightFamily_mem first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (timeShiftConnectedPathRightFamily_mem second)
    exact hrecoverFirst.symm.trans
      ((congrArg
        (fun support => ambientOrderedFamily (base + shift)
          (canonicalSurfaceFamily (base + shift) support))
        hrightSupport).trans hrecoverSecond)
  have hleftSource : first.val.1.val = second.val.1.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup (base + shift))
      (compatibleAmbientFamily_sublist
        (timeShiftCylinderSourceLeftCompatible first.val))
      (compatibleAmbientFamily_sublist
        (timeShiftCylinderSourceLeftCompatible second.val))
      (timeShiftConnectedPathTest first)
      (timeShiftConnectedPathTest second)
      hleftPath hleftBackground
  have hrightSource : first.val.2.val = second.val.2.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup (base + shift))
      (compatibleAmbientFamily_sublist
        (timeShiftCylinderSourceRightCompatible first.val))
      (compatibleAmbientFamily_sublist
        (timeShiftCylinderSourceRightCompatible second.val))
      (timeShiftConnectedPathTest first)
      (timeShiftConnectedPathTest second)
      hrightPath hrightBackground
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hleftSource
  · exact Subtype.ext hrightSource

/-! ## 4. The literal carrier support is connected -/

theorem timeShiftConnectedPathAtom_mem_coloredFamily
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {atom : CanonicalAtom (base + shift)}
    (hatom : atom ∈ timeShiftConnectedPathAtoms entry) :
    atom.val ∈ timeShiftConnectedPathLeftFamily entry ∨
      atom.val ∈ timeShiftConnectedPathRightFamily entry := by
  have htest : timeShiftConnectedPathTest entry atom.val = true := by
    unfold timeShiftConnectedPathTest timeShiftConnectedPathValues
    apply (memberB_eq_true_iff _ _).2
    exact List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rcases timeShiftConnectedPathAtoms_exclusive
      hrootsInside entry atom hatom with hleft | hright
  · apply Or.inl
    unfold timeShiftConnectedPathLeftFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (timeShiftCylinderSourceLeftCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hleft.1), htest⟩
  · apply Or.inr
    unfold timeShiftConnectedPathRightFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (timeShiftCylinderSourceRightCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hright.2), htest⟩

def timeShiftConnectedCarrierSupport
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) : List Nat :=
  familyUnionSupport (base + shift)
    (timeShiftConnectedPathLeftFamily entry ++
      timeShiftConnectedPathRightFamily entry)

theorem timeShiftConnectedPathAtom_face_mem_support
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {atom : CanonicalAtom (base + shift)}
    (hatom : atom ∈ timeShiftConnectedPathAtoms entry)
    {face : Nat} (hface : face ∈ atom.val) :
    face ∈ timeShiftConnectedCarrierSupport entry := by
  unfold timeShiftConnectedCarrierSupport
  rw [mem_familyUnionSupport_iff]
  constructor
  · exact mem_of_mem_sublists (physicalFaceEdges (base + shift)) atom.val
      (canonicalSurfacePolymer_mem_faceSupports atom.property) face hface
  · refine ⟨atom.val, ?_, hface⟩
    rcases timeShiftConnectedPathAtom_mem_coloredFamily
        hrootsInside entry hatom with hleft | hright
    · exact List.mem_append_left _ hleft
    · exact List.mem_append_right _ hright

theorem timeShiftConnectedColoredFamily_pathTest
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {polymer : List Nat}
    (hpolymer : polymer ∈ timeShiftConnectedPathLeftFamily entry ++
      timeShiftConnectedPathRightFamily entry) :
    timeShiftConnectedPathTest entry polymer = true := by
  rcases List.mem_append.mp hpolymer with hleft | hright
  · exact (List.mem_filter.mp hleft).2
  · exact (List.mem_filter.mp hright).2

def timeShiftConnectedCarrierSupport_face_witness
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {face : Nat} (hface : face ∈ timeShiftConnectedCarrierSupport entry) :
    Σ' atom : CanonicalAtom (base + shift),
      (atom ∈ timeShiftConnectedPathAtoms entry) ×' (face ∈ atom.val) := by
  have hcontains : familyContainsFaceB face
      (timeShiftConnectedPathLeftFamily entry ++
        timeShiftConnectedPathRightFamily entry) = true := by
    exact (List.mem_filter.mp hface).2
  obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
    familyContainsFaceWitness face _ hcontains
  have hpathTest : timeShiftConnectedPathTest entry polymer = true :=
    timeShiftConnectedColoredFamily_pathTest entry hpolymer
  have hpathValue : polymer ∈ timeShiftConnectedPathValues entry :=
    (memberB_eq_true_iff _ _).1 hpathTest
  obtain ⟨atom, hatom, hatomValue⟩ :=
    decodeMapMember Subtype.val (timeShiftConnectedPathAtoms entry)
      polymer hpathValue
  refine ⟨atom, hatom, ?_⟩
  rw [hatomValue]
  exact hfacePolymer

theorem timeShiftConnectedCarrierSupport_mem_faceSupports
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    timeShiftConnectedCarrierSupport entry ∈
      cutoffOneFaceSupports (base + shift) :=
  familyUnionSupport_mem_cutoffOneFaceSupports (base + shift) _

def timeShiftDisagreementCWalk_faceChainFromStart
    {n : Nat} {left right : PolymerFamily}
    (hleft : left ∈ canonicalCompatibleAmbientFamilies n)
    (hright : right ∈ canonicalCompatibleAmbientFamilies n) :
    ∀ {first last : CanonicalAtom n}
      (walk : CWalk
        (disagreementEdge (canonicalAmbientAtoms n)
          (canonicalAtomCompatibleB n)
          (memberB (canonicalFamilyAtoms hleft))
          (memberB (canonicalFamilyAtoms hright))) first last)
      (support : List Nat),
      (∀ atom, atom ∈ walk.vertices →
        ∀ face, face ∈ atom.val → face ∈ support) →
      ∀ {target : CanonicalAtom n}, target ∈ walk.vertices →
        ∀ {start finish : Nat}, start ∈ first.val →
          finish ∈ target.val →
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
            canonicalDisagreementEdge_incompatible hleft hright hedge
          obtain ⟨leftContact, hleftContact, rightContact,
              hrightContact, hcontact⟩ :=
            canonicalPolymerIncompatibleContact hincompatible
          have hhead : ChainIn (faceLinkAdjacentB n) support
              start leftContact :=
            ChainIn.mono
              (fun face hface =>
                hcover first List.mem_cons_self face hface)
              ((canonicalSurfacePolymers_allConnected n) first
                first.property start leftContact hstart hleftContact)
          have htail : ChainIn (faceLinkAdjacentB n) support
              rightContact finish :=
            timeShiftDisagreementCWalk_faceChainFromStart hleft hright
              rest support
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

def timeShiftConnectedCarrierSupport_chain_from_root
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {rootFace face : Nat}
    (hrootFace : rootFace ∈ (timeShiftSourceRootAtom entry.val).val)
    (hface : face ∈ timeShiftConnectedCarrierSupport entry) :
    ChainIn (faceLinkAdjacentB (base + shift))
      (timeShiftConnectedCarrierSupport entry) rootFace face := by
  obtain ⟨target, htarget, hfaceTarget⟩ :=
    timeShiftConnectedCarrierSupport_face_witness entry hface
  exact timeShiftDisagreementCWalk_faceChainFromStart
    (timeShiftCylinderSourceLeftCompatible entry.val)
    (timeShiftCylinderSourceRightCompatible entry.val)
    (timeShiftConnectedPath entry).walk
    (timeShiftConnectedCarrierSupport entry)
    (fun atom hatom found hfound =>
      timeShiftConnectedPathAtom_face_mem_support
        hrootsInside entry hatom hfound)
    htarget hrootFace hfaceTarget

theorem timeShiftConnectedCarrierSupport_root_mem
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (timeShiftSourceRootAtom entry.val).val) :
    rootFace ∈ timeShiftConnectedCarrierSupport entry :=
  timeShiftConnectedPathAtom_face_mem_support hrootsInside entry
    (by simpa [timeShiftConnectedPathAtoms] using
      CWalk.start_mem_vertices (timeShiftConnectedPath entry).walk)
    hrootFace

def timeShiftConnectedCarrierSupport_internallyConnected
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (timeShiftSourceRootAtom entry.val).val) :
    InternallyConnected (faceLinkAdjacentB (base + shift))
      (timeShiftConnectedCarrierSupport entry) := by
  intro first last hfirst hlast
  have hrootFirst := timeShiftConnectedCarrierSupport_chain_from_root
    hrootsInside entry hrootFace hfirst
  have hrootLast := timeShiftConnectedCarrierSupport_chain_from_root
    hrootsInside entry hrootFace hlast
  exact ChainIn.trans
    (chainInReverse (faceLinkAdjacentB_symmetric (base + shift))
      hrootFirst
      (timeShiftConnectedCarrierSupport_root_mem
        hrootsInside entry hrootFace))
    hrootLast

/-! ## 5. Explicit shifted exit and the size floor -/

def timeShiftSourceOutsideGeometricWitness
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    Σ' plaquette : Z4Plaq,
      (plaquette ∈ geometricPolymer (base + shift)
        (timeShiftSourceOutsideAtom entry.val).val) ×'
      (plaquette ∉ timeShiftedPlaquetteList shift base) := by
  have houtside := timeShiftSourceOutsideAtom_outside entry
  unfold targetRootInsideTimeShiftB at houtside
  let witness := allFalseWitness
    (fun plaquette => decide
      (plaquette ∈ timeShiftedPlaquetteList shift base))
    (geometricPolymer (base + shift)
      (timeShiftSourceOutsideAtom entry.val).val) houtside
  exact ⟨witness.1, witness.2.1,
    of_decide_eq_false witness.2.2⟩

theorem timeShiftConnectedCarrierSupport_shifted_boundary_floor
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {lower : Z4Vertex} {inner distance rootFace : Nat}
    (hrootFace : rootFace ∈ (timeShiftSourceRootAtom entry.val).val)
    (hrootCore : insideShiftedBoxB (addUniform lower distance) inner
      (boxPlaquetteAt (base + shift) rootFace) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ timeShiftedPlaquetteList shift base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    distance + 2 ≤ (timeShiftConnectedCarrierSupport entry).length := by
  let witness := timeShiftSourceOutsideGeometricWitness entry
  let plaquette := witness.1
  have hplaquetteGeom : plaquette ∈
      geometricPolymer (base + shift)
        (timeShiftSourceOutsideAtom entry.val).val := witness.2.1
  have hplaquetteNotRegion : plaquette ∉
      timeShiftedPlaquetteList shift base := witness.2.2
  obtain ⟨exitFace, hexitFaceOutside, hexitEq⟩ :=
    decodeMapMember (boxPlaquetteAt (base + shift))
      (timeShiftSourceOutsideAtom entry.val).val
      plaquette hplaquetteGeom
  have houtsidePath : timeShiftSourceOutsideAtom entry.val ∈
      timeShiftConnectedPathAtoms entry := by
    simpa [timeShiftConnectedPathAtoms] using
      CWalk.end_mem_vertices (timeShiftConnectedPath entry).walk
  have hexitSupport : exitFace ∈
      timeShiftConnectedCarrierSupport entry :=
    timeShiftConnectedPathAtom_face_mem_support
      hrootsInside entry houtsidePath hexitFaceOutside
  have hexit : outsideShiftedBoxB lower
      (inner + distance + distance)
      (boxPlaquetteAt (base + shift) exitFace) = true := by
    rw [hexitEq]
    exact houterExit plaquette hplaquetteNotRegion
  exact connectedFaceSupport_shifted_boundary_floor
    (timeShiftConnectedCarrierSupport_mem_faceSupports entry)
    (timeShiftConnectedCarrierSupport_internallyConnected
      hrootsInside entry hrootFace)
    (timeShiftConnectedCarrierSupport_root_mem
      hrootsInside entry hrootFace)
    hrootCore hexitSupport hexit

#print axioms timeShiftSourceOutsideAtom_spec
#print axioms timeShiftSourceRootAtom_spec
#print axioms timeShiftConnectedPathAtoms_exclusive
#print axioms timeShiftConnectedBackgroundRightFamily_mem_embedded
#print axioms timeShiftConnectedCarrier_injective
#print axioms timeShiftConnectedCarrierSupport_internallyConnected
#print axioms timeShiftConnectedCarrierSupport_shifted_boundary_floor

end YMGap.Continuum.Z4TimeShiftedConnectedCarrier
