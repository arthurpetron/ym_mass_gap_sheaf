/-
# Recoverable carriers for the uniformly padded boundary residue

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

import YMGap.Continuum.Z4UniformShiftCylinderSwitchSummation
import YMGap.Continuum.Z4ShiftedSubboxCarrierTail
import YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize

namespace YMGap.Continuum.Z4UniformShiftConnectedCarrier

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
open YMGap.Continuum.Z4UniformShiftCylinderSwitchSummation
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftEmbeddedRegion
open YMGap.Continuum.Z4UniformShiftPhysicalTransport
open Dir4

abbrev PolymerFamily := List (List Nat)

abbrev UniformShiftConnectedEntry
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) :=
  {pair : UniformShiftCylinderSourcePair padding base roots predicate //
    pair ∈ connectedUniformShiftCylinderSourcePairs}

/-! ## 1. Deterministic outside endpoint and marked root -/

theorem uniformShiftConnectedReach_true
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftBoundaryOutsideMarkedReachB
      (uniformShiftCylinderSourceLeftCompatible entry.val)
      (uniformShiftCylinderSourceRightCompatible entry.val) roots = true := by
  have htest := (List.mem_filter.mp entry.property).2
  unfold uniformShiftCylinderSourceSeparatedB at htest
  cases hreach : uniformShiftBoundaryOutsideMarkedReachB
      (uniformShiftCylinderSourceLeftCompatible entry.val)
      (uniformShiftCylinderSourceRightCompatible entry.val) roots <;>
    simp_all

def uniformShiftBoundaryDefaultAtom
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    CanonicalAtom (uniformPaddedBase padding base) :=
  let witness := allFalseWitness
    (targetRootInsideUniformShiftB padding base) pair.1.val
    (mem_uniformShiftBoundaryTargetFamilies_iff.mp
      (uniformShiftCylinderSourceLeftBoundary pair)).2
  ⟨witness.1, compatibleAmbientFamily_member_ambient
    (uniformShiftCylinderSourceLeftCompatible pair) witness.2.1⟩

def uniformShiftSourceOutsideTest
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate)
    (atom : CanonicalAtom (uniformPaddedBase padding base)) : Bool :=
  (!(targetRootInsideUniformShiftB padding base atom.val)) &&
    canonicalMarkedCut
      (uniformShiftCylinderSourceLeftCompatible pair)
      (uniformShiftCylinderSourceRightCompatible pair) roots atom

def uniformShiftSourceOutsideAtom
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    CanonicalAtom (uniformPaddedBase padding base) :=
  firstTrueOr (uniformShiftBoundaryDefaultAtom pair)
    (uniformShiftSourceOutsideTest pair)
    (canonicalFamilyAtoms (uniformShiftCylinderSourceLeftCompatible pair))

theorem uniformShiftSourceOutsideAtom_spec
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftSourceOutsideTest entry.val
        (uniformShiftSourceOutsideAtom entry.val) = true ∧
      uniformShiftSourceOutsideAtom entry.val ∈
        canonicalFamilyAtoms
          (uniformShiftCylinderSourceLeftCompatible entry.val) := by
  apply firstTrueOr_spec
  simpa [uniformShiftBoundaryOutsideMarkedReachB,
    uniformShiftSourceOutsideTest] using uniformShiftConnectedReach_true entry

theorem uniformShiftSourceOutsideAtom_outside
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    targetRootInsideUniformShiftB padding base
      (uniformShiftSourceOutsideAtom entry.val).val = false := by
  have htest := (Bool.and_eq_true _ _).mp
    (uniformShiftSourceOutsideAtom_spec entry).1 |>.1
  cases hinside : targetRootInsideUniformShiftB padding base
      (uniformShiftSourceOutsideAtom entry.val).val <;> simp_all

theorem uniformShiftSourceOutsideAtom_markedCut
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    canonicalMarkedCut
      (uniformShiftCylinderSourceLeftCompatible entry.val)
      (uniformShiftCylinderSourceRightCompatible entry.val) roots
      (uniformShiftSourceOutsideAtom entry.val) = true :=
  (Bool.and_eq_true _ _).mp
    (uniformShiftSourceOutsideAtom_spec entry).1 |>.2

def uniformShiftSourceRootTest
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate)
    (root : CanonicalAtom (uniformPaddedBase padding base)) : Bool :=
  canonicalDisagreementCut
    (uniformShiftCylinderSourceLeftCompatible pair)
    (uniformShiftCylinderSourceRightCompatible pair) root
    (uniformShiftSourceOutsideAtom pair)

def uniformShiftSourceRootAtom
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    CanonicalAtom (uniformPaddedBase padding base) :=
  firstTrueOr (uniformShiftSourceOutsideAtom pair)
    (uniformShiftSourceRootTest pair) roots

theorem uniformShiftSourceRootAtom_spec
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftSourceRootTest entry.val
        (uniformShiftSourceRootAtom entry.val) = true ∧
      uniformShiftSourceRootAtom entry.val ∈ roots := by
  apply firstTrueOr_spec
  have hmarked := uniformShiftSourceOutsideAtom_markedCut entry
  simpa [canonicalMarkedCut, markedRootCut,
    uniformShiftSourceRootTest] using hmarked

theorem uniformShiftSourceRootAtom_reaches
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    canonicalDisagreementCut
      (uniformShiftCylinderSourceLeftCompatible entry.val)
      (uniformShiftCylinderSourceRightCompatible entry.val)
      (uniformShiftSourceRootAtom entry.val)
      (uniformShiftSourceOutsideAtom entry.val) = true :=
  (uniformShiftSourceRootAtom_spec entry).1

/-! ## 2. The loop-erased disagreement path and its two colors -/

def uniformShiftSourceDisagreementEdge
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate) :
    CanonicalAtom (uniformPaddedBase padding base) →
      CanonicalAtom (uniformPaddedBase padding base) → Bool :=
  disagreementEdge (canonicalAmbientAtoms (uniformPaddedBase padding base))
    (canonicalAtomCompatibleB (uniformPaddedBase padding base))
    (memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceLeftCompatible pair)))
    (memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceRightCompatible pair)))

def uniformShiftConnectedPath
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    CWalk.Simple (uniformShiftSourceDisagreementEdge entry.val)
      (uniformShiftSourceRootAtom entry.val)
      (uniformShiftSourceOutsideAtom entry.val) :=
  simpleWalkOfWarshall (uniformShiftSourceDisagreementEdge entry.val)
    (canonicalAmbientAtoms (uniformPaddedBase padding base))
    (uniformShiftSourceRootAtom entry.val)
    (uniformShiftSourceOutsideAtom entry.val)
    (uniformShiftSourceRootAtom_reaches entry)

def uniformShiftConnectedPathAtoms
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    List (CanonicalAtom (uniformPaddedBase padding base)) :=
  (uniformShiftConnectedPath entry).walk.vertices

def uniformShiftConnectedPathValues
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    List (List Nat) :=
  (uniformShiftConnectedPathAtoms entry).map Subtype.val

def uniformShiftSourceExclusive
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate)
    (atom : CanonicalAtom (uniformPaddedBase padding base)) : Prop :=
  (memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceLeftCompatible pair)) atom = true ∧
    memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceRightCompatible pair)) atom = false) ∨
  (memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceLeftCompatible pair)) atom = false ∧
    memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceRightCompatible pair)) atom = true)

theorem uniformShiftSourceRootAtom_exclusive
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftSourceExclusive entry.val
      (uniformShiftSourceRootAtom entry.val) := by
  let root := uniformShiftSourceRootAtom entry.val
  let outside := uniformShiftSourceOutsideAtom entry.val
  have hrootInside : targetRootInsideUniformShiftB
      padding base root.val = true :=
    hrootsInside root (uniformShiftSourceRootAtom_spec entry).2
  have houtside : targetRootInsideUniformShiftB
      padding base outside.val = false :=
    uniformShiftSourceOutsideAtom_outside entry
  have hne : root ≠ outside := by
    intro heq
    have hrootAtOutside := hrootInside
    rw [heq] at hrootAtOutside
    rw [hrootAtOutside] at houtside
    exact Bool.false_ne_true houtside.symm
  have hwalk := warshallSound
    (uniformShiftSourceDisagreementEdge entry.val)
    (canonicalAmbientAtoms (uniformPaddedBase padding base)) root outside
    (uniformShiftSourceRootAtom_reaches entry)
  obtain ⟨next, hedge⟩ := dWalk_start_edge_of_ne _ hwalk hne
  rcases disagreementEdge_source_exclusive _ _ _ _ hedge with
    hleft | hright
  · exact Or.inl hleft
  · exact Or.inr hright

theorem uniformShiftSourceDisagreementEdge_target_exclusive
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (pair : UniformShiftCylinderSourcePair padding base roots predicate)
    {first second : CanonicalAtom (uniformPaddedBase padding base)}
    (hedge : uniformShiftSourceDisagreementEdge pair first second = true) :
    uniformShiftSourceExclusive pair second := by
  have hbits := (Bool.and_eq_true _ _).mp hedge |>.2
  unfold uniformShiftSourceDisagreementEdge disagreementBits
    leftOnly rightOnly at hbits
  unfold uniformShiftSourceExclusive
  cases hleftFirst : memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceLeftCompatible pair)) first <;>
    cases hrightFirst : memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceRightCompatible pair)) first <;>
    cases hleftSecond : memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceLeftCompatible pair)) second <;>
    cases hrightSecond : memberB (canonicalFamilyAtoms
      (uniformShiftCylinderSourceRightCompatible pair)) second <;>
    simp_all

theorem uniformShiftConnectedPathAtoms_exclusive
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    ∀ atom, atom ∈ uniformShiftConnectedPathAtoms entry →
      uniformShiftSourceExclusive entry.val atom := by
  exact CWalk.all_vertices_of_start
    (uniformShiftSourceExclusive entry.val)
    (fun _ _ hedge _ =>
      uniformShiftSourceDisagreementEdge_target_exclusive entry.val hedge)
    (uniformShiftConnectedPath entry).walk
    (uniformShiftSourceRootAtom_exclusive hrootsInside entry)

def uniformShiftConnectedPathTest
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    List Nat → Bool :=
  memberB (uniformShiftConnectedPathValues entry)

def uniformShiftConnectedPathLeftFamily
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    PolymerFamily :=
  entry.val.1.val.filter (uniformShiftConnectedPathTest entry)

def uniformShiftConnectedBackgroundLeftFamily
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    PolymerFamily :=
  entry.val.1.val.filter
    (fun polymer => !(uniformShiftConnectedPathTest entry polymer))

def uniformShiftConnectedPathRightFamily
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    PolymerFamily :=
  entry.val.2.val.filter (uniformShiftConnectedPathTest entry)

def uniformShiftConnectedBackgroundRightFamily
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    PolymerFamily :=
  entry.val.2.val.filter
    (fun polymer => !(uniformShiftConnectedPathTest entry polymer))

theorem uniformShiftConnectedPathLeftFamily_mem
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftConnectedPathLeftFamily entry ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) :=
  canonicalFilteredFamily_mem
    (uniformShiftCylinderSourceLeftCompatible entry.val)
    (uniformShiftConnectedPathTest entry)

theorem uniformShiftConnectedBackgroundLeftFamily_mem
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftConnectedBackgroundLeftFamily entry ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) :=
  canonicalFilteredFamily_mem
    (uniformShiftCylinderSourceLeftCompatible entry.val)
    (fun polymer => !(uniformShiftConnectedPathTest entry polymer))

theorem uniformShiftConnectedPathRightFamily_mem
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftConnectedPathRightFamily entry ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) :=
  canonicalFilteredFamily_mem
    (uniformShiftCylinderSourceRightCompatible entry.val)
    (uniformShiftConnectedPathTest entry)

theorem uniformShiftConnectedBackgroundRightFamily_mem
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftConnectedBackgroundRightFamily entry ∈
      canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base) :=
  canonicalFilteredFamily_mem
    (uniformShiftCylinderSourceRightCompatible entry.val)
    (fun polymer => !(uniformShiftConnectedPathTest entry polymer))

theorem uniformShiftConnectedBackgroundRightFamily_mem_embedded
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftConnectedBackgroundRightFamily entry ∈
      uniformShiftEmbeddedTargetFamilies padding base := by
  apply mem_uniformShiftEmbeddedTargetFamilies_iff.mpr
  refine ⟨uniformShiftConnectedBackgroundRightFamily_mem entry, ?_⟩
  rw [List.all_eq_true]
  intro support hsupport
  have hsource : support ∈ entry.val.2.val :=
    (List.mem_filter.mp hsupport).1
  exact List.all_eq_true.mp
    (mem_uniformShiftEmbeddedTargetFamilies_iff.mp
      (uniformShiftCylinderSourceRightEmbedded entry.val)).2
    support hsource

/-! ## 3. Support/background recovery -/

def uniformShiftConnectedLeftColorSupport
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) : List Nat :=
  familyUnionSupport (uniformPaddedBase padding base)
    (uniformShiftConnectedPathLeftFamily entry)

def uniformShiftConnectedRightColorSupport
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) : List Nat :=
  familyUnionSupport (uniformPaddedBase padding base)
    (uniformShiftConnectedPathRightFamily entry)

def uniformShiftConnectedCarrier
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    ConnectedCarrier :=
  ((uniformShiftConnectedLeftColorSupport entry,
      uniformShiftConnectedRightColorSupport entry),
    (uniformShiftConnectedBackgroundLeftFamily entry,
      uniformShiftConnectedBackgroundRightFamily entry))

theorem uniformShiftConnectedCarrier_injective
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (first second : UniformShiftConnectedEntry padding base roots predicate)
    (heq : uniformShiftConnectedCarrier first =
      uniformShiftConnectedCarrier second) : first = second := by
  have hleftSupport : uniformShiftConnectedLeftColorSupport first =
      uniformShiftConnectedLeftColorSupport second :=
    congrArg (fun carrier => carrier.1.1) heq
  have hrightSupport : uniformShiftConnectedRightColorSupport first =
      uniformShiftConnectedRightColorSupport second :=
    congrArg (fun carrier => carrier.1.2) heq
  have hleftBackground : uniformShiftConnectedBackgroundLeftFamily first =
      uniformShiftConnectedBackgroundLeftFamily second :=
    congrArg (fun carrier => carrier.2.1) heq
  have hrightBackground : uniformShiftConnectedBackgroundRightFamily first =
      uniformShiftConnectedBackgroundRightFamily second :=
    congrArg (fun carrier => carrier.2.2) heq
  have hleftPath : uniformShiftConnectedPathLeftFamily first =
      uniformShiftConnectedPathLeftFamily second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (uniformShiftConnectedPathLeftFamily_mem first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (uniformShiftConnectedPathLeftFamily_mem second)
    exact hrecoverFirst.symm.trans
      ((congrArg
        (fun support => ambientOrderedFamily (uniformPaddedBase padding base)
          (canonicalSurfaceFamily (uniformPaddedBase padding base) support))
        hleftSupport).trans hrecoverSecond)
  have hrightPath : uniformShiftConnectedPathRightFamily first =
      uniformShiftConnectedPathRightFamily second := by
    have hrecoverFirst := compatibleAmbientFamily_eq_unionAmbientOrdered
      (uniformShiftConnectedPathRightFamily_mem first)
    have hrecoverSecond := compatibleAmbientFamily_eq_unionAmbientOrdered
      (uniformShiftConnectedPathRightFamily_mem second)
    exact hrecoverFirst.symm.trans
      ((congrArg
        (fun support => ambientOrderedFamily (uniformPaddedBase padding base)
          (canonicalSurfaceFamily (uniformPaddedBase padding base) support))
        hrightSupport).trans hrecoverSecond)
  have hleftSource : first.val.1.val = second.val.1.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup (uniformPaddedBase padding base))
      (compatibleAmbientFamily_sublist
        (uniformShiftCylinderSourceLeftCompatible first.val))
      (compatibleAmbientFamily_sublist
        (uniformShiftCylinderSourceLeftCompatible second.val))
      (uniformShiftConnectedPathTest first)
      (uniformShiftConnectedPathTest second)
      hleftPath hleftBackground
  have hrightSource : first.val.2.val = second.val.2.val := by
    exact ambientSubfamilies_eq_of_partition
      (canonicalSurfacePolymers_nodup (uniformPaddedBase padding base))
      (compatibleAmbientFamily_sublist
        (uniformShiftCylinderSourceRightCompatible first.val))
      (compatibleAmbientFamily_sublist
        (uniformShiftCylinderSourceRightCompatible second.val))
      (uniformShiftConnectedPathTest first)
      (uniformShiftConnectedPathTest second)
      hrightPath hrightBackground
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hleftSource
  · exact Subtype.ext hrightSource

/-! ## 4. The literal carrier support is connected -/

theorem uniformShiftConnectedPathAtom_mem_coloredFamily
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {atom : CanonicalAtom (uniformPaddedBase padding base)}
    (hatom : atom ∈ uniformShiftConnectedPathAtoms entry) :
    atom.val ∈ uniformShiftConnectedPathLeftFamily entry ∨
      atom.val ∈ uniformShiftConnectedPathRightFamily entry := by
  have htest : uniformShiftConnectedPathTest entry atom.val = true := by
    unfold uniformShiftConnectedPathTest uniformShiftConnectedPathValues
    apply (memberB_eq_true_iff _ _).2
    exact List.mem_map.mpr ⟨atom, hatom, rfl⟩
  rcases uniformShiftConnectedPathAtoms_exclusive
      hrootsInside entry atom hatom with hleft | hright
  · apply Or.inl
    unfold uniformShiftConnectedPathLeftFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (uniformShiftCylinderSourceLeftCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hleft.1), htest⟩
  · apply Or.inr
    unfold uniformShiftConnectedPathRightFamily
    apply List.mem_filter.mpr
    exact ⟨(canonicalFamilyAtom_mem_iff
      (uniformShiftCylinderSourceRightCompatible entry.val) atom).1
        ((memberB_eq_true_iff _ _).1 hright.2), htest⟩

def uniformShiftConnectedCarrierSupport
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) : List Nat :=
  familyUnionSupport (uniformPaddedBase padding base)
    (uniformShiftConnectedPathLeftFamily entry ++
      uniformShiftConnectedPathRightFamily entry)

theorem uniformShiftConnectedPathAtom_face_mem_support
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {atom : CanonicalAtom (uniformPaddedBase padding base)}
    (hatom : atom ∈ uniformShiftConnectedPathAtoms entry)
    {face : Nat} (hface : face ∈ atom.val) :
    face ∈ uniformShiftConnectedCarrierSupport entry := by
  unfold uniformShiftConnectedCarrierSupport
  rw [mem_familyUnionSupport_iff]
  constructor
  · exact mem_of_mem_sublists (physicalFaceEdges (uniformPaddedBase padding base)) atom.val
      (canonicalSurfacePolymer_mem_faceSupports atom.property) face hface
  · refine ⟨atom.val, ?_, hface⟩
    rcases uniformShiftConnectedPathAtom_mem_coloredFamily
        hrootsInside entry hatom with hleft | hright
    · exact List.mem_append_left _ hleft
    · exact List.mem_append_right _ hright

theorem uniformShiftConnectedColoredFamily_pathTest
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {polymer : List Nat}
    (hpolymer : polymer ∈ uniformShiftConnectedPathLeftFamily entry ++
      uniformShiftConnectedPathRightFamily entry) :
    uniformShiftConnectedPathTest entry polymer = true := by
  rcases List.mem_append.mp hpolymer with hleft | hright
  · exact (List.mem_filter.mp hleft).2
  · exact (List.mem_filter.mp hright).2

def uniformShiftConnectedCarrierSupport_face_witness
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {face : Nat} (hface : face ∈ uniformShiftConnectedCarrierSupport entry) :
    Σ' atom : CanonicalAtom (uniformPaddedBase padding base),
      (atom ∈ uniformShiftConnectedPathAtoms entry) ×' (face ∈ atom.val) := by
  have hcontains : familyContainsFaceB face
      (uniformShiftConnectedPathLeftFamily entry ++
        uniformShiftConnectedPathRightFamily entry) = true := by
    exact (List.mem_filter.mp hface).2
  obtain ⟨polymer, hpolymer, hfacePolymer⟩ :=
    familyContainsFaceWitness face _ hcontains
  have hpathTest : uniformShiftConnectedPathTest entry polymer = true :=
    uniformShiftConnectedColoredFamily_pathTest entry hpolymer
  have hpathValue : polymer ∈ uniformShiftConnectedPathValues entry :=
    (memberB_eq_true_iff _ _).1 hpathTest
  obtain ⟨atom, hatom, hatomValue⟩ :=
    decodeMapMember Subtype.val (uniformShiftConnectedPathAtoms entry)
      polymer hpathValue
  refine ⟨atom, hatom, ?_⟩
  rw [hatomValue]
  exact hfacePolymer

theorem uniformShiftConnectedCarrierSupport_mem_faceSupports
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    uniformShiftConnectedCarrierSupport entry ∈
      cutoffOneFaceSupports (uniformPaddedBase padding base) :=
  familyUnionSupport_mem_cutoffOneFaceSupports (uniformPaddedBase padding base) _

def uniformShiftDisagreementCWalk_faceChainFromStart
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
            uniformShiftDisagreementCWalk_faceChainFromStart hleft hright
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

def uniformShiftConnectedCarrierSupport_chain_from_root
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {rootFace face : Nat}
    (hrootFace : rootFace ∈ (uniformShiftSourceRootAtom entry.val).val)
    (hface : face ∈ uniformShiftConnectedCarrierSupport entry) :
    ChainIn (faceLinkAdjacentB (uniformPaddedBase padding base))
      (uniformShiftConnectedCarrierSupport entry) rootFace face := by
  obtain ⟨target, htarget, hfaceTarget⟩ :=
    uniformShiftConnectedCarrierSupport_face_witness entry hface
  exact uniformShiftDisagreementCWalk_faceChainFromStart
    (uniformShiftCylinderSourceLeftCompatible entry.val)
    (uniformShiftCylinderSourceRightCompatible entry.val)
    (uniformShiftConnectedPath entry).walk
    (uniformShiftConnectedCarrierSupport entry)
    (fun atom hatom found hfound =>
      uniformShiftConnectedPathAtom_face_mem_support
        hrootsInside entry hatom hfound)
    htarget hrootFace hfaceTarget

theorem uniformShiftConnectedCarrierSupport_root_mem
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (uniformShiftSourceRootAtom entry.val).val) :
    rootFace ∈ uniformShiftConnectedCarrierSupport entry :=
  uniformShiftConnectedPathAtom_face_mem_support hrootsInside entry
    (by simpa [uniformShiftConnectedPathAtoms] using
      CWalk.start_mem_vertices (uniformShiftConnectedPath entry).walk)
    hrootFace

def uniformShiftConnectedCarrierSupport_internallyConnected
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (uniformShiftSourceRootAtom entry.val).val) :
    InternallyConnected (faceLinkAdjacentB (uniformPaddedBase padding base))
      (uniformShiftConnectedCarrierSupport entry) := by
  intro first last hfirst hlast
  have hrootFirst := uniformShiftConnectedCarrierSupport_chain_from_root
    hrootsInside entry hrootFace hfirst
  have hrootLast := uniformShiftConnectedCarrierSupport_chain_from_root
    hrootsInside entry hrootFace hlast
  exact ChainIn.trans
    (chainInReverse (faceLinkAdjacentB_symmetric (uniformPaddedBase padding base))
      hrootFirst
      (uniformShiftConnectedCarrierSupport_root_mem
        hrootsInside entry hrootFace))
    hrootLast

/-! ## 5. Explicit shifted exit and the size floor -/

def uniformShiftSourceOutsideGeometricWitness
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    Σ' plaquette : Z4Plaq,
      (plaquette ∈ geometricPolymer (uniformPaddedBase padding base)
        (uniformShiftSourceOutsideAtom entry.val).val) ×'
      (plaquette ∉ uniformShiftedPlaquetteList padding base) := by
  have houtside := uniformShiftSourceOutsideAtom_outside entry
  unfold targetRootInsideUniformShiftB at houtside
  let witness := allFalseWitness
    (fun plaquette => decide
      (plaquette ∈ uniformShiftedPlaquetteList padding base))
    (geometricPolymer (uniformPaddedBase padding base)
      (uniformShiftSourceOutsideAtom entry.val).val) houtside
  exact ⟨witness.1, witness.2.1,
    of_decide_eq_false witness.2.2⟩

theorem uniformShiftConnectedCarrierSupport_shifted_boundary_floor
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {lower : Z4Vertex} {inner distance rootFace : Nat}
    (hrootFace : rootFace ∈ (uniformShiftSourceRootAtom entry.val).val)
    (hrootCore : insideShiftedBoxB (addUniform lower distance) inner
      (boxPlaquetteAt (uniformPaddedBase padding base) rootFace) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ uniformShiftedPlaquetteList padding base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    distance + 2 ≤ (uniformShiftConnectedCarrierSupport entry).length := by
  let witness := uniformShiftSourceOutsideGeometricWitness entry
  let plaquette := witness.1
  have hplaquetteGeom : plaquette ∈
      geometricPolymer (uniformPaddedBase padding base)
        (uniformShiftSourceOutsideAtom entry.val).val := witness.2.1
  have hplaquetteNotRegion : plaquette ∉
      uniformShiftedPlaquetteList padding base := witness.2.2
  obtain ⟨exitFace, hexitFaceOutside, hexitEq⟩ :=
    decodeMapMember (boxPlaquetteAt (uniformPaddedBase padding base))
      (uniformShiftSourceOutsideAtom entry.val).val
      plaquette hplaquetteGeom
  have houtsidePath : uniformShiftSourceOutsideAtom entry.val ∈
      uniformShiftConnectedPathAtoms entry := by
    simpa [uniformShiftConnectedPathAtoms] using
      CWalk.end_mem_vertices (uniformShiftConnectedPath entry).walk
  have hexitSupport : exitFace ∈
      uniformShiftConnectedCarrierSupport entry :=
    uniformShiftConnectedPathAtom_face_mem_support
      hrootsInside entry houtsidePath hexitFaceOutside
  have hexit : outsideShiftedBoxB lower
      (inner + distance + distance)
      (boxPlaquetteAt (uniformPaddedBase padding base) exitFace) = true := by
    rw [hexitEq]
    exact houterExit plaquette hplaquetteNotRegion
  exact connectedFaceSupport_shifted_boundary_floor
    (uniformShiftConnectedCarrierSupport_mem_faceSupports entry)
    (uniformShiftConnectedCarrierSupport_internallyConnected
      hrootsInside entry hrootFace)
    (uniformShiftConnectedCarrierSupport_root_mem
      hrootsInside entry hrootFace)
    hrootCore hexitSupport hexit

#print axioms uniformShiftSourceOutsideAtom_spec
#print axioms uniformShiftSourceRootAtom_spec
#print axioms uniformShiftConnectedPathAtoms_exclusive
#print axioms uniformShiftConnectedBackgroundRightFamily_mem_embedded
#print axioms uniformShiftConnectedCarrier_injective
#print axioms uniformShiftConnectedCarrierSupport_internallyConnected
#print axioms uniformShiftConnectedCarrierSupport_shifted_boundary_floor

end YMGap.Continuum.Z4UniformShiftConnectedCarrier
