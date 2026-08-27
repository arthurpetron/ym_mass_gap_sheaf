/-
# A recoupling-invariant paired physical-support component

The strand-pairing component used by the first two-replica switch depends on
the chosen fusion tree.  A Schur recoupling can therefore change that graph,
which is the wrong dependency for a common target-column argument.

This module replaces it by the coarser graph on the union of the two physical
plaquette supports.  Two supported slab faces are adjacent when they occur at
one actual boundary-complete slab link.  This graph depends only on the two
physical labellings.  Its target-rooted component is consequently unchanged
by intertwiner recoupling, and its Boolean face switch is involutive.

The coarser component also has the decisive local property: every two
positive faces incident on one slab link have the same component bit.  Thus a
later intertwiner switch can transpose whole link witnesses instead of
splitting individual strands.

No auxiliary-witness switch, column-capacity theorem, correlation estimate,
or spectral gap is claimed here.

Constructive contract: finite Boolean graph search and literal slab
incidence only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaFaceSwapCertificate
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. Actual-link adjacency on slab face identifiers -/

/-- Boolean recognition that two numerical slab-face identifiers occur at
one link in a displayed slab-link list. -/
def slabShareListedLinkB (extent left right : Nat) : List SlabLink → Bool
  | [] => false
  | link :: links =>
      (decide (left ∈ slabIncidentPlaqIds extent link) &&
          decide (right ∈ slabIncidentPlaqIds extent link)) ||
        slabShareListedLinkB extent left right links

theorem slabShareListedLinkB_symm (extent left right : Nat) :
    ∀ links,
      slabShareListedLinkB extent left right links =
        slabShareListedLinkB extent right left links
  | [] => rfl
  | link :: links => by
      simp only [slabShareListedLinkB]
      rw [slabShareListedLinkB_symm extent left right links]
      cases decide (left ∈ slabIncidentPlaqIds extent link) <;>
        cases decide (right ∈ slabIncidentPlaqIds extent link) <;> rfl

theorem slabShareListedLinkB_true_of_mem
    {extent left right : Nat} {link : SlabLink} :
    ∀ {links : List SlabLink}, link ∈ links →
      left ∈ slabIncidentPlaqIds extent link →
      right ∈ slabIncidentPlaqIds extent link →
      slabShareListedLinkB extent left right links = true
  | [], hmem, _, _ => False.elim (List.not_mem_nil hmem)
  | head :: links, hmem, hleft, hright => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp [slabShareListedLinkB, hleft, hright]
      · have ih := slabShareListedLinkB_true_of_mem htail hleft hright
        simp [slabShareListedLinkB, ih]

/-- The fixed physical adjacency used by the paired-support component. -/
def slabSupportFaceAdjacentB (extent left right : Nat) : Bool :=
  slabShareListedLinkB extent left right
    (boundaryCompleteSlabLinks extent)

theorem slabSupportFaceAdjacentB_symmetric (extent : Nat) :
    SymmetricAdj (slabSupportFaceAdjacentB extent) := by
  intro left right
  exact slabShareListedLinkB_symm extent left right
    (boundaryCompleteSlabLinks extent)

theorem slabSupportFaceAdjacentB_true_of_link
    {extent left right : Nat} {link : SlabLink}
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hleft : left ∈ slabIncidentPlaqIds extent link)
    (hright : right ∈ slabIncidentPlaqIds extent link) :
    slabSupportFaceAdjacentB extent left right = true :=
  slabShareListedLinkB_true_of_mem hlink hleft hright

/-! ## 2. The union-support carrier and its canonical component -/

/-- A face is retained exactly when at least one physical replica has a
positive twice-spin there. -/
def slabTwoReplicaSupportFaceB
    (left right : SlabLabelling) (faceId : Nat) : Bool :=
  decide (0 < left faceId ∨ 0 < right faceId)

/-- The literal union of the two physical face supports. -/
def slabTwoReplicaSupportFaceVertices
    (extent : Nat) (left right : SlabLabelling) : List Nat :=
  (slabPhysicalFaceEdges extent).filter
    (slabTwoReplicaSupportFaceB left right)

theorem mem_slabTwoReplicaSupportFaceVertices
    {extent : Nat} {left right : SlabLabelling} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (hsupport : 0 < left faceId ∨ 0 < right faceId) :
    faceId ∈ slabTwoReplicaSupportFaceVertices extent left right := by
  apply List.mem_filter.mpr
  exact ⟨hface, decide_eq_true hsupport⟩

/-- The target-rooted component in the union physical-support graph. -/
def slabTwoReplicaTargetSupportComponent
    (extent : Nat) (left right : SlabLabelling)
    (targetFaceId : Nat) : List Nat :=
  rootComponent (slabSupportFaceAdjacentB extent)
    (slabTwoReplicaSupportFaceVertices extent left right) targetFaceId

/-- Swap exactly the target-rooted union-support component. -/
def slabTwoReplicaSupportSwapMask
    (extent : Nat) (left right : SlabLabelling)
    (targetFaceId faceId : Nat) : Bool :=
  decide (faceId ∈
    slabTwoReplicaTargetSupportComponent
      extent left right targetFaceId)

theorem slabTwoReplicaSupportSwapMask_target
    {extent targetFaceId : Nat} {left right : SlabLabelling}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (hsupport : 0 < left targetFaceId ∨ 0 < right targetFaceId) :
    slabTwoReplicaSupportSwapMask
      extent left right targetFaceId targetFaceId = true := by
  unfold slabTwoReplicaSupportSwapMask
    slabTwoReplicaTargetSupportComponent
  exact decide_eq_true
    (root_mem_rootComponent
      (slabSupportFaceAdjacentB extent)
      (mem_slabTwoReplicaSupportFaceVertices htarget hsupport))

/-- Component membership is constant on any actual link between two
supported incident faces. -/
theorem slabTwoReplicaSupportSwapMask_eq_of_link
    {extent targetFaceId leftFaceId rightFaceId : Nat}
    {left right : SlabLabelling} {link : SlabLink}
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges extent)
    (htargetSupport : 0 < left targetFaceId ∨ 0 < right targetFaceId)
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hleftIncident : leftFaceId ∈ slabIncidentPlaqIds extent link)
    (hrightIncident : rightFaceId ∈ slabIncidentPlaqIds extent link)
    (hleftSupport : 0 < left leftFaceId ∨ 0 < right leftFaceId)
    (hrightSupport : 0 < left rightFaceId ∨ 0 < right rightFaceId) :
    slabTwoReplicaSupportSwapMask
        extent left right targetFaceId rightFaceId =
      slabTwoReplicaSupportSwapMask
        extent left right targetFaceId leftFaceId := by
  let vertices := slabTwoReplicaSupportFaceVertices extent left right
  let component := slabTwoReplicaTargetSupportComponent
    extent left right targetFaceId
  have hseed : targetFaceId ∈ vertices :=
    mem_slabTwoReplicaSupportFaceVertices htarget htargetSupport
  have hleftVertex : leftFaceId ∈ vertices :=
    mem_slabTwoReplicaSupportFaceVertices
      (slabIncidentPlaqId_physical hleftIncident) hleftSupport
  have hrightVertex : rightFaceId ∈ vertices :=
    mem_slabTwoReplicaSupportFaceVertices
      (slabIncidentPlaqId_physical hrightIncident) hrightSupport
  have hadj : slabSupportFaceAdjacentB extent
      leftFaceId rightFaceId = true :=
    slabSupportFaceAdjacentB_true_of_link
      hlink hleftIncident hrightIncident
  by_cases hleftMem : leftFaceId ∈ component
  · have hrightMem : rightFaceId ∈ component :=
      rootComponent_closed_under_edge
        (slabSupportFaceAdjacentB extent)
        (slabSupportFaceAdjacentB_symmetric extent)
        hseed hleftMem hrightVertex hadj
    simp [slabTwoReplicaSupportSwapMask, component,
      hleftMem, hrightMem]
  · by_cases hrightMem : rightFaceId ∈ component
    · have hreverse : slabSupportFaceAdjacentB extent
          rightFaceId leftFaceId = true := by
        rw [slabSupportFaceAdjacentB_symmetric extent
          rightFaceId leftFaceId]
        exact hadj
      have hleftMem' : leftFaceId ∈ component :=
        rootComponent_closed_under_edge
          (slabSupportFaceAdjacentB extent)
          (slabSupportFaceAdjacentB_symmetric extent)
          hseed hrightMem hleftVertex hreverse
      exact False.elim (hleftMem hleftMem')
    · simp [slabTwoReplicaSupportSwapMask, component,
        hleftMem, hrightMem]

/-! ## 3. Recoupling invariance and physical involution -/

/-- Facewise transposition preserves the union-support predicate pointwise. -/
theorem slabTwoReplicaSupportFaceB_faceSwap
    (selected : Nat → Bool) (left right : SlabLabelling)
    (faceId : Nat) :
    slabTwoReplicaSupportFaceB
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) faceId =
      slabTwoReplicaSupportFaceB left right faceId := by
  cases hselected : selected faceId <;>
    simp [slabTwoReplicaSupportFaceB, twoReplicaFaceSwapLeft,
      twoReplicaFaceSwapRight, hselected, Or.comm]

/-- Hence every recoupling target above a fixed physical face swap has the
same union-support vertex carrier as its source. -/
theorem slabTwoReplicaSupportFaceVertices_faceSwap
    (extent : Nat) (selected : Nat → Bool)
    (left right : SlabLabelling) :
    slabTwoReplicaSupportFaceVertices extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) =
      slabTwoReplicaSupportFaceVertices extent left right := by
  unfold slabTwoReplicaSupportFaceVertices
  apply List.filter_congr
  intro faceId _
  exact slabTwoReplicaSupportFaceB_faceSwap
    selected left right faceId

/-- The canonical target-rooted component itself is invariant under any
facewise transposition of the two replicas. -/
theorem slabTwoReplicaTargetSupportComponent_faceSwap
    (extent targetFaceId : Nat) (selected : Nat → Bool)
    (left right : SlabLabelling) :
    slabTwoReplicaTargetSupportComponent extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) targetFaceId =
      slabTwoReplicaTargetSupportComponent
        extent left right targetFaceId := by
  unfold slabTwoReplicaTargetSupportComponent
  rw [slabTwoReplicaSupportFaceVertices_faceSwap]

/-- The canonical support mask is therefore recoverable from either side of
the physical switch. -/
theorem slabTwoReplicaSupportSwapMask_faceSwap
    (extent targetFaceId : Nat) (selected : Nat → Bool)
    (left right : SlabLabelling) :
    slabTwoReplicaSupportSwapMask extent
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) targetFaceId =
      slabTwoReplicaSupportSwapMask extent left right targetFaceId := by
  funext faceId
  unfold slabTwoReplicaSupportSwapMask
  rw [slabTwoReplicaTargetSupportComponent_faceSwap]

/-- Applying the canonical union-support switch twice recovers the first
physical replica. -/
theorem slabTwoReplicaCanonicalSupportSwapLeft_involutive
    (extent targetFaceId : Nat) (left right : SlabLabelling) :
    let selected := slabTwoReplicaSupportSwapMask
      extent left right targetFaceId
    twoReplicaFaceSwapLeft
        (slabTwoReplicaSupportSwapMask extent
          (twoReplicaFaceSwapLeft selected left right)
          (twoReplicaFaceSwapRight selected left right) targetFaceId)
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) = left := by
  dsimp only
  rw [slabTwoReplicaSupportSwapMask_faceSwap]
  exact twoReplicaFaceSwapLeft_involutive
    (slabTwoReplicaSupportSwapMask extent left right targetFaceId)
    left right

/-- The complementary physical replica is recovered at the same time. -/
theorem slabTwoReplicaCanonicalSupportSwapRight_involutive
    (extent targetFaceId : Nat) (left right : SlabLabelling) :
    let selected := slabTwoReplicaSupportSwapMask
      extent left right targetFaceId
    twoReplicaFaceSwapRight
        (slabTwoReplicaSupportSwapMask extent
          (twoReplicaFaceSwapLeft selected left right)
          (twoReplicaFaceSwapRight selected left right) targetFaceId)
        (twoReplicaFaceSwapLeft selected left right)
        (twoReplicaFaceSwapRight selected left right) = right := by
  dsimp only
  rw [slabTwoReplicaSupportSwapMask_faceSwap]
  exact twoReplicaFaceSwapRight_involutive
    (slabTwoReplicaSupportSwapMask extent left right targetFaceId)
    left right

/-! ## 4. Specialization to the observable two-replica carrier -/

def slabObservableTwoReplicaPairPairedSupportSwapMask
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId faceId : Nat) : Bool :=
  slabTwoReplicaSupportSwapMask D.extent
    pair.1.1.1 pair.2.1.1 targetFaceId faceId

def slabObservableTwoReplicaPairPairedSupportConnectedB
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : Bool :=
  slabObservableTwoReplicaPairPairedSupportSwapMask
    D pair targetFaceId rootFaceId

theorem slabObservableTwoReplicaPairPairedSupportSwapMask_target
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    slabObservableTwoReplicaPairPairedSupportSwapMask
      D pair targetFaceId targetFaceId = true := by
  apply slabTwoReplicaSupportSwapMask_target htarget
  left
  exact slabObservableTwoReplicaPairLeft_target_positive_of_mem_source
    D rootFaceId targetFaceId pair hpair

theorem slabObservableTwoReplicaPairPairedSupportSwapMask_root_of_disconnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hdisconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId pair = false) :
    slabObservableTwoReplicaPairPairedSupportSwapMask
      D pair targetFaceId rootFaceId = false :=
  hdisconnected

end YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent.slabSupportFaceAdjacentB_true_of_link
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent.slabTwoReplicaSupportSwapMask_eq_of_link
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent.slabTwoReplicaSupportFaceVertices_faceSwap
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent.slabTwoReplicaSupportSwapMask_faceSwap
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent.slabTwoReplicaCanonicalSupportSwapLeft_involutive
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent.slabTwoReplicaCanonicalSupportSwapRight_involutive
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent.slabObservableTwoReplicaPairPairedSupportSwapMask_target
