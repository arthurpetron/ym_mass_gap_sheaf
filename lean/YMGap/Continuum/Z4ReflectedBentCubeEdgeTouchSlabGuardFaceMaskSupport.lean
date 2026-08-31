/-
# The guarded paired-face mask is supported on the fixed reflected pattern

The cleared reflected-bent guard does more than preserve the inserted
channel.  Any positive graft face outside the guard is physically
nonadjacent to every inserted pattern face, while every guard face outside
the pattern is vacuum in both replicas.  Consequently the target-rooted
physical support component cannot leave the fixed sixteen-face pattern.

The paired strand graph refines the physical support graph.  Hence the
assignment-dependent face-switch mask of any accepted pair with the grafted
physical fields also vanishes away from that same fixed pattern.  This turns
the still-open mask-recovery problem into a cutoff-independent finite code;
it does not recover the mask bits or the switched auxiliary assignments.

Constructive contract: explicit finite graph chains, the proved guard
separation law, and Boolean component refinement only; no `Classical`,
choice, `native_decide`, `sorry`, new axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardFaceMaskSupport

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

/-! ## 1. One supported neighbour of the pattern stays in the pattern -/

/-- A positive graft face physically adjacent to an inserted pattern face is
itself one of the fixed pattern faces.  Inside the guard this follows from
literal agreement with the reflected pattern; outside the guard it follows
from the proved separating-collar law. -/
theorem reflectedBentGuardGraft_supportNeighbor_mem_pattern
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {patternFaceId faceId : Nat}
    (hpattern : patternFaceId ∈ reflectedBentPatternFaceIds)
    (hface : faceId ∈ slabTwoReplicaSupportFaceVertices 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state))
    (hadjacent : slabSupportFaceAdjacentB 5 patternFaceId faceId = true) :
    faceId ∈ reflectedBentPatternFaceIds := by
  have hparts := List.mem_filter.mp hface
  have hpositive :
      0 < reflectedBentGuardGraftLeftPhysical D hextent state faceId ∨
        0 < reflectedBentGuardGraftRightPhysical D hextent state faceId :=
    of_decide_eq_true hparts.2
  by_cases hguard : faceId ∈ reflectedBentPatternGuardFaceIds
  · have hleftEq :=
      reflectedBentGuardGraftLeftPhysical_eq_pattern_on_guard
        D hextent state faceId hguard
    have hrightEq :=
      reflectedBentGuardGraftRightPhysical_eq_pattern_on_guard
        D hextent state faceId hguard
    have hphysical : faceId ∈ slabPhysicalFaceEdges 5 := hparts.1
    apply (mem_reflectedBentPatternFaceIds_iff hphysical).mpr
    rcases hpositive with hleft | hright
    · rwa [hleftEq] at hleft
    · rw [hrightEq, reflectedBentSwitchRightPhysical_eq_zero] at hright
      omega
  · have hphysical : faceId ∈ slabPhysicalFaceEdges D.extent := by
      simpa only [hextent] using hparts.1
    have hseparated :=
      reflectedBentGuardGraft_no_exterior_support_adjacency
        D hextent state hphysical hguard hpositive hpattern
    have hreverse :
        slabSupportFaceAdjacentB 5 faceId patternFaceId = true := by
      rw [slabSupportFaceAdjacentB_symmetric 5 faceId patternFaceId]
      exact hadjacent
    rw [hreverse] at hseparated
    cases hseparated

/-! ## 2. The target-rooted physical component is fixed and local -/

private def reflectedBentGuardGraft_supportChainEnd_mem_pattern
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    {first last : Nat} →
      ChainIn (slabSupportFaceAdjacentB 5)
        (slabTwoReplicaSupportFaceVertices 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state))
        first last →
      first ∈ reflectedBentPatternFaceIds →
      last ∈ reflectedBentPatternFaceIds
  | _, _, .refl _, hfirst => hfirst
  | _, _, .step hedge hnext rest, hfirst =>
      reflectedBentGuardGraft_supportChainEnd_mem_pattern
        D hextent state rest
        (reflectedBentGuardGraft_supportNeighbor_mem_pattern
          D hextent state hfirst hnext hedge)

/-- The complete target-rooted union-support component of the graft is
contained in the fixed reflected pattern.  Exterior background support may
exist, but the cleared collar places it in other components. -/
theorem reflectedBentGuardGraft_targetSupportComponent_subset_pattern
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {faceId : Nat}
    (hface : faceId ∈ slabTwoReplicaTargetSupportComponent 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      reflectedBentTargetFaceId) :
    faceId ∈ reflectedBentPatternFaceIds := by
  let vertices := slabTwoReplicaSupportFaceVertices 5
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state)
  have htarget : reflectedBentTargetFaceId ∈ vertices :=
    mem_slabTwoReplicaSupportFaceVertices
      reflectedBentTargetFaceId_physical
      (Or.inl
        (reflectedBentGuardGraftLeftPhysical_target_pos
          D hextent state))
  have hchain : ChainIn (slabSupportFaceAdjacentB 5)
      (slabTwoReplicaTargetSupportComponent 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        reflectedBentTargetFaceId)
      reflectedBentTargetFaceId faceId :=
    rootComponent_connected
      (slabSupportFaceAdjacentB 5)
      (slabSupportFaceAdjacentB_symmetric 5)
      htarget reflectedBentTargetFaceId faceId
      (root_mem_rootComponent (slabSupportFaceAdjacentB 5) htarget)
      hface
  have hchainVertices : ChainIn (slabSupportFaceAdjacentB 5)
      vertices reflectedBentTargetFaceId faceId :=
    ChainIn.mono
      (fun point hpoint =>
        rootComponent_subset
          (slabSupportFaceAdjacentB 5) htarget hpoint)
      hchain
  exact reflectedBentGuardGraft_supportChainEnd_mem_pattern
    D hextent state hchainVertices reflectedBentTargetFaceId_mem_pattern

/-! ## 3. The assignment-dependent strand mask has the same fixed support -/

/-- Every face in the target-rooted paired strand component lies in the
fixed pattern whenever the accepted pair has the two grafted physical
fields. -/
theorem reflectedBentGuardGraft_pairTargetFaceComponent_subset_pattern
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hleft : pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent state)
    (hright : pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent state)
    {faceId : Nat}
    (hface : faceId ∈
      slabObservableTwoReplicaPairTargetFaceComponent
        D pair reflectedBentTargetFaceId) :
    faceId ∈ reflectedBentPatternFaceIds := by
  have hsupport :=
    slabObservableTwoReplicaPairTargetFaceComponent_subset_support
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (by simpa only [hextent] using reflectedBentTargetFaceId_physical)
      pair hpair hface
  have hsupportFixed : faceId ∈ slabTwoReplicaTargetSupportComponent 5
      (reflectedBentGuardGraftLeftPhysical D hextent state)
      (reflectedBentGuardGraftRightPhysical D hextent state)
      reflectedBentTargetFaceId := by
    simpa only [hextent, hleft, hright] using hsupport
  exact reflectedBentGuardGraft_targetSupportComponent_subset_pattern
    D hextent state hsupportFixed

/-- Exact cutoff-independent support statement for the still-open strand
mask: every face outside the sixteen-face reflected pattern has mask bit
`false`. -/
theorem reflectedBentGuardGraft_pairFaceSwapMask_eq_false_outside_pattern
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hleft : pair.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent state)
    (hright : pair.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent state)
    (faceId : Nat) (houtside : faceId ∉ reflectedBentPatternFaceIds) :
    slabObservableTwoReplicaPairPairedFaceSwapMask
      D pair reflectedBentTargetFaceId faceId = false := by
  unfold slabObservableTwoReplicaPairPairedFaceSwapMask
  exact decide_eq_false fun hface =>
    houtside
      (reflectedBentGuardGraft_pairTargetFaceComponent_subset_pattern
        D hextent state pair hpair hleft hright hface)

/-! ## 4. A fixed finite code faithfully records every guarded mask -/

/-- The assignment-dependent mask restricted to the fixed reflected support.
The carrier list is independent of the cutoff, accepted state, and auxiliary
assignment. -/
def reflectedBentGuardGraft_pairFaceSwapMaskCode
    (D : SlabPhysicalData)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    List Bool :=
  reflectedBentPatternFaceIds.map
    (slabObservableTwoReplicaPairPairedFaceSwapMask
      D pair reflectedBentTargetFaceId)

@[simp] theorem reflectedBentGuardGraft_pairFaceSwapMaskCode_length
    (D : SlabPhysicalData)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    (reflectedBentGuardGraft_pairFaceSwapMaskCode D pair).length =
      reflectedBentPatternFaceIds.length := by
  unfold reflectedBentGuardGraft_pairFaceSwapMaskCode
  simp only [List.length_map]

private theorem map_eq_map_value_of_mem_local
    {A B : Type} (first second : A → B) :
    ∀ {items : List A}, items.map first = items.map second →
      ∀ {item : A}, item ∈ items → first item = second item
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, heq, item, hmem => by
      have hhead : first head = second head := by
        have hsome : some (first head) = some (second head) := by
          simpa only [List.map_cons, List.head?_cons] using
            congrArg List.head? heq
        exact Option.some.inj hsome
      have htail : tail.map first = tail.map second := by
        exact congrArg List.tail heq
      rcases List.mem_cons.mp hmem with rfl | hmemTail
      · exact hhead
      · exact map_eq_map_value_of_mem_local
          first second htail hmemTail

/-- On the guarded graft carrier, equality of the fixed finite mask code
implies equality of the complete `Nat → Bool` strand masks.  The proof uses
the code on pattern faces and the support theorem's forced `false` value
everywhere else. -/
theorem reflectedBentGuardGraft_pairFaceSwapMask_eq_of_code_eq
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (firstState secondState : SlabAcceptedTwoReplicaState D)
    (first second :
      SlabObservableTwoReplicaPair D reflectedBentRootFaceId)
    (hfirstPair : first ∈ slabObservableFourCellSourcePairs
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hsecondPair : second ∈ slabObservableFourCellSourcePairs
      D reflectedBentRootFaceId reflectedBentTargetFaceId)
    (hfirstLeft : first.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent firstState)
    (hfirstRight : first.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent firstState)
    (hsecondLeft : second.1.1.1 =
      reflectedBentGuardGraftLeftPhysical D hextent secondState)
    (hsecondRight : second.2.1.1 =
      reflectedBentGuardGraftRightPhysical D hextent secondState)
    (hcode : reflectedBentGuardGraft_pairFaceSwapMaskCode D first =
      reflectedBentGuardGraft_pairFaceSwapMaskCode D second) :
    slabObservableTwoReplicaPairPairedFaceSwapMask
        D first reflectedBentTargetFaceId =
      slabObservableTwoReplicaPairPairedFaceSwapMask
        D second reflectedBentTargetFaceId := by
  funext faceId
  by_cases hpattern : faceId ∈ reflectedBentPatternFaceIds
  · exact map_eq_map_value_of_mem_local
      (slabObservableTwoReplicaPairPairedFaceSwapMask
        D first reflectedBentTargetFaceId)
      (slabObservableTwoReplicaPairPairedFaceSwapMask
        D second reflectedBentTargetFaceId)
      hcode hpattern
  · rw [reflectedBentGuardGraft_pairFaceSwapMask_eq_false_outside_pattern
        D hextent firstState first hfirstPair hfirstLeft hfirstRight
        faceId hpattern,
      reflectedBentGuardGraft_pairFaceSwapMask_eq_false_outside_pattern
        D hextent secondState second hsecondPair hsecondLeft hsecondRight
        faceId hpattern]

/-! ## 5. An explicit cutoff-independent carrier for all mask codes -/

/-- Every Boolean word of one exact length, used only for the fixed guarded
mask carrier. -/
def reflectedBentGuardBoolWords : Nat → List (List Bool)
  | 0 => [[]]
  | count + 1 =>
      (reflectedBentGuardBoolWords count).map (fun bits => false :: bits) ++
        (reflectedBentGuardBoolWords count).map (fun bits => true :: bits)

theorem reflectedBentGuardBoolWords_complete :
    ∀ {count : Nat} (bits : List Bool), bits.length = count →
      bits ∈ reflectedBentGuardBoolWords count
  | 0, bits, hlength => by
      cases bits with
      | nil => exact List.mem_cons_self
      | cons _ _ => simp only [List.length_cons] at hlength; omega
  | count + 1, [], hlength => by
      simp only [List.length_nil] at hlength
      omega
  | count + 1, bit :: bits, hlength => by
      have htail : bits.length = count := by
        simp only [List.length_cons] at hlength
        omega
      cases bit with
      | false =>
          apply List.mem_append_left
          exact List.mem_map.mpr
            ⟨bits, reflectedBentGuardBoolWords_complete bits htail, rfl⟩
      | true =>
          apply List.mem_append_right
          exact List.mem_map.mpr
            ⟨bits, reflectedBentGuardBoolWords_complete bits htail, rfl⟩

@[simp] theorem reflectedBentGuardBoolWords_length :
    ∀ count : Nat,
      (reflectedBentGuardBoolWords count).length = 2 ^ count
  | 0 => rfl
  | count + 1 => by
      simp only [reflectedBentGuardBoolWords, List.length_append,
        List.length_map, reflectedBentGuardBoolWords_length]
      rw [Nat.pow_succ]
      omega

/-- The fixed, exhaustive carrier of all possible guarded strand-mask codes.
Its definition contains no cutoff, state, or auxiliary data. -/
def reflectedBentGuardFaceSwapMaskCodeSpace : List (List Bool) :=
  reflectedBentGuardBoolWords reflectedBentPatternFaceIds.length

theorem reflectedBentGuardGraft_pairFaceSwapMaskCode_mem_codeSpace
    (D : SlabPhysicalData)
    (pair : SlabObservableTwoReplicaPair D reflectedBentRootFaceId) :
    reflectedBentGuardGraft_pairFaceSwapMaskCode D pair ∈
      reflectedBentGuardFaceSwapMaskCodeSpace := by
  unfold reflectedBentGuardFaceSwapMaskCodeSpace
  apply reflectedBentGuardBoolWords_complete
  exact reflectedBentGuardGraft_pairFaceSwapMaskCode_length D pair

@[simp] theorem reflectedBentGuardFaceSwapMaskCodeSpace_length :
    reflectedBentGuardFaceSwapMaskCodeSpace.length =
      2 ^ reflectedBentPatternFaceIds.length := by
  unfold reflectedBentGuardFaceSwapMaskCodeSpace
  exact reflectedBentGuardBoolWords_length _

#print axioms reflectedBentGuardGraft_supportNeighbor_mem_pattern
#print axioms reflectedBentGuardGraft_targetSupportComponent_subset_pattern
#print axioms reflectedBentGuardGraft_pairTargetFaceComponent_subset_pattern
#print axioms reflectedBentGuardGraft_pairFaceSwapMask_eq_false_outside_pattern
#print axioms reflectedBentGuardGraft_pairFaceSwapMaskCode
#print axioms reflectedBentGuardGraft_pairFaceSwapMaskCode_length
#print axioms reflectedBentGuardGraft_pairFaceSwapMask_eq_of_code_eq
#print axioms reflectedBentGuardBoolWords_complete
#print axioms reflectedBentGuardBoolWords_length
#print axioms reflectedBentGuardGraft_pairFaceSwapMaskCode_mem_codeSpace
#print axioms reflectedBentGuardFaceSwapMaskCodeSpace_length

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardFaceMaskSupport
