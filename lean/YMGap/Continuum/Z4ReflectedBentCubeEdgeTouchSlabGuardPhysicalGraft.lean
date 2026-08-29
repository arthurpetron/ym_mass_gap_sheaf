/-
# Physical graft of the reflected channel into a cleared guard

After guarded canonical peeling, both terminal replicas vanish on the whole
separating collar.  Insert the fixed reflected-bent left physical pattern on
its sixteen support faces and retain the terminal physical fields everywhere
else; the right inserted pattern is vacuum.

The graft agrees exactly with the known reflected source throughout the
guard and exactly with the canonical terminal outside it.  Since the guard
separates its support from every positive exterior face, no physical-support
bypass can cross between the inserted channel and the retained background.

This is a physical-labelling theorem.  Linkwise auxiliary acceptance and the
positive recoupling graft are separate downstream obligations.

Constructive contract: pointwise decidable insertion and the proved guard
clearing/separation laws only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

/-! ## 1. Pointwise physical insertion -/

/-- Insert the fixed reflected left support wherever it is positive and keep
the peeled terminal left field elsewhere. -/
def reflectedBentGuardGraftLeftPhysical
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : SlabLabelling :=
  fun faceId =>
    if 0 < reflectedBentSwitchLeftPhysical faceId then
      reflectedBentSwitchLeftPhysical faceId
    else
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 faceId

/-- The reflected right inserted pattern is vacuum, so retain the terminal
right field. -/
def reflectedBentGuardGraftRightPhysical
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : SlabLabelling :=
  (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1

theorem reflectedBentSwitchRightPhysical_eq_zero (faceId : Nat) :
    reflectedBentSwitchRightPhysical faceId = 0 := by
  unfold reflectedBentSwitchRightPhysical
  rw [reflectedBentCarrier_rightPhysical]
  unfold slabBinarySupportLabelling
  split
  · simp
  · rfl

/-! ## 2. Exact agreement on the guard and its complement -/

/-- On every guard face, the grafted left field is literally the known
reflected left pattern. -/
theorem reflectedBentGuardGraftLeftPhysical_eq_pattern_on_guard
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hguard : faceId ∈ reflectedBentPatternGuardFaceIds) :
    reflectedBentGuardGraftLeftPhysical D hextent state faceId =
      reflectedBentSwitchLeftPhysical faceId := by
  have hzero :=
    reflectedBentGuardCanonicalPeeling_final_zero
      D hextent state faceId hguard
  unfold reflectedBentGuardGraftLeftPhysical
  split
  · rfl
  · rename_i hpositive
    have hpatternZero : reflectedBentSwitchLeftPhysical faceId = 0 := by
      omega
    rw [hzero.1, hpatternZero]

/-- On every guard face, the retained terminal right field is literally the
known reflected vacuum field. -/
theorem reflectedBentGuardGraftRightPhysical_eq_pattern_on_guard
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat) (hguard : faceId ∈ reflectedBentPatternGuardFaceIds) :
    reflectedBentGuardGraftRightPhysical D hextent state faceId =
      reflectedBentSwitchRightPhysical faceId := by
  have hzero :=
    reflectedBentGuardCanonicalPeeling_final_zero
      D hextent state faceId hguard
  unfold reflectedBentGuardGraftRightPhysical
  rw [hzero.2, reflectedBentSwitchRightPhysical_eq_zero]

/-- Outside the guard, the reflected pattern is absent and the graft leaves
the terminal left field literally unchanged. -/
theorem reflectedBentGuardGraftLeftPhysical_eq_terminal_outside
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (faceId : Nat)
    (hphysical : faceId ∈ slabPhysicalFaceEdges D.extent)
    (houtside : faceId ∉ reflectedBentPatternGuardFaceIds) :
    reflectedBentGuardGraftLeftPhysical D hextent state faceId =
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 faceId := by
  have hphysicalFive : faceId ∈ slabPhysicalFaceEdges 5 := by
    simpa only [hextent] using hphysical
  have hnotPattern : faceId ∉ reflectedBentPatternFaceIds := by
    intro hpattern
    exact houtside (reflectedBentPatternFace_mem_guard hpattern)
  have hnotPositive : ¬ 0 < reflectedBentSwitchLeftPhysical faceId := by
    intro hpositive
    exact hnotPattern
      ((mem_reflectedBentPatternFaceIds_iff hphysicalFive).mpr hpositive)
  unfold reflectedBentGuardGraftLeftPhysical
  split
  · rename_i hpositive
    exact False.elim (hnotPositive hpositive)
  · rfl

theorem reflectedBentGuardGraftRightPhysical_eq_terminal
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) (faceId : Nat) :
    reflectedBentGuardGraftRightPhysical D hextent state faceId =
      (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1 faceId :=
  rfl

/-! ## 3. No background bypass into the graft -/

/-- Every positive grafted face outside the guard is a positive terminal
background face, and is therefore nonadjacent to every inserted support
face. -/
theorem reflectedBentGuardGraft_no_exterior_support_adjacency
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {queryFaceId patternFaceId : Nat}
    (hqueryPhysical : queryFaceId ∈ slabPhysicalFaceEdges D.extent)
    (hqueryOutside : queryFaceId ∉ reflectedBentPatternGuardFaceIds)
    (hqueryPositive :
      0 < reflectedBentGuardGraftLeftPhysical
          D hextent state queryFaceId ∨
        0 < reflectedBentGuardGraftRightPhysical
          D hextent state queryFaceId)
    (hpattern : patternFaceId ∈ reflectedBentPatternFaceIds) :
    slabSupportFaceAdjacentB 5 queryFaceId patternFaceId = false := by
  have hleftEq :=
    reflectedBentGuardGraftLeftPhysical_eq_terminal_outside
      D hextent state queryFaceId hqueryPhysical hqueryOutside
  have hrightEq :=
    reflectedBentGuardGraftRightPhysical_eq_terminal
      D hextent state queryFaceId
  have hterminalPositive :
      0 < (reflectedBentGuardCanonicalPeeling
          D hextent state).1.1.1.1 queryFaceId ∨
        0 < (reflectedBentGuardCanonicalPeeling
          D hextent state).1.2.1.1 queryFaceId := by
    rcases hqueryPositive with hleft | hright
    · exact Or.inl (by rwa [hleftEq] at hleft)
    · exact Or.inr (by rwa [hrightEq] at hright)
  have hzero : ∀ faceId,
      faceId ∈ reflectedBentPatternGuardFaceIds →
        (reflectedBentGuardCanonicalPeeling
          D hextent state).1.1.1.1 faceId = 0 ∧
        (reflectedBentGuardCanonicalPeeling
          D hextent state).1.2.1.1 faceId = 0 :=
    fun faceId hface =>
      reflectedBentGuardCanonicalPeeling_final_zero
        D hextent state faceId hface
  have hqueryPhysicalFive : queryFaceId ∈ slabPhysicalFaceEdges 5 := by
    simpa only [hextent] using hqueryPhysical
  exact reflectedBentGuard_zero_separates_positive_background
    (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1
    (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1
    hzero hqueryPhysicalFive hterminalPositive hpattern

/-! ## 4. Both marked reflected faces belong to the inserted support -/

theorem reflectedBentRootFaceId_mem_pattern :
    reflectedBentRootFaceId ∈ reflectedBentPatternFaceIds := by
  apply (mem_reflectedBentPatternFaceIds_iff
    reflectedBentRootFaceId_physical).mpr
  exact reflectedBentBinaryConnectedCarrier.face_positive
    reflectedBentBinaryConnectedCarrier.rootPlaquette
    reflectedBentBinaryConnectedCarrier.root_mem

theorem reflectedBentTargetFaceId_mem_pattern :
    reflectedBentTargetFaceId ∈ reflectedBentPatternFaceIds := by
  apply (mem_reflectedBentPatternFaceIds_iff
    reflectedBentTargetFaceId_physical).mpr
  exact reflectedBentBinaryConnectedCarrier.face_positive
    reflectedBentBinaryConnectedCarrier.targetPlaquette
    reflectedBentBinaryConnectedCarrier.target_mem

#print axioms reflectedBentGuardGraftLeftPhysical
#print axioms reflectedBentGuardGraftRightPhysical
#print axioms reflectedBentSwitchRightPhysical_eq_zero
#print axioms reflectedBentGuardGraftLeftPhysical_eq_pattern_on_guard
#print axioms reflectedBentGuardGraftRightPhysical_eq_pattern_on_guard
#print axioms reflectedBentGuardGraftLeftPhysical_eq_terminal_outside
#print axioms reflectedBentGuardGraft_no_exterior_support_adjacency
#print axioms reflectedBentRootFaceId_mem_pattern
#print axioms reflectedBentTargetFaceId_mem_pattern

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
