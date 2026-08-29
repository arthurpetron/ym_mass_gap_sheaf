/-
# A separating guard for the reflected bent-channel support

The reflected bent positive channel occupies sixteen physical faces in the
extent-five corrected slab.  Define its guard to contain every physical face
in the support and every physical face adjacent to that support through a
complete-slab link.

The complement of this guard has no physical-support edge to the inserted
channel.  Hence any paired background which is zero on the guard cannot make
a bypass from the reflected channel into its unchanged exterior support.
This is the finite geometric collar required before background-stable
insertion.

Constructive contract: finite filters and decidable corrected-slab adjacency
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

private theorem range_nodup : ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count :=
              List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

/-! ## 1. Literal support faces and their closed adjacency collar -/

/-- Physical face identifiers carrying the left-replica reflected pattern. -/
def reflectedBentPatternFaceIds : List Nat :=
  (slabPhysicalFaceEdges 5).filter fun faceId =>
    decide (0 < reflectedBentSwitchLeftPhysical faceId)

/-- A physical face is guarded when it belongs to the inserted support or is
adjacent to some inserted support face through a complete-slab link. -/
def reflectedBentPatternGuardB (faceId : Nat) : Bool :=
  decide
    (faceId ∈ reflectedBentPatternFaceIds ∨
      ∃ patternFaceId,
        patternFaceId ∈ reflectedBentPatternFaceIds ∧
        slabSupportFaceAdjacentB 5 faceId patternFaceId = true)

/-- The finite separating collar, in corrected-slab physical-face order. -/
def reflectedBentPatternGuardFaceIds : List Nat :=
  (slabPhysicalFaceEdges 5).filter reflectedBentPatternGuardB

theorem reflectedBentPatternFaceIds_nodup :
    reflectedBentPatternFaceIds.Nodup := by
  unfold reflectedBentPatternFaceIds
  exact List.filter_sublist.nodup (range_nodup _)

theorem reflectedBentPatternGuardFaceIds_nodup :
    reflectedBentPatternGuardFaceIds.Nodup := by
  unfold reflectedBentPatternGuardFaceIds
  exact List.filter_sublist.nodup (range_nodup _)

theorem reflectedBentPatternFaceId_mem_physical
    {faceId : Nat} (hface : faceId ∈ reflectedBentPatternFaceIds) :
    faceId ∈ slabPhysicalFaceEdges 5 :=
  (List.mem_filter.mp hface).1

theorem reflectedBentPatternGuardFaceId_mem_physical
    {faceId : Nat} (hface : faceId ∈ reflectedBentPatternGuardFaceIds) :
    faceId ∈ slabPhysicalFaceEdges 5 :=
  (List.mem_filter.mp hface).1

theorem mem_reflectedBentPatternFaceIds_iff
    {faceId : Nat} (hphysical : faceId ∈ slabPhysicalFaceEdges 5) :
    faceId ∈ reflectedBentPatternFaceIds ↔
      0 < reflectedBentSwitchLeftPhysical faceId := by
  unfold reflectedBentPatternFaceIds
  rw [List.mem_filter]
  simp only [hphysical, true_and, decide_eq_true_eq]

/-- The support itself is contained in its guard. -/
theorem reflectedBentPatternFace_mem_guard
    {faceId : Nat} (hface : faceId ∈ reflectedBentPatternFaceIds) :
    faceId ∈ reflectedBentPatternGuardFaceIds := by
  unfold reflectedBentPatternGuardFaceIds
  apply List.mem_filter.mpr
  refine ⟨reflectedBentPatternFaceId_mem_physical hface, ?_⟩
  unfold reflectedBentPatternGuardB
  exact decide_eq_true (Or.inl hface)

/-! ## 2. The guard separates the inserted pattern from the exterior -/

/-- A physical face outside the guard has no support-adjacency edge to any
face of the reflected pattern. -/
theorem slabSupportFaceAdjacentB_eq_false_of_not_mem_reflectedBentGuard
    {queryFaceId patternFaceId : Nat}
    (hqueryPhysical : queryFaceId ∈ slabPhysicalFaceEdges 5)
    (hqueryOutside : queryFaceId ∉ reflectedBentPatternGuardFaceIds)
    (hpattern : patternFaceId ∈ reflectedBentPatternFaceIds) :
    slabSupportFaceAdjacentB 5 queryFaceId patternFaceId = false := by
  have hguardFalse : reflectedBentPatternGuardB queryFaceId = false := by
    cases hguard : reflectedBentPatternGuardB queryFaceId with
    | false => rfl
    | true =>
        exact False.elim (hqueryOutside
          (List.mem_filter.mpr ⟨hqueryPhysical, hguard⟩))
  have hguardNot :
      ¬ (queryFaceId ∈ reflectedBentPatternFaceIds ∨
        ∃ supportFaceId,
          supportFaceId ∈ reflectedBentPatternFaceIds ∧
          slabSupportFaceAdjacentB
            5 queryFaceId supportFaceId = true) := by
    unfold reflectedBentPatternGuardB at hguardFalse
    exact of_decide_eq_false hguardFalse
  cases hadjacent :
      slabSupportFaceAdjacentB 5 queryFaceId patternFaceId with
  | false => rfl
  | true =>
      exact False.elim (hguardNot
        (Or.inr ⟨patternFaceId, hpattern, hadjacent⟩))

/-- If both replicas of a physical background vanish on the guard, every
positive exterior face is nonadjacent to the inserted reflected support. -/
theorem reflectedBentGuard_zero_separates_positive_background
    (left right : SlabLabelling)
    (hzero : ∀ faceId, faceId ∈ reflectedBentPatternGuardFaceIds →
      left faceId = 0 ∧ right faceId = 0)
    {queryFaceId patternFaceId : Nat}
    (hqueryPhysical : queryFaceId ∈ slabPhysicalFaceEdges 5)
    (hqueryPositive : 0 < left queryFaceId ∨ 0 < right queryFaceId)
    (hpattern : patternFaceId ∈ reflectedBentPatternFaceIds) :
    slabSupportFaceAdjacentB 5 queryFaceId patternFaceId = false := by
  have hqueryOutside :
      queryFaceId ∉ reflectedBentPatternGuardFaceIds := by
    intro hguard
    have hvalues := hzero queryFaceId hguard
    rcases hqueryPositive with hleft | hright
    · rw [hvalues.1] at hleft
      omega
    · rw [hvalues.2] at hright
      omega
  exact
    slabSupportFaceAdjacentB_eq_false_of_not_mem_reflectedBentGuard
      hqueryPhysical hqueryOutside hpattern

#print axioms reflectedBentPatternFaceIds
#print axioms reflectedBentPatternGuardFaceIds
#print axioms reflectedBentPatternFace_mem_guard
#print axioms slabSupportFaceAdjacentB_eq_false_of_not_mem_reflectedBentGuard
#print axioms reflectedBentGuard_zero_separates_positive_background

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
