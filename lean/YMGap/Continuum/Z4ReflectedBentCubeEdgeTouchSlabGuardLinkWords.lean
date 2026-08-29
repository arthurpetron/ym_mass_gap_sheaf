/-
# Link-word dichotomy for the guarded reflected graft

At a complete corrected-slab link, ask whether one of the incident faces
belongs to the inserted reflected support.  If so, every incident face lies
in the cleared guard and the entire grafted external spin word is exactly the
known reflected word.  If not, the inserted pattern vanishes on every
incident face and the entire word is exactly the peeled terminal word.

This two-word dichotomy is the local compatibility statement needed to splice
the two already accepted auxiliary assignments link by link.  It does not yet
construct that global assignment or transport the positive recoupling row.

Constructive contract: finite `List.any`, corrected-slab incidence, and the
proved guard equalities only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportWholeLinkSwitch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

/-! ## 1. Executable recognition of a pattern-active link -/

/-- A link is active for the inserted pattern exactly when the finite support
list contains an incident face. -/
def reflectedBentPatternActiveLinkB (link : SlabLink) : Bool :=
  reflectedBentPatternFaceIds.any fun faceId =>
    decide (faceId ∈ slabIncidentPlaqIds 5 link)

theorem reflectedBentPatternActiveLinkB_eq_true_iff
    (link : SlabLink) :
    reflectedBentPatternActiveLinkB link = true ↔
      ∃ faceId, faceId ∈ reflectedBentPatternFaceIds ∧
        faceId ∈ slabIncidentPlaqIds 5 link := by
  constructor
  · intro hactive
    obtain ⟨faceId, hpattern, hincident⟩ :=
      List.any_eq_true.mp hactive
    exact ⟨faceId, hpattern, of_decide_eq_true hincident⟩
  · rintro ⟨faceId, hpattern, hincident⟩
    apply List.any_eq_true.mpr
    exact ⟨faceId, hpattern, decide_eq_true hincident⟩

theorem reflectedBentPatternActiveLinkB_eq_false_iff
    (link : SlabLink) :
    reflectedBentPatternActiveLinkB link = false ↔
      ∀ faceId, faceId ∈ slabIncidentPlaqIds 5 link →
        faceId ∉ reflectedBentPatternFaceIds := by
  constructor
  · intro hinactive faceId hincident hpattern
    have htrue : reflectedBentPatternActiveLinkB link = true :=
      (reflectedBentPatternActiveLinkB_eq_true_iff link).mpr
        ⟨faceId, hpattern, hincident⟩
    rw [hinactive] at htrue
    contradiction
  · intro hnone
    cases hactive : reflectedBentPatternActiveLinkB link with
    | false => rfl
    | true =>
        obtain ⟨faceId, hpattern, hincident⟩ :=
          (reflectedBentPatternActiveLinkB_eq_true_iff link).mp hactive
        exact False.elim (hnone faceId hincident hpattern)

/-! ## 2. Active links see the known reflected word -/

/-- Any face sharing a complete-slab link with an inserted support face lies
in the closed guard. -/
theorem reflectedBentIncidentFace_mem_guard_of_active
    {link : SlabLink}
    (hlink : link ∈ boundaryCompleteSlabLinks 5)
    (hactive : reflectedBentPatternActiveLinkB link = true)
    {faceId : Nat} (hincident : faceId ∈ slabIncidentPlaqIds 5 link) :
    faceId ∈ reflectedBentPatternGuardFaceIds := by
  obtain ⟨patternFaceId, hpattern, hpatternIncident⟩ :=
    (reflectedBentPatternActiveLinkB_eq_true_iff link).mp hactive
  unfold reflectedBentPatternGuardFaceIds
  apply List.mem_filter.mpr
  refine ⟨slabIncidentPlaqId_physical hincident, ?_⟩
  unfold reflectedBentPatternGuardB
  apply decide_eq_true
  exact Or.inr ⟨patternFaceId, hpattern,
    slabSupportFaceAdjacentB_true_of_link
      hlink hincident hpatternIncident⟩

theorem reflectedBentGuardGraft_eq_pattern_on_active_link
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {link : SlabLink}
    (hlink : link ∈ boundaryCompleteSlabLinks 5)
    (hactive : reflectedBentPatternActiveLinkB link = true)
    (faceId : Nat) (hincident : faceId ∈ slabIncidentPlaqIds 5 link) :
    reflectedBentGuardGraftLeftPhysical D hextent state faceId =
        reflectedBentSwitchLeftPhysical faceId ∧
      reflectedBentGuardGraftRightPhysical D hextent state faceId =
        reflectedBentSwitchRightPhysical faceId := by
  have hguard := reflectedBentIncidentFace_mem_guard_of_active
    hlink hactive hincident
  exact ⟨
    reflectedBentGuardGraftLeftPhysical_eq_pattern_on_guard
      D hextent state faceId hguard,
    reflectedBentGuardGraftRightPhysical_eq_pattern_on_guard
      D hextent state faceId hguard⟩

theorem reflectedBentGuardGraftLeftExternalSpins_eq_pattern_of_active
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {link : SlabLink}
    (hlink : link ∈ boundaryCompleteSlabLinks 5)
    (hactive : reflectedBentPatternActiveLinkB link = true) :
    slabLinkExternalSpins 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) link =
      slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical link := by
  apply slabLinkExternalSpins_eq_of_eq_on_incident
  intro faceId hincident
  exact (reflectedBentGuardGraft_eq_pattern_on_active_link
    D hextent state hlink hactive faceId hincident).1

theorem reflectedBentGuardGraftRightExternalSpins_eq_pattern_of_active
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {link : SlabLink}
    (hlink : link ∈ boundaryCompleteSlabLinks 5)
    (hactive : reflectedBentPatternActiveLinkB link = true) :
    slabLinkExternalSpins 5
        (reflectedBentGuardGraftRightPhysical D hextent state) link =
      slabLinkExternalSpins 5 reflectedBentSwitchRightPhysical link := by
  apply slabLinkExternalSpins_eq_of_eq_on_incident
  intro faceId hincident
  exact (reflectedBentGuardGraft_eq_pattern_on_active_link
    D hextent state hlink hactive faceId hincident).2

/-! ## 3. Inactive links see the peeled terminal word -/

theorem reflectedBentGuardGraftLeftPhysical_eq_terminal_on_inactive_link
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {link : SlabLink}
    (hinactive : reflectedBentPatternActiveLinkB link = false)
    (faceId : Nat) (hincident : faceId ∈ slabIncidentPlaqIds 5 link) :
    reflectedBentGuardGraftLeftPhysical D hextent state faceId =
      (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 faceId := by
  have hnotPattern : faceId ∉ reflectedBentPatternFaceIds :=
    (reflectedBentPatternActiveLinkB_eq_false_iff link).mp
      hinactive faceId hincident
  have hnotPositive : ¬ 0 < reflectedBentSwitchLeftPhysical faceId := by
    intro hpositive
    exact hnotPattern
      ((mem_reflectedBentPatternFaceIds_iff
        (slabIncidentPlaqId_physical hincident)).mpr hpositive)
  unfold reflectedBentGuardGraftLeftPhysical
  split
  · rename_i hpositive
    exact False.elim (hnotPositive hpositive)
  · rfl

theorem reflectedBentGuardGraftLeftExternalSpins_eq_terminal_of_inactive
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {link : SlabLink}
    (hinactive : reflectedBentPatternActiveLinkB link = false) :
    slabLinkExternalSpins 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) link =
      slabLinkExternalSpins 5
        (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 link := by
  apply slabLinkExternalSpins_eq_of_eq_on_incident
  intro faceId hincident
  exact reflectedBentGuardGraftLeftPhysical_eq_terminal_on_inactive_link
    D hextent state hinactive faceId hincident

theorem reflectedBentGuardGraftRightExternalSpins_eq_terminal
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) (link : SlabLink) :
    slabLinkExternalSpins 5
        (reflectedBentGuardGraftRightPhysical D hextent state) link =
      slabLinkExternalSpins 5
        (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1 link :=
  rfl

/-! ## 4. The same dichotomy for literal accepted local fibers -/

theorem reflectedBentGuardGraftLeftFusionWitnesses_eq_pattern_of_active
    (K : Nat) (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {link : SlabLink}
    (hlink : link ∈ boundaryCompleteSlabLinks 5)
    (hactive : reflectedBentPatternActiveLinkB link = true) :
    slabLinkFusionWitnesses K 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) link =
      slabLinkFusionWitnesses K 5 reflectedBentSwitchLeftPhysical link := by
  apply slabLinkFusionWitnesses_eq_of_eq_on_incident
  intro faceId hincident
  exact (reflectedBentGuardGraft_eq_pattern_on_active_link
    D hextent state hlink hactive faceId hincident).1

theorem reflectedBentGuardGraftLeftFusionWitnesses_eq_terminal_of_inactive
    (K : Nat) (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    {link : SlabLink}
    (hinactive : reflectedBentPatternActiveLinkB link = false) :
    slabLinkFusionWitnesses K 5
        (reflectedBentGuardGraftLeftPhysical D hextent state) link =
      slabLinkFusionWitnesses K 5
        (reflectedBentGuardCanonicalPeeling D hextent state).1.1.1.1 link := by
  apply slabLinkFusionWitnesses_eq_of_eq_on_incident
  intro faceId hincident
  exact reflectedBentGuardGraftLeftPhysical_eq_terminal_on_inactive_link
    D hextent state hinactive faceId hincident

theorem reflectedBentGuardGraftRightFusionWitnesses_eq_terminal
    (K : Nat) (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) (link : SlabLink) :
    slabLinkFusionWitnesses K 5
        (reflectedBentGuardGraftRightPhysical D hextent state) link =
      slabLinkFusionWitnesses K 5
        (reflectedBentGuardCanonicalPeeling D hextent state).1.2.1.1 link := by
  apply slabLinkFusionWitnesses_eq_of_eq_on_incident
  intro faceId _
  rfl

#print axioms reflectedBentPatternActiveLinkB_eq_true_iff
#print axioms reflectedBentPatternActiveLinkB_eq_false_iff
#print axioms reflectedBentIncidentFace_mem_guard_of_active
#print axioms reflectedBentGuardGraftLeftExternalSpins_eq_pattern_of_active
#print axioms reflectedBentGuardGraftLeftExternalSpins_eq_terminal_of_inactive
#print axioms reflectedBentGuardGraftLeftFusionWitnesses_eq_pattern_of_active
#print axioms reflectedBentGuardGraftLeftFusionWitnesses_eq_terminal_of_inactive
#print axioms reflectedBentGuardGraftRightFusionWitnesses_eq_terminal

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLinkWords
