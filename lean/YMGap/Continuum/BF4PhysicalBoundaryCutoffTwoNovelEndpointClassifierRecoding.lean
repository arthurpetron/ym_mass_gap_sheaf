/-
# Classifier-normal form for novel endpoint pairs

The later cutoff-two old/new partition is now decided directly from the
represented state.  This module transports that partition through the novel
endpoint-pair enumeration.  A pair is novel exactly when both endpoints lie
in the later vacuum component and at least one endpoint is rejected by the
cutoff-two 65-sector classifier.

Because the accepted block always has 65 entries, the exact number of ordered
novel pairs is `n^2 + 130 n`, where `n` is the number of genuinely new states.
Thus every variable endpoint-pair cost is explicitly a function of shell
size alone.

No bound on that shell size, route congestion, cofinal capacity,
thermodynamic/continuum construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. The accept/reject partition -/

def cutoffTwoClassifierAcceptedIndices (later : Nat) : List Nat :=
  (cutoffTwoEdgeLoadFullStates later).filter
    (fun index =>
      cutoffTwoCubeSectorStateB
        (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 index))

def cutoffTwoClassifierRejectedIndices (later : Nat) : List Nat :=
  (cutoffTwoEdgeLoadFullStates later).filter
    (fun index =>
      !(cutoffTwoCubeSectorStateB
        (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 index)))

theorem cutoffTwoEdgeLoadOldStates_eq_classifierAcceptedIndices
    {later : Nat} (hcutoff : 2 ≤ later) :
    cutoffTwoEdgeLoadOldStates later =
      cutoffTwoClassifierAcceptedIndices later := by
  unfold cutoffTwoClassifierAcceptedIndices
  exact cutoffTwoEdgeLoadOldStates_eq_classifierAcceptFilter hcutoff

theorem cutoffTwoEdgeLoadNewStates_eq_classifierRejectedIndices
    {later : Nat} (hcutoff : 2 ≤ later) :
    cutoffTwoEdgeLoadNewStates later =
      cutoffTwoClassifierRejectedIndices later := by
  unfold cutoffTwoClassifierRejectedIndices
  exact cutoffTwoEdgeLoadNewStates_eq_classifierRejectFilter hcutoff

theorem mem_cutoffTwoEdgeLoadOldStates_iff_classifier_accept
    {later index : Nat} (hcutoff : 2 ≤ later) :
    index ∈ cutoffTwoEdgeLoadOldStates later ↔
      index ∈ cutoffTwoEdgeLoadFullStates later ∧
        cutoffTwoCubeSectorStateB
          (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
            (by decide) later 0 index) = true := by
  rw [cutoffTwoEdgeLoadOldStates_eq_classifierAcceptedIndices hcutoff]
  unfold cutoffTwoClassifierAcceptedIndices
  exact List.mem_filter

/-! ## 2. Exact classifier presentation of novel pairs -/

def cutoffTwoClassifierNovelEndpointPairs (later : Nat) :
    List (Nat × Nat) :=
  cartesian
      (cutoffTwoClassifierRejectedIndices later)
      (cutoffTwoClassifierRejectedIndices later) ++
    (cartesian
        (cutoffTwoClassifierAcceptedIndices later)
        (cutoffTwoClassifierRejectedIndices later) ++
      cartesian
        (cutoffTwoClassifierRejectedIndices later)
        (cutoffTwoClassifierAcceptedIndices later))

theorem cutoffTwoNovelEndpointPairs_eq_classifierPairs
    {later : Nat} (hcutoff : 2 ≤ later) :
    cutoffTwoNovelEndpointPairs later =
      cutoffTwoClassifierNovelEndpointPairs later := by
  unfold cutoffTwoNovelEndpointPairs cutoffTwoCanonicalCrossEndpointPairs
    cutoffTwoClassifierNovelEndpointPairs
  rw [cutoffTwoEdgeLoadOldStates_eq_classifierAcceptedIndices hcutoff,
    cutoffTwoEdgeLoadNewStates_eq_classifierRejectedIndices hcutoff]

theorem mem_cutoffTwoNovelEndpointPairs_iff_classifier_reject
    {later : Nat} (hcutoff : 2 ≤ later) (pair : Nat × Nat) :
    pair ∈ cutoffTwoNovelEndpointPairs later ↔
      pair.1 ∈ cutoffTwoEdgeLoadFullStates later ∧
        pair.2 ∈ cutoffTwoEdgeLoadFullStates later ∧
          (cutoffTwoCubeSectorStateB
                (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                  (by decide) later 0 pair.1) = false ∨
            cutoffTwoCubeSectorStateB
                (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                  (by decide) later 0 pair.2) = false) := by
  constructor
  · intro hpair
    have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
    refine ⟨hfull.1, hfull.2, ?_⟩
    unfold cutoffTwoNovelEndpointPairs
      cutoffTwoCanonicalCrossEndpointPairs at hpair
    rcases List.mem_append.mp hpair with hnewNew | hcross
    · have hblocks :=
        (mem_cartesian_iff
          (cutoffTwoEdgeLoadNewStates later)
          (cutoffTwoEdgeLoadNewStates later) pair).mp hnewNew
      exact Or.inl
        ((mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject hcutoff).mp
          hblocks.1).2
    · rcases List.mem_append.mp hcross with holdNew | hnewOld
      · have hblocks :=
          (mem_cartesian_iff
            (cutoffTwoEdgeLoadOldStates later)
            (cutoffTwoEdgeLoadNewStates later) pair).mp holdNew
        exact Or.inr
          ((mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject hcutoff).mp
            hblocks.2).2
      · have hblocks :=
          (mem_cartesian_iff
            (cutoffTwoEdgeLoadNewStates later)
            (cutoffTwoEdgeLoadOldStates later) pair).mp hnewOld
        exact Or.inl
          ((mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject hcutoff).mp
            hblocks.1).2
  · rintro ⟨hleftFull, hrightFull, hreject⟩
    unfold cutoffTwoNovelEndpointPairs cutoffTwoCanonicalCrossEndpointPairs
    rcases hreject with hleftReject | hrightReject
    · have hleftNew :=
        (mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject hcutoff).mpr
          ⟨hleftFull, hleftReject⟩
      by_cases hrightReject' :
          cutoffTwoCubeSectorStateB
              (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                (by decide) later 0 pair.2) = false
      · have hrightNew :=
          (mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject hcutoff).mpr
            ⟨hrightFull, hrightReject'⟩
        exact List.mem_append.mpr
          (Or.inl ((mem_cartesian_iff _ _ pair).mpr
            ⟨hleftNew, hrightNew⟩))
      · have hrightAccept :
            cutoffTwoCubeSectorStateB
                (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                  (by decide) later 0 pair.2) = true := by
          cases hclassifier :
              cutoffTwoCubeSectorStateB
                (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                  (by decide) later 0 pair.2) with
          | false => exact False.elim (hrightReject' hclassifier)
          | true => rfl
        have hrightOld :=
          (mem_cutoffTwoEdgeLoadOldStates_iff_classifier_accept hcutoff).mpr
            ⟨hrightFull, hrightAccept⟩
        exact List.mem_append.mpr
          (Or.inr (List.mem_append.mpr
            (Or.inr ((mem_cartesian_iff _ _ pair).mpr
              ⟨hleftNew, hrightOld⟩))))
    · have hrightNew :=
        (mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject hcutoff).mpr
          ⟨hrightFull, hrightReject⟩
      by_cases hleftReject' :
          cutoffTwoCubeSectorStateB
              (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                (by decide) later 0 pair.1) = false
      · have hleftNew :=
          (mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject hcutoff).mpr
            ⟨hleftFull, hleftReject'⟩
        exact List.mem_append.mpr
          (Or.inl ((mem_cartesian_iff _ _ pair).mpr
            ⟨hleftNew, hrightNew⟩))
      · have hleftAccept :
            cutoffTwoCubeSectorStateB
                (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                  (by decide) later 0 pair.1) = true := by
          cases hclassifier :
              cutoffTwoCubeSectorStateB
                (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                  (by decide) later 0 pair.1) with
          | false => exact False.elim (hleftReject' hclassifier)
          | true => rfl
        have hleftOld :=
          (mem_cutoffTwoEdgeLoadOldStates_iff_classifier_accept hcutoff).mpr
            ⟨hleftFull, hleftAccept⟩
        exact List.mem_append.mpr
          (Or.inr (List.mem_append.mpr
            (Or.inl ((mem_cartesian_iff _ _ pair).mpr
              ⟨hleftOld, hrightNew⟩))))

/-! ## 3. Exact endpoint-pair count in terms of shell size -/

private theorem cartesian_length_local
    {A B : Type} (right : List B) : ∀ left : List A,
    (cartesian left right).length = left.length * right.length
  | [] => by
      simp [cartesian]
  | head :: tail => by
      change
        (right.map (fun item => (head, item)) ++
          cartesian tail right).length =
        (head :: tail).length * right.length
      simp only [List.length_append, List.length_map, List.length_cons]
      rw [cartesian_length_local right tail]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

theorem cutoffTwoNovelEndpointPairs_length
    {later : Nat} (hcutoff : 2 ≤ later) :
    (cutoffTwoNovelEndpointPairs later).length =
      (cutoffTwoEdgeLoadNewStates later).length *
          (cutoffTwoEdgeLoadNewStates later).length +
        130 * (cutoffTwoEdgeLoadNewStates later).length := by
  unfold cutoffTwoNovelEndpointPairs cutoffTwoCanonicalCrossEndpointPairs
  simp only [List.length_append, cartesian_length_local]
  rw [cutoffTwoEdgeLoadOldStates_length_of_later hcutoff]
  omega

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding.cutoffTwoEdgeLoadOldStates_eq_classifierAcceptedIndices
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding.mem_cutoffTwoEdgeLoadOldStates_iff_classifier_accept
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding.cutoffTwoNovelEndpointPairs_eq_classifierPairs
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding.mem_cutoffTwoNovelEndpointPairs_iff_classifier_reject
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointClassifierRecoding.cutoffTwoNovelEndpointPairs_length
