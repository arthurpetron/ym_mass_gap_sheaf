/-
# Coordinate reindexing for finite scoped-factor partition sums

This is the finite change-of-variables theorem needed for factor-graph
automorphisms. A source coordinate list is renamed injectively, the same
finite label word is decoded on the renamed list, and pointwise product
transport lifts to equality of the complete partition sums.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteScopedFactorTableCertificate

namespace YMGap.Continuum.FiniteScopedFactorCoordinateReindex

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.FiniteVariableEliminationCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- A coordinate renaming is injective on the finite source carrier. -/
def InjectiveOnCoordinates
    (coordinates : List Nat) (rename : Nat → Nat) : Prop :=
  ∀ left, left ∈ coordinates →
    ∀ right, right ∈ coordinates →
      rename left = rename right → left = right

/-- A source and target labelling carry the same digits under a renaming. -/
def LabellingsAgreeUnder
    (coordinates : List Nat) (rename : Nat → Nat)
    (source target : EdgeLabelling) : Prop :=
  ∀ id, id ∈ coordinates → target (rename id) = source id

private theorem injectiveOnCoordinates_tail
    {head : Nat} {tail : List Nat} {rename : Nat → Nat}
    (hinjective : InjectiveOnCoordinates (head :: tail) rename) :
    InjectiveOnCoordinates tail rename := by
  intro left hleft right hright heq
  exact hinjective left (List.mem_cons_of_mem head hleft)
    right (List.mem_cons_of_mem head hright) heq

/-- Decoding the same word on an injectively renamed coordinate list gives
paired labellings. -/
theorem wordToEdgeLabelling_rename_agree
    (rename : Nat → Nat) (coordinates labels : List Nat)
    (hnodup : coordinates.Nodup)
    (hinjective : InjectiveOnCoordinates coordinates rename)
    (hlength : labels.length = coordinates.length) :
    LabellingsAgreeUnder coordinates rename
      (wordToEdgeLabelling coordinates labels)
      (wordToEdgeLabelling (coordinates.map rename) labels) := by
  induction coordinates generalizing labels with
  | nil =>
      cases labels with
      | nil =>
          intro id hid
          exact False.elim (List.not_mem_nil hid)
      | cons head tail => exact False.elim (Nat.noConfusion hlength)
  | cons head tail induction =>
      cases labels with
      | nil => exact False.elim (Nat.noConfusion hlength)
      | cons spin spins =>
          have hparts := List.nodup_cons.mp hnodup
          have htailLength : spins.length = tail.length := by
            exact Nat.succ.inj hlength
          have hinduction := induction spins hparts.2
            (injectiveOnCoordinates_tail hinjective)
            htailLength
          intro id hid
          rcases List.mem_cons.mp hid with rfl | hidTail
          · change
              (if rename id = rename id then spin else
                wordToEdgeLabelling (tail.map rename) spins (rename id)) =
              (if id = id then spin else
                wordToEdgeLabelling tail spins id)
            rw [if_pos rfl, if_pos rfl]
          · have hsourceNe : id ≠ head := by
              intro heq
              subst id
              exact hparts.1 hidTail
            have htargetNe : rename id ≠ rename head := by
              intro heq
              exact hsourceNe
                (hinjective id (List.mem_cons_of_mem head hidTail)
                  head List.mem_cons_self heq)
            change
              (if rename id = rename head then spin else
                wordToEdgeLabelling (tail.map rename) spins (rename id)) =
              (if id = head then spin else
                wordToEdgeLabelling tail spins id)
            rw [if_neg htargetNe, if_neg hsourceNe]
            exact hinduction id hidTail

private theorem mem_allSeqs_length
    (domainSize : Nat) : ∀ {variables : Nat} {word : List Nat},
    word ∈ allSeqs domainSize variables → word.length = variables
  | 0, word, hword => by
      simp only [allSeqs] at hword
      exact List.mem_singleton.mp hword ▸ rfl
  | variables + 1, word, hword => by
      simp only [allSeqs] at hword
      rcases List.mem_flatMap.mp hword with ⟨label, _, hlabel⟩
      rcases List.mem_map.mp hlabel with ⟨tail, htail, rfl⟩
      simp only [List.length_cons]
      exact congrArg Nat.succ (mem_allSeqs_length domainSize htail)

/-- Exact finite change of variables for scoped-factor partition sums. -/
theorem scopedFactorPartitionSum_coordinate_reindex
    (K : Nat)
    (sourceCoordinates targetCoordinates : List Nat)
    (rename : Nat → Nat)
    (sourceFactors targetFactors : List ScopedQFactor)
    (hsourceNodup : sourceCoordinates.Nodup)
    (hinjective : InjectiveOnCoordinates sourceCoordinates rename)
    (hcarrier : (sourceCoordinates.map rename).Perm targetCoordinates)
    (hproduct : ∀ source target,
      LabellingsAgreeUnder sourceCoordinates rename source target →
      (∀ id, id ∈ sourceCoordinates → source id < K + 1) →
      scopedFactorProduct sourceFactors source ≈
        scopedFactorProduct targetFactors target) :
    scopedFactorPartitionSum K sourceCoordinates sourceFactors ≈
      scopedFactorPartitionSum K targetCoordinates targetFactors := by
  unfold scopedFactorPartitionSum
  refine Q'.eqv_trans _
    (listQSum (scopedFactorProduct targetFactors)
      (boundedEdgeLabellings K (sourceCoordinates.map rename))) _ ?_ ?_
  · rw [boundedEdgeLabellings_eq_map_allSeqs,
      boundedEdgeLabellings_eq_map_allSeqs]
    simp only [List.length_map]
    rw [listQSum_map, listQSum_map]
    apply listQSum_congr_on
    intro labels hlabels
    apply hproduct
    · exact wordToEdgeLabelling_rename_agree rename
        sourceCoordinates labels hsourceNodup hinjective
        (mem_allSeqs_length (K + 1) hlabels)
    · exact (boundedEdgeLabellings_sound K sourceCoordinates
        (wordToEdgeLabelling sourceCoordinates labels) (by
          rw [boundedEdgeLabellings_eq_map_allSeqs]
          exact List.mem_map.mpr ⟨labels, hlabels, rfl⟩)).1
  · exact listQSum_bounded_perm K
      (scopedFactorProduct targetFactors) hcarrier

end YMGap.Continuum.FiniteScopedFactorCoordinateReindex

#print axioms
  YMGap.Continuum.FiniteScopedFactorCoordinateReindex.wordToEdgeLabelling_rename_agree
#print axioms
  YMGap.Continuum.FiniteScopedFactorCoordinateReindex.scopedFactorPartitionSum_coordinate_reindex
