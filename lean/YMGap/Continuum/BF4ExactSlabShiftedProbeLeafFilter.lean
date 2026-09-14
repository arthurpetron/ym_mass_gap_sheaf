/-
# All-positive-spin leaf rejection in the SAME original connected expansion

A temporal link occupied by exactly one positive-spin face kills each of
the four original shifted-probe moments. The finite incidence checker
therefore removes such replicas from the full connected-selection sum.
It detects even-spin leaves as well as odd ones. No sign, global minimum
area, or positive response floor is asserted for the survivors.
-/

import YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink
import YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion

namespace YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabSingletonOccupiedLink
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "N" margin => List.length (boundaryCompleteSlabLinks (responseExtent margin))

theorem vertical_not_endpoint (margin time : Nat) (v : Z4Vertex) :
    (v,Dir4.x3) ∉ edgesOf (sliceFace margin time) := by
  simp [sliceFace, edgesOf, dirsOf]

theorem insertion_supported (margin : Nat) (lo hi : Bool) :
    SupportedQuaternionBlocks (N margin) (insertion margin lo hi) := by
  cases lo <;> cases hi
  · exact supported_polyMul (supported_one _) (supported_one _)
  · exact supported_polyMul (supported_one _) (upper_supported _)
  · exact supported_polyMul (lower_supported _) (supported_one _)
  · exact supported_polyMul (lower_supported _) (upper_supported _)

theorem insertion_vertical_degree_zero (margin : Nat) (lo hi : Bool) (v : Z4Vertex)
    (hl : (v,Dir4.x3) ∈ boundaryCompleteSlabLinks (responseExtent margin)) :
    HasQuaternionBlockDegree ((boundaryCompleteSlabLinks (responseExtent margin)).idxOf (v,Dir4.x3)) 0
      (insertion margin lo hi) := by
  have h0 := hasQuaternionBlockDegree_one ((boundaryCompleteSlabLinks (responseExtent margin)).idxOf (v,Dir4.x3))
  have hp := linkLocal_degree_zero (lower_link_local margin) (v,Dir4.x3) hl (vertical_not_endpoint margin 0 v)
  have hq := linkLocal_degree_zero (upper_link_local margin) (v,Dir4.x3) hl (vertical_not_endpoint margin 3 v)
  cases lo <;> cases hi
  · exact h0.mul h0
  · exact h0.mul hq
  · exact hp.mul h0
  · exact hp.mul hq

theorem moment_singleton_zero (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (v : Z4Vertex) (hl : (v,Dir4.x3) ∈ boundaryCompleteSlabLinks (responseExtent margin)) (face : Z4Plaq)
    (hf : incidentOccupied (responseExtent margin) state (v,Dir4.x3) = [face]) :
    moment margin lo hi state ≈ 0 :=
  incident_singleton_zero _ state _ (insertion_supported margin lo hi) _ face hf
    (insertion_vertical_degree_zero margin lo hi v hl)

def linkKeep (extent : Nat) (state : EdgeLabelling) (link : Z4Link) : Bool :=
  if link.2 = .x3 then decide ((incidentOccupied extent state link).length ≠ 1) else true

def leafKeep (margin : Nat) (state : EdgeLabelling) : Bool :=
  (boundaryCompleteSlabLinks (responseExtent margin)).all (linkKeep (responseExtent margin) state)

/-- Geometry-facing consequence for every physical temporal link of a retained replica. -/
theorem retained_link_not_singleton {margin : Nat} {state : EdgeLabelling}
    (h : leafKeep margin state = true) (v : Z4Vertex)
    (hl : (v,Dir4.x3) ∈ boundaryCompleteSlabLinks (responseExtent margin)) :
    (incidentOccupied (responseExtent margin) state (v,Dir4.x3)).length ≠ 1 := by
  have hk := List.all_eq_true.mp h (v,Dir4.x3) hl
  exact of_decide_eq_true (by simpa only [linkKeep, ↓reduceIte] using hk)

private theorem all_false_witness {A : Type} (f : A → Bool) : ∀ xs : List A,
    xs.all f = false → ∃ b, b ∈ xs ∧ f b = false
  | [], h => by cases h
  | b::bs, h => by
    cases hb : f b with
    | false => exact ⟨b,List.mem_cons_self,hb⟩
    | true =>
      have ht : bs.all f = false := by simpa only [List.all_cons, hb, Bool.true_and] using h
      obtain ⟨c,hc,hf⟩ := all_false_witness f bs ht
      exact ⟨c,List.mem_cons_of_mem b hc,hf⟩

theorem moment_leaf_rejected (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (h : leafKeep margin state = false) : moment margin lo hi state ≈ 0 := by
  obtain ⟨⟨v,dir⟩,hl,hk⟩ := all_false_witness _ _ h
  have hd : dir = .x3 := by
    by_cases hd : dir = .x3
    · exact hd
    · simp only [linkKeep, if_neg hd, Bool.true_eq_false] at hk
  subst dir
  have hlen : (incidentOccupied (responseExtent margin) state (v,Dir4.x3)).length = 1 := by
    have hn : ¬(incidentOccupied (responseExtent margin) state (v,Dir4.x3)).length ≠ 1 := by
      simpa only [linkKeep, ↓reduceIte, decide_eq_false_iff_not] using hk
    by_cases he : (incidentOccupied (responseExtent margin) state (v,Dir4.x3)).length = 1
    · exact he
    · exact False.elim (hn he)
  cases he : incidentOccupied (responseExtent margin) state (v,Dir4.x3) with
  | nil => simp only [he, List.length_nil] at hlen; cases hlen
  | cons face rest =>
    cases rest with
    | nil => exact moment_singleton_zero margin lo hi state v hl face he
    | cons other rest => simp only [he, List.length_cons] at hlen; omega

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

theorem pair_left_leaf_rejected (margin : Nat) (state other : EdgeLabelling)
    (h : leafKeep margin state = false) : pairTerm margin state other ≈ 0 :=
  Q'.eqv_trans _ _ _ (pairTerm_pin margin state other)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (qmul (moment_leaf_rejected margin true true state h) (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (qmul (moment_leaf_rejected margin true false state h) (Q'.eqv_refl _))))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.zero_mul_eqv _)
        (Q'.neg_eqv_congr _ _ (Q'.zero_mul_eqv _))) (by decide)))

theorem pair_right_leaf_rejected (margin : Nat) (state other : EdgeLabelling)
    (h : leafKeep margin other = false) : pairTerm margin state other ≈ 0 :=
  Q'.eqv_trans _ _ _ (pairTerm_pin margin state other)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (qmul (Q'.eqv_refl _) (moment_leaf_rejected margin false false other h))
      (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl _) (moment_leaf_rejected margin false true other h))))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.mul_zero_eqv _)
        (Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv _))) (by decide)))

def pairLeafKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  leafKeep margin pair.1 && leafKeep margin pair.2

theorem weighted_leaf_rejected (w : Q') (K margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (h : pairLeafKeep margin pair = false) : weightedPairTerm w K margin pair ≈ 0 := by
  have hz : pairTerm margin pair.1 pair.2 ≈ 0 := by
    cases hl : leafKeep margin pair.1 with
    | false => exact pair_left_leaf_rejected margin pair.1 pair.2 hl
    | true =>
      exact pair_right_leaf_rejected margin pair.1 pair.2
        (by simpa only [pairLeafKeep, hl, Bool.true_and] using h)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)

theorem weighted_leaf_filter (w : Q') (K margin : Nat) (pairs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (weightedPairTerm w K margin) pairs ≈
      listQSum (weightedPairTerm w K margin) (pairs.filter (pairLeafKeep margin)) :=
  sum_filter_zero _ _ _ (fun pair _ h => weighted_leaf_rejected w K margin pair h)

/-- The original connected-support and odd-cut expansion, now also free of all-spin leaves. -/
theorem original_numerator_leaf_filter (w : Q') (K margin time : Nat) :
    connectedNumerator w K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ≈
      listQSum (fun ids => listQSum (weightedPairTerm w K margin)
        (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
        (connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
          (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin))) :=
  Q'.eqv_trans _ _ _ (original_numerator_joint_filter w K margin time)
    (listQSum_congr_on _ _ _ (fun _ _ => weighted_leaf_filter w K margin _))

end YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter

#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.vertical_not_endpoint
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.insertion_supported
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.insertion_vertical_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.moment_singleton_zero
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.linkKeep
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.leafKeep
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.retained_link_not_singleton
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.moment_leaf_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.pair_left_leaf_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.pair_right_leaf_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.pairLeafKeep
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.weighted_leaf_rejected
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.weighted_leaf_filter
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter.original_numerator_leaf_filter
