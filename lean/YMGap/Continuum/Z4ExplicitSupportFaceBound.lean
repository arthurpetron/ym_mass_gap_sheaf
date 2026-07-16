/-
# Face-activity decay indexed by the exact excitation support

For a physical labelling drawn from the cutoff-`K` Cartesian support, every
zero-spin face coefficient is exactly one and every excited face coefficient
is at most the fundamental coefficient `1/4` at the constructed coupling
`w = 1/2`.  Thus the complete face product is bounded by `quarter` to the
number of excited plaquettes, with no ambient-volume exponent.
-/

import YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
import YMGap.Continuum.PinnedCluster

namespace YMGap.Continuum.Z4ExplicitSupportFaceBound

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

def excitedPlaquetteIds (n : Nat) (physical : EdgeLabelling) : List Nat :=
  (physicalFaceEdges n).filter (fun edge => decide (1 ≤ physical edge))

/-! ## 1. Numerical plaquette entries and IDs have the same support size -/

private theorem enumerateFrom_map_fst (start : Nat) :
    ∀ {A : Type} (xs : List A),
      (enumerateFrom start xs).map Prod.fst =
        (List.range xs.length).map (fun i => start + i)
  | _, [] => rfl
  | A, _ :: rest => by
      simp only [enumerateFrom, List.map_cons, List.length_cons,
        List.range_succ_eq_map, List.map_map]
      rw [enumerateFrom_map_fst (start + 1) rest]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      omega

theorem enumerate_map_fst_eq_range {A : Type} (xs : List A) :
    (enumerate xs).map Prod.fst = List.range xs.length := by
  unfold enumerate
  rw [enumerateFrom_map_fst]
  simp

theorem map_excitedPlaquetteEntries_fst (n : Nat)
    (physical : EdgeLabelling) :
    (excitedPlaquetteEntries n physical).map Prod.fst =
      excitedPlaquetteIds n physical := by
  unfold excitedPlaquetteEntries excitedPlaquetteIds physicalFaceEdges
  let pred : Nat → Bool := fun edge => decide (1 ≤ physical edge)
  change (((enumerate (Z4FiniteBoxExhaustion.boxPlaquettes n)).filter
      (pred ∘ Prod.fst)).map Prod.fst) =
    (List.range (plaquetteEdgeCount n)).filter pred
  rw [← List.filter_map, enumerate_map_fst_eq_range]
  rfl

theorem excitedPlaquetteEntries_length_eq_ids (n : Nat)
    (physical : EdgeLabelling) :
    (excitedPlaquetteEntries n physical).length =
      (excitedPlaquetteIds n physical).length := by
  have h := congrArg List.length
    (map_excitedPlaquetteEntries_fst n physical)
  simpa only [List.length_map] using h

/-! ## 2. A finite product with unit vacuum factors -/

private theorem eliminateLinks_nonnegative_local (value : Nat → Q')
    (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat, (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest => Q'.mul_nonneg _ _ (hvalue edge)
      (eliminateLinks_nonnegative_local value hvalue rest)

private theorem eliminateLinks_le_filteredPow
    (value : Nat → Q') (excited : Nat → Bool) (q : Q')
    (hq0 : (0 : Q') ≤ q)
    (hvalue0 : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → excited edge = false → value edge ≈ 1) →
      (∀ edge, edge ∈ edges → excited edge = true → value edge ≤ q) →
      eliminateLinks value edges ≤ q ^ (edges.filter excited).length
  | [], _, _ => Q'.le_refl' 1
  | edge :: rest, hvacuum, hexcited => by
      have hvacuumRest : ∀ item, item ∈ rest → excited item = false →
          value item ≈ 1 := by
        intro item hitem hzero
        exact hvacuum item (List.mem_cons_of_mem edge hitem) hzero
      have hexcitedRest : ∀ item, item ∈ rest → excited item = true →
          value item ≤ q := by
        intro item hitem hexc
        exact hexcited item (List.mem_cons_of_mem edge hitem) hexc
      have ih := eliminateLinks_le_filteredPow value excited q hq0 hvalue0
        rest hvacuumRest hexcitedRest
      cases hedge : excited edge with
      | false =>
          simp only [List.filter_cons, hedge, Bool.false_eq_true, if_false]
          have hhead := hvacuum edge List.mem_cons_self hedge
          have hdrop : eliminateLinks value (edge :: rest) ≈
              eliminateLinks value rest := by
            exact Q'.eqv_trans _ (1 * eliminateLinks value rest) _
              (qmul_congr hhead (Q'.eqv_refl _))
              (Q'.one_mul_eqv _)
          exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdrop) ih
      | true =>
          simp only [List.filter_cons, hedge, if_true, List.length_cons]
          rw [Q'.pow_succ]
          have hrest0 : (0 : Q') ≤ eliminateLinks value rest :=
            eliminateLinks_nonnegative_local value hvalue0 rest
          have hpow0 : (0 : Q') ≤ q ^ (rest.filter excited).length :=
            Q'.pow_nonneg q hq0 _
          have hfirst : value edge * eliminateLinks value rest ≤
              q * eliminateLinks value rest :=
            Q'.mul_le_mul_of_nonneg_right _ _ _
              (hexcited edge List.mem_cons_self hedge) hrest0
          have hsecond : q * eliminateLinks value rest ≤
              q * q ^ (rest.filter excited).length :=
            Q'.mul_le_mul_of_nonneg_left _ _ _ ih hq0
          exact Q'.le_trans' _ _ _ hfirst hsecond

/-! ## 3. Exact support-size face bound -/

theorem excitedFaceCoefficient_le_quarter
    {K n edge : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings K n)
    (hedge : edge ∈ physicalFaceEdges n)
    (hexcited : 1 ≤ physical edge) :
    coeffAt (heatKernelPacket K coupling) (physical edge) ≤ quarter := by
  have hsound := boundedEdgeLabellings_sound K
    (physicalFaceEdges n) physical hphysical
  have hspin : physical edge < K + 1 := hsound.1 edge hedge
  rw [coeffAt_heatKernelPacket hspin]
  have hdom := coeffW_le_one_le
    (Q'.le_of_lt coupling_window.1)
    (show coupling ≤ Q'.mkPos 1 2 (by decide) from Q'.le_refl' coupling)
    (physical edge) hexcited
  exact Q'.le_trans' _ _ _ hdom
    (Q'.le_of_eqv interaction_coeff_fundamental)

theorem explicitPhysicalFaceFactor_le_supportPow
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings K n) :
    explicitPhysicalFaceFactor K n physical ≤
      quarter ^ (excitedPlaquetteIds n physical).length := by
  unfold explicitPhysicalFaceFactor excitedPlaquetteIds
  apply eliminateLinks_le_filteredPow
  · decide
  · intro edge
    exact heatKernelPacketCoefficient_nonnegative K (physical edge)
  · intro edge _ hzero
    have hnot : ¬ 1 ≤ physical edge := by
      simpa only [decide_eq_false_iff_not] using hzero
    have hspin : physical edge = 0 := by omega
    rw [hspin, heatKernelPacketCoefficient_zero_eq_one]
    exact Q'.eqv_refl 1
  · intro edge hedge hexcited
    have hpos : 1 ≤ physical edge := by
      simpa only [decide_eq_true_eq] using hexcited
    exact excitedFaceCoefficient_le_quarter hphysical hedge hpos

theorem explicitPhysicalFaceFactor_le_entryPow
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ explicitPhysicalLabellings K n) :
    explicitPhysicalFaceFactor K n physical ≤
      quarter ^ (excitedPlaquetteEntries n physical).length := by
  rw [excitedPlaquetteEntries_length_eq_ids]
  exact explicitPhysicalFaceFactor_le_supportPow hphysical

end YMGap.Continuum.Z4ExplicitSupportFaceBound

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitSupportFaceBound.enumerate_map_fst_eq_range
#print axioms YMGap.Continuum.Z4ExplicitSupportFaceBound.excitedPlaquetteEntries_length_eq_ids
#print axioms YMGap.Continuum.Z4ExplicitSupportFaceBound.excitedFaceCoefficient_le_quarter
#print axioms YMGap.Continuum.Z4ExplicitSupportFaceBound.explicitPhysicalFaceFactor_le_supportPow
#print axioms YMGap.Continuum.Z4ExplicitSupportFaceBound.explicitPhysicalFaceFactor_le_entryPow
