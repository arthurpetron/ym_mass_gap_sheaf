/-
# Exact removal of spurious physical spins above the face cutoff

The fusion-complete graph uses the enlarged `6*K` coordinate window for all
edge identifiers, so the first explicit spin-foam formula also enumerates
physical face labels through `6*K`.  The face packet itself is supported only
through `K`.  This file deletes every extra physical labelling exactly: one
out-of-window face coefficient is zero, hence the entire summand is zero.
-/

import YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence

namespace YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem range_nodup (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

/-! ## 1. A rejected Cartesian label has an offending coordinate -/

theorem labelWithinB_false_exists (K : Nat) :
    ∀ (edges : List Nat) (label : EdgeLabelling),
      labelWithinB K edges label = false →
        ∃ edge, edge ∈ edges ∧ K < label edge
  | [], _, h => by cases h
  | edge :: rest, label, h => by
      unfold labelWithinB at h
      by_cases hedge : label edge < K + 1
      · simp only [hedge, decide_true, Bool.true_and] at h
        obtain ⟨bad, hbad, hlarge⟩ :=
          labelWithinB_false_exists K rest label h
        exact ⟨bad, List.mem_cons_of_mem edge hbad, hlarge⟩
      · exact ⟨edge, List.mem_cons_self, by omega⟩

/-! ## 2. Every rejected explicit spin-foam summand is zero -/

private theorem eliminateLinks_zero_of_mem
    (f : Nat → Q') {edge : Nat} : ∀ {edges : List Nat},
    edge ∈ edges → f edge ≈ 0 → eliminateLinks f edges ≈ 0
  | [], hmem, _ => by cases hmem
  | head :: rest, hmem, hz => by
      rcases List.mem_cons.mp hmem with rfl | hrest
      · exact Q'.eqv_trans _ (0 * eliminateLinks f rest) _
          (qmul_congr hz (Q'.eqv_refl _)) (Q'.zero_mul_eqv _)
      · exact Q'.eqv_trans _ (f head * 0) _
          (qmul_congr (Q'.eqv_refl _)
            (eliminateLinks_zero_of_mem f hrest hz))
          (Q'.mul_zero_eqv _)

theorem explicitPhysicalFaceFactor_zero_of_rejected
    (K n : Nat) (physical : EdgeLabelling)
    (hrejected : labelWithinB K
      (List.range (plaquetteEdgeCount n)) physical = false) :
    explicitPhysicalFaceFactor K n physical ≈ 0 := by
  obtain ⟨edge, hedge, hlarge⟩ := labelWithinB_false_exists K
    (List.range (plaquetteEdgeCount n)) physical hrejected
  unfold explicitPhysicalFaceFactor
  apply eliminateLinks_zero_of_mem _ hedge
  rw [coeffAt_of_gt (heatKernelPacket K coupling) hlarge]
  exact Q'.eqv_refl 0

theorem explicitSpinFoamSummand_zero_of_rejected
    (K n : Nat) (physical : EdgeLabelling)
    (hrejected : labelWithinB K
      (List.range (plaquetteEdgeCount n)) physical = false) :
    explicitPhysicalFaceFactor K n physical *
        explicitLinkMultiplicityProduct K n physical
          (enumerate (distinctBoxLinks n)) ≈ 0 := by
  exact Q'.eqv_trans _
    (0 * explicitLinkMultiplicityProduct K n physical
      (enumerate (distinctBoxLinks n))) _
    (qmul_congr
      (explicitPhysicalFaceFactor_zero_of_rejected K n physical hrejected)
      (Q'.eqv_refl _))
    (Q'.zero_mul_eqv _)

private theorem listQSum_eq_filter_of_zero
    (f : EdgeLabelling → Q') (p : EdgeLabelling → Bool) :
    ∀ xs : List EdgeLabelling,
      (∀ x, x ∈ xs → p x = false → f x ≈ 0) →
      listQSum f xs ≈ listQSum f (xs.filter p)
  | [], _ => Q'.eqv_refl _
  | x :: xs, hz => by
      have htail : ∀ y, y ∈ xs → p y = false → f y ≈ 0 := by
        intro y hy hp
        exact hz y (List.mem_cons_of_mem x hy) hp
      cases hp : p x with
      | false =>
          simp only [List.filter, hp, listQSum]
          exact Q'.eqv_trans _ (0 + listQSum f (xs.filter p)) _
            (Q'.add_eqv_congr' (hz x List.mem_cons_self hp)
              (listQSum_eq_filter_of_zero f p xs htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter, hp, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero f p xs htail)

/-! ## 3. The physical Cartesian sum uses exactly cutoff K -/

/-- **Exact physical-cutoff reduction.**  Internal channel counts retain the
fusion-complete `6*K` window, while physical face labellings now range only
through their genuine packet cutoff `K`. -/
theorem fusionCompleteBoxVertexCartesianSum_eq_physicalCutoffSpinFoam
    (K n : Nat) :
    fusionCompleteBoxVertexCartesianSum K n ≈
      listQSum
        (fun physical =>
          explicitPhysicalFaceFactor K n physical *
            explicitLinkMultiplicityProduct K n physical
              (enumerate (distinctBoxLinks n)))
        (boundedEdgeLabellings K
          (List.range (plaquetteEdgeCount n))) := by
  let term : EdgeLabelling → Q' := fun physical =>
    explicitPhysicalFaceFactor K n physical *
      explicitLinkMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n))
  refine Q'.eqv_trans _
    (listQSum term
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (List.range (plaquetteEdgeCount n)))) _
    (fusionCompleteBoxVertexCartesianSum_eq_explicitSpinFoam K n) ?_
  refine Q'.eqv_trans _
    (listQSum term
      ((boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (List.range (plaquetteEdgeCount n))).filter
          (labelWithinB K (List.range (plaquetteEdgeCount n))))) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero
    intro physical _ hrejected
    exact explicitSpinFoamSummand_zero_of_rejected K n physical hrejected
  · rw [boundedEdgeLabellings_filter_cutoff
      (externalCutoff_le_linkAuxiliaryCutoff K)
      (List.range (plaquetteEdgeCount n))]
    · exact Q'.eqv_refl _
    · exact range_nodup _

end YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction.labelWithinB_false_exists
#print axioms YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction.explicitPhysicalFaceFactor_zero_of_rejected
#print axioms YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction.explicitSpinFoamSummand_zero_of_rejected
#print axioms YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction.fusionCompleteBoxVertexCartesianSum_eq_physicalCutoffSpinFoam
