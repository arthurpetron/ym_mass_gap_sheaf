/-
# Lift a collapsed stretched SU(2) fusion witness

For source spins `left :: right :: rest`, the stretched first channel is
`left + right`.  A canonical auxiliary witness for the collapsed word
`(left + right) :: rest` therefore determines a canonical source witness:
insert the forced first channel and shift the remaining internal channels.

This file defines that finite-valence coordinate transplant and proves it
preserves membership in the literal accepted fusion-witness list through
valence six.  The proof checks each of the five possible collapsed canonical
chains and separately verifies bounded support and every SU(2) fusion rule.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
import YMGap.Continuum.SU2StretchedTrivalentStrandContinuation

namespace YMGap.Continuum.SU2StretchedFusionWitnessLift

set_option autoImplicit false

open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtFiber
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2StretchedTrivalentStrandContinuation
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Public fixed-valence views of the canonical Boolean constraint -/

theorem canonicalAllowed_one (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 1 external auxiliary =
      (fusionOK (external 0) (auxiliary 1) (auxiliary 1) &&
        decide (auxiliary 1 = 0)) := by
  unfold canonicalLinkConditionalAllowedB
  rw [show List.range 1 = [0] by rfl]
  simp [fuseLabels, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

theorem canonicalAllowed_two (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 2 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 2) &&
        decide (auxiliary 2 = 0)) := by
  unfold canonicalLinkConditionalAllowedB
  rw [show List.range 2 = [0, 1] by rfl]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

theorem canonicalAllowed_three (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 3 external auxiliary =
      fusionOK (external 0) (external 1) (external 2) := by
  unfold canonicalLinkConditionalAllowedB
  rw [show List.range 3 = [0, 1, 2] by rfl]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates, overlayOn]

theorem canonicalAllowed_four (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 4 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 5) &&
        fusionOK (auxiliary 5) (external 2) (external 3)) := by
  unfold canonicalLinkConditionalAllowedB
  rw [show List.range 4 = [0, 1, 2, 3] by rfl]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

theorem canonicalAllowed_five (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 5 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 6) &&
        (fusionOK (auxiliary 6) (external 2) (auxiliary 7) &&
          fusionOK (auxiliary 7) (external 3) (external 4))) := by
  unfold canonicalLinkConditionalAllowedB
  rw [show List.range 5 = [0, 1, 2, 3, 4] by rfl]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

theorem canonicalAllowed_six (external auxiliary : EdgeLabelling) :
    canonicalLinkConditionalAllowedB 6 external auxiliary =
      (fusionOK (external 0) (external 1) (auxiliary 7) &&
        (fusionOK (auxiliary 7) (external 2) (auxiliary 8) &&
          (fusionOK (auxiliary 8) (external 3) (auxiliary 9) &&
            fusionOK (auxiliary 9) (external 4) (external 5)))) := by
  unfold canonicalLinkConditionalAllowedB
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] by rfl]
  simp [fuseLabels, fuseChain, verticesAdmissibleB,
    canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    canonicalAuxiliaryEdgeAllowedB, overlayOn]

/-! ## 2. Insert and shift the internal coordinates -/

def stretchedFusionWitnessLift (left right : Nat) :
    List Nat → EdgeLabelling → EdgeLabelling
  | [], _ => zeroEdgeLabelling
  | [_], _ => zeroEdgeLabelling
  | _ :: _ :: [], _ =>
      setEdgeLabel zeroEdgeLabelling 5 (left + right)
  | _ :: _ :: _ :: [], collapsed =>
      setEdgeLabel
        (setEdgeLabel zeroEdgeLabelling 7 (collapsed 5))
        6 (left + right)
  | _ :: _ :: _ :: _ :: [], collapsed =>
      setEdgeLabel
        (setEdgeLabel
          (setEdgeLabel zeroEdgeLabelling 9 (collapsed 7))
          8 (collapsed 6))
        7 (left + right)
  | _, _ => zeroEdgeLabelling

/-! ## 3. Membership preservation through valence six -/

theorem stretchedFusionWitnessLift_mem
    (cutoff left right : Nat) (rest : List Nat)
    (hlength : (left :: right :: rest).length ≤ 6)
    (hstretched : left + right ≤ cutoff)
    (collapsed : EdgeLabelling)
    (hcollapsed : collapsed ∈ fusionWitnessesForSpins cutoff
      ((left + right) :: rest)) :
    stretchedFusionWitnessLift left right rest collapsed ∈
      fusionWitnessesForSpins cutoff (left :: right :: rest) := by
  cases rest with
  | nil =>
      unfold fusionWitnessesForSpins at hcollapsed ⊢
      simp only [List.length_cons, List.length_nil, Nat.zero_add]
        at hcollapsed ⊢
      obtain ⟨hbounded, hallowed⟩ := List.mem_filter.mp hcollapsed
      apply List.mem_filter.mpr
      constructor
      · apply boundedEdgeLabellings_complete
        · intro edge hedge
          change edge ∈ [2] at hedge
          simp only [List.mem_singleton] at hedge
          subst edge
          simp [stretchedFusionWitnessLift, zeroEdgeLabelling]
        · intro edge hedge
          rfl
      · rw [canonicalAllowed_one] at hallowed
        rw [canonicalAllowed_two]
        simp [externalSpinsOfList, stretchedFusionWitnessLift,
          zeroEdgeLabelling] at hallowed ⊢
        have hsum : left + right = 0 := by
          rcases hallowed with ⟨hfusion, hzero⟩
          have haux : collapsed 1 = 0 := by simpa using hzero
          rw [haux] at hfusion
          obtain ⟨depth, hdepthSum, hdepthZero, hsumDepth⟩ :=
            (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
              (left + right) 0 0).mp hfusion
          omega
        have hleft : left = 0 := by omega
        have hright : right = 0 := by omega
        subst left
        subst right
        decide
  | cons c tail =>
      cases tail with
      | nil =>
          unfold fusionWitnessesForSpins at hcollapsed ⊢
          simp only [List.length_cons, List.length_nil, Nat.zero_add]
            at hcollapsed ⊢
          obtain ⟨hbounded, hallowed⟩ := List.mem_filter.mp hcollapsed
          apply List.mem_filter.mpr
          constructor
          · apply boundedEdgeLabellings_complete
            · intro edge hedge
              change edge ∈ [] at hedge
              simp at hedge
            · intro edge hedge
              rfl
          · rw [canonicalAllowed_two] at hallowed
            rw [canonicalAllowed_three]
            simp [externalSpinsOfList] at hallowed ⊢
            rcases hallowed with ⟨hfusion, hzero⟩
            have haux : collapsed 2 = 0 := by simpa using hzero
            rw [haux] at hfusion
            have hc : left + right = c := by
              obtain ⟨depth, hdepthSum, hdepthC, hsumDepth⟩ :=
                (YMGap.Continuum.FusionBratteli.fusionOK_iff_ladder
                  (left + right) c 0).mp hfusion
              omega
            rw [← hc]
            exact fusionOK_stretched left right
      | cons d tail =>
          cases tail with
          | nil =>
              unfold fusionWitnessesForSpins at hcollapsed ⊢
              simp only [List.length_cons, List.length_nil, Nat.zero_add]
                at hcollapsed ⊢
              obtain ⟨hbounded, hallowed⟩ := List.mem_filter.mp hcollapsed
              apply List.mem_filter.mpr
              constructor
              · apply boundedEdgeLabellings_complete
                · intro edge hedge
                  change edge ∈ [5] at hedge
                  simp only [List.mem_singleton] at hedge
                  subst edge
                  simp [stretchedFusionWitnessLift, setEdgeLabel]
                  omega
                · intro edge hedge
                  change edge ∉ [5] at hedge
                  have hne : edge ≠ 5 := by
                    intro heq
                    subst edge
                    exact hedge (by simp)
                  simp [stretchedFusionWitnessLift, setEdgeLabel,
                    zeroEdgeLabelling, hne]
              · rw [canonicalAllowed_three] at hallowed
                rw [canonicalAllowed_four]
                have hallowed' : fusionOK (left + right) c d = true := by
                  simpa [externalSpinsOfList] using hallowed
                simp [externalSpinsOfList, stretchedFusionWitnessLift,
                  setEdgeLabel,
                  fusionOK_stretched, hallowed']
          | cons e tail =>
              cases tail with
              | nil =>
                  unfold fusionWitnessesForSpins at hcollapsed ⊢
                  simp only [List.length_cons, List.length_nil, Nat.zero_add]
                    at hcollapsed ⊢
                  obtain ⟨hbounded, hallowed⟩ :=
                    List.mem_filter.mp hcollapsed
                  have hcollapsedBound :=
                    (boundedEdgeLabellings_sound cutoff [5] collapsed hbounded).1
                      5 (by simp)
                  apply List.mem_filter.mpr
                  constructor
                  · apply boundedEdgeLabellings_complete
                    · intro edge hedge
                      change edge ∈ [6, 7] at hedge
                      simp only [List.mem_cons, List.not_mem_nil,
                        or_false] at hedge
                      rcases hedge with rfl | rfl
                      · change left + right < cutoff + 1
                        omega
                      · change collapsed 5 < cutoff + 1
                        exact hcollapsedBound
                    · intro edge hedge
                      change edge ∉ [6, 7] at hedge
                      have hneSix : edge ≠ 6 := by
                        intro heq
                        subst edge
                        exact hedge (by simp)
                      have hneSeven : edge ≠ 7 := by
                        intro heq
                        subst edge
                        exact hedge (by simp)
                      simp [stretchedFusionWitnessLift, setEdgeLabel,
                        zeroEdgeLabelling, hneSix, hneSeven]
                  · rw [canonicalAllowed_four] at hallowed
                    rw [canonicalAllowed_five]
                    have hallowed' :
                        fusionOK (left + right) c (collapsed 5) = true ∧
                          fusionOK (collapsed 5) d e = true := by
                      simpa [externalSpinsOfList] using hallowed
                    simp [externalSpinsOfList, stretchedFusionWitnessLift,
                      setEdgeLabel, fusionOK_stretched,
                      hallowed'.1, hallowed'.2]
              | cons f tail =>
                  cases tail with
                  | nil =>
                      unfold fusionWitnessesForSpins at hcollapsed ⊢
                      simp only [List.length_cons, List.length_nil,
                        Nat.zero_add] at hcollapsed ⊢
                      obtain ⟨hbounded, hallowed⟩ :=
                        List.mem_filter.mp hcollapsed
                      have hcollapsedSound :=
                        (boundedEdgeLabellings_sound cutoff [6, 7]
                          collapsed hbounded).1
                      have hboundSix := hcollapsedSound 6 (by simp)
                      have hboundSeven := hcollapsedSound 7 (by simp)
                      apply List.mem_filter.mpr
                      constructor
                      · apply boundedEdgeLabellings_complete
                        · intro edge hedge
                          change edge ∈ [7, 8, 9] at hedge
                          simp only [List.mem_cons, List.not_mem_nil,
                            or_false] at hedge
                          rcases hedge with rfl | rfl | rfl
                          · change left + right < cutoff + 1
                            omega
                          · change collapsed 6 < cutoff + 1
                            exact hboundSix
                          · change collapsed 7 < cutoff + 1
                            exact hboundSeven
                        · intro edge hedge
                          change edge ∉ [7, 8, 9] at hedge
                          have hneSeven : edge ≠ 7 := by
                            intro heq
                            subst edge
                            exact hedge (by simp)
                          have hneEight : edge ≠ 8 := by
                            intro heq
                            subst edge
                            exact hedge (by simp)
                          have hneNine : edge ≠ 9 := by
                            intro heq
                            subst edge
                            exact hedge (by simp)
                          simp [stretchedFusionWitnessLift, setEdgeLabel,
                            zeroEdgeLabelling, hneSeven, hneEight, hneNine]
                      · rw [canonicalAllowed_five] at hallowed
                        rw [canonicalAllowed_six]
                        have hallowed' :
                            fusionOK (left + right) c (collapsed 6) = true ∧
                              fusionOK (collapsed 6) d (collapsed 7) = true ∧
                              fusionOK (collapsed 7) e f = true := by
                          simpa [externalSpinsOfList] using hallowed
                        simp [externalSpinsOfList,
                          stretchedFusionWitnessLift, setEdgeLabel,
                          fusionOK_stretched,
                          hallowed'.1, hallowed'.2.1, hallowed'.2.2]
                  | cons g tail =>
                      simp only [List.length_cons] at hlength
                      have himpossible : False := by omega
                      exact False.elim himpossible

end YMGap.Continuum.SU2StretchedFusionWitnessLift

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.SU2StretchedFusionWitnessLift.stretchedFusionWitnessLift
#print axioms
  YMGap.Continuum.SU2StretchedFusionWitnessLift.stretchedFusionWitnessLift_mem
