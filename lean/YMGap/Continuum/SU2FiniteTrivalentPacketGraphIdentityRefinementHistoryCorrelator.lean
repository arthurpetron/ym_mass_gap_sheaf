/-
# Complete correlator compatibility for compensation histories

The finite reciprocal compensation product makes successive identity
refinements composable at the eigenvalue and selected-summand levels.  This
module installs every such history as a positive finite spectral model and
collapses the two fresh label sums.  Adding one more refinement therefore
preserves the complete integer-time correlator of the preceding history.

Honest scope: arbitrary finite refinement chains now have a local
correlator-level composition law.  A directed family of graphs, uniform
volume estimates, and a continuum limit are still separate obligations.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactTransferGNS
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphAllTimeCutoffInvariance
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementSum
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQSum_zero {A : Type} {f : A → Q'}
    (hz : ∀ x, f x ≈ 0) : ∀ xs, listQSum f xs ≈ 0
  | [] => Q'.eqv_refl 0
  | x :: xs => by
      change f x + listQSum f xs ≈ 0
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr' (hz x) (listQSum_zero hz xs))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_congr_mem {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h => by
      change f x + listQSum f xs ≈ g x + listQSum g xs
      exact Q'.add_eqv_congr'
        (h x List.mem_cons_self)
        (listQSum_congr_mem xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem setEdgeLabel_current (label : EdgeLabelling) (edge : Nat) :
    setEdgeLabel label edge (label edge) = label := by
  funext e
  by_cases h : e = edge
  · subst e
    simp [setEdgeLabel]
  · simp [setEdgeLabel, h]

/-! ## A positive spectral model for every finite history -/

def historyGraphSquaredEigen {K : Nat} (copiedEdges : List Nat)
    (edges : List Nat) (vertices : List TrivalentVertex) (i : Nat) : Q' :=
  let label := physicalModeLabel K edges vertices i
  let e := historyGraphEigen copiedEdges edges label
  e * e

theorem historyGraphSquaredEigen_nonneg {K : Nat} (copiedEdges : List Nat)
    (edges : List Nat) (vertices : List TrivalentVertex) (i : Nat) :
    (0 : Q') ≤ historyGraphSquaredEigen (K := K) copiedEdges edges vertices i := by
  unfold historyGraphSquaredEigen
  exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _

/-- The physical packet weight, extended by exact zero outside the finite
mode range.  This makes all total spectral statements insensitive to the
default label returned by `supportLabel` beyond the retained list. -/
def historyPacketGraphModeWeight {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex) (packet : Nat → CharacterPacket K)
    (i : Nat) : Q' :=
  if i < (physicalEdgeLabellings K edges vertices).length then
    packetGraphModeWeight edges vertices packet i else 0

theorem historyPacketGraphModeWeight_nonneg {K : Nat} (edges : List Nat)
    (vertices : List TrivalentVertex) (packet : Nat → CharacterPacket K)
    (i : Nat) :
    (0 : Q') ≤ historyPacketGraphModeWeight edges vertices packet i := by
  unfold historyPacketGraphModeWeight
  by_cases hi : i < (physicalEdgeLabellings K edges vertices).length
  · rw [if_pos hi]
    exact packetGraphModeWeight_nonneg edges vertices packet i
  · rw [if_neg hi]
    exact Q'.le_refl' 0

def historyPacketGraphSpectralModel {K : Nat} (copiedEdges : List Nat)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : SpectralModel :=
  diagOp.toSpectralModel
    (historyGraphSquaredEigen (K := K) copiedEdges edges vertices)
    (historyPacketGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length
    (historyPacketGraphModeWeight_nonneg edges vertices packet)
    (historyGraphSquaredEigen_nonneg copiedEdges edges vertices)

theorem historyProjectedCorrTerm_zero_of_unphysical {K : Nat}
    (copiedEdges : List Nat) (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling)
    (h : graphPhysicalB edges vertices label = false) :
    historyProjectedCorrTerm copiedEdges edges vertices packet n label ≈ 0 := by
  unfold historyProjectedCorrTerm
  exact Q'.eqv_trans _
    (0 * (historyGraphEigen copiedEdges edges label *
      historyGraphEigen copiedEdges edges label) ^ n) _
    (q_mul_congr
      (projectedSquare_zero_of_unphysical edges vertices packet label h)
      (Q'.eqv_refl _))
    (Q'.zero_mul_eqv _)

private theorem history_physical_filter_corr_eq_full {K : Nat}
    (copiedEdges : List Nat) (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat) :
    listQSum (historyProjectedCorrTerm copiedEdges edges vertices packet n)
        (physicalEdgeLabellings K edges vertices) ≈
      listQSum (historyProjectedCorrTerm copiedEdges edges vertices packet n)
        (boundedEdgeLabellings K edges) := by
  unfold physicalEdgeLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun label => if graphPhysicalB edges vertices label then
        historyProjectedCorrTerm copiedEdges edges vertices packet n label else 0)
      (boundedEdgeLabellings K edges)) _
    (listQSum_filter _ _ _) ?_
  apply listQSum_congr
  intro label
  cases hp : graphPhysicalB edges vertices label with
  | false =>
      exact Q'.eqv_symm
        (historyProjectedCorrTerm_zero_of_unphysical
          copiedEdges edges vertices packet n label hp)
  | true => exact Q'.eqv_refl _

theorem historyPacketGraph_corr_eq_full {K : Nat}
    (copiedEdges : List Nat) (edges : List Nat)
    (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat) :
    corr (historyPacketGraphSpectralModel
        copiedEdges edges vertices packet) n ≈
      listQSum (historyProjectedCorrTerm
        copiedEdges edges vertices packet n)
        (boundedEdgeLabellings K edges) := by
  let support := physicalEdgeLabellings K edges vertices
  let term := historyProjectedCorrTerm copiedEdges edges vertices packet n
  have hindexed :
      corr (historyPacketGraphSpectralModel
          copiedEdges edges vertices packet) n ≈
        fsum (fun i => term (supportLabel support i)) support.length := by
    unfold corr historyPacketGraphSpectralModel
      CompactTransferGNS.diagOp.toSpectralModel
    rw [← YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
    intro i hi
    have hi' : i < (physicalEdgeLabellings K edges vertices).length := hi
    change (if i < (physicalEdgeLabellings K edges vertices).length then
        packetGraphModeWeight edges vertices packet i else 0) *
        (historyGraphSquaredEigen copiedEdges edges vertices i) ^ n ≈
      term (supportLabel support i)
    rw [if_pos hi']
    unfold term historyProjectedCorrTerm packetGraphModeWeight
      historyGraphSquaredEigen physicalModeLabel projectedSquare
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hindexed
    (Q'.eqv_trans _ _ _
      (fsum_supportLabel_eq_listQSum term support)
      (history_physical_filter_corr_eq_full
        copiedEdges edges vertices packet n))

/-! ## Complete one-step composition of histories -/

private theorem historyCorrTerm_vacuum_spin_ne_zero {K : Nat}
    (copiedEdges : List Nat)
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (newSpin vacuumSpin : Nat)
    (hvacSpin : vacuumSpin ≠ 0) :
    historyProjectedCorrTerm copiedEdges
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (setEdgeLabel
          (setEdgeLabel tail newEdge newSpin) vacuumEdge vacuumSpin) ≈ 0 := by
  let label := setEdgeLabel
    (setEdgeLabel tail newEdge newSpin) vacuumEdge vacuumSpin
  have hcoeff : coeffAt
      (identityRefinedPacket newEdge vacuumEdge P vacuumEdge)
      (label vacuumEdge) ≈ 0 := by
    rw [show label vacuumEdge = vacuumSpin by
      simp [label, setEdgeLabel]]
    rw [identityRefinedPacket, if_pos rfl]
    rw [coeffAt_vacuumPacket]
    simp [hvacSpin]
    exact Q'.eqv_refl 0
  have hbare : packetGraphBareAmplitude
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedPacket newEdge vacuumEdge P) label ≈ 0 := by
    unfold packetGraphBareAmplitude identityRefinedEdges
    change coeffAt
        (identityRefinedPacket newEdge vacuumEdge P vacuumEdge)
        (label vacuumEdge) *
      eliminateLinks
        (fun edge => coeffAt
          (identityRefinedPacket newEdge vacuumEdge P edge) (label edge))
        (newEdge :: edges) ≈ 0
    exact Q'.eqv_trans _
      (0 * eliminateLinks
        (fun edge => coeffAt
          (identityRefinedPacket newEdge vacuumEdge P edge) (label edge))
        (newEdge :: edges)) _
      (Q'.mul_eqv_congr_right _ _ _ hcoeff)
      (Q'.zero_mul_eqv _)
  unfold historyProjectedCorrTerm projectedSquare
    packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices) label
  · rw [if_pos hp]
    exact Q'.eqv_trans _
      ((0 * 0) *
        (historyGraphEigen copiedEdges
          (identityRefinedEdges newEdge vacuumEdge edges) label *
         historyGraphEigen copiedEdges
          (identityRefinedEdges newEdge vacuumEdge edges) label) ^ n) _
      (q_mul_congr (q_mul_congr hbare hbare) (Q'.eqv_refl _))
      (Q'.zero_mul_eqv _)
  · rw [if_neg hp]
    exact Q'.zero_mul_eqv _

private theorem refinedGenerated_unphysical_of_new_ne
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (tail : EdgeLabelling)
    (spin : Nat) (hspin : spin ≠ tail oldEdge)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge) :
    graphPhysicalB
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0) =
      false := by
  let label := setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0
  have hold : label oldEdge = tail oldEdge := by
    simp [label, setEdgeLabel, Ne.symm hno, Ne.symm hvo]
  have hnew : label newEdge = spin := by
    simp [label, setEdgeLabel, hnv]
  have hvac : label vacuumEdge = 0 := by
    simp [label, setEdgeLabel]
  have hfusion : fusionOK (label oldEdge) (label newEdge)
      (label vacuumEdge) = false := by
    rw [hold, hnew, hvac]
    exact YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_ne
      (tail oldEdge) spin (Ne.symm hspin)
  unfold graphPhysicalB identityRefinedVertices identityRefinedVertex
    verticesAdmissibleB
  rw [hfusion]
  simp

private theorem historyCorrTerm_new_spin_ne {K : Nat}
    (copiedEdges : List Nat)
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (spin : Nat)
    (hspin : spin ≠ tail oldEdge)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge) :
    historyProjectedCorrTerm copiedEdges
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0) ≈ 0 := by
  apply historyProjectedCorrTerm_zero_of_unphysical
  exact refinedGenerated_unphysical_of_new_ne
    oldEdge newEdge vacuumEdge edges vertices tail spin hspin hno hvo hnv

theorem history_identity_new_segment_slice {K : Nat}
    (copiedEdges : List Nat)
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (hold : oldEdge ∈ edges)
    (htail : tail ∈ boundedEdgeLabellings K edges)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices)
    (hcopied : ∀ edge, edge ∈ copiedEdges → edge ∈ edges) :
    fsum (fun spin => historyProjectedCorrTerm (oldEdge :: copiedEdges)
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1) ≈
      historyProjectedCorrTerm copiedEdges edges vertices P n tail := by
  let slice : Nat → Q' := fun spin =>
    historyProjectedCorrTerm (oldEdge :: copiedEdges)
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
      (identityRefinedPacket newEdge vacuumEdge P) n
      (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0)
  have hbound : tail oldEdge < K + 1 :=
    (boundedEdgeLabellings_sound K edges tail htail).1 oldEdge hold
  have hcollapse : fsum slice (K + 1) ≈ slice (tail oldEdge) := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    intro spin hspin
    exact historyCorrTerm_new_spin_ne (oldEdge :: copiedEdges)
      oldEdge newEdge vacuumEdge edges vertices P n tail spin
        hspin hno hvo hnv
    exact hbound
  exact Q'.eqv_trans _ (slice (tail oldEdge)) _ hcollapse
    (historyProjectedCorrTerm_identity_refinement copiedEdges
      oldEdge newEdge vacuumEdge edges vertices P n tail hold hbound
        hnew hvac hno hvo hnv hnewV hvacV hcopied)

/-- Adding one more compensated identity refinement preserves the complete
correlator of an arbitrary preceding finite compensation history. -/
theorem history_packetGraph_corr_identity_refinement {K : Nat}
    (copiedEdges : List Nat)
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (hold : oldEdge ∈ edges)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices)
    (hcopied : ∀ edge, edge ∈ copiedEdges → edge ∈ edges) :
    corr (historyPacketGraphSpectralModel (oldEdge :: copiedEdges)
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P)) n ≈
      corr (historyPacketGraphSpectralModel
        copiedEdges edges vertices P) n := by
  let refinedTerm : EdgeLabelling → Q' :=
    historyProjectedCorrTerm (oldEdge :: copiedEdges)
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
      (identityRefinedPacket newEdge vacuumEdge P) n
  let vacuumSlice : Nat → Q' := fun vacuumSpin =>
    listQSum
      (fun label => refinedTerm (setEdgeLabel label vacuumEdge vacuumSpin))
      (boundedEdgeLabellings K (newEdge :: edges))
  have hvacCollapse : fsum vacuumSlice (K + 1) ≈ vacuumSlice 0 := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    intro vacuumSpin hspin
    apply listQSum_zero
    intro label
    have hz := historyCorrTerm_vacuum_spin_ne_zero
      (oldEdge :: copiedEdges) oldEdge newEdge vacuumEdge
      edges vertices P n label (label newEdge) vacuumSpin hspin
    rw [setEdgeLabel_current label newEdge] at hz
    exact hz
    exact Nat.succ_pos K
  have hnewExpand : vacuumSlice 0 ≈
      fsum (fun spin => listQSum
        (fun tail => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (boundedEdgeLabellings K edges)) (K + 1) := by
    exact listQSum_bounded_cons K newEdge edges
      (fun label => refinedTerm (setEdgeLabel label vacuumEdge 0))
  have hswap :
      fsum (fun spin => listQSum
        (fun tail => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (boundedEdgeLabellings K edges)) (K + 1) ≈
      listQSum (fun tail => fsum (fun spin => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1)) (boundedEdgeLabellings K edges) :=
    fsum_listQSum_swap
      (fun spin tail => refinedTerm
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
      (boundedEdgeLabellings K edges) (K + 1)
  have hsliceCollapse :
      listQSum (fun tail => fsum (fun spin => refinedTerm
          (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1)) (boundedEdgeLabellings K edges) ≈
      listQSum
        (historyProjectedCorrTerm copiedEdges edges vertices P n)
        (boundedEdgeLabellings K edges) := by
    apply listQSum_congr_mem
    intro tail htail
    exact history_identity_new_segment_slice copiedEdges
      oldEdge newEdge vacuumEdge edges vertices P n tail hold htail
        hnew hvac hno hvo hnv hnewV hvacV hcopied
  exact Q'.eqv_trans _
    (listQSum refinedTerm
      (boundedEdgeLabellings K
        (identityRefinedEdges newEdge vacuumEdge edges))) _
    (historyPacketGraph_corr_eq_full (oldEdge :: copiedEdges)
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
      (identityRefinedPacket newEdge vacuumEdge P) n)
    (Q'.eqv_trans _ (fsum vacuumSlice (K + 1)) _
      (listQSum_bounded_cons K vacuumEdge (newEdge :: edges) refinedTerm)
      (Q'.eqv_trans _ (vacuumSlice 0) _ hvacCollapse
        (Q'.eqv_trans _ _ _ hnewExpand
          (Q'.eqv_trans _ _ _ hswap
            (Q'.eqv_trans _
              (listQSum
                (historyProjectedCorrTerm copiedEdges edges vertices P n)
                (boundedEdgeLabellings K edges)) _
              hsliceCollapse
              (Q'.eqv_symm
                (historyPacketGraph_corr_eq_full
                  copiedEdges edges vertices P n)))))))

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator.historyGraphSquaredEigen_nonneg
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator.historyPacketGraph_corr_eq_full
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator.history_identity_new_segment_slice
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator.history_packetGraph_corr_identity_refinement
