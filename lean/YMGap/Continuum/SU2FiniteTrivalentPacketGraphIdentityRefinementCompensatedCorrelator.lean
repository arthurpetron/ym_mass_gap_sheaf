/-
# Complete compensated correlator collapse under identity refinement

The reciprocal copied-edge normalization was previously proved to preserve
every fusion-selected spectral summand.  Here it is installed as the
diagonal of a positive finite spectral model.  The two new Cartesian label
sums are then collapsed exactly, proving equality of the complete
integer-time correlators before and after one interacting identity
refinement.

Honest scope: this supplies one local graph-refinement compatibility map.
It does not yet prove coherence of composites, construct a thermodynamic
directed system, or control a continuum limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedTransfer

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedCorrelator

set_option maxHeartbeats 1600000
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
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedTransfer

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

/-! ## The compensated positive spectral model -/

/-- The squared compensated eigenvalue on the `i`th physical graph mode. -/
def compensatedGraphSquaredEigen {K : Nat} (oldEdge : Nat)
    (edges : List Nat) (vertices : List TrivalentVertex) (i : Nat) : Q' :=
  let label := physicalModeLabel K edges vertices i
  let e := compensatedGraphEigen oldEdge edges label
  e * e

theorem compensatedGraphSquaredEigen_nonneg {K : Nat} (oldEdge : Nat)
    (edges : List Nat) (vertices : List TrivalentVertex) (i : Nat) :
    (0 : Q') ≤ compensatedGraphSquaredEigen (K := K) oldEdge edges vertices i := by
  unfold compensatedGraphSquaredEigen
  exact YMGap.Constructive.SumOfSquares.q_mul_self_nonneg _

/-- The finite positive spectral model with the local copied-edge transfer
factor divided out exactly. -/
def compensatedPacketGraphSpectralModel {K : Nat} (oldEdge : Nat)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) : SpectralModel :=
  diagOp.toSpectralModel
    (compensatedGraphSquaredEigen (K := K) oldEdge edges vertices)
    (packetGraphModeWeight edges vertices packet)
    (physicalEdgeLabellings K edges vertices).length
    (packetGraphModeWeight_nonneg edges vertices packet)
    (compensatedGraphSquaredEigen_nonneg oldEdge edges vertices)

theorem compensatedProjectedCorrTerm_zero_of_unphysical {K : Nat}
    (oldEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat)
    (label : EdgeLabelling)
    (h : graphPhysicalB edges vertices label = false) :
    compensatedProjectedCorrTerm oldEdge edges vertices packet n label ≈ 0 := by
  unfold compensatedProjectedCorrTerm
  exact Q'.eqv_trans _
    (0 * (compensatedGraphEigen oldEdge edges label *
      compensatedGraphEigen oldEdge edges label) ^ n) _
    (q_mul_congr
      (projectedSquare_zero_of_unphysical edges vertices packet label h)
      (Q'.eqv_refl _))
    (Q'.zero_mul_eqv _)

private theorem compensated_physical_filter_corr_eq_full {K : Nat}
    (oldEdge : Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat) :
    listQSum (compensatedProjectedCorrTerm oldEdge edges vertices packet n)
        (physicalEdgeLabellings K edges vertices) ≈
      listQSum (compensatedProjectedCorrTerm oldEdge edges vertices packet n)
        (boundedEdgeLabellings K edges) := by
  unfold physicalEdgeLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun label => if graphPhysicalB edges vertices label then
        compensatedProjectedCorrTerm oldEdge edges vertices packet n label else 0)
      (boundedEdgeLabellings K edges)) _
    (listQSum_filter _ _ _) ?_
  apply listQSum_congr
  intro label
  cases hp : graphPhysicalB edges vertices label with
  | false =>
      exact Q'.eqv_symm
        (compensatedProjectedCorrTerm_zero_of_unphysical
          oldEdge edges vertices packet n label hp)
  | true => exact Q'.eqv_refl _

/-- Every compensated correlator is the complete Cartesian sum of its
compensated full-support summands. -/
theorem compensatedPacketGraph_corr_eq_full {K : Nat} (oldEdge : Nat)
    (edges : List Nat) (vertices : List TrivalentVertex)
    (packet : Nat → CharacterPacket K) (n : Nat) :
    corr (compensatedPacketGraphSpectralModel oldEdge edges vertices packet) n ≈
      listQSum (compensatedProjectedCorrTerm oldEdge edges vertices packet n)
        (boundedEdgeLabellings K edges) := by
  let support := physicalEdgeLabellings K edges vertices
  let term := compensatedProjectedCorrTerm oldEdge edges vertices packet n
  have hindexed :
      corr (compensatedPacketGraphSpectralModel
          oldEdge edges vertices packet) n ≈
        fsum (fun i => term (supportLabel support i)) support.length := by
    unfold corr compensatedPacketGraphSpectralModel
      CompactTransferGNS.diagOp.toSpectralModel
    rw [← YMGap.Continuum.MovingCutoff.fsum_eq_finSum]
    apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr_lt
    intro i _
    unfold term compensatedProjectedCorrTerm packetGraphModeWeight
      compensatedGraphSquaredEigen physicalModeLabel projectedSquare
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hindexed
    (Q'.eqv_trans _ _ _
      (fsum_supportLabel_eq_listQSum term support)
      (compensated_physical_filter_corr_eq_full
        oldEdge edges vertices packet n))

/-! ## Exact collapse of the two refinement labels -/

private theorem compensatedCorrTerm_vacuum_spin_ne_zero {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (newSpin vacuumSpin : Nat)
    (hvacSpin : vacuumSpin ≠ 0) :
    compensatedProjectedCorrTerm oldEdge
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
  unfold compensatedProjectedCorrTerm projectedSquare
    packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices) label
  · rw [if_pos hp]
    exact Q'.eqv_trans _
      ((0 * 0) *
        (compensatedGraphEigen oldEdge
          (identityRefinedEdges newEdge vacuumEdge edges) label *
         compensatedGraphEigen oldEdge
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

private theorem compensatedCorrTerm_new_spin_ne {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (spin : Nat)
    (hspin : spin ≠ tail oldEdge)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge) :
    compensatedProjectedCorrTerm oldEdge
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0) ≈ 0 := by
  apply compensatedProjectedCorrTerm_zero_of_unphysical
  exact refinedGenerated_unphysical_of_new_ne
    oldEdge newEdge vacuumEdge edges vertices tail spin hspin hno hvo hnv

/-- For a fixed old labelling, the compensated new-segment sum has exactly
one fusion-diagonal survivor, equal to the original old-graph summand at
every integer time. -/
theorem compensated_identity_new_segment_slice {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (tail : EdgeLabelling) (hold : oldEdge ∈ edges)
    (htail : tail ∈ boundedEdgeLabellings K edges)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    fsum (fun spin => compensatedProjectedCorrTerm oldEdge
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) n
        (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0))
        (K + 1) ≈
      projectedCorrTerm edges vertices P n tail := by
  let slice : Nat → Q' := fun spin => compensatedProjectedCorrTerm oldEdge
    (identityRefinedEdges newEdge vacuumEdge edges)
    (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
    (identityRefinedPacket newEdge vacuumEdge P) n
    (setEdgeLabel (setEdgeLabel tail newEdge spin) vacuumEdge 0)
  have hbound : tail oldEdge < K + 1 :=
    (boundedEdgeLabellings_sound K edges tail htail).1 oldEdge hold
  have hcollapse : fsum slice (K + 1) ≈ slice (tail oldEdge) := by
    apply YMGap.Continuum.FusionQuotientCollapse.fsum_collapse
    intro spin hspin
    exact compensatedCorrTerm_new_spin_ne oldEdge newEdge vacuumEdge
      edges vertices P n tail spin hspin hno hvo hnv
    exact hbound
  exact Q'.eqv_trans _ (slice (tail oldEdge)) _ hcollapse
    (compensatedProjectedCorrTerm_identity_refinement
      oldEdge newEdge vacuumEdge edges vertices P n tail hold hbound
        hnew hvac hno hvo hnv hnewV hvacV)

/-- A complete interacting identity refinement, equipped with its exact local
transfer compensation, preserves the full finite spectral correlator at
every integer time. -/
theorem compensated_packetGraph_corr_identity_refinement {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (n : Nat) (hold : oldEdge ∈ edges)
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    corr (compensatedPacketGraphSpectralModel oldEdge
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P)) n ≈
      corr (packetGraphSpectralModel edges vertices P) n := by
  let refinedTerm : EdgeLabelling → Q' := compensatedProjectedCorrTerm oldEdge
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
    have hz := compensatedCorrTerm_vacuum_spin_ne_zero
      oldEdge newEdge vacuumEdge edges vertices P n label
        (label newEdge) vacuumSpin hspin
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
      listQSum (projectedCorrTerm edges vertices P n)
        (boundedEdgeLabellings K edges) := by
    apply listQSum_congr_mem
    intro tail htail
    exact compensated_identity_new_segment_slice
      oldEdge newEdge vacuumEdge edges vertices P n tail hold htail
        hnew hvac hno hvo hnv hnewV hvacV
  exact Q'.eqv_trans _
    (listQSum refinedTerm
      (boundedEdgeLabellings K
        (identityRefinedEdges newEdge vacuumEdge edges))) _
    (compensatedPacketGraph_corr_eq_full oldEdge
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
      (identityRefinedPacket newEdge vacuumEdge P) n)
    (Q'.eqv_trans _ (fsum vacuumSlice (K + 1)) _
      (listQSum_bounded_cons K vacuumEdge (newEdge :: edges) refinedTerm)
      (Q'.eqv_trans _ (vacuumSlice 0) _ hvacCollapse
        (Q'.eqv_trans _ _ _ hnewExpand
          (Q'.eqv_trans _ _ _ hswap
            (Q'.eqv_trans _
              (listQSum (projectedCorrTerm edges vertices P n)
                (boundedEdgeLabellings K edges)) _
              hsliceCollapse
              (Q'.eqv_symm
                (packetGraph_corr_eq_full edges vertices P n)))))))

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedCorrelator

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedCorrelator.compensatedGraphSquaredEigen_nonneg
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedCorrelator.compensatedPacketGraph_corr_eq_full
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedCorrelator.compensated_identity_new_segment_slice
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensatedCorrelator.compensated_packetGraph_corr_identity_refinement
