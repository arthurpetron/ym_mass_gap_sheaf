/-
# Weighted spectral-gap transport through compensated refinement

Support pruning turns a weighted gap into an ordinary spectral gap, but a
volume-uniform construction also needs the same weighted bound at every
refinement stage.  This module proves the missing local transport theorem.

A nonzero refined packet amplitude forces the vacuum leg to carry label zero;
the fresh trivalent fusion guard then forces the copied segment to equal the
old segment.  Thus every nonzero-weight refined label is the canonical image
of an old physical label.  The compensation-history eigenvalue identity then
transports one common labelwise spectral bound through the move.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport

set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteSpinNetworkSpectralEnvelope
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementCompensationHistory
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementHistoryCorrelator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCompensatedRefinementPath
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphSupportedRefinementPath

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- Remove the two fresh coordinates from a refined labelling. -/
def eraseIdentityCoordinates (newEdge vacuumEdge : Nat)
    (label : EdgeLabelling) : EdgeLabelling :=
  setEdgeLabel (setEdgeLabel label newEdge 0) vacuumEdge 0

private theorem eraseIdentityCoordinates_old
    (oldEdge newEdge vacuumEdge : Nat) (label : EdgeLabelling)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge) :
    eraseIdentityCoordinates newEdge vacuumEdge label oldEdge =
      label oldEdge := by
  simp [eraseIdentityCoordinates, setEdgeLabel, Ne.symm hno, Ne.symm hvo]

/-- If the fresh coordinates have the identity-channel values, erasing them
and applying the canonical refinement recovers the refined label exactly. -/
theorem identityRefinedLabel_erase_eq
    (oldEdge newEdge vacuumEdge : Nat) (label : EdgeLabelling)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hvac : label vacuumEdge = 0)
    (hcopy : label newEdge = label oldEdge) :
    identityRefinedLabel oldEdge newEdge vacuumEdge
        (eraseIdentityCoordinates newEdge vacuumEdge label) = label := by
  funext edge
  by_cases hev : edge = vacuumEdge
  · subst edge
    simp [identityRefinedLabel, setEdgeLabel, hvac]
  by_cases hen : edge = newEdge
  · subst edge
    simp [identityRefinedLabel, eraseIdentityCoordinates, setEdgeLabel,
      hnv, Ne.symm hno, Ne.symm hvo, hcopy]
  · simp [identityRefinedLabel, eraseIdentityCoordinates, setEdgeLabel,
      hen, hev]

/-! ## Nonzero amplitude forces the identity channel -/

/-- A nonzero label on the new vacuum packet kills the refined projected
square exactly. -/
theorem refinedProjectedSquare_zero_of_vacuum_ne {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (label : EdgeLabelling) (hvac : label vacuumEdge ≠ 0) :
    projectedSquare
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) label ≈ 0 := by
  have hcoeff : coeffAt
      (identityRefinedPacket newEdge vacuumEdge P vacuumEdge)
      (label vacuumEdge) ≈ 0 := by
    rw [identityRefinedPacket, if_pos rfl]
    rw [SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket]
    simp [hvac]
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
  unfold projectedSquare packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices) label
  · rw [if_pos hp]
    exact q_mul_congr hbare hbare
  · rw [if_neg hp]
    exact Q'.mul_zero_eqv 0

/-- With vacuum label zero, unequal copied labels violate the fresh fusion
guard and kill the projected square exactly. -/
theorem refinedProjectedSquare_zero_of_copy_ne {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (label : EdgeLabelling) (hvac : label vacuumEdge = 0)
    (hcopy : label newEdge ≠ label oldEdge) :
    projectedSquare
        (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedPacket newEdge vacuumEdge P) label ≈ 0 := by
  apply projectedSquare_zero_of_unphysical
  have hfusion : fusionOK (label oldEdge) (label newEdge)
      (label vacuumEdge) = false := by
    rw [hvac]
    exact YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_ne
      (label oldEdge) (label newEdge) (Ne.symm hcopy)
  unfold graphPhysicalB identityRefinedVertices identityRefinedVertex
    verticesAdmissibleB
  rw [hfusion]
  simp

/-- Every nonzero-weight physical refined label descends to a physical old
label, with nonzero old weight, and is exactly its canonical refinement. -/
theorem nonzero_refined_label_descends {K : Nat}
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (P : Nat → CharacterPacket K)
    (label : EdgeLabelling) (hold : oldEdge ∈ edges)
    (hnew : newEdge ∉ edges) (hvacFresh : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices)
    (hmem : label ∈ physicalEdgeLabellings K
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices))
    (hnz : ¬ (projectedSquare
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
      (identityRefinedPacket newEdge vacuumEdge P) label ≈ 0)) :
    ∃ oldLabel : EdgeLabelling,
      oldLabel ∈ physicalEdgeLabellings K edges vertices ∧
      ¬ (projectedSquare edges vertices P oldLabel ≈ 0) ∧
      identityRefinedLabel oldEdge newEdge vacuumEdge oldLabel = label := by
  have hvac : label vacuumEdge = 0 := by
    by_cases h : label vacuumEdge = 0
    · exact h
    · exact False.elim (hnz
        (refinedProjectedSquare_zero_of_vacuum_ne
          oldEdge newEdge vacuumEdge edges vertices P label h))
  have hcopy : label newEdge = label oldEdge := by
    by_cases h : label newEdge = label oldEdge
    · exact h
    · exact False.elim (hnz
        (refinedProjectedSquare_zero_of_copy_ne
          oldEdge newEdge vacuumEdge edges vertices P label hvac h))
  let oldLabel := eraseIdentityCoordinates newEdge vacuumEdge label
  have hcanon : identityRefinedLabel oldEdge newEdge vacuumEdge oldLabel =
      label := by
    exact identityRefinedLabel_erase_eq oldEdge newEdge vacuumEdge label
      hno hvo hnv hvac hcopy
  have hrefBounded := (List.mem_filter.mp hmem).1
  have hrefSound := boundedEdgeLabellings_sound K
    (identityRefinedEdges newEdge vacuumEdge edges) label hrefBounded
  have holdBounded : oldLabel ∈ boundedEdgeLabellings K edges := by
    apply boundedEdgeLabellings_complete
    · intro edge hedge
      have hrefMem : edge ∈ identityRefinedEdges newEdge vacuumEdge edges :=
        List.mem_cons_of_mem vacuumEdge
          (List.mem_cons_of_mem newEdge hedge)
      have hlt := hrefSound.1 edge hrefMem
      unfold oldLabel eraseIdentityCoordinates
      have hen : edge ≠ newEdge := by
        intro heq
        subst edge
        exact hnew hedge
      have hev : edge ≠ vacuumEdge := by
        intro heq
        subst edge
        exact hvacFresh hedge
      simpa [setEdgeLabel, hen, hev] using hlt
    · intro edge hedge
      unfold oldLabel eraseIdentityCoordinates
      by_cases hen : edge = newEdge
      · subst edge
        simp [setEdgeLabel]
      by_cases hev : edge = vacuumEdge
      · subst edge
        simp [setEdgeLabel]
      have hrefNot : edge ∉
          identityRefinedEdges newEdge vacuumEdge edges := by
        simp [identityRefinedEdges, hen, hev, hedge]
      have hz := hrefSound.2 edge hrefNot
      simpa [setEdgeLabel, hen, hev] using hz
  have hrefPhysical := (List.mem_filter.mp hmem).2
  have hphysEq := graphPhysicalB_identity_refinement
    oldEdge newEdge vacuumEdge edges vertices oldLabel hold hnew hvacFresh
      hno hvo hnv hnewV hvacV
  rw [hcanon] at hphysEq
  have holdPhysical : graphPhysicalB edges vertices oldLabel = true := by
    rw [← hphysEq]
    exact hrefPhysical
  have holdMem : oldLabel ∈ physicalEdgeLabellings K edges vertices :=
    List.mem_filter.mpr ⟨holdBounded, holdPhysical⟩
  have holdCoord : oldLabel oldEdge = label oldEdge := by
    unfold oldLabel
    exact eraseIdentityCoordinates_old oldEdge newEdge vacuumEdge label hno hvo
  have holdSpinBound : oldLabel oldEdge < K + 1 :=
    (boundedEdgeLabellings_sound K edges oldLabel holdBounded).1
      oldEdge hold
  have hamp := packetGraphProjectedAmplitude_identity_refinement
    oldEdge newEdge vacuumEdge edges vertices P oldLabel hold holdSpinBound
      hnew hvacFresh hno hvo hnv hnewV hvacV
  have hsquare : projectedSquare
      (identityRefinedEdges newEdge vacuumEdge edges)
      (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
      (identityRefinedPacket newEdge vacuumEdge P)
      (identityRefinedLabel oldEdge newEdge vacuumEdge oldLabel) ≈
      projectedSquare edges vertices P oldLabel := by
    unfold projectedSquare
    exact q_mul_congr hamp hamp
  rw [hcanon] at hsquare
  have holdNZ : ¬ (projectedSquare edges vertices P oldLabel ≈ 0) := by
    intro hz
    exact hnz (Q'.eqv_trans _ _ _ hsquare hz)
  exact ⟨oldLabel, holdMem, holdNZ, hcanon⟩

/-! ## Labelwise and spectral gap transport -/

/-- A spectral bound stated directly on every physical, nonzero-weight graph
label.  This form is stable under the canonical label descent above. -/
def LabelWeightedGraphGap {K : Nat} (S : CompensatedGraphState K)
    (mu : Q') : Prop :=
  ∀ label, label ∈ physicalEdgeLabellings K S.edges S.vertices →
    ¬ (projectedSquare S.edges S.vertices S.packet label ≈ 0) →
    historyGraphEigen S.copiedEdges S.edges label *
      historyGraphEigen S.copiedEdges S.edges label ≤ mu

/-- One certified compensated refinement transports the same labelwise gap
bound with no volume-dependent loss. -/
theorem move_labelWeightedGap {K : Nat} {S : CompensatedGraphState K}
    (M : IdentityRefinementMove S) (mu : Q')
    (hgap : LabelWeightedGraphGap S mu) :
    LabelWeightedGraphGap M.next mu := by
  intro label hmem hnz
  rcases nonzero_refined_label_descends
    M.oldEdge M.newEdge M.vacuumEdge S.edges S.vertices S.packet label
      M.old_mem M.new_fresh M.vacuum_fresh M.new_ne_old M.vacuum_ne_old
      M.new_ne_vacuum M.vertices_avoid_new M.vertices_avoid_vacuum
      hmem hnz with ⟨oldLabel, holdMem, holdNZ, hcanon⟩
  have he := historyGraphEigen_identity_refinement S.copiedEdges
    M.oldEdge M.newEdge M.vacuumEdge S.edges oldLabel
    M.new_fresh M.vacuum_fresh M.new_ne_old M.vacuum_ne_old
    M.new_ne_vacuum S.copied_mem
  rw [hcanon] at he
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (q_mul_congr he he))
    (hgap oldLabel holdMem holdNZ)

/-- A labelwise bound controls the weighted finite spectral presentation;
all indices beyond the retained physical list have exact zero weight. -/
theorem weightedGraphGap_of_labelGap {K : Nat}
    (S : CompensatedGraphState K) (mu : Q')
    (hgap : LabelWeightedGraphGap S mu) : WeightedGraphGap S mu := by
  intro i hnz
  let support := physicalEdgeLabellings K S.edges S.vertices
  by_cases hi : i < support.length
  · have hmem : physicalModeLabel K S.edges S.vertices i ∈ support :=
      supportLabel_mem hi
    have hweightNZ : ¬ (projectedSquare S.edges S.vertices S.packet
        (physicalModeLabel K S.edges S.vertices i) ≈ 0) := by
      intro hz
      apply hnz
      change historyPacketGraphModeWeight S.edges S.vertices S.packet i ≈ 0
      unfold historyPacketGraphModeWeight
      rw [if_pos hi]
      unfold packetGraphModeWeight physicalModeLabel
      exact hz
    change historyGraphSquaredEigen S.copiedEdges S.edges S.vertices i ≤ mu
    unfold historyGraphSquaredEigen
    exact hgap _ hmem hweightNZ
  · exfalso
    apply hnz
    change historyPacketGraphModeWeight S.edges S.vertices S.packet i ≈ 0
    unfold historyPacketGraphModeWeight
    rw [if_neg hi]
    exact Q'.eqv_refl 0

/-- Hence every transported labelwise gap is an ordinary gap of the exact
support-pruned spectral model. -/
theorem supportedGraph_gap_of_labelGap {K : Nat}
    (S : CompensatedGraphState K) (mu : Q')
    (hmu : (0 : Q') ≤ mu) (hgap : LabelWeightedGraphGap S mu) :
    SpectralGap.SpectralGapBound (supportedGraphSpectralModel S) mu :=
  supportedGraph_gap S mu hmu (weightedGraphGap_of_labelGap S mu hgap)

/-- Labelwise gap transport iterates along every certified finite refinement
path with exactly the same separator. -/
theorem path_labelWeightedGap {K : Nat} {S T : CompensatedGraphState K}
    (path : CompensatedRefinementPath S T) (mu : Q')
    (hgap : LabelWeightedGraphGap S mu) :
    LabelWeightedGraphGap T mu := by
  induction path with
  | refl _ => exact hgap
  | step M tail ih =>
      exact ih (move_labelWeightedGap M mu hgap)

/-- With no accumulated reciprocal history, every physical graph label lies
below the universal strong-coupling separator `(1/8)^2`. -/
theorem uncompensated_labelWeightedGap {K : Nat}
    (S : CompensatedGraphState K) (hcopy : S.copiedEdges = []) :
    LabelWeightedGraphGap S (eighth * eighth) := by
  intro label hmem _
  have hphysicalB := (List.mem_filter.mp hmem).2
  have hphysical : GraphPhysical S.edges S.vertices label := hphysicalB
  have hexc := graphPhysical_exists_excited hphysical
  have ha : (0 : Q') ≤ networkEigen S.edges label :=
    networkEigen_nonneg label S.edges
  have hae : networkEigen S.edges label ≤ eighth :=
    networkEigen_excited_le_eighth label S.edges hexc
  have h1 : networkEigen S.edges label * networkEigen S.edges label ≤
      eighth * networkEigen S.edges label :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hae ha
  have h2 : eighth * networkEigen S.edges label ≤ eighth * eighth :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hae (by decide)
  have hsquare : networkEigen S.edges label * networkEigen S.edges label ≤
      eighth * eighth := Q'.le_trans' _ _ _ h1 h2
  have he : historyGraphEigen S.copiedEdges S.edges label ≈
      networkEigen S.edges label := by
    rw [hcopy]
    exact historyGraphEigen_nil S.edges label
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (q_mul_congr he he)) hsquare

/-- Consequently, every terminal graph in a certified finite refinement path
from an uncompensated state has the same ordinary support-pruned spectral
gap bound `(1/8)^2`, independent of the number of refinements. -/
theorem path_supported_gap_from_uncompensated {K : Nat}
    {S T : CompensatedGraphState K} (path : CompensatedRefinementPath S T)
    (hcopy : S.copiedEdges = []) :
    SpectralGap.SpectralGapBound (supportedGraphSpectralModel T)
      (eighth * eighth) := by
  exact supportedGraph_gap_of_labelGap T (eighth * eighth)
    (Q'.mul_nonneg _ _ (by decide) (by decide))
    (path_labelWeightedGap path (eighth * eighth)
      (uncompensated_labelWeightedGap S hcopy))

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.identityRefinedLabel_erase_eq
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.refinedProjectedSquare_zero_of_vacuum_ne
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.nonzero_refined_label_descends
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.move_labelWeightedGap
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.weightedGraphGap_of_labelGap
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.supportedGraph_gap_of_labelGap
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.path_labelWeightedGap
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.uncompensated_labelWeightedGap
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphWeightedGapTransport.path_supported_gap_from_uncompensated
