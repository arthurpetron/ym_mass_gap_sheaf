/-
# Presentation compatibility for finite trivalent packet graphs

A finite graph should not depend on the order used to list its edges or its
trivalent vertices.  This file proves the pointwise part of that statement
constructively.  The excited-edge guard and the vertex-admissibility guard
are invariant under list permutations; hence the actual packet amplitude,
gauge/vacuum projection, transfer summand, and their squares are invariant.

Because changing only the vertex order leaves the Cartesian edge-label list
unchanged, the full and filtered exact norms are also proved invariant under
arbitrary vertex permutations.  Edge-order invariance of the *summands* is
proved here; reindexing the nested Cartesian enumeration under an edge
permutation is left as the next finite combinatorial step.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility

set_option maxHeartbeats 800000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## Permutation invariance of the Boolean graph guards -/

theorem hasExcitedB_perm (label : EdgeLabelling) {A B : List Nat}
    (h : A.Perm B) : hasExcitedB label A = hasExcitedB label B := by
  induction h with
  | nil => rfl
  | cons edge h ih =>
      unfold hasExcitedB
      by_cases he : 1 ≤ label edge
      · rw [if_pos he, if_pos he]
      · rw [if_neg he, if_neg he, ih]
  | swap a b rest =>
      by_cases ha : 1 ≤ label a
      <;> by_cases hb : 1 ≤ label b
      <;> simp [hasExcitedB, ha, hb]
  | trans hAB hBC ihAB ihBC => exact ihAB.trans ihBC

theorem verticesAdmissibleB_perm (label : EdgeLabelling)
    {A B : List TrivalentVertex} (h : A.Perm B) :
    verticesAdmissibleB A label = verticesAdmissibleB B label := by
  induction h with
  | nil => rfl
  | cons vertex h ih =>
      unfold verticesAdmissibleB
      by_cases hv : fusionOK (label vertex.1) (label vertex.2.1)
          (label vertex.2.2) = true
      · rw [if_pos hv, if_pos hv, ih]
      · rw [if_neg hv, if_neg hv]
  | swap u v rest =>
      by_cases hu : fusionOK (label u.1) (label u.2.1) (label u.2.2) = true
      <;> by_cases hv : fusionOK (label v.1) (label v.2.1)
          (label v.2.2) = true
      <;> simp [verticesAdmissibleB, hu, hv]
  | trans hAB hBC ihAB ihBC => exact ihAB.trans ihBC

theorem graphPhysicalB_edge_perm (vertices : List TrivalentVertex)
    (label : EdgeLabelling) {A B : List Nat} (h : A.Perm B) :
    graphPhysicalB A vertices label = graphPhysicalB B vertices label := by
  unfold graphPhysicalB
  rw [hasExcitedB_perm label h]

theorem graphPhysicalB_vertex_perm (edges : List Nat)
    (label : EdgeLabelling) {A B : List TrivalentVertex} (h : A.Perm B) :
    graphPhysicalB edges A label = graphPhysicalB edges B label := by
  unfold graphPhysicalB
  rw [verticesAdmissibleB_perm label h]

/-! ## Pointwise amplitude and transfer compatibility -/

theorem packetGraphBareAmplitude_edge_perm {K : Nat}
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    {A B : List Nat} (h : A.Perm B) :
    packetGraphBareAmplitude A packet label ≈
      packetGraphBareAmplitude B packet label := by
  unfold packetGraphBareAmplitude
  exact eliminateLinks_perm
    (fun edge => coeffAt (packet edge) (label edge)) h

theorem packetGraphProjectedAmplitude_edge_perm {K : Nat}
    (vertices : List TrivalentVertex) (packet : Nat → CharacterPacket K)
    (label : EdgeLabelling) {A B : List Nat} (h : A.Perm B) :
    packetGraphProjectedAmplitude A vertices packet label ≈
      packetGraphProjectedAmplitude B vertices packet label := by
  have hphys : GraphPhysical A vertices label ↔
      GraphPhysical B vertices label := by
    constructor
    · intro hp
      change graphPhysicalB A vertices label = true at hp
      change graphPhysicalB B vertices label = true
      rwa [← graphPhysicalB_edge_perm vertices label h]
    · intro hp
      change graphPhysicalB B vertices label = true at hp
      change graphPhysicalB A vertices label = true
      rwa [graphPhysicalB_edge_perm vertices label h]
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical B vertices label
  · rw [if_pos (hphys.mpr hp), if_pos hp]
    exact packetGraphBareAmplitude_edge_perm packet label h
  · rw [if_neg (fun hpa => hp (hphys.mp hpa)), if_neg hp]
    exact Q'.eqv_refl 0

theorem packetGraphProjectedAmplitude_vertex_perm {K : Nat}
    (edges : List Nat) (packet : Nat → CharacterPacket K)
    (label : EdgeLabelling) {A B : List TrivalentVertex} (h : A.Perm B) :
    packetGraphProjectedAmplitude edges A packet label ≈
      packetGraphProjectedAmplitude edges B packet label := by
  have hphys : GraphPhysical edges A label ↔
      GraphPhysical edges B label := by
    constructor
    · intro hp
      change graphPhysicalB edges A label = true at hp
      change graphPhysicalB edges B label = true
      rwa [← graphPhysicalB_vertex_perm edges label h]
    · intro hp
      change graphPhysicalB edges B label = true at hp
      change graphPhysicalB edges A label = true
      rwa [graphPhysicalB_vertex_perm edges label h]
  unfold packetGraphProjectedAmplitude graphGaugeVacuumProject
  by_cases hp : GraphPhysical edges B label
  · rw [if_pos (hphys.mpr hp), if_pos hp]
    exact Q'.eqv_refl _
  · rw [if_neg (fun hpa => hp (hphys.mp hpa)), if_neg hp]
    exact Q'.eqv_refl 0

theorem projectedSquare_edge_perm {K : Nat}
    (vertices : List TrivalentVertex) (packet : Nat → CharacterPacket K)
    (label : EdgeLabelling) {A B : List Nat} (h : A.Perm B) :
    projectedSquare A vertices packet label ≈
      projectedSquare B vertices packet label := by
  unfold projectedSquare
  exact q_mul_congr
    (packetGraphProjectedAmplitude_edge_perm vertices packet label h)
    (packetGraphProjectedAmplitude_edge_perm vertices packet label h)

theorem projectedSquare_vertex_perm {K : Nat} (edges : List Nat)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    {A B : List TrivalentVertex} (h : A.Perm B) :
    projectedSquare edges A packet label ≈
      projectedSquare edges B packet label := by
  unfold projectedSquare
  exact q_mul_congr
    (packetGraphProjectedAmplitude_vertex_perm edges packet label h)
    (packetGraphProjectedAmplitude_vertex_perm edges packet label h)

theorem transferredProjectedSquare_edge_perm {K : Nat}
    (vertices : List TrivalentVertex) (packet : Nat → CharacterPacket K)
    (label : EdgeLabelling) {A B : List Nat} (h : A.Perm B) :
    transferredProjectedSquare A vertices packet label ≈
      transferredProjectedSquare B vertices packet label := by
  unfold transferredProjectedSquare graphTransfer
  have he := graphEigen_order_independent label h
  have ha := packetGraphProjectedAmplitude_edge_perm vertices packet label h
  exact q_mul_congr (q_mul_congr he ha) (q_mul_congr he ha)

theorem transferredProjectedSquare_vertex_perm {K : Nat} (edges : List Nat)
    (packet : Nat → CharacterPacket K) (label : EdgeLabelling)
    {A B : List TrivalentVertex} (h : A.Perm B) :
    transferredProjectedSquare edges A packet label ≈
      transferredProjectedSquare edges B packet label := by
  unfold transferredProjectedSquare graphTransfer
  have ha := packetGraphProjectedAmplitude_vertex_perm edges packet label h
  exact q_mul_congr
    (Q'.mul_eqv_congr_left _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ ha)

/-! ## Exact norm invariance under vertex presentation changes -/

theorem packetGraphFullExactNorm_vertex_perm {K : Nat} (edges : List Nat)
    (packet : Nat → CharacterPacket K) {A B : List TrivalentVertex}
    (h : A.Perm B) :
    packetGraphFullExactNorm edges A packet ≈
      packetGraphFullExactNorm edges B packet := by
  unfold packetGraphFullExactNorm
  exact listQSum_congr
    (fun label => projectedSquare_vertex_perm edges packet label h) _

theorem packetGraphFullTransferredNorm_vertex_perm {K : Nat}
    (edges : List Nat) (packet : Nat → CharacterPacket K)
    {A B : List TrivalentVertex} (h : A.Perm B) :
    packetGraphFullTransferredNorm edges A packet ≈
      packetGraphFullTransferredNorm edges B packet := by
  unfold packetGraphFullTransferredNorm
  exact listQSum_congr
    (fun label => transferredProjectedSquare_vertex_perm edges packet label h) _

theorem packetGraphExactNorm_vertex_perm {K : Nat} (edges : List Nat)
    (packet : Nat → CharacterPacket K) {A B : List TrivalentVertex}
    (h : A.Perm B) :
    packetGraphExactNorm edges A packet ≈
      packetGraphExactNorm edges B packet := by
  exact Q'.eqv_trans _ (packetGraphFullExactNorm edges A packet) _
    (packetGraphExactNorm_eq_full edges A packet)
    (Q'.eqv_trans _ (packetGraphFullExactNorm edges B packet) _
      (packetGraphFullExactNorm_vertex_perm edges packet h)
      (Q'.eqv_symm (packetGraphExactNorm_eq_full edges B packet)))

theorem packetGraphOperatorTransferredNorm_vertex_perm {K : Nat}
    (edges : List Nat) (packet : Nat → CharacterPacket K)
    {A B : List TrivalentVertex} (h : A.Perm B) :
    packetGraphOperatorTransferredNorm edges A packet ≈
      packetGraphOperatorTransferredNorm edges B packet := by
  exact Q'.eqv_trans _ (packetGraphFullTransferredNorm edges A packet) _
    (packetGraphOperatorTransferredNorm_eq_full edges A packet)
    (Q'.eqv_trans _ (packetGraphFullTransferredNorm edges B packet) _
      (packetGraphFullTransferredNorm_vertex_perm edges packet h)
      (Q'.eqv_symm
        (packetGraphOperatorTransferredNorm_eq_full edges B packet)))

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility.hasExcitedB_perm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility.verticesAdmissibleB_perm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility.packetGraphProjectedAmplitude_edge_perm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility.transferredProjectedSquare_edge_perm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility.packetGraphExactNorm_vertex_perm
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphPresentationCompatibility.packetGraphOperatorTransferredNorm_vertex_perm
