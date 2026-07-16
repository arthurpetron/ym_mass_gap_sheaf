/-
# Cartesian graph sums under fresh identifier renaming

This module proves the finite-Fubini half of identifier transport.  Two edge
labellings are related when their coordinates agree through an injective
renaming on a finite edge list.  Coordinate updates preserve that relation,
so induction through `boundedEdgeLabellings` identifies the two complete
Cartesian sums.

For a trivalent graph whose vertex identifiers are covered by the edge list,
the fusion guards and packet product are pointwise invariant under the same
renaming.  The final theorem therefore transports the literal vertex-only
graph sum, including every nested finite label sum, without choosing an
inverse permutation or invoking classical choice.

Honest scope: this is a generic exact reindexing theorem.  The next step is to
instantiate its packet and coverage hypotheses for the canonical
`fuseLabels` block and then identify that canonical sum with the
left-associated fusion kernel.
-/

import YMGap.Continuum.Z4FuseChainIdentifierTransport
import YMGap.Continuum.Z4FiniteGraphVacuumCompletion

namespace YMGap.Continuum.Z4GraphIdentifierCartesianTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FuseChainIdentifierTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Coordinate relations and finite Fubini -/

/-- The renaming is injective on the displayed finite coordinate list. -/
def InjectiveOnList (f : Nat → Nat) (edges : List Nat) : Prop :=
  ∀ x, x ∈ edges → ∀ y, y ∈ edges → f x = f y → x = y

/-- Duplicate-freeness of the renamed coordinate list supplies exactly the
finite injectivity premise used by the Cartesian induction. -/
theorem injectiveOnList_of_map_nodup (f : Nat → Nat) :
    ∀ edges : List Nat, (edges.map f).Nodup → InjectiveOnList f edges
  | [], _ => by
      intro x hx
      cases hx
  | edge :: rest, h => by
      have hp := List.nodup_cons.mp h
      intro x hx y hy hxy
      simp only [List.mem_cons] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · rfl
      · exfalso
        apply hp.1
        exact List.mem_map.mpr ⟨y, hy, hxy.symm⟩
      · exfalso
        apply hp.1
        exact List.mem_map.mpr ⟨x, hx, hxy⟩
      · exact injectiveOnList_of_map_nodup f rest hp.2 x hx y hy hxy

/-- Actual and canonical labellings agree on every displayed coordinate. -/
def LabelsAgreeOnRename (f : Nat → Nat) (edges : List Nat)
    (canonical actual : EdgeLabelling) : Prop :=
  ∀ edge, edge ∈ edges → actual (f edge) = canonical edge

private theorem injectiveOnList_tail (f : Nat → Nat) (edge : Nat)
    (rest : List Nat) (h : InjectiveOnList f (edge :: rest)) :
    InjectiveOnList f rest := by
  intro x hx y hy hxy
  exact h x (List.mem_cons_of_mem edge hx)
    y (List.mem_cons_of_mem edge hy) hxy

private theorem zeroLabelsAgree (f : Nat → Nat) (edges : List Nat) :
    LabelsAgreeOnRename f edges zeroEdgeLabelling zeroEdgeLabelling := by
  intro edge _
  rfl

/-- Matching coordinate updates preserve agreement through an injective
renaming. -/
theorem labelsAgree_setEdgeLabel (f : Nat → Nat)
    (edge spin : Nat) (rest : List Nat)
    (canonical actual : EdgeLabelling)
    (hinj : InjectiveOnList f (edge :: rest))
    (hagree : LabelsAgreeOnRename f rest canonical actual) :
    LabelsAgreeOnRename f (edge :: rest)
      (setEdgeLabel canonical edge spin)
      (setEdgeLabel actual (f edge) spin) := by
  intro x hx
  by_cases hxe : x = edge
  · subst x
    simp [setEdgeLabel]
  · have hxrest : x ∈ rest := by
      exact (List.mem_cons.mp hx).resolve_left hxe
    have hfxe : f x ≠ f edge := by
      intro h
      have hsame := hinj x hx edge List.mem_cons_self h
      exact hxe hsame
    simp only [setEdgeLabel, if_neg hfxe, if_neg hxe]
    exact hagree x hxrest

/-- **Constructive Cartesian reindexing.**  Pointwise agreement on related
labellings lifts through every coordinate of the complete bounded labelling
enumeration. -/
theorem listQSum_bounded_rename (K : Nat) (f : Nat → Nat) :
    ∀ (edges : List Nat) (actualTerm canonicalTerm : EdgeLabelling → Q'),
      InjectiveOnList f edges →
      (∀ canonical actual,
        LabelsAgreeOnRename f edges canonical actual →
          actualTerm actual ≈ canonicalTerm canonical) →
      listQSum actualTerm (boundedEdgeLabellings K (edges.map f)) ≈
        listQSum canonicalTerm (boundedEdgeLabellings K edges)
  | [], actualTerm, canonicalTerm, _, hterm => by
      change actualTerm zeroEdgeLabelling + 0 ≈
        canonicalTerm zeroEdgeLabelling + 0
      exact Q'.add_eqv_congr'
        (hterm zeroEdgeLabelling zeroEdgeLabelling
          (zeroLabelsAgree f []))
        (Q'.eqv_refl 0)
  | edge :: rest, actualTerm, canonicalTerm, hinj, hterm => by
      refine Q'.eqv_trans _
        (fsum (fun spin =>
          listQSum
            (fun actual => actualTerm
              (setEdgeLabel actual (f edge) spin))
            (boundedEdgeLabellings K (rest.map f))) (K + 1)) _
        (listQSum_bounded_cons K (f edge) (rest.map f) actualTerm) ?_
      refine Q'.eqv_trans _
        (fsum (fun spin =>
          listQSum
            (fun canonical => canonicalTerm
              (setEdgeLabel canonical edge spin))
            (boundedEdgeLabellings K rest)) (K + 1)) _ ?_
        (Q'.eqv_symm
          (listQSum_bounded_cons K edge rest canonicalTerm))
      apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      intro spin
      apply listQSum_bounded_rename K f rest
        (fun actual => actualTerm
          (setEdgeLabel actual (f edge) spin))
        (fun canonical => canonicalTerm
          (setEdgeLabel canonical edge spin))
      · exact injectiveOnList_tail f edge rest hinj
      · intro canonical actual hagree
        exact hterm
          (setEdgeLabel canonical edge spin)
          (setEdgeLabel actual (f edge) spin)
          (labelsAgree_setEdgeLabel f edge spin rest canonical actual
            hinj hagree)

/-! ## 2. Pointwise graph invariance -/

/-- Every numerical coordinate of every vertex occurs in the graph edge
list. -/
def VerticesCoveredBy (edges : List Nat) (vertices : List TrivalentVertex) :
    Prop :=
  ∀ v, v ∈ vertices → ∀ edge, VertexContains edge v → edge ∈ edges

/-- All exact trivalent fusion guards are invariant under a covered
identifier renaming. -/
theorem verticesAdmissibleB_rename (f : Nat → Nat)
    (edges : List Nat) : ∀ (vertices : List TrivalentVertex)
    (canonical actual : EdgeLabelling),
    VerticesCoveredBy edges vertices →
    LabelsAgreeOnRename f edges canonical actual →
    verticesAdmissibleB (vertices.map (mapTrivalentVertex f)) actual =
      verticesAdmissibleB vertices canonical
  | [], _, _, _, _ => rfl
  | v :: rest, canonical, actual, hcover, hagree => by
      have hfirst : actual (f v.1) = canonical v.1 :=
        hagree v.1 (hcover v List.mem_cons_self v.1 (Or.inl rfl))
      have hsecond : actual (f v.2.1) = canonical v.2.1 :=
        hagree v.2.1
          (hcover v List.mem_cons_self v.2.1
            (Or.inr (Or.inl rfl)))
      have hthird : actual (f v.2.2) = canonical v.2.2 :=
        hagree v.2.2
          (hcover v List.mem_cons_self v.2.2
            (Or.inr (Or.inr rfl)))
      have hrestCover : VerticesCoveredBy edges rest := by
        intro w hw edge hedge
        exact hcover w (List.mem_cons_of_mem v hw) edge hedge
      have ih := verticesAdmissibleB_rename f edges rest canonical actual
        hrestCover hagree
      simp only [List.map_cons, verticesAdmissibleB, mapTrivalentVertex]
      rw [hfirst, hsecond, hthird]
      by_cases hfusion :
          fusionOK (canonical v.1) (canonical v.2.1)
            (canonical v.2.2) = true
      · rw [if_pos hfusion, if_pos hfusion]
        exact ih
      · rw [if_neg hfusion, if_neg hfusion]

private theorem eliminateLinks_packet_rename {K : Nat} (f : Nat → Nat) :
    ∀ (edges : List Nat)
      (canonicalPacket actualPacket : Nat → CharacterPacket K)
      (canonical actual : EdgeLabelling),
      (∀ edge, edge ∈ edges →
        actualPacket (f edge) = canonicalPacket edge) →
      LabelsAgreeOnRename f edges canonical actual →
      eliminateLinks
          (fun edge => coeffAt (actualPacket edge) (actual edge))
          (edges.map f) =
        eliminateLinks
          (fun edge => coeffAt (canonicalPacket edge) (canonical edge))
          edges
  | [], _, _, _, _, _, _ => rfl
  | edge :: rest, canonicalPacket, actualPacket, canonical, actual,
      hpacket, hagree => by
      simp only [List.map_cons, eliminateLinks]
      rw [hpacket edge List.mem_cons_self,
        hagree edge List.mem_cons_self]
      apply congrArg (fun q =>
        coeffAt (canonicalPacket edge) (canonical edge) * q)
      exact eliminateLinks_packet_rename f rest canonicalPacket actualPacket
        canonical actual
        (fun e he => hpacket e (List.mem_cons_of_mem edge he))
        (fun e he => hagree e (List.mem_cons_of_mem edge he))

/-- The packet product over a renamed edge list is literally the same exact
rational as the canonical packet product. -/
theorem packetGraphBareAmplitude_rename_eq {K : Nat}
    (f : Nat → Nat) (edges : List Nat)
    (canonicalPacket actualPacket : Nat → CharacterPacket K)
    (canonical actual : EdgeLabelling)
    (hpacket : ∀ edge, edge ∈ edges →
      actualPacket (f edge) = canonicalPacket edge)
    (hagree : LabelsAgreeOnRename f edges canonical actual) :
    packetGraphBareAmplitude (edges.map f) actualPacket actual =
      packetGraphBareAmplitude edges canonicalPacket canonical := by
  unfold packetGraphBareAmplitude
  exact eliminateLinks_packet_rename f edges canonicalPacket actualPacket
    canonical actual hpacket hagree

/-- The complete vertex-only graph integrand is invariant under a covered
identifier renaming. -/
theorem graphVertexProject_rename_eq {K : Nat}
    (f : Nat → Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (canonicalPacket actualPacket : Nat → CharacterPacket K)
    (canonical actual : EdgeLabelling)
    (hcover : VerticesCoveredBy edges vertices)
    (hpacket : ∀ edge, edge ∈ edges →
      actualPacket (f edge) = canonicalPacket edge)
    (hagree : LabelsAgreeOnRename f edges canonical actual) :
    graphVertexProject (vertices.map (mapTrivalentVertex f))
        (packetGraphBareAmplitude (edges.map f) actualPacket) actual =
      graphVertexProject vertices
        (packetGraphBareAmplitude edges canonicalPacket) canonical := by
  unfold graphVertexProject
  rw [verticesAdmissibleB_rename f edges vertices canonical actual
      hcover hagree,
    packetGraphBareAmplitude_rename_eq f edges canonicalPacket actualPacket
      canonical actual hpacket hagree]

/-! ## 3. The complete vertex-Cartesian transport theorem -/

/-- **Graph identifier transport through every finite Cartesian sum.** -/
theorem vertexCartesianSum_rename {K : Nat}
    (f : Nat → Nat) (edges : List Nat) (vertices : List TrivalentVertex)
    (canonicalPacket actualPacket : Nat → CharacterPacket K)
    (hinj : InjectiveOnList f edges)
    (hcover : VerticesCoveredBy edges vertices)
    (hpacket : ∀ edge, edge ∈ edges →
      actualPacket (f edge) = canonicalPacket edge) :
    listQSum
        (graphVertexProject (vertices.map (mapTrivalentVertex f))
          (packetGraphBareAmplitude (edges.map f) actualPacket))
        (boundedEdgeLabellings K (edges.map f)) ≈
      listQSum
        (graphVertexProject vertices
          (packetGraphBareAmplitude edges canonicalPacket))
        (boundedEdgeLabellings K edges) := by
  apply listQSum_bounded_rename K f edges
  · exact hinj
  · intro canonical actual hagree
    exact Q'.eqv_of_eq
      (graphVertexProject_rename_eq f edges vertices
        canonicalPacket actualPacket canonical actual
        hcover hpacket hagree)

end YMGap.Continuum.Z4GraphIdentifierCartesianTransport

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4GraphIdentifierCartesianTransport.labelsAgree_setEdgeLabel
#print axioms YMGap.Continuum.Z4GraphIdentifierCartesianTransport.injectiveOnList_of_map_nodup
#print axioms YMGap.Continuum.Z4GraphIdentifierCartesianTransport.listQSum_bounded_rename
#print axioms YMGap.Continuum.Z4GraphIdentifierCartesianTransport.verticesAdmissibleB_rename
#print axioms YMGap.Continuum.Z4GraphIdentifierCartesianTransport.packetGraphBareAmplitude_rename_eq
#print axioms YMGap.Continuum.Z4GraphIdentifierCartesianTransport.graphVertexProject_rename_eq
#print axioms YMGap.Continuum.Z4GraphIdentifierCartesianTransport.vertexCartesianSum_rename
