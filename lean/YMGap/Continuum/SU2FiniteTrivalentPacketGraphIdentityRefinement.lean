/-
# A trivalent identity refinement of one graph edge

A fresh trivalent vertex with a vacuum third leg imposes the exact SU(2)
identity channel: `fusionOK a b 0` forces the two remaining labels to agree.
This file constructs the resulting refined labelling and proves that its
physical projector is exactly the original graph projector.  The refined
graph eigenvalue is also computed: it is the old eigenvalue times one extra
copy of the subdivided edge eigenvalue.

This is a genuinely interacting local refinement (the new equality is
enforced by a fusion guard), but it is not yet the complete finite-sum
elimination theorem or a thermodynamic limit.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder

namespace YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement

set_option maxHeartbeats 800000
set_option maxRecDepth 14000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

local infix:50 " ≈ " => Q'.eqv

/-- A vertex list avoids an edge identifier when none of its three slots
uses that identifier. -/
def VerticesAvoid (edge : Nat) (vertices : List TrivalentVertex) : Prop :=
  ∀ v, v ∈ vertices →
    edge ≠ v.1 ∧ edge ≠ v.2.1 ∧ edge ≠ v.2.2

/-- Insert a new segment and a vacuum leg.  The new segment copies the label
of the old segment; the vacuum leg is fixed to zero. -/
def identityRefinedLabel (oldEdge newEdge vacuumEdge : Nat)
    (label : EdgeLabelling) : EdgeLabelling :=
  setEdgeLabel
    (setEdgeLabel label newEdge (label oldEdge)) vacuumEdge 0

def identityRefinedVertex (oldEdge newEdge vacuumEdge : Nat) :
    TrivalentVertex :=
  (oldEdge, (newEdge, vacuumEdge))

def identityRefinedEdges (newEdge vacuumEdge : Nat)
    (edges : List Nat) : List Nat :=
  vacuumEdge :: newEdge :: edges

def identityRefinedVertices (oldEdge newEdge vacuumEdge : Nat)
    (vertices : List TrivalentVertex) : List TrivalentVertex :=
  identityRefinedVertex oldEdge newEdge vacuumEdge :: vertices

theorem identityRefinedLabel_old (oldEdge newEdge vacuumEdge : Nat)
    (label : EdgeLabelling) (hno : newEdge ≠ oldEdge)
    (hvo : vacuumEdge ≠ oldEdge) :
    identityRefinedLabel oldEdge newEdge vacuumEdge label oldEdge =
      label oldEdge := by
  have hon : oldEdge ≠ newEdge := Ne.symm hno
  have hov : oldEdge ≠ vacuumEdge := Ne.symm hvo
  simp [identityRefinedLabel, setEdgeLabel, hon, hov]

theorem identityRefinedLabel_new (oldEdge newEdge vacuumEdge : Nat)
    (label : EdgeLabelling) (hnv : newEdge ≠ vacuumEdge) :
    identityRefinedLabel oldEdge newEdge vacuumEdge label newEdge =
      label oldEdge := by
  simp [identityRefinedLabel, setEdgeLabel, hnv]

theorem identityRefinedLabel_vacuum (oldEdge newEdge vacuumEdge : Nat)
    (label : EdgeLabelling) :
    identityRefinedLabel oldEdge newEdge vacuumEdge label vacuumEdge = 0 := by
  simp [identityRefinedLabel, setEdgeLabel]

private theorem hasExcitedB_congr_on
    (a b : EdgeLabelling) : ∀ edges,
    (∀ edge, edge ∈ edges → a edge = b edge) →
      hasExcitedB a edges = hasExcitedB b edges
  | [], _ => rfl
  | edge :: rest, h => by
      have hedge := h edge List.mem_cons_self
      have hrest : ∀ e, e ∈ rest → a e = b e :=
        fun e he => h e (List.mem_cons_of_mem edge he)
      simp only [hasExcitedB]
      rw [hedge, hasExcitedB_congr_on a b rest hrest]

private theorem hasExcitedB_true_of_mem
    (label : EdgeLabelling) {edge : Nat} : ∀ edges,
    edge ∈ edges → 1 ≤ label edge → hasExcitedB label edges = true
  | [], hmem, _ => by cases hmem
  | head :: rest, hmem, hexc => by
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hrest
      · simp [hasExcitedB, hexc]
      · by_cases hh : 1 ≤ label head
        · simp [hasExcitedB, hh]
        · simp [hasExcitedB, hh,
            hasExcitedB_true_of_mem label rest hrest hexc]

private theorem verticesAdmissibleB_congr_on
    (a b : EdgeLabelling) : ∀ vertices,
    (∀ v, v ∈ vertices →
      a v.1 = b v.1 ∧ a v.2.1 = b v.2.1 ∧ a v.2.2 = b v.2.2) →
      verticesAdmissibleB vertices a = verticesAdmissibleB vertices b
  | [], _ => rfl
  | v :: rest, h => by
      have hv := h v List.mem_cons_self
      have hrest : ∀ w, w ∈ rest →
          a w.1 = b w.1 ∧ a w.2.1 = b w.2.1 ∧
            a w.2.2 = b w.2.2 :=
        fun w hw => h w (List.mem_cons_of_mem v hw)
      simp only [verticesAdmissibleB]
      rw [hv.1, hv.2.1, hv.2.2,
        verticesAdmissibleB_congr_on a b rest hrest]

theorem identityRefinedLabel_eq_on_old_edges
    (oldEdge newEdge vacuumEdge : Nat) (label : EdgeLabelling)
    {edges : List Nat}
    (hnew : newEdge ∉ edges) (hvac : vacuumEdge ∉ edges) :
    ∀ edge, edge ∈ edges →
      identityRefinedLabel oldEdge newEdge vacuumEdge label edge = label edge := by
  intro edge hmem
  have hen : edge ≠ newEdge := by
    intro h
    subst edge
    exact hnew hmem
  have hev : edge ≠ vacuumEdge := by
    intro h
    subst edge
    exact hvac hmem
  simp [identityRefinedLabel, setEdgeLabel, hen, hev]

private theorem identityRefinedLabel_eq_on_old_vertices
    (oldEdge newEdge vacuumEdge : Nat) (label : EdgeLabelling)
    {vertices : List TrivalentVertex}
    (hnew : VerticesAvoid newEdge vertices)
    (hvac : VerticesAvoid vacuumEdge vertices) :
    ∀ v, v ∈ vertices →
      identityRefinedLabel oldEdge newEdge vacuumEdge label v.1 = label v.1 ∧
      identityRefinedLabel oldEdge newEdge vacuumEdge label v.2.1 = label v.2.1 ∧
      identityRefinedLabel oldEdge newEdge vacuumEdge label v.2.2 = label v.2.2 := by
  intro v hmem
  have hn := hnew v hmem
  have hv := hvac v hmem
  constructor
  · simp [identityRefinedLabel, setEdgeLabel, Ne.symm hn.1, Ne.symm hv.1]
  constructor
  · simp [identityRefinedLabel, setEdgeLabel,
      Ne.symm hn.2.1, Ne.symm hv.2.1]
  · simp [identityRefinedLabel, setEdgeLabel,
      Ne.symm hn.2.2, Ne.symm hv.2.2]

private theorem eliminateLinks_eq_on
    (f g : Nat → Q') : ∀ edges,
    (∀ edge, edge ∈ edges → f edge = g edge) →
      eliminateLinks f edges = eliminateLinks g edges
  | [], _ => rfl
  | edge :: rest, h => by
      have hedge := h edge List.mem_cons_self
      have hrest : ∀ e, e ∈ rest → f e = g e :=
        fun e he => h e (List.mem_cons_of_mem edge he)
      simp only [eliminateLinks]
      rw [hedge, eliminateLinks_eq_on f g rest hrest]

/-- The fresh identity vertex is admissible because its vacuum-output fusion
guard is exactly diagonal. -/
theorem identityRefinedVertex_admissible
    (oldEdge newEdge vacuumEdge : Nat) (label : EdgeLabelling)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge) :
    fusionOK
      (identityRefinedLabel oldEdge newEdge vacuumEdge label oldEdge)
      (identityRefinedLabel oldEdge newEdge vacuumEdge label newEdge)
      (identityRefinedLabel oldEdge newEdge vacuumEdge label vacuumEdge) =
        true := by
  rw [identityRefinedLabel_old oldEdge newEdge vacuumEdge label hno hvo,
    identityRefinedLabel_new oldEdge newEdge vacuumEdge label hnv,
    identityRefinedLabel_vacuum]
  exact YMGap.Continuum.FusionQuotientCollapse.fusionOK_zero_diag_self
    (label oldEdge)

/-- The refined label is physical precisely when the original label is.
The proof uses the nontrivial fusion guard at the new vertex, not a
disconnected tensor factor. -/
theorem graphPhysicalB_identity_refinement
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (vertices : List TrivalentVertex) (label : EdgeLabelling)
    (hold : oldEdge ∈ edges) (hnew : newEdge ∉ edges)
    (hvac : vacuumEdge ∉ edges)
    (hno : newEdge ≠ oldEdge) (hvo : vacuumEdge ≠ oldEdge)
    (hnv : newEdge ≠ vacuumEdge)
    (hnewV : VerticesAvoid newEdge vertices)
    (hvacV : VerticesAvoid vacuumEdge vertices) :
    graphPhysicalB (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedVertices oldEdge newEdge vacuumEdge vertices)
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) =
      graphPhysicalB edges vertices label := by
  let refined := identityRefinedLabel oldEdge newEdge vacuumEdge label
  have holdCoord : refined oldEdge = label oldEdge :=
    identityRefinedLabel_old oldEdge newEdge vacuumEdge label hno hvo
  have hnewCoord : refined newEdge = label oldEdge :=
    identityRefinedLabel_new oldEdge newEdge vacuumEdge label hnv
  have hvacCoord : refined vacuumEdge = 0 :=
    identityRefinedLabel_vacuum oldEdge newEdge vacuumEdge label
  have hedgeCongr : hasExcitedB refined edges = hasExcitedB label edges :=
    hasExcitedB_congr_on refined label edges
      (identityRefinedLabel_eq_on_old_edges
        oldEdge newEdge vacuumEdge label hnew hvac)
  have hvertexCongr : verticesAdmissibleB vertices refined =
      verticesAdmissibleB vertices label :=
    verticesAdmissibleB_congr_on refined label vertices
      (identityRefinedLabel_eq_on_old_vertices
        oldEdge newEdge vacuumEdge label hnewV hvacV)
  have hnewVertex : fusionOK (refined oldEdge) (refined newEdge)
      (refined vacuumEdge) = true :=
    identityRefinedVertex_admissible oldEdge newEdge vacuumEdge label
      hno hvo hnv
  change
    ((if 1 ≤ refined vacuumEdge then true
      else if 1 ≤ refined newEdge then true else hasExcitedB refined edges) &&
      (if fusionOK (refined oldEdge) (refined newEdge)
          (refined vacuumEdge) = true then
        verticesAdmissibleB vertices refined else false)) =
      (hasExcitedB label edges && verticesAdmissibleB vertices label)
  have hvacNot : ¬ 1 ≤ refined vacuumEdge := by omega
  rw [if_neg hvacNot, hnewVertex, hnewCoord]
  by_cases hexc : 1 ≤ label oldEdge
  · rw [if_pos hexc,
      hasExcitedB_true_of_mem label edges hold hexc,
      hvertexCongr]
    simp
  · rw [if_neg hexc, hedgeCongr, hvertexCongr]
    simp

/-- The identity refinement inserts exactly one additional copy of the old
edge transfer eigenvalue.  This is the exact local time/coupling rescaling
that a later continuum refinement must account for. -/
theorem graphEigen_identity_refinement
    (oldEdge newEdge vacuumEdge : Nat) (edges : List Nat)
    (label : EdgeLabelling) (hnew : newEdge ∉ edges)
    (hvac : vacuumEdge ∉ edges)
    (hnv : newEdge ≠ vacuumEdge) :
    graphEigen (identityRefinedEdges newEdge vacuumEdge edges)
        (identityRefinedLabel oldEdge newEdge vacuumEdge label) ≈
      eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge) *
        graphEigen edges label := by
  let refined := identityRefinedLabel oldEdge newEdge vacuumEdge label
  have hvacCoord : refined vacuumEdge = 0 :=
    identityRefinedLabel_vacuum oldEdge newEdge vacuumEdge label
  have hnewCoord : refined newEdge = label oldEdge :=
    identityRefinedLabel_new oldEdge newEdge vacuumEdge label hnv
  have hrest : eliminateLinks
      (fun e => eigA SU2PeterWeylWilsonBlock.coupling (refined e)) edges =
      eliminateLinks
        (fun e => eigA SU2PeterWeylWilsonBlock.coupling (label e)) edges := by
    apply eliminateLinks_eq_on
    intro edge hmem
    change eigA SU2PeterWeylWilsonBlock.coupling
        (identityRefinedLabel oldEdge newEdge vacuumEdge label edge) =
      eigA SU2PeterWeylWilsonBlock.coupling (label edge)
    rw [identityRefinedLabel_eq_on_old_edges
      oldEdge newEdge vacuumEdge label hnew hvac edge hmem]
  unfold graphEigen identityRefinedEdges
  change eigA SU2PeterWeylWilsonBlock.coupling (refined vacuumEdge) *
      (eigA SU2PeterWeylWilsonBlock.coupling (refined newEdge) *
        eliminateLinks
          (fun e => eigA SU2PeterWeylWilsonBlock.coupling (refined e)) edges) ≈
    eigA SU2PeterWeylWilsonBlock.coupling (label oldEdge) *
      eliminateLinks
        (fun e => eigA SU2PeterWeylWilsonBlock.coupling (label e)) edges
  rw [hvacCoord, eigA_zero, hnewCoord, hrest]
  exact Q'.one_mul_eqv _

end YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement

#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement.identityRefinedVertex_admissible
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement.identityRefinedLabel_eq_on_old_edges
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement.graphPhysicalB_identity_refinement
#print axioms YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinement.graphEigen_identity_refinement
