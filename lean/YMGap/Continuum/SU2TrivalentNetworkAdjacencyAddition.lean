/-
# Additivity of slot-forgotten SU(2) network adjacency

The canonical resolution of one admissible trivalent vertex is additive, so
its Boolean leg adjacency is the union of the two summand adjacencies.  This
module forgets strand slots but retains graph-edge identifiers, then folds the
local relation through an ordered trivalent network.

The result is the graph-level algebra needed by the paired-face decoder:
componentwise addition of two accepted label fields takes the union of their
resolved local edge-adjacency relations.  This is intentionally weaker than
equality of the dependent strand-copy lists, whose slot indices can change
under addition, and exactly preserves the connectivity datum used by a
component switch.

No statement about the complete slab face graph, the component-switch
decoder, posterior column capacity, or a spectral gap is made here.

Constructive contract: finite Boolean folds and explicit admissibility
proofs only; no `Classical`, choice, `native_decide`, `sorry`, new axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.ResolvedTrivalentNetworkPorts
import YMGap.Continuum.SU2TrivalentStrandResolutionAddition

namespace YMGap.Continuum.SU2TrivalentNetworkAdjacencyAddition

set_option autoImplicit false

open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.SU2TrivalentStrandResolutionAddition

/-! ## 1. Finite Boolean existential unions -/

private theorem listAny_or {A : Type} (items : List A)
    (left right : A → Bool) :
    items.any (fun item => left item || right item) =
      (items.any left || items.any right) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.any_cons]
      rw [ih]
      cases left head <;> cases right head <;>
        cases tail.any left <;> cases tail.any right <;> rfl

private theorem listAny_congr {A : Type} (left right : A → Bool) :
    ∀ (items : List A),
      (∀ item, item ∈ items → left item = right item) →
        items.any left = items.any right
  | [], _ => rfl
  | head :: tail, heq => by
      rw [List.any_cons, List.any_cons,
        heq head List.mem_cons_self]
      apply congrArg (fun value => right head || value)
      exact listAny_congr left right tail fun item hmem =>
        heq item (List.mem_cons_of_mem head hmem)

private theorem listAny₂_or {A B : Type} (outer : List A) (inner : List B)
    (left right : A → B → Bool) :
    outer.any (fun first =>
        inner.any (fun second => left first second || right first second)) =
      (outer.any (fun first => inner.any (left first)) ||
        outer.any (fun first => inner.any (right first))) := by
  induction outer with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.any_cons]
      rw [listAny_or inner (left head) (right head), ih]
      cases inner.any (left head) <;> cases inner.any (right head) <;>
        cases tail.any (fun first => inner.any (left first)) <;>
          cases tail.any (fun first => inner.any (right first)) <;> rfl

/-! ## 2. One vertex after forgetting strand slots -/

/-- The complete finite carrier of trivalent legs. -/
def trivalentLegs : List TrivalentLeg := [.a, .b, .c]

/-- One possible ordered leg witness for adjacency between two displayed
graph-edge identifiers. -/
def canonicalTrivalentLegEdgeAdjacentB
    (vertex : TrivalentVertex) (label : EdgeLabelling)
    (hadmissible :
      fusionOK (label vertex.1) (label vertex.2.1) (label vertex.2.2) = true)
    (leftEdge rightEdge : Nat) (leftLeg rightLeg : TrivalentLeg) : Bool :=
  decide (vertexEdgeId vertex leftLeg = leftEdge) &&
    decide (vertexEdgeId vertex rightLeg = rightEdge) &&
      canonicalTrivalentLegAdjacentB
        (label vertex.1) (label vertex.2.1) (label vertex.2.2)
        hadmissible leftLeg rightLeg

/-- A fixed ordered leg witness is present in a summed vertex exactly when
it is present in one of the two summands. -/
theorem canonicalTrivalentLegEdgeAdjacentB_add
    (vertex : TrivalentVertex) (left right : EdgeLabelling)
    (hleft :
      fusionOK (left vertex.1) (left vertex.2.1) (left vertex.2.2) = true)
    (hright :
      fusionOK (right vertex.1) (right vertex.2.1) (right vertex.2.2) = true)
    (leftEdge rightEdge : Nat) (leftLeg rightLeg : TrivalentLeg) :
    canonicalTrivalentLegEdgeAdjacentB vertex
        (addEdgeLabelling left right) (fusionOK_add hleft hright)
        leftEdge rightEdge leftLeg rightLeg =
      (canonicalTrivalentLegEdgeAdjacentB vertex left hleft
          leftEdge rightEdge leftLeg rightLeg ||
        canonicalTrivalentLegEdgeAdjacentB vertex right hright
          leftEdge rightEdge leftLeg rightLeg) := by
  unfold canonicalTrivalentLegEdgeAdjacentB addEdgeLabelling
  rw [canonicalTrivalentLegAdjacentB_add hleft hright]
  cases decide (vertexEdgeId vertex leftLeg = leftEdge) <;>
    cases decide (vertexEdgeId vertex rightLeg = rightEdge) <;> rfl

/-- Slot-forgotten local adjacency on the graph-edge identifiers incident at
one resolved trivalent vertex. -/
def canonicalTrivalentVertexEdgeAdjacentB
    (vertex : TrivalentVertex) (label : EdgeLabelling)
    (hadmissible :
      fusionOK (label vertex.1) (label vertex.2.1) (label vertex.2.2) = true)
    (leftEdge rightEdge : Nat) : Bool :=
  trivalentLegs.any fun leftLeg =>
    trivalentLegs.any fun rightLeg =>
      canonicalTrivalentLegEdgeAdjacentB vertex label hadmissible
        leftEdge rightEdge leftLeg rightLeg

/-- Componentwise label addition takes the union of the complete local
edge-adjacency relations at one fixed trivalent vertex. -/
theorem canonicalTrivalentVertexEdgeAdjacentB_add
    (vertex : TrivalentVertex) (left right : EdgeLabelling)
    (hleft :
      fusionOK (left vertex.1) (left vertex.2.1) (left vertex.2.2) = true)
    (hright :
      fusionOK (right vertex.1) (right vertex.2.1) (right vertex.2.2) = true)
    (leftEdge rightEdge : Nat) :
    canonicalTrivalentVertexEdgeAdjacentB vertex
        (addEdgeLabelling left right) (fusionOK_add hleft hright)
        leftEdge rightEdge =
      (canonicalTrivalentVertexEdgeAdjacentB vertex left hleft
          leftEdge rightEdge ||
        canonicalTrivalentVertexEdgeAdjacentB vertex right hright
          leftEdge rightEdge) := by
  unfold canonicalTrivalentVertexEdgeAdjacentB
  rw [listAny_congr
    (fun leftLeg => trivalentLegs.any fun rightLeg =>
      canonicalTrivalentLegEdgeAdjacentB vertex
        (addEdgeLabelling left right) (fusionOK_add hleft hright)
        leftEdge rightEdge leftLeg rightLeg)
    (fun leftLeg => trivalentLegs.any fun rightLeg =>
      canonicalTrivalentLegEdgeAdjacentB vertex left hleft
          leftEdge rightEdge leftLeg rightLeg ||
        canonicalTrivalentLegEdgeAdjacentB vertex right hright
          leftEdge rightEdge leftLeg rightLeg)
    trivalentLegs (by
      intro leftLeg _
      exact listAny_congr
        (fun rightLeg =>
          canonicalTrivalentLegEdgeAdjacentB vertex
            (addEdgeLabelling left right) (fusionOK_add hleft hright)
            leftEdge rightEdge leftLeg rightLeg)
        (fun rightLeg =>
          canonicalTrivalentLegEdgeAdjacentB vertex left hleft
              leftEdge rightEdge leftLeg rightLeg ||
            canonicalTrivalentLegEdgeAdjacentB vertex right hright
              leftEdge rightEdge leftLeg rightLeg)
        trivalentLegs (by
          intro rightLeg _
          exact canonicalTrivalentLegEdgeAdjacentB_add
            vertex left right hleft hright leftEdge rightEdge
            leftLeg rightLeg))]
  exact listAny₂_or trivalentLegs trivalentLegs
    (fun leftLeg rightLeg =>
      canonicalTrivalentLegEdgeAdjacentB vertex left hleft
        leftEdge rightEdge leftLeg rightLeg)
    (fun leftLeg rightLeg =>
      canonicalTrivalentLegEdgeAdjacentB vertex right hright
        leftEdge rightEdge leftLeg rightLeg)

/-! ## 3. Ordered finite trivalent networks -/

/-- Boolean adjacency generated by every canonical local strand bundle in an
ordered admissible trivalent network.  Auxiliary and physical graph-edge
identifiers remain visible, while strand-copy slots are forgotten. -/
def canonicalTrivalentNetworkEdgeAdjacentB (label : EdgeLabelling) :
    (vertices : List TrivalentVertex) →
      verticesAdmissibleB vertices label = true → Nat → Nat → Bool
  | [], _, _, _ => false
  | vertex :: rest, hadmissible, leftEdge, rightEdge =>
      let parts :=
        (verticesAdmissibleB_cons_true_iff vertex rest label).mp hadmissible
      canonicalTrivalentVertexEdgeAdjacentB vertex label parts.1
          leftEdge rightEdge ||
        canonicalTrivalentNetworkEdgeAdjacentB label rest parts.2
          leftEdge rightEdge

/-- **Ordered-network union law.**  On one fixed trivalent graph, the
slot-forgotten resolved adjacency of the summed admissible label field is the
pointwise Boolean union of the two input adjacencies. -/
theorem canonicalTrivalentNetworkEdgeAdjacentB_add
    (vertices : List TrivalentVertex) (left right : EdgeLabelling)
    (hleft : verticesAdmissibleB vertices left = true)
    (hright : verticesAdmissibleB vertices right = true)
    (leftEdge rightEdge : Nat) :
    canonicalTrivalentNetworkEdgeAdjacentB
        (addEdgeLabelling left right) vertices
        (verticesAdmissibleB_add vertices left right hleft hright)
        leftEdge rightEdge =
      (canonicalTrivalentNetworkEdgeAdjacentB left vertices hleft
          leftEdge rightEdge ||
        canonicalTrivalentNetworkEdgeAdjacentB right vertices hright
          leftEdge rightEdge) := by
  revert hleft hright
  induction vertices with
  | nil =>
      intro _ _
      rfl
  | cons vertex rest ih =>
      intro hleft hright
      let leftParts :=
        (verticesAdmissibleB_cons_true_iff vertex rest left).mp hleft
      let rightParts :=
        (verticesAdmissibleB_cons_true_iff vertex rest right).mp hright
      simp only [canonicalTrivalentNetworkEdgeAdjacentB]
      rw [canonicalTrivalentVertexEdgeAdjacentB_add
          vertex left right leftParts.1 rightParts.1 leftEdge rightEdge,
        ih leftParts.2 rightParts.2]
      cases canonicalTrivalentVertexEdgeAdjacentB vertex left leftParts.1
          leftEdge rightEdge <;>
        cases canonicalTrivalentVertexEdgeAdjacentB vertex right rightParts.1
          leftEdge rightEdge <;>
        cases canonicalTrivalentNetworkEdgeAdjacentB left rest leftParts.2
          leftEdge rightEdge <;>
        cases canonicalTrivalentNetworkEdgeAdjacentB right rest rightParts.2
          leftEdge rightEdge <;> rfl

end YMGap.Continuum.SU2TrivalentNetworkAdjacencyAddition

#print axioms YMGap.Continuum.SU2TrivalentNetworkAdjacencyAddition.canonicalTrivalentLegEdgeAdjacentB_add
#print axioms YMGap.Continuum.SU2TrivalentNetworkAdjacencyAddition.canonicalTrivalentVertexEdgeAdjacentB_add
#print axioms YMGap.Continuum.SU2TrivalentNetworkAdjacencyAddition.canonicalTrivalentNetworkEdgeAdjacentB_add
