/-
# Coherent simultaneous strand removal on a resolved trivalent network

The local SU(2) fusion rule becomes linear in strand coordinates.  This
module packages the exact global compatibility condition needed to use that
fact on a finite resolved network: every trivalent vertex chooses bounded
removal counts `(ab,bc,ca)`, while one common edge-drop labelling agrees with
the sum of the two incident removal counts on each of its three legs.

Structural induction then proves that subtracting the common edge drops
preserves every trivalent fusion constraint simultaneously.  The result is
specialized to the complete canonical one-link guard, including its forced
vacuum terminator.  Thus a coherent strand-removal plan constructs an actual
accepted lower auxiliary labelling; no local fusion condition is re-assumed.

Honest scope: this module consumes a coherent removal plan.  Constructing
that plan from a global corrected-slab strand component, and bounding inverse
component records, remain open.

Constructive contract: finite inductive data, `Nat` subtraction, and Boolean
list recursion only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.ResolvedTrivalentNetworkPorts

namespace YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPeeling
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. One common edge-drop labelling -/

/-- Subtract a natural edge-drop labelling pointwise. -/
def lowerEdgeLabellingBy
    (label drop : EdgeLabelling) : EdgeLabelling :=
  fun edge => label edge - drop edge

/-- Pointwise lowering commutes exactly with the physical/auxiliary overlay. -/
theorem overlayOn_lowerEdgeLabellingBy
    (edges : List Nat) (outer inner drop : EdgeLabelling) :
    overlayOn edges
        (lowerEdgeLabellingBy outer drop)
        (lowerEdgeLabellingBy inner drop) =
      lowerEdgeLabellingBy (overlayOn edges outer inner) drop := by
  funext edge
  by_cases hmem : edge ∈ edges <;>
    simp [overlayOn, lowerEdgeLabellingBy, hmem]

/-! ## 2. Coherent vertexwise strand subtraction -/

/-- A simultaneous removal plan aligned with an ordered resolved network.
At each vertex the common edge drop equals the number of removed strands
incident on that leg. -/
inductive ResolvedTrivalentRemovalPlan
    (label drop : EdgeLabelling) :
    List (ResolvedTrivalentVertex label) -> Type
  | nil : ResolvedTrivalentRemovalPlan label drop []
  | cons
      (head : ResolvedTrivalentVertex label)
      (tail : List (ResolvedTrivalentVertex label))
      (removal : TrivalentStrandRemoval head.strands)
      (a_drop : drop head.vertex.1 = removal.ca + removal.ab)
      (b_drop : drop head.vertex.2.1 = removal.bc + removal.ab)
      (c_drop : drop head.vertex.2.2 = removal.bc + removal.ca)
      (rest : ResolvedTrivalentRemovalPlan label drop tail) :
      ResolvedTrivalentRemovalPlan label drop (head :: tail)

/-- **Network fusion preservation.**  A coherent removal plan proves every
target trivalent constraint after the common edge subtraction. -/
theorem ResolvedTrivalentRemovalPlan.vertices_admissible
    {label drop : EdgeLabelling} :
    forall {resolved : List (ResolvedTrivalentVertex label)},
      ResolvedTrivalentRemovalPlan label drop resolved ->
        verticesAdmissibleB
          (resolved.map (fun item => item.vertex))
          (lowerEdgeLabellingBy label drop) = true
  | [], .nil => rfl
  | head :: tail,
      .cons _ _ removal a_drop b_drop c_drop rest => by
      apply (verticesAdmissibleB_cons_true_iff
        head.vertex (tail.map (fun item => item.vertex))
        (lowerEdgeLabellingBy label drop)).mpr
      constructor
      · change fusionOK
          (label head.vertex.1 - drop head.vertex.1)
          (label head.vertex.2.1 - drop head.vertex.2.1)
          (label head.vertex.2.2 - drop head.vertex.2.2) = true
        rw [a_drop, b_drop, c_drop,
          <- removal.nextLabels_a,
          <- removal.nextLabels_b,
          <- removal.nextLabels_c]
        exact removal.next_admissible
      · exact rest.vertices_admissible

/-- A data-bearing coherent removal on a resolved network. -/
structure CoherentResolvedTrivalentRemoval
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label) : Type where
  drop : EdgeLabelling
  plan : ResolvedTrivalentRemovalPlan label drop network.resolved

/-- The common target edge labelling. -/
def CoherentResolvedTrivalentRemoval.target
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (removal : CoherentResolvedTrivalentRemoval network) : EdgeLabelling :=
  lowerEdgeLabellingBy label removal.drop

/-- A coherent resolved-network removal preserves the complete original
ordered vertex guard. -/
theorem CoherentResolvedTrivalentRemoval.vertices_admissible
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (removal : CoherentResolvedTrivalentRemoval network) :
    verticesAdmissibleB vertices removal.target = true := by
  have hresolved := removal.plan.vertices_admissible
  rw [network.vertices_exact] at hresolved
  exact hresolved

/-! ## 3. The complete canonical one-link guard -/

/-- A coherent strand-removal plan on the accepted canonical one-link
network. -/
abbrev CanonicalLinkStrandRemovalPlan
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (drop : EdgeLabelling) :=
  ResolvedTrivalentRemovalPlan
    (canonicalLinkLabelling degree external auxiliary) drop
    (canonicalLinkResolvedStrandNetwork
      degree external auxiliary hallowed).resolved

/-- Pointwise subtraction preserves support in a bounded Cartesian edge
window. -/
theorem lowerEdgeLabellingBy_mem_bounded
    {cutoff : Nat} (edges : List Nat)
    {label drop : EdgeLabelling}
    (hlabel : label ∈ boundedEdgeLabellings cutoff edges) :
    lowerEdgeLabellingBy label drop ∈
      boundedEdgeLabellings cutoff edges := by
  have hsound := boundedEdgeLabellings_sound cutoff edges label hlabel
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    unfold lowerEdgeLabellingBy
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hsound.1 edge hedge)
  · intro edge hedge
    unfold lowerEdgeLabellingBy
    rw [hsound.2 edge hedge]
    exact Nat.zero_sub _

/-- **Accepted one-link fusion preservation.**  Any coherent removal plan
constructs a true complete canonical link guard for the lowered external and
auxiliary labellings, including the forced-zero terminator condition. -/
theorem canonicalLinkConditionalAllowedB_lower_of_plan
    {degree : Nat} {external auxiliary drop : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (plan : CanonicalLinkStrandRemovalPlan hallowed drop) :
    canonicalLinkConditionalAllowedB degree
        (lowerEdgeLabellingBy external drop)
        (lowerEdgeLabellingBy auxiliary drop) = true := by
  let sourceNetwork := canonicalLinkResolvedStrandNetwork
    degree external auxiliary hallowed
  let coherent : CoherentResolvedTrivalentRemoval sourceNetwork :=
    { drop := drop, plan := plan }
  have hsourceParts :
      verticesAdmissibleB
          (canonicalLinkVertices degree)
          (canonicalLinkLabelling degree external auxiliary) = true ∧
        (canonicalUsedAuxiliaryCoordinates degree).all
          (canonicalAuxiliaryEdgeAllowedB degree
            (canonicalLinkLabelling degree external auxiliary)) = true := by
    simpa only [canonicalLinkConditionalAllowedB, Bool.and_eq_true,
      canonicalLinkVertices, canonicalLinkLabelling] using hallowed
  unfold canonicalLinkConditionalAllowedB
  rw [Bool.and_eq_true]
  constructor
  · change verticesAdmissibleB
      (canonicalLinkVertices degree)
      (canonicalLinkLabelling degree
        (lowerEdgeLabellingBy external drop)
        (lowerEdgeLabellingBy auxiliary drop)) = true
    unfold canonicalLinkLabelling
    rw [overlayOn_lowerEdgeLabellingBy]
    exact coherent.vertices_admissible
  · apply List.all_eq_true.mpr
    intro edge hedge
    have hsourceEdge :=
      List.all_eq_true.mp hsourceParts.2 edge hedge
    unfold canonicalAuxiliaryEdgeAllowedB at hsourceEdge ⊢
    by_cases heq : edge = degree
    · rw [if_pos heq] at hsourceEdge ⊢
      simp only [decide_eq_true_eq] at hsourceEdge ⊢
      unfold canonicalLinkLabelling at hsourceEdge
      rw [overlayOn_lowerEdgeLabellingBy]
      unfold lowerEdgeLabellingBy
      rw [hsourceEdge]
      exact Nat.zero_sub _
    · rw [if_neg heq] at hsourceEdge ⊢

/-! ## 4. Literal corrected-slab accepted witnesses -/

/-- A coherent removal plan on one literal accepted corrected-slab link
witness. -/
abbrev SlabLinkStrandRemovalPlan
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link)
    (drop : EdgeLabelling) :=
  CanonicalLinkStrandRemovalPlan
    (slabLinkFusionWitness_mem_allowed
      cutoff extent physical link auxiliary hmem) drop

/-- **Literal accepted-witness update.**  If the target physical labelling
realizes the planned drops on this link's canonical external coordinates,
then pointwise subtraction of the same drops from the source auxiliary
labelling is an actual member of the target corrected-slab fusion-witness
list. -/
theorem slabLinkFusionWitness_lower_mem_of_plan
    {cutoff extent : Nat}
    {sourcePhysical targetPhysical : SlabLabelling} {link : SlabLink}
    {sourceAuxiliary drop : SlabLabelling}
    (hmem : sourceAuxiliary ∈
      slabLinkFusionWitnesses cutoff extent sourcePhysical link)
    (hexternal :
      slabLinkExternalSpins extent targetPhysical link =
        lowerEdgeLabellingBy
          (slabLinkExternalSpins extent sourcePhysical link) drop)
    (plan : SlabLinkStrandRemovalPlan hmem drop) :
    lowerEdgeLabellingBy sourceAuxiliary drop ∈
      slabLinkFusionWitnesses cutoff extent targetPhysical link := by
  have hsourceParts := List.mem_filter.mp hmem
  unfold slabLinkFusionWitnesses
  apply List.mem_filter.mpr
  constructor
  · exact lowerEdgeLabellingBy_mem_bounded
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length)
      hsourceParts.1
  · dsimp only
    rw [hexternal]
    exact canonicalLinkConditionalAllowedB_lower_of_plan
      (slabLinkFusionWitness_mem_allowed
        cutoff extent sourcePhysical link sourceAuxiliary hmem)
      plan

#print axioms lowerEdgeLabellingBy
#print axioms overlayOn_lowerEdgeLabellingBy
#print axioms ResolvedTrivalentRemovalPlan
#print axioms ResolvedTrivalentRemovalPlan.vertices_admissible
#print axioms CoherentResolvedTrivalentRemoval
#print axioms CoherentResolvedTrivalentRemoval.target
#print axioms CoherentResolvedTrivalentRemoval.vertices_admissible
#print axioms CanonicalLinkStrandRemovalPlan
#print axioms lowerEdgeLabellingBy_mem_bounded
#print axioms canonicalLinkConditionalAllowedB_lower_of_plan
#print axioms SlabLinkStrandRemovalPlan
#print axioms slabLinkFusionWitness_lower_mem_of_plan

end YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
