/-
# Conditional auxiliary-channel elimination for the finite Z4 graph

The exact one-link Haar calculations cannot be multiplied after all local
coordinates have been summed: physical plaquette labels are shared by the
links on their boundaries, and the heat-kernel coefficient of a physical
face occurs only once in the global packet product.

This module starts the correct finite-Fubini assembly.  It first factors the
global trivalent admissibility guard over concatenated vertex blocks and over
the `flatMap` presentation of `resolutionVertices`.  It also factors packet
products over concatenated edge lists.  These identities are deliberately
pointwise in one fixed global edge labelling; no shared physical coordinate
is resummed and no independence assumption is introduced.

Honest scope: this is the structural conditional-elimination layer.  The
next layer fixes the physical plaquette labelling, sums only the private
auxiliary coordinates in each enumerated link block, and identifies the
result with the corresponding exact SU(2) invariant multiplicity.
-/

import YMGap.Continuum.Z4ActualLinkUsedPacketBridge

namespace YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

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
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact factorization of the vertex guard -/

/-- Trivalent admissibility on a concatenation is exactly Boolean
conjunction.  This is stronger than the earlier one-way `true` lemma and is
the pointwise algebra needed to eliminate link-local auxiliary channels
while a global plaquette labelling remains fixed. -/
theorem verticesAdmissibleB_append (label : EdgeLabelling) :
    ∀ xs ys : List TrivalentVertex,
      verticesAdmissibleB (xs ++ ys) label =
        (verticesAdmissibleB xs label && verticesAdmissibleB ys label)
  | [], ys => by simp [verticesAdmissibleB]
  | x :: xs, ys => by
      simp only [List.cons_append, verticesAdmissibleB]
      cases hguard :
          fusionOK (label x.1) (label x.2.1) (label x.2.2) with
      | false => simp
      | true =>
          simp only [if_true]
          exact verticesAdmissibleB_append label xs ys

/-- The complete guard on a flattened family is exactly the `List.all` of
the guards of its blocks.  Applied to the enumerated links, this is the
finite-volume gauge constraint with the shared physical labelling held
fixed. -/
theorem verticesAdmissibleB_flatMap {A : Type}
    (label : EdgeLabelling) (f : A → List TrivalentVertex) :
    ∀ xs : List A,
      verticesAdmissibleB (xs.flatMap f) label =
        xs.all (fun x => verticesAdmissibleB (f x) label)
  | [] => by simp [verticesAdmissibleB]
  | x :: xs => by
      simp only [List.flatMap_cons, List.all_cons]
      rw [verticesAdmissibleB_append,
        verticesAdmissibleB_flatMap label f xs]

/-- The production graph's global fusion guard is literally the conjunction
of the local resolver guards, evaluated at one and the same edge labelling.
In particular, physical plaquette coordinates remain shared. -/
theorem resolutionVertices_admissible_factor (n : Nat)
    (label : EdgeLabelling) :
    verticesAdmissibleB (resolutionVertices n) label =
      (enumerate (distinctBoxLinks n)).all fun indexed =>
        verticesAdmissibleB
          (linkResolutionVertices n indexed.1 indexed.2) label := by
  unfold resolutionVertices
  exact verticesAdmissibleB_flatMap label
    (fun indexed => linkResolutionVertices n indexed.1 indexed.2)
    (enumerate (distinctBoxLinks n))

/-! ## 2. Pointwise factorization of packet products and projectors -/

/-- Exact packet products split over concatenated edge lists. -/
theorem eliminateLinks_append (value : Nat → Q') : ∀ xs ys : List Nat,
    eliminateLinks value (xs ++ ys) ≈
      eliminateLinks value xs * eliminateLinks value ys
  | [], ys => Q'.eqv_symm (Q'.one_mul_eqv _)
  | x :: xs, ys => by
      simp only [List.cons_append, eliminateLinks]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_append value xs ys))
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))

/-- The bare character-packet amplitude contains each edge coefficient once;
splitting its edge order therefore yields one physical factor and one
auxiliary factor without duplicating either. -/
theorem packetGraphBareAmplitude_append {K : Nat}
    (xs ys : List Nat) (packet : Nat → CharacterPacket K)
    (label : EdgeLabelling) :
    packetGraphBareAmplitude (xs ++ ys) packet label ≈
      packetGraphBareAmplitude xs packet label *
        packetGraphBareAmplitude ys packet label := by
  unfold packetGraphBareAmplitude
  exact eliminateLinks_append
    (fun edge => coeffAt (packet edge) (label edge)) xs ys

/-- A concatenated vertex projector can be staged: first test the left block,
then apply the right-block projector.  This identity is pointwise and keeps
the amplitude itself unsplit. -/
theorem graphVertexProject_append (xs ys : List TrivalentVertex)
    (f : GraphPacket) (label : EdgeLabelling) :
    graphVertexProject (xs ++ ys) f label =
      if verticesAdmissibleB xs label = true then
        graphVertexProject ys f label
      else 0 := by
  unfold graphVertexProject
  rw [verticesAdmissibleB_append]
  cases hx : verticesAdmissibleB xs label <;>
    cases hy : verticesAdmissibleB ys label <;>
    simp

/-! ## 3. Constructive finite Fubini with shared coordinates fixed -/

/-- Overlay the coordinates in `outerEdges` from `outer` onto a background
labelling `inner`.  This is a constructive finite update: membership in a
list of natural-number identifiers is decidable. -/
def overlayOn (outerEdges : List Nat) (outer inner : EdgeLabelling) :
    EdgeLabelling :=
  fun edge => if edge ∈ outerEdges then outer edge else inner edge

theorem overlayOn_nil (outer inner : EdgeLabelling) :
    overlayOn [] outer inner = inner := by
  funext edge
  rfl

/-- Adding the head coordinate to an overlay is exactly one `setEdgeLabel`
over the tail overlay.  No disjointness premise is needed: the head update
has precedence on both sides. -/
theorem overlayOn_cons_setEdgeLabel (edge spin : Nat)
    (rest : List Nat) (outer inner : EdgeLabelling) :
    overlayOn (edge :: rest) (setEdgeLabel outer edge spin) inner =
      setEdgeLabel (overlayOn rest outer inner) edge spin := by
  funext coordinate
  by_cases hcoordinate : coordinate = edge
  · subst coordinate
    simp [overlayOn, setEdgeLabel]
  · by_cases hrest : coordinate ∈ rest <;>
      simp [overlayOn, setEdgeLabel, hcoordinate, hrest]

/-- **Finite Cartesian Fubini, with an explicit overlay.**  Labellings on a
prefix and suffix may be summed separately, and `overlayOn` reconstructs the
single global labelling seen by the integrand.  This is the exact operation
needed to hold all physical plaquette labels fixed while auxiliary channels
are summed. -/
theorem listQSum_bounded_append_fubini (K : Nat) :
    ∀ (outerEdges innerEdges : List Nat)
      (f : EdgeLabelling → Q'),
      listQSum f
          (boundedEdgeLabellings K (outerEdges ++ innerEdges)) ≈
        listQSum
          (fun outer =>
            listQSum
              (fun inner => f (overlayOn outerEdges outer inner))
              (boundedEdgeLabellings K innerEdges))
          (boundedEdgeLabellings K outerEdges)
  | [], innerEdges, f => by
      simp only [List.nil_append, boundedEdgeLabellings, listQSum,
        overlayOn_nil]
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))
  | edge :: rest, innerEdges, f => by
      let outerTerm : EdgeLabelling → Q' := fun outer =>
        listQSum
          (fun inner => f (overlayOn (edge :: rest) outer inner))
          (boundedEdgeLabellings K innerEdges)
      refine Q'.eqv_trans _
        (fsum (fun spin =>
          listQSum
            (fun label => f (setEdgeLabel label edge spin))
            (boundedEdgeLabellings K (rest ++ innerEdges))) (K + 1)) _
        (listQSum_bounded_cons K edge (rest ++ innerEdges) f) ?_
      refine Q'.eqv_trans _
        (fsum (fun spin =>
          listQSum
            (fun outer =>
              listQSum
                (fun inner =>
                  f (setEdgeLabel (overlayOn rest outer inner) edge spin))
                (boundedEdgeLabellings K innerEdges))
            (boundedEdgeLabellings K rest)) (K + 1)) _ ?_ ?_
      · apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
        intro spin
        exact listQSum_bounded_append_fubini K rest innerEdges
          (fun label => f (setEdgeLabel label edge spin))
      · refine Q'.eqv_trans _
          (fsum (fun spin =>
            listQSum
              (fun outer => outerTerm
                (setEdgeLabel outer edge spin))
              (boundedEdgeLabellings K rest)) (K + 1)) _ ?_
          (Q'.eqv_symm
            (listQSum_bounded_cons K edge rest outerTerm))
        apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
        intro spin
        apply listQSum_congr
        intro outer
        dsimp [outerTerm]
        apply listQSum_congr
        intro inner
        rw [overlayOn_cons_setEdgeLabel]
        exact Q'.eqv_refl _

/-! ## 4. The production physical/auxiliary split -/

/-- A packet product depends only on the labels carried by its displayed
edge list. -/
theorem packetGraphBareAmplitude_label_eq_on {K : Nat}
    (packet : Nat → CharacterPacket K) :
    ∀ (edges : List Nat) (left right : EdgeLabelling),
      (∀ edge, edge ∈ edges → left edge = right edge) →
      packetGraphBareAmplitude edges packet left =
        packetGraphBareAmplitude edges packet right
  | [], left, right, _ => rfl
  | edge :: rest, left, right, hagree => by
      unfold packetGraphBareAmplitude
      simp only [eliminateLinks]
      rw [hagree edge List.mem_cons_self]
      apply congrArg
        (fun q => coeffAt (packet edge) (right edge) * q)
      change packetGraphBareAmplitude rest packet left =
        packetGraphBareAmplitude rest packet right
      exact packetGraphBareAmplitude_label_eq_on packet rest left right
        (fun e he => hagree e (List.mem_cons_of_mem edge he))

theorem overlayOn_apply_of_mem {edge : Nat} {edges : List Nat}
    {outer inner : EdgeLabelling} (hedge : edge ∈ edges) :
    overlayOn edges outer inner edge = outer edge := by
  simp [overlayOn, hedge]

/-- The projected production integrand on the fusion-complete box graph. -/
def fusionCompleteBoxVertexIntegrand (K n : Nat) : GraphPacket :=
  graphVertexProject (resolutionVertices n)
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (gaugeHeatKernelBoxPacketsFusionComplete K n))

/-- The full production Cartesian graph sum, before removal of the global
all-vacuum mode, at the fusion-complete cutoff. -/
def fusionCompleteBoxVertexCartesianSum (K n : Nat) : Q' :=
  listQSum
    (fusionCompleteBoxVertexIntegrand K n)
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (usedResolutionEdges n))

/-- Conditional auxiliary-channel sum at one fixed physical plaquette
labelling.  Only the deduplicated auxiliary identifiers are enumerated; the
physical coefficients remain outside this definition. -/
def conditionalBoxAuxiliarySum (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  listQSum
    (fun auxiliary =>
      graphVertexProject (resolutionVertices n)
        (packetGraphBareAmplitude (usedAuxiliaryEdges n)
          (gaugeHeatKernelBoxPacketsFusionComplete K n))
        (overlayOn (List.range (plaquetteEdgeCount n))
          physical auxiliary))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (usedAuxiliaryEdges n))

/-- At a fixed physical labelling, the unique physical face-coefficient
product can be pulled in front of the conditional auxiliary sum. -/
def physicalBoxPacketFactor (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  packetGraphBareAmplitude (List.range (plaquetteEdgeCount n))
    (gaugeHeatKernelBoxPacketsFusionComplete K n) physical

/-- Overlaying auxiliary labels cannot change the physical face factor. -/
theorem physicalBoxPacketFactor_overlay (K n : Nat)
    (physical auxiliary : EdgeLabelling) :
    packetGraphBareAmplitude (List.range (plaquetteEdgeCount n))
        (gaugeHeatKernelBoxPacketsFusionComplete K n)
        (overlayOn (List.range (plaquetteEdgeCount n))
          physical auxiliary) =
      physicalBoxPacketFactor K n physical := by
  unfold physicalBoxPacketFactor
  apply packetGraphBareAmplitude_label_eq_on
  intro edge hedge
  exact overlayOn_apply_of_mem hedge

/-- **Pointwise conditional factorization.**  For one fixed physical
labelling and one auxiliary labelling, the production integrand is the one
global physical face product times the auxiliary packet product under the
same global fusion guard.  Hence no face coefficient is duplicated. -/
theorem fusionCompleteBoxVertexIntegrand_overlay_factor
    (K n : Nat) (physical auxiliary : EdgeLabelling) :
    fusionCompleteBoxVertexIntegrand K n
        (overlayOn (List.range (plaquetteEdgeCount n))
          physical auxiliary) ≈
      physicalBoxPacketFactor K n physical *
        graphVertexProject (resolutionVertices n)
          (packetGraphBareAmplitude (usedAuxiliaryEdges n)
            (gaugeHeatKernelBoxPacketsFusionComplete K n))
          (overlayOn (List.range (plaquetteEdgeCount n))
            physical auxiliary) := by
  let label := overlayOn (List.range (plaquetteEdgeCount n))
    physical auxiliary
  let packet := gaugeHeatKernelBoxPacketsFusionComplete K n
  have hsplit :
      packetGraphBareAmplitude (usedResolutionEdges n) packet label ≈
        packetGraphBareAmplitude (List.range (plaquetteEdgeCount n))
            packet label *
          packetGraphBareAmplitude (usedAuxiliaryEdges n) packet label := by
    simpa only [usedResolutionEdges] using
      (packetGraphBareAmplitude_append
        (List.range (plaquetteEdgeCount n)) (usedAuxiliaryEdges n)
        packet label)
  have hphysical :
      packetGraphBareAmplitude (List.range (plaquetteEdgeCount n))
          packet label = physicalBoxPacketFactor K n physical := by
    dsimp [packet, label]
    exact physicalBoxPacketFactor_overlay K n physical auxiliary
  by_cases hadmissible :
      verticesAdmissibleB (resolutionVertices n) label = true
  · unfold fusionCompleteBoxVertexIntegrand graphVertexProject
    dsimp only [label] at hadmissible ⊢
    rw [if_pos hadmissible, if_pos hadmissible]
    dsimp only [packet] at hsplit hphysical ⊢
    rw [hphysical] at hsplit
    exact hsplit
  · unfold fusionCompleteBoxVertexIntegrand graphVertexProject
    dsimp only [label] at hadmissible ⊢
    rw [if_neg hadmissible, if_neg hadmissible]
    exact Q'.eqv_symm (Q'.mul_zero_eqv _)

/-! ## 5. Exact conditional finite-volume formula -/

/-- A constant factor pulls through a structural finite list sum. -/
theorem listQSum_const_mul {A : Type} (constant : Q') (f : A → Q') :
    ∀ xs : List A,
      listQSum (fun x => constant * f x) xs ≈
        constant * listQSum f xs
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | x :: xs => by
      simp only [listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_const_mul constant f xs))
        (Q'.eqv_symm (Q'.mul_add_eqv constant (f x)
          (listQSum f xs)))

/-- The auxiliary sum at fixed physical labels factors out the unique
physical face coefficient product. -/
theorem conditionalBoxInnerSum_factor (K n : Nat)
    (physical : EdgeLabelling) :
    listQSum
        (fun auxiliary =>
          fusionCompleteBoxVertexIntegrand K n
            (overlayOn (List.range (plaquetteEdgeCount n))
              physical auxiliary))
        (boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (usedAuxiliaryEdges n)) ≈
      physicalBoxPacketFactor K n physical *
        conditionalBoxAuxiliarySum K n physical := by
  refine Q'.eqv_trans _
    (listQSum
      (fun auxiliary =>
        physicalBoxPacketFactor K n physical *
          graphVertexProject (resolutionVertices n)
            (packetGraphBareAmplitude (usedAuxiliaryEdges n)
              (gaugeHeatKernelBoxPacketsFusionComplete K n))
            (overlayOn (List.range (plaquetteEdgeCount n))
              physical auxiliary))
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (usedAuxiliaryEdges n))) _ ?_ ?_
  · apply listQSum_congr
    intro auxiliary
    exact fusionCompleteBoxVertexIntegrand_overlay_factor
      K n physical auxiliary
  · unfold conditionalBoxAuxiliarySum
    exact listQSum_const_mul (physicalBoxPacketFactor K n physical)
      (fun auxiliary =>
        graphVertexProject (resolutionVertices n)
          (packetGraphBareAmplitude (usedAuxiliaryEdges n)
            (gaugeHeatKernelBoxPacketsFusionComplete K n))
          (overlayOn (List.range (plaquetteEdgeCount n))
            physical auxiliary))
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (usedAuxiliaryEdges n))

/-- **Production physical/auxiliary Fubini formula.**  The complete finite
box graph is one sum over physical plaquette labels.  Each summand contains
exactly one product of heat-kernel face coefficients and one conditional
sum over private auxiliary fusion channels. -/
theorem fusionCompleteBoxVertexCartesianSum_eq_conditional
    (K n : Nat) :
    fusionCompleteBoxVertexCartesianSum K n ≈
      listQSum
        (fun physical =>
          physicalBoxPacketFactor K n physical *
            conditionalBoxAuxiliarySum K n physical)
        (boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (List.range (plaquetteEdgeCount n))) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        listQSum
          (fun auxiliary =>
            fusionCompleteBoxVertexIntegrand K n
              (overlayOn (List.range (plaquetteEdgeCount n))
                physical auxiliary))
          (boundedEdgeLabellings (linkAuxiliaryCutoff K)
            (usedAuxiliaryEdges n)))
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (List.range (plaquetteEdgeCount n)))) _ ?_ ?_
  · unfold fusionCompleteBoxVertexCartesianSum
    simpa only [usedResolutionEdges] using
      (listQSum_bounded_append_fubini (linkAuxiliaryCutoff K)
        (List.range (plaquetteEdgeCount n)) (usedAuxiliaryEdges n)
        (fusionCompleteBoxVertexIntegrand K n))
  · apply listQSum_congr
    intro physical
    exact conditionalBoxInnerSum_factor K n physical

end YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.verticesAdmissibleB_append
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.verticesAdmissibleB_flatMap
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.resolutionVertices_admissible_factor
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.eliminateLinks_append
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.packetGraphBareAmplitude_append
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.graphVertexProject_append
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.overlayOn_cons_setEdgeLabel
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.listQSum_bounded_append_fubini
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.packetGraphBareAmplitude_label_eq_on
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.physicalBoxPacketFactor_overlay
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.fusionCompleteBoxVertexIntegrand_overlay_factor
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.conditionalBoxInnerSum_factor
#print axioms YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination.fusionCompleteBoxVertexCartesianSum_eq_conditional
