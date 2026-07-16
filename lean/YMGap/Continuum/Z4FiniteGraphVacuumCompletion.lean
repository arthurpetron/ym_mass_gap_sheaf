/-
# Exact vacuum completion of finite trivalent graph sums

The finite-graph spectral projector deliberately removes the globally
all-zero edge labelling.  A Haar character integral, by contrast, includes
that normalized vacuum contribution.  This module proves the exact bridge
between the two conventions before any local fusion-chain Fubini rewrite is
attempted.

For a duplicate-free finite edge list, the cutoff-zero slice of the complete
Cartesian enumeration is exactly the singleton zero labelling.  Moreover the
zero labelling satisfies every trivalent vertex guard.  Consequently the
complete vertex-admissible Cartesian sum is the graph gauge/vacuum-projected
sum plus the bare amplitude at the zero labelling.  The latter is derived
from the supplied packets; it is not stipulated to be one.

Honest scope: this fixes the exact vacuum normalization interface for every
finite trivalent packet graph.  It does not yet identify the remaining
vertex-admissible Cartesian sum with the canonical sequential fusion fold.
-/

import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
import YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar

namespace YMGap.Continuum.Z4FiniteGraphVacuumCompletion

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Boolean zero-labelling characterizations -/

/-- Failure of the nonvacuum guard says exactly that every listed edge has
label zero. -/
theorem hasExcitedB_false_iff_zero_on (label : EdgeLabelling) : ∀ edges,
    hasExcitedB label edges = false ↔
      ∀ edge, edge ∈ edges → label edge = 0
  | [] => by simp [hasExcitedB]
  | head :: rest => by
      by_cases hhead : 1 ≤ label head
      · have hne : label head ≠ 0 := by omega
        simp [hasExcitedB, hhead, hne]
      · have hzero : label head = 0 := by omega
        simp [hasExcitedB, hzero,
          hasExcitedB_false_iff_zero_on label rest]

/-- Every trivalent guard accepts the all-vacuum representation labels. -/
theorem verticesAdmissibleB_zero : ∀ vertices : List TrivalentVertex,
    verticesAdmissibleB vertices zeroEdgeLabelling = true
  | [] => rfl
  | _ :: rest => by
      simp only [verticesAdmissibleB, zeroEdgeLabelling]
      rw [if_pos]
      · exact verticesAdmissibleB_zero rest
      · decide

/-- Inside the complete bounded Cartesian support, the cutoff-zero predicate
selects precisely the global zero labelling. -/
theorem enumerated_labelWithinB_zero_iff {K : Nat} {edges : List Nat}
    {label : EdgeLabelling}
    (hmem : label ∈ boundedEdgeLabellings K edges) :
    labelWithinB 0 edges label = true ↔ label = zeroEdgeLabelling := by
  have hsound := boundedEdgeLabellings_sound K edges label hmem
  constructor
  · intro hwithin
    have hbound := (labelWithinB_true_iff 0 edges label).1 hwithin
    funext edge
    by_cases hedge : edge ∈ edges
    · have := hbound edge hedge
      change label edge = zeroEdgeLabelling edge
      simp only [zeroEdgeLabelling]
      omega
    · change label edge = zeroEdgeLabelling edge
      simp only [zeroEdgeLabelling]
      exact hsound.2 edge hedge
  · intro hlabel
    subst label
    apply (labelWithinB_true_iff 0 edges zeroEdgeLabelling).2
    intro edge _
    simp [zeroEdgeLabelling]

theorem boundedEdgeLabellings_zero : ∀ edges : List Nat,
    boundedEdgeLabellings 0 edges = [zeroEdgeLabelling]
  | [] => rfl
  | edge :: rest => by
      rw [boundedEdgeLabellings, boundedEdgeLabellings_zero rest]
      change [setEdgeLabel zeroEdgeLabelling edge 0] = [zeroEdgeLabelling]
      congr 1
      funext e
      simp [setEdgeLabel, zeroEdgeLabelling]

/-! ## 2. Vertex-only and vacuum-completed amplitudes -/

/-- The local gauge projector before the global nonvacuum condition is
imposed. -/
def graphVertexProject (vertices : List TrivalentVertex) (f : GraphPacket) :
    GraphPacket :=
  fun label => if verticesAdmissibleB vertices label = true then f label else 0

/-- Pointwise decomposition on every enumerated labelling: the vertex-only
projector is the nonvacuum graph projector plus a term supported exactly on
the zero-labelling slice. -/
theorem graphVertexProject_eq_projected_add_zeroSlice
    {K : Nat} {edges : List Nat} {vertices : List TrivalentVertex}
    (f : GraphPacket) {label : EdgeLabelling}
    (hmem : label ∈ boundedEdgeLabellings K edges) :
    graphVertexProject vertices f label ≈
      graphGaugeVacuumProject edges vertices f label +
        (if labelWithinB 0 edges label then f zeroEdgeLabelling else 0) := by
  have hzeroIff := enumerated_labelWithinB_zero_iff hmem
  by_cases hvertex : verticesAdmissibleB vertices label = true
  · by_cases hexcited : hasExcitedB label edges = true
    · have hphysical : GraphPhysical edges vertices label := by
        unfold GraphPhysical graphPhysicalB
        rw [hexcited, hvertex]
        rfl
      have hnotzero : label ≠ zeroEdgeLabelling := by
        intro hlabel
        subst label
        have hzfalse : hasExcitedB zeroEdgeLabelling edges = false :=
          (hasExcitedB_false_iff_zero_on zeroEdgeLabelling edges).2 (by
            intro edge _
            rfl)
        simp [hzfalse] at hexcited
      have hwithin : labelWithinB 0 edges label = false := by
        cases h : labelWithinB 0 edges label with
        | false => rfl
        | true => exact False.elim (hnotzero (hzeroIff.mp h))
      unfold graphVertexProject graphGaugeVacuumProject
      rw [if_pos hvertex, if_pos hphysical, hwithin]
      exact Q'.eqv_symm (q_add_zero_eqv _)
    · have hexcitedFalse : hasExcitedB label edges = false := by
        cases h : hasExcitedB label edges with
        | false => rfl
        | true => exact False.elim (hexcited h)
      have hzeroOn :=
        (hasExcitedB_false_iff_zero_on label edges).1 hexcitedFalse
      have hsound := boundedEdgeLabellings_sound K edges label hmem
      have hlabel : label = zeroEdgeLabelling := by
        funext edge
        by_cases hedge : edge ∈ edges
        · change label edge = zeroEdgeLabelling edge
          simp only [zeroEdgeLabelling]
          exact hzeroOn edge hedge
        · change label edge = zeroEdgeLabelling edge
          simp only [zeroEdgeLabelling]
          exact hsound.2 edge hedge
      have hnotphysical : ¬ GraphPhysical edges vertices label := by
        unfold GraphPhysical graphPhysicalB
        rw [hexcitedFalse]
        simp
      have hwithin : labelWithinB 0 edges label = true := hzeroIff.mpr hlabel
      unfold graphVertexProject graphGaugeVacuumProject
      rw [if_pos hvertex, if_neg hnotphysical, hwithin, hlabel]
      simp only [if_true]
      exact Q'.eqv_symm (q_zero_add_eqv _)
  · have hnotphysical : ¬ GraphPhysical edges vertices label := by
      intro hphysical
      unfold GraphPhysical graphPhysicalB at hphysical
      cases hexcited : hasExcitedB label edges <;>
        simp [hexcited, hvertex] at hphysical
    have hwithin : labelWithinB 0 edges label = false := by
      cases h : labelWithinB 0 edges label with
      | false => rfl
      | true =>
          have hlabel := hzeroIff.mp h
          have hz := verticesAdmissibleB_zero vertices
          subst label
          exact False.elim (hvertex hz)
    unfold graphVertexProject graphGaugeVacuumProject
    rw [if_neg hvertex, if_neg hnotphysical, hwithin]
    exact Q'.eqv_symm (q_zero_add_eqv 0)

/-! ## 3. Exact finite-sum vacuum completion -/

private theorem listQSum_add {A : Type} (f g : A → Q') : ∀ xs : List A,
    listQSum (fun x => f x + g x) xs ≈
      listQSum f xs + listQSum g xs
  | [] => Q'.eqv_symm (q_zero_add_eqv 0)
  | x :: xs => by
      change (f x + g x) + listQSum (fun y => f y + g y) xs ≈
        (f x + listQSum f xs) + (g x + listQSum g xs)
      refine Q'.eqv_trans _
        ((f x + g x) + (listQSum f xs + listQSum g xs)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (listQSum_add f g xs)) ?_
      exact Q'.eqv_trans _
        (f x + (g x + (listQSum f xs + listQSum g xs))) _
        (Q'.add_assoc_eqv _ _ _) (by
          refine Q'.eqv_trans _
            (f x + ((g x + listQSum f xs) + listQSum g xs)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))) ?_
          refine Q'.eqv_trans _
            (f x + ((listQSum f xs + g x) + listQSum g xs)) _
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (Q'.add_eqv_congr' (Q'.add_comm_eqv _ _)
                (Q'.eqv_refl _))) ?_
          exact Q'.eqv_trans _
            (f x + (listQSum f xs + (g x + listQSum g xs))) _
            (Q'.add_eqv_congr' (Q'.eqv_refl _)
              (Q'.add_assoc_eqv _ _ _))
            (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)))

private theorem listQSum_congr_mem {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h => by
      exact Q'.add_eqv_congr'
        (h x List.mem_cons_self)
        (listQSum_congr_mem xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem zeroSlice_sum {K : Nat} (edges : List Nat)
    (hnodup : edges.Nodup) (vacuum : Q') :
    listQSum
        (fun label => if labelWithinB 0 edges label then vacuum else 0)
        (boundedEdgeLabellings K edges) ≈ vacuum := by
  have hfilter := boundedEdgeLabellings_filter_cutoff
    (K := 0) (L := K) (Nat.zero_le K) edges hnodup
  have hsum := listQSum_filter (fun _ : EdgeLabelling => vacuum)
    (labelWithinB 0 edges) (boundedEdgeLabellings K edges)
  refine Q'.eqv_trans _
    (listQSum (fun _ : EdgeLabelling => vacuum)
      ((boundedEdgeLabellings K edges).filter (labelWithinB 0 edges))) _
    (Q'.eqv_symm hsum) ?_
  rw [hfilter, boundedEdgeLabellings_zero]
  change vacuum + 0 ≈ vacuum
  exact q_add_zero_eqv _

/-- **Exact vacuum-completion identity.**  On a duplicate-free finite edge
enumeration, imposing only the trivalent vertex guards is precisely the
nonvacuum graph projection plus the derived bare zero-labelling amplitude. -/
theorem vertexCartesianSum_eq_vacuum_add_projected
    {K : Nat} (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) (f : GraphPacket) :
    listQSum (graphVertexProject vertices f)
        (boundedEdgeLabellings K edges) ≈
      f zeroEdgeLabelling +
        listQSum (graphGaugeVacuumProject edges vertices f)
          (boundedEdgeLabellings K edges) := by
  let support := boundedEdgeLabellings K edges
  let projected := graphGaugeVacuumProject edges vertices f
  let zeroSlice : EdgeLabelling → Q' := fun label =>
    if labelWithinB 0 edges label then f zeroEdgeLabelling else 0
  have hpoint : listQSum (graphVertexProject vertices f) support ≈
      listQSum (fun label => projected label + zeroSlice label) support :=
    listQSum_congr_mem support
      (fun label hlabel =>
        graphVertexProject_eq_projected_add_zeroSlice f hlabel)
  refine Q'.eqv_trans _ _ _ hpoint ?_
  refine Q'.eqv_trans _
    (listQSum projected support + listQSum zeroSlice support) _
    (listQSum_add projected zeroSlice support) ?_
  have hz : listQSum zeroSlice support ≈ f zeroEdgeLabelling := by
    exact zeroSlice_sum edges hnodup (f zeroEdgeLabelling)
  exact Q'.eqv_trans _
    (listQSum projected support + f zeroEdgeLabelling) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) hz)
    (Q'.add_comm_eqv _ _)

end YMGap.Continuum.Z4FiniteGraphVacuumCompletion

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FiniteGraphVacuumCompletion.hasExcitedB_false_iff_zero_on
#print axioms YMGap.Continuum.Z4FiniteGraphVacuumCompletion.verticesAdmissibleB_zero
#print axioms YMGap.Continuum.Z4FiniteGraphVacuumCompletion.enumerated_labelWithinB_zero_iff
#print axioms YMGap.Continuum.Z4FiniteGraphVacuumCompletion.boundedEdgeLabellings_zero
#print axioms YMGap.Continuum.Z4FiniteGraphVacuumCompletion.graphVertexProject_eq_projected_add_zeroSlice
#print axioms YMGap.Continuum.Z4FiniteGraphVacuumCompletion.vertexCartesianSum_eq_vacuum_add_projected
