/-
# Exact cutoff-one support enumeration

At physical cutoff one, a bounded face labelling is exactly the indicator of a
unique sublist of the duplicate-free physical-face list.  This module proves
that statement at the level of the actual enumeration lists, not merely as an
existence theorem.  Consequently the canonical component-product partition can
be reindexed definitionally over the finite power set without a permutation or
multiplicity correction.
-/

import YMGap.Continuum.CayleyInjection
import YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

namespace YMGap.Continuum.Z4CutoffOneSupportBijection

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4ExplicitExcitationIncidenceBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ExplicitSupportFaceBound
open YMGap.Continuum.Z4LinkSeparatedFamilyFactorization
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels

local infix:50 " ≈ " => Q'.eqv

private theorem range_nodup_local (N : Nat) : (List.range N).Nodup := by
  induction N with
  | zero => exact List.nodup_nil
  | succ N ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyN : y = N := List.mem_singleton.mp hy
      rw [hxy, hyN] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl N)

theorem physicalFaceEdges_nodup (n : Nat) :
    (physicalFaceEdges n).Nodup := by
  unfold physicalFaceEdges
  exact range_nodup_local _

theorem setEdgeLabel_componentLabel_zero_of_not_mem
    {edge : Nat} {support : List Nat} (hnot : edge ∉ support) :
    setEdgeLabel (componentLabel support) edge 0 =
      componentLabel support := by
  funext queried
  by_cases heq : queried = edge
  · subst queried
    simp [setEdgeLabel, componentLabel, hnot]
  · simp [setEdgeLabel, heq]

theorem setEdgeLabel_componentLabel_one
    (edge : Nat) (support : List Nat) :
    setEdgeLabel (componentLabel support) edge 1 =
      componentLabel (edge :: support) := by
  funext queried
  by_cases heq : queried = edge
  · subst queried
    simp [setEdgeLabel, componentLabel]
  · simp [setEdgeLabel, componentLabel, heq]

private theorem head_not_mem_sublists
    {edge : Nat} {rest support : List Nat}
    (hfresh : edge ∉ rest) (hsupport : support ∈ sublists rest) :
    edge ∉ support := by
  intro hmem
  exact hfresh (mem_of_mem_sublists rest support hsupport edge hmem)

theorem boundedEdgeLabellings_one_eq_componentLabels :
    ∀ edges : List Nat, edges.Nodup →
      boundedEdgeLabellings 1 edges =
        (sublists edges).map componentLabel
  | [], _ => rfl
  | edge :: rest, hnodup => by
      have hfresh : edge ∉ rest := (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      rw [boundedEdgeLabellings, sublists_cons',
        boundedEdgeLabellings_one_eq_componentLabels rest hrestNodup]
      simp only [List.range_succ, List.range_zero, List.append_nil,
        List.map_append, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.map_map, List.append_assoc]
      have hzero :
          (sublists rest).map
              (fun support =>
                setEdgeLabel (componentLabel support) edge 0) =
            (sublists rest).map componentLabel := by
        apply List.map_congr_left
        intro support hsupport
        exact setEdgeLabel_componentLabel_zero_of_not_mem
          (head_not_mem_sublists hfresh hsupport)
      have hone :
          (sublists rest).map
              (fun support =>
                setEdgeLabel (componentLabel support) edge 1) =
            (sublists rest).map
              (fun support => componentLabel (edge :: support)) := by
        apply List.map_congr_left
        intro support _
        exact setEdgeLabel_componentLabel_one edge support
      simp only [List.nil_append]
      change
        (sublists rest).map
              (fun support =>
                setEdgeLabel (componentLabel support) edge 0) ++
            (sublists rest).map
              (fun support =>
                setEdgeLabel (componentLabel support) edge 1) =
          (sublists rest).map componentLabel ++
            (sublists rest).map
              (fun support => componentLabel (edge :: support))
      rw [hzero, hone]

def cutoffOneFaceSupports (n : Nat) : List (List Nat) :=
  sublists (physicalFaceEdges n)

theorem explicitPhysicalLabellings_one_eq_supportIndicators (n : Nat) :
    explicitPhysicalLabellings 1 n =
      (cutoffOneFaceSupports n).map componentLabel := by
  unfold explicitPhysicalLabellings cutoffOneFaceSupports
  exact boundedEdgeLabellings_one_eq_componentLabels
    (physicalFaceEdges n) (physicalFaceEdges_nodup n)

theorem cutoffOneFaceSupports_nodup (n : Nat) :
    (cutoffOneFaceSupports n).Nodup := by
  unfold cutoffOneFaceSupports
  exact sublists_nodup (physicalFaceEdges n) (physicalFaceEdges_nodup n)

theorem filter_mem_sublists {A : Type} (predicate : A → Bool) :
    ∀ xs : List A, xs.filter predicate ∈ sublists xs
  | [] => List.mem_cons_self
  | head :: tail => by
      rw [sublists_cons']
      cases hhead : predicate head with
      | false =>
          simp only [List.filter_cons, hhead, Bool.false_eq_true, if_false]
          exact List.mem_append_left _
            (filter_mem_sublists predicate tail)
      | true =>
          simp only [List.filter_cons, hhead, if_true]
          apply List.mem_append_right
          rw [List.mem_map]
          exact ⟨tail.filter predicate,
            filter_mem_sublists predicate tail, rfl⟩

theorem excitedPlaquetteIds_componentLabel_eq_support
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    excitedPlaquetteIds n (componentLabel support) = support := by
  have hsupport' : support ∈ sublists (physicalFaceEdges n) := hsupport
  apply sublists_eq_of_mem_iff
    (physicalFaceEdges n)
    (excitedPlaquetteIds n (componentLabel support)) support
    (physicalFaceEdges_nodup n)
  · unfold excitedPlaquetteIds
    exact filter_mem_sublists _ _
  · exact hsupport'
  · intro edge
    by_cases hedge : edge ∈ support
    · have hphysical : edge ∈ physicalFaceEdges n :=
        mem_of_mem_sublists (physicalFaceEdges n) support hsupport' edge hedge
      simp [excitedPlaquetteIds, componentLabel, hedge, hphysical]
    · simp [excitedPlaquetteIds, componentLabel, hedge]

theorem excitedPlaquetteEntries_componentLabel_length
    {n : Nat} {support : List Nat}
    (hsupport : support ∈ cutoffOneFaceSupports n) :
    (excitedPlaquetteEntries n (componentLabel support)).length =
      support.length := by
  rw [excitedPlaquetteEntries_length_eq_ids,
    excitedPlaquetteIds_componentLabel_eq_support hsupport]

private theorem listQSum_map_local {A B : Type}
    (f : B → Q') (g : A → B) : ∀ xs : List A,
    listQSum f (xs.map g) = listQSum (fun x => f (g x)) xs
  | [] => rfl
  | _ :: xs => congrArg (fun tail => f (g _) + tail)
      (listQSum_map_local f g xs)

def parametricCanonicalSupportGasPartition (w : Q') (n : Nat) : Q' :=
  listQSum
    (fun support =>
      parametricLocalizedWeightProduct w n
        (surfaceComponentLabels n (componentLabel support)))
    (cutoffOneFaceSupports n)

theorem parametricCanonicalComponentProductPartition_eq_supportGas
    (w : Q') (n : Nat) :
    parametricCanonicalComponentProductPartition w n =
      parametricCanonicalSupportGasPartition w n := by
  unfold parametricCanonicalComponentProductPartition
    parametricCanonicalSupportGasPartition
  rw [explicitPhysicalLabellings_one_eq_supportIndicators]
  exact listQSum_map_local _ _ _

theorem parametricLocalizedSpinFoamPartition_eq_supportGas
    (w : Q') (n : Nat) :
    parametricLocalizedSpinFoamPartition w n ≈
      parametricCanonicalSupportGasPartition w n := by
  exact Q'.eqv_trans _ _ _
    (parametricLocalizedSpinFoamPartition_eq_componentProduct w n)
    (Q'.eqv_of_eq
      (parametricCanonicalComponentProductPartition_eq_supportGas w n))

end YMGap.Continuum.Z4CutoffOneSupportBijection

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.physicalFaceEdges_nodup
#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.boundedEdgeLabellings_one_eq_componentLabels
#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.explicitPhysicalLabellings_one_eq_supportIndicators
#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.cutoffOneFaceSupports_nodup
#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.filter_mem_sublists
#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.excitedPlaquetteIds_componentLabel_eq_support
#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.excitedPlaquetteEntries_componentLabel_length
#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.parametricCanonicalComponentProductPartition_eq_supportGas
#print axioms YMGap.Continuum.Z4CutoffOneSupportBijection.parametricLocalizedSpinFoamPartition_eq_supportGas
