/-
# Exact vacuum/activity decomposition of the explicit spin-foam sum

The literal finite-box spin-foam formula has a distinguished all-zero
physical labelling.  This file proves, from the displayed fusion-path counts,
that its face factor and every link factor are exactly one.  It then partitions
the physical Cartesian sum into that unit vacuum term and the nonnegative sum
over labellings with at least one excited plaquette.

This is an algebraic interface for a subsequent connected/polymer expansion.
It does not assert volume-uniform smallness of the excited sum.
-/

import YMGap.Continuum.Z4ExplicitSpinFoamBounds
import YMGap.Continuum.Z4FiniteGraphVacuumCompletion

namespace YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. Every all-zero local path count is one -/

theorem oneValentMultiplicity_allZero (cutoff : Nat) :
    oneValentMultiplicity cutoff 0 = 1 := by
  rw [oneValentMultiplicity_cutoff_independent
    (bound := 0) (cutoff := cutoff) (a := 0) (Nat.zero_le cutoff)]
  rfl

theorem twoValentMultiplicity_allZero (cutoff : Nat) :
    twoValentMultiplicity cutoff 0 0 = 1 := by
  rw [twoValentMultiplicity_cutoff_independent
    (bound := 0) (cutoff := cutoff) (a := 0) (b := 0)
      (Nat.zero_le cutoff)]
  rfl

theorem oneChannelMultiplicity_allZero (cutoff : Nat) :
    oneChannelMultiplicity cutoff 0 0 0 0 = 1 := by
  have h := oneChannelMultiplicity_cutoff_independent
    (K := 0) (cutoff := cutoff) (a := 0) (b := 0) (c := 0) (d := 0)
    (by unfold linkAuxiliaryCutoff linkIncidenceBound; omega)
    (Nat.zero_le 0) (Nat.zero_le 0)
  rw [h]
  rfl

theorem twoChannelMultiplicity_allZero (cutoff : Nat) :
    twoChannelMultiplicity cutoff 0 0 0 0 0 = 1 := by
  have h := twoChannelMultiplicity_cutoff_independent
    (K := 0) (cutoff := cutoff) (a := 0) (b := 0) (c := 0)
    (d := 0) (e := 0)
    (by unfold linkAuxiliaryCutoff linkIncidenceBound; omega)
    (Nat.zero_le 0) (Nat.zero_le 0) (Nat.zero_le 0)
  rw [h]
  rfl

theorem threeChannelMultiplicity_allZero (cutoff : Nat) :
    threeChannelMultiplicity cutoff 0 0 0 0 0 0 = 1 := by
  have h := threeChannelMultiplicity_cutoff_independent
    (K := 0) (cutoff := cutoff) (a := 0) (b := 0) (c := 0)
    (d := 0) (e := 0) (f := 0)
    (by unfold linkAuxiliaryCutoff linkIncidenceBound; omega)
    (Nat.zero_le 0) (Nat.zero_le 0) (Nat.zero_le 0) (Nat.zero_le 0)
  rw [h]
  rfl

theorem explicitValenceMultiplicity_allZero
    (cutoff degree : Nat) (hdegree : degree ≤ linkIncidenceBound) :
    explicitValenceMultiplicity cutoff degree zeroEdgeLabelling = 1 := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact oneValentMultiplicity_allZero cutoff
  · exact twoValentMultiplicity_allZero cutoff
  · rfl
  · exact oneChannelMultiplicity_allZero cutoff
  · exact twoChannelMultiplicity_allZero cutoff
  · exact threeChannelMultiplicity_allZero cutoff

/-! ## 2. The literal all-zero global summand is exactly one -/

theorem heatKernelPacketCoefficient_zero_eq_one (K : Nat) :
    coeffAt (heatKernelPacket K coupling) 0 = (1 : Q') := by
  rw [coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]

private theorem eliminateLinks_eqv_one_local (value : Nat → Q') :
    ∀ edges : List Nat, (∀ edge, edge ∈ edges → value edge ≈ 1) →
      eliminateLinks value edges ≈ 1
  | [], _ => Q'.eqv_refl 1
  | edge :: rest, hvalue => by
      have hhead := hvalue edge List.mem_cons_self
      have hrest := eliminateLinks_eqv_one_local value rest
        (fun item hitem => hvalue item (List.mem_cons_of_mem edge hitem))
      exact Q'.eqv_trans _ (1 * 1) _
        (qmul_congr hhead hrest) (Q'.one_mul_eqv 1)

theorem explicitPhysicalFaceFactor_zero_eqv_one (K n : Nat) :
    explicitPhysicalFaceFactor K n zeroEdgeLabelling ≈ 1 := by
  unfold explicitPhysicalFaceFactor
  apply eliminateLinks_eqv_one_local
  intro edge _
  exact Q'.eqv_of_eq (heatKernelPacketCoefficient_zero_eq_one K)

theorem explicitLinkMultiplicityProduct_zero_eqv_one (K n : Nat) :
    ∀ links : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link),
      explicitLinkMultiplicityProduct K n zeroEdgeLabelling links ≈ 1
  | [] => Q'.eqv_refl 1
  | indexed :: rest => by
      have hdegree := incidentPlaqIds_length_le_six n indexed.2
      have hlocal : explicitValenceMultiplicity (linkAuxiliaryCutoff K)
          (incidentPlaqIds n indexed.2).length
          (fun position => zeroEdgeLabelling
            (localIdentifierRename (incidentPlaqIds n indexed.2)
              (linkBlockBase n indexed.1) position)) = 1 := by
        simpa only [zeroEdgeLabelling] using
          explicitValenceMultiplicity_allZero (linkAuxiliaryCutoff K)
            (incidentPlaqIds n indexed.2).length hdegree
      unfold explicitLinkMultiplicityProduct
      rw [hlocal]
      exact Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
        (explicitLinkMultiplicityProduct_zero_eqv_one K n rest)

def explicitSpinFoamWeight (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  explicitPhysicalFaceFactor K n physical *
    explicitLinkMultiplicityProduct K n physical
      (enumerate (distinctBoxLinks n))

theorem explicitSpinFoamWeight_zero_eqv_one (K n : Nat) :
    explicitSpinFoamWeight K n zeroEdgeLabelling ≈ 1 := by
  unfold explicitSpinFoamWeight
  exact Q'.eqv_trans _ (1 * 1) _
    (qmul_congr
      (explicitPhysicalFaceFactor_zero_eqv_one K n)
      (explicitLinkMultiplicityProduct_zero_eqv_one K n _))
    (Q'.one_mul_eqv 1)

/-! ## 3. Exact separation of the vacuum and excited physical labels -/

def physicalFaceEdges (n : Nat) : List Nat :=
  List.range (plaquetteEdgeCount n)

def explicitPhysicalLabellings (K n : Nat) : List EdgeLabelling :=
  boundedEdgeLabellings K (physicalFaceEdges n)

def explicitExcitedPhysicalLabellings (K n : Nat) : List EdgeLabelling :=
  (explicitPhysicalLabellings K n).filter
    (fun physical => hasExcitedB physical (physicalFaceEdges n))

def explicitPhysicalSpinFoamPartition (K n : Nat) : Q' :=
  listQSum (explicitSpinFoamWeight K n)
    (explicitPhysicalLabellings K n)

def explicitExcitedSpinFoamSum (K n : Nat) : Q' :=
  listQSum (explicitSpinFoamWeight K n)
    (explicitExcitedPhysicalLabellings K n)

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

private theorem listQSum_add_local {A : Type} (f g : A → Q') :
    ∀ xs : List A,
      listQSum (fun x => f x + g x) xs ≈
        listQSum f xs + listQSum g xs
  | [] => Q'.eqv_symm (q_zero_add_eqv 0)
  | x :: xs => by
      change (f x + g x) + listQSum (fun y => f y + g y) xs ≈
        (f x + listQSum f xs) + (g x + listQSum g xs)
      refine Q'.eqv_trans _
        ((f x + g x) + (listQSum f xs + listQSum g xs)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_add_local f g xs)) ?_
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

private theorem listQSum_congr_mem_local {A : Type} {f g : A → Q'} :
    ∀ xs : List A, (∀ x, x ∈ xs → f x ≈ g x) →
      listQSum f xs ≈ listQSum g xs
  | [], _ => Q'.eqv_refl 0
  | x :: xs, h =>
      Q'.add_eqv_congr' (h x List.mem_cons_self)
        (listQSum_congr_mem_local xs
          (fun y hy => h y (List.mem_cons_of_mem x hy)))

private theorem zeroSlice_sum_local {K : Nat} (edges : List Nat)
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
  exact Q'.eqv_of_eq (Q'.add_zero' vacuum)

private theorem weight_eq_excited_add_zeroSlice
    {K n : Nat} {physical : EdgeLabelling}
    (hmem : physical ∈ explicitPhysicalLabellings K n) :
    explicitSpinFoamWeight K n physical ≈
      (if hasExcitedB physical (physicalFaceEdges n) then
          explicitSpinFoamWeight K n physical else 0) +
        (if labelWithinB 0 (physicalFaceEdges n) physical then
          explicitSpinFoamWeight K n zeroEdgeLabelling else 0) := by
  have hzeroIff := enumerated_labelWithinB_zero_iff
    (K := K) (edges := physicalFaceEdges n) hmem
  by_cases hexcited : hasExcitedB physical (physicalFaceEdges n) = true
  · have hnotzero : physical ≠ zeroEdgeLabelling := by
      intro hlabel
      subst physical
      have hzfalse : hasExcitedB zeroEdgeLabelling
          (physicalFaceEdges n) = false :=
        (hasExcitedB_false_iff_zero_on zeroEdgeLabelling
          (physicalFaceEdges n)).2 (fun _ _ => rfl)
      rw [hzfalse] at hexcited
      cases hexcited
    have hwithin : labelWithinB 0 (physicalFaceEdges n) physical = false := by
      cases h : labelWithinB 0 (physicalFaceEdges n) physical with
      | false => rfl
      | true => exact False.elim (hnotzero (hzeroIff.mp h))
    rw [hexcited, hwithin]
    exact Q'.eqv_symm (q_add_zero_eqv _)
  · have hexcitedFalse : hasExcitedB physical
        (physicalFaceEdges n) = false := by
      cases h : hasExcitedB physical (physicalFaceEdges n) with
      | false => rfl
      | true => exact False.elim (hexcited h)
    have hzeroOn :=
      (hasExcitedB_false_iff_zero_on physical (physicalFaceEdges n)).1
        hexcitedFalse
    have hsound := boundedEdgeLabellings_sound K
      (physicalFaceEdges n) physical hmem
    have hlabel : physical = zeroEdgeLabelling := by
      funext edge
      by_cases hedge : edge ∈ physicalFaceEdges n
      · change physical edge = zeroEdgeLabelling edge
        simpa only [zeroEdgeLabelling] using hzeroOn edge hedge
      · change physical edge = zeroEdgeLabelling edge
        simpa only [zeroEdgeLabelling] using hsound.2 edge hedge
    have hwithin : labelWithinB 0 (physicalFaceEdges n) physical = true :=
      hzeroIff.mpr hlabel
    rw [hexcitedFalse, hwithin, hlabel]
    exact Q'.eqv_symm (q_zero_add_eqv _)

theorem explicitPhysicalSpinFoamPartition_eq_vacuum_add_excited
    (K n : Nat) :
    explicitPhysicalSpinFoamPartition K n ≈
      explicitSpinFoamWeight K n zeroEdgeLabelling +
        explicitExcitedSpinFoamSum K n := by
  let support := explicitPhysicalLabellings K n
  let excitedTerm : EdgeLabelling → Q' := fun physical =>
    if hasExcitedB physical (physicalFaceEdges n) then
      explicitSpinFoamWeight K n physical else 0
  let zeroSlice : EdgeLabelling → Q' := fun physical =>
    if labelWithinB 0 (physicalFaceEdges n) physical then
      explicitSpinFoamWeight K n zeroEdgeLabelling else 0
  have hpoint : listQSum (explicitSpinFoamWeight K n) support ≈
      listQSum (fun physical => excitedTerm physical + zeroSlice physical)
        support :=
    listQSum_congr_mem_local support
      (fun physical hphysical => weight_eq_excited_add_zeroSlice hphysical)
  refine Q'.eqv_trans _ _ _ hpoint ?_
  refine Q'.eqv_trans _
    (listQSum excitedTerm support + listQSum zeroSlice support) _
    (listQSum_add_local excitedTerm zeroSlice support) ?_
  have hexcited : listQSum excitedTerm support ≈
      explicitExcitedSpinFoamSum K n := by
    exact Q'.eqv_symm
      (listQSum_filter (explicitSpinFoamWeight K n)
        (fun physical => hasExcitedB physical (physicalFaceEdges n)) support)
  have hzero : listQSum zeroSlice support ≈
      explicitSpinFoamWeight K n zeroEdgeLabelling := by
    exact zeroSlice_sum_local (physicalFaceEdges n)
      (range_nodup_local _) (explicitSpinFoamWeight K n zeroEdgeLabelling)
  exact Q'.eqv_trans _
    (explicitExcitedSpinFoamSum K n +
      explicitSpinFoamWeight K n zeroEdgeLabelling) _
    (Q'.add_eqv_congr' hexcited hzero)
    (Q'.add_comm_eqv _ _)

theorem explicitPhysicalSpinFoamPartition_eq_one_add_excited
    (K n : Nat) :
    explicitPhysicalSpinFoamPartition K n ≈
      1 + explicitExcitedSpinFoamSum K n :=
  Q'.eqv_trans _
    (explicitSpinFoamWeight K n zeroEdgeLabelling +
      explicitExcitedSpinFoamSum K n) _
    (explicitPhysicalSpinFoamPartition_eq_vacuum_add_excited K n)
    (Q'.add_eqv_congr'
      (explicitSpinFoamWeight_zero_eqv_one K n) (Q'.eqv_refl _))

private theorem listQSum_nonnegative_local {A : Type} (value : A → Q')
    (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs : List A, (0 : Q') ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | x :: rest => Q'.zero_le_add _ _ (hvalue x)
      (listQSum_nonnegative_local value hvalue rest)

theorem explicitExcitedSpinFoamSum_nonnegative (K n : Nat) :
    (0 : Q') ≤ explicitExcitedSpinFoamSum K n := by
  unfold explicitExcitedSpinFoamSum
  apply listQSum_nonnegative_local
  intro physical
  exact explicitSpinFoamSummand_nonnegative K n physical

theorem one_le_explicitPhysicalSpinFoamPartition (K n : Nat) :
    (1 : Q') ≤ explicitPhysicalSpinFoamPartition K n := by
  have hadd : (1 : Q') ≤ 1 + explicitExcitedSpinFoamSum K n :=
    Q'.add_le_self_of_nonneg _ _
      (explicitExcitedSpinFoamSum_nonnegative K n)
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv
      (explicitPhysicalSpinFoamPartition_eq_one_add_excited K n))

theorem fusionCompleteBoxVertexCartesianSum_eq_one_add_excited
    (K n : Nat) :
    fusionCompleteBoxVertexCartesianSum K n ≈
      1 + explicitExcitedSpinFoamSum K n := by
  exact Q'.eqv_trans _ (explicitPhysicalSpinFoamPartition K n) _
    (by
      unfold explicitPhysicalSpinFoamPartition explicitSpinFoamWeight
      unfold explicitPhysicalLabellings physicalFaceEdges
      exact fusionCompleteBoxVertexCartesianSum_eq_physicalCutoffSpinFoam K n)
    (explicitPhysicalSpinFoamPartition_eq_one_add_excited K n)

theorem one_le_fusionCompleteBoxVertexCartesianSum (K n : Nat) :
    (1 : Q') ≤ fusionCompleteBoxVertexCartesianSum K n :=
  Q'.le_trans' _ (explicitPhysicalSpinFoamPartition K n) _
    (one_le_explicitPhysicalSpinFoamPartition K n)
    (Q'.ge_of_eqv (by
      unfold explicitPhysicalSpinFoamPartition explicitSpinFoamWeight
      unfold explicitPhysicalLabellings physicalFaceEdges
      exact fusionCompleteBoxVertexCartesianSum_eq_physicalCutoffSpinFoam K n))

end YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition.explicitValenceMultiplicity_allZero
#print axioms YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition.explicitSpinFoamWeight_zero_eqv_one
#print axioms YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition.explicitPhysicalSpinFoamPartition_eq_one_add_excited
#print axioms YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition.explicitExcitedSpinFoamSum_nonnegative
#print axioms YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition.fusionCompleteBoxVertexCartesianSum_eq_one_add_excited
#print axioms YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition.one_le_fusionCompleteBoxVertexCartesianSum
