/-
# Derived vacuum floor for vacuum-inclusive finite graph sums

The exact vacuum-completion identity is converted here into positivity and
normalization data.  For any nonnegative graph packet, the vertex-admissible
Cartesian sum dominates its derived zero-labelling amplitude.  A strictly
positive vacuum amplitude therefore supplies a constructive positive
denominator and a normalized vacuum fraction in `(0,1]`.

This is an abstract finite-graph theorem.  Its intended concrete input is the
heat-kernel packet whose Cartesian/fusion identification is developed in the
neighboring Z4 bridge modules.
-/

import YMGap.Constructive.RegularCRealArith
import YMGap.Continuum.ClusteringImpliesGap
import YMGap.Continuum.Z4FiniteGraphVacuumCompletion
import YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
import YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff

namespace YMGap.Continuum.Z4FiniteGraphVacuumFloor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4FiniteBoxHeatKernelCutoffPersistence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphIdentityRefinementAmplitude
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_nonnegative {A : Type} (g : A → Q')
    (hg : ∀ x, (0 : Q') ≤ g x) :
    ∀ xs : List A, (0 : Q') ≤ listQSum g xs
  | [] => Q'.le_refl' 0
  | x :: xs => Q'.zero_le_add _ _ (hg x) (listQSum_nonnegative g hg xs)

theorem graphGaugeVacuumProject_nonneg
    (edges : List Nat) (vertices : List TrivalentVertex) (f : GraphPacket)
    (hf : ∀ label, (0 : Q') ≤ f label) (label : EdgeLabelling) :
    (0 : Q') ≤ graphGaugeVacuumProject edges vertices f label := by
  unfold graphGaugeVacuumProject
  by_cases h : GraphPhysical edges vertices label
  · rw [if_pos h]
    exact hf label
  · rw [if_neg h]
    exact Q'.le_refl' 0

theorem graphVertexProject_nonneg
    (vertices : List TrivalentVertex) (f : GraphPacket)
    (hf : ∀ label, (0 : Q') ≤ f label) (label : EdgeLabelling) :
    (0 : Q') ≤ graphVertexProject vertices f label := by
  unfold graphVertexProject
  by_cases h : verticesAdmissibleB vertices label = true
  · rw [if_pos h]
    exact hf label
  · rw [if_neg h]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative (v : Nat → Q')
    (hv : ∀ edge, (0 : Q') ≤ v edge) :
    ∀ edges, (0 : Q') ≤ eliminateLinks v edges
  | [] => by
      change (0 : Q') ≤ 1
      decide
  | edge :: edges =>
      Q'.mul_nonneg _ _ (hv edge) (eliminateLinks_nonnegative v hv edges)

private theorem eliminateLinks_eqv_one (v : Nat → Q') :
    ∀ edges, (∀ edge, edge ∈ edges → v edge ≈ (1 : Q')) →
      eliminateLinks v edges ≈ (1 : Q')
  | [], _ => Q'.eqv_refl 1
  | edge :: edges, h => by
      refine Q'.eqv_trans _ ((1 : Q') * eliminateLinks v edges) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (h edge List.mem_cons_self)
      refine Q'.eqv_trans _ ((1 : Q') * (1 : Q')) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (eliminateLinks_eqv_one v edges
            (fun e he => h e (List.mem_cons_of_mem edge he)))
      · exact Q'.one_mul_eqv 1

/-- Every coefficient of the actual finite-cutoff heat-kernel/vacuum/identity
packet family is nonnegative, including zero padding above the cutoff. -/
theorem gaugeHeatKernelBoxPacket_coeff_nonneg
    (K n edge spin : Nat) :
    (0 : Q') ≤ coeffAt (gaugeHeatKernelBoxPacketsAtCutoff K n edge) spin := by
  unfold gaugeHeatKernelBoxPacketsAtCutoff
  by_cases hface : edge < plaquetteEdgeCount n
  · rw [if_pos hface]
    by_cases hspin : spin < K + 1
    · rw [coeffAt_heatKernelPacket hspin]
      exact coeffW_nonneg (by decide) spin
    · rw [coeffAt_of_gt _ (by omega)]
      exact Q'.le_refl' 0
  · rw [if_neg hface]
    by_cases hvac : edge ∈ vacuumBaseEdgeIds n
    · rw [if_pos hvac, coeffAt_vacuumPacket]
      split <;> decide
    · rw [if_neg hvac]
      by_cases hspin : spin < K + 1
      · rw [coeffAt_allOnesPacket hspin]
        decide
      · rw [coeffAt_of_gt _ (by omega)]
        exact Q'.le_refl' 0

/-- The actual finite-box heat-kernel bare graph packet is pointwise
nonnegative before imposing any fusion guard. -/
theorem gaugeHeatKernelBoxBareAmplitude_nonneg
    (K n : Nat) (label : EdgeLabelling) :
    (0 : Q') ≤
      packetGraphBareAmplitude (usedResolutionEdges n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n) label := by
  unfold packetGraphBareAmplitude
  exact eliminateLinks_nonnegative _
    (fun edge => gaugeHeatKernelBoxPacket_coeff_nonneg K n edge (label edge)) _

private theorem gaugeHeatKernelBoxPacket_coeff_zero
    (K n edge : Nat) :
    coeffAt (gaugeHeatKernelBoxPacketsAtCutoff K n edge) 0 = 1 := by
  unfold gaugeHeatKernelBoxPacketsAtCutoff
  by_cases hface : edge < plaquetteEdgeCount n
  · rw [if_pos hface, coeffAt_heatKernelPacket (Nat.succ_pos K), coeffW_zero]
  · rw [if_neg hface]
    by_cases hvac : edge ∈ vacuumBaseEdgeIds n
    · rw [if_pos hvac, coeffAt_vacuumPacket]
      rfl
    · rw [if_neg hvac, coeffAt_allOnesPacket (Nat.succ_pos K)]

/-- The all-zero labelling has exactly unit bare amplitude in the actual
finite-box heat-kernel packet, for every volume and cutoff. -/
theorem gaugeHeatKernelBoxBareAmplitude_zero_eqv_one
    (K n : Nat) :
    packetGraphBareAmplitude (usedResolutionEdges n)
        (gaugeHeatKernelBoxPacketsAtCutoff K n) zeroEdgeLabelling ≈
      (1 : Q') := by
  unfold packetGraphBareAmplitude
  apply eliminateLinks_eqv_one
  intro edge _
  exact Q'.eqv_of_eq (gaugeHeatKernelBoxPacket_coeff_zero K n edge)

/-- The repaired fusion-complete packet with auxiliary cutoff `6K` remains
pointwise nonnegative. -/
theorem gaugeHeatKernelBoxFusionComplete_coeff_nonneg
    (K n edge spin : Nat) :
    (0 : Q') ≤
      coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge) spin := by
  by_cases hface : edge < plaquetteEdgeCount n
  · by_cases hspin : spin ≤ K
    · rw [faceCoefficient_fusionComplete_of_le hface hspin]
      exact coeffW_nonneg (by decide) spin
    · rw [faceCoefficient_fusionComplete_zero_above hface (by omega)]
      exact Q'.le_refl' 0
  · by_cases hvac : edge ∈ vacuumBaseEdgeIds n
    · rw [vacuumCoefficient_fusionComplete hface hvac]
      split <;> decide
    · by_cases hspin : spin ≤ linkAuxiliaryCutoff K
      · rw [auxiliaryCoefficient_fusionComplete_one hface hvac hspin]
        decide
      · rw [coeffAt_of_gt _ (by omega)]
        exact Q'.le_refl' 0

theorem gaugeHeatKernelBoxFusionCompleteBareAmplitude_nonneg
    (K n : Nat) (label : EdgeLabelling) :
    (0 : Q') ≤
      packetGraphBareAmplitude (usedResolutionEdges n)
        (gaugeHeatKernelBoxPacketsFusionComplete K n) label := by
  unfold packetGraphBareAmplitude
  exact eliminateLinks_nonnegative _
    (fun edge => gaugeHeatKernelBoxFusionComplete_coeff_nonneg
      K n edge (label edge)) _

private theorem gaugeHeatKernelBoxFusionComplete_coeff_zero
    (K n edge : Nat) :
    coeffAt (gaugeHeatKernelBoxPacketsFusionComplete K n edge) 0 = 1 := by
  by_cases hface : edge < plaquetteEdgeCount n
  · rw [faceCoefficient_fusionComplete_of_le hface (Nat.zero_le K), coeffW_zero]
  · by_cases hvac : edge ∈ vacuumBaseEdgeIds n
    · rw [vacuumCoefficient_fusionComplete hface hvac]
      rfl
    · rw [auxiliaryCoefficient_fusionComplete_one hface hvac
        (Nat.zero_le (linkAuxiliaryCutoff K))]

/-- The repaired complete-fusion graph also has exactly unit bare vacuum
amplitude, uniformly in box volume and external cutoff. -/
theorem gaugeHeatKernelBoxFusionCompleteBareAmplitude_zero_eqv_one
    (K n : Nat) :
    packetGraphBareAmplitude (usedResolutionEdges n)
        (gaugeHeatKernelBoxPacketsFusionComplete K n) zeroEdgeLabelling ≈
      (1 : Q') := by
  unfold packetGraphBareAmplitude
  apply eliminateLinks_eqv_one
  intro edge _
  exact Q'.eqv_of_eq
    (gaugeHeatKernelBoxFusionComplete_coeff_zero K n edge)

private theorem range_nodup (N : Nat) : (List.range N).Nodup := by
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

private theorem filtered_eraseDups_nodup_nat (xs : List Nat) :
    ∀ p : Nat → Bool, (xs.filter p).eraseDups.Nodup := by
  induction xs with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons a as ih =>
      intro p
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, ih (fun b => (!b == a) && p b)⟩
        intro ha
        have ha' : a ∈ as.filter (fun b => (!b == a) && p b) :=
          List.mem_eraseDups.mp ha
        have hfalse := (List.mem_filter.mp ha').2
        have hself : (a == a) = true := Nat.instLawfulBEq.rfl (a := a)
        rw [hself] at hfalse
        contradiction
      · exact ih p

private theorem filter_true_nat :
    ∀ xs : List Nat, xs.filter (fun _ => true) = xs
  | [] => rfl
  | a :: as => congrArg (List.cons a) (filter_true_nat as)

private theorem eraseDups_nodup_nat (xs : List Nat) : xs.eraseDups.Nodup := by
  have h := filtered_eraseDups_nodup_nat xs (fun _ => true)
  rw [filter_true_nat] at h
  exact h

/-- The actual box graph edge enumeration is duplicate-free: physical face
identifiers lie below the plaquette count, while every retained auxiliary
identifier lies above it. -/
theorem usedResolutionEdges_nodup (n : Nat) :
    (usedResolutionEdges n).Nodup := by
  unfold usedResolutionEdges
  apply List.nodup_append.mpr
  refine ⟨range_nodup _, eraseDups_nodup_nat _, ?_⟩
  intro x hx y hy hxy
  have hxlt : x < plaquetteEdgeCount n := List.mem_range.mp hx
  unfold usedAuxiliaryEdges at hy
  have hy' := List.mem_eraseDups.mp hy
  have hyfilter := (List.mem_filter.mp hy').2
  have hyge : plaquetteEdgeCount n ≤ y := by
    simpa only [decide_eq_true_eq] using hyfilter
  subst y
  omega

/-- The vacuum-inclusive vertex Cartesian sum dominates the actual derived
zero-labelling amplitude. -/
theorem vertexCartesianSum_vacuum_floor
    {K : Nat} (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) (f : GraphPacket)
    (hf : ∀ label, (0 : Q') ≤ f label) :
    f zeroEdgeLabelling ≤
      listQSum (graphVertexProject vertices f)
        (boundedEdgeLabellings K edges) := by
  have hcompletion :=
    vertexCartesianSum_eq_vacuum_add_projected (K := K)
      edges hnodup vertices f
  have hprojected : (0 : Q') ≤
      listQSum (graphGaugeVacuumProject edges vertices f)
        (boundedEdgeLabellings K edges) :=
    listQSum_nonnegative _
      (graphGaugeVacuumProject_nonneg edges vertices f hf) _
  have hadd : f zeroEdgeLabelling ≤
      f zeroEdgeLabelling +
        listQSum (graphGaugeVacuumProject edges vertices f)
          (boundedEdgeLabellings K edges) :=
    Q'.add_le_self_of_nonneg _ _ hprojected
  exact Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hcompletion)

/-- A positive derived vacuum amplitude makes the complete Cartesian graph
partition strictly positive. -/
theorem vertexCartesianSum_pos
    {K : Nat} (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) (f : GraphPacket)
    (hf : ∀ label, (0 : Q') ≤ f label)
    (hvac : (0 : Q') < f zeroEdgeLabelling) :
    (0 : Q') <
      listQSum (graphVertexProject vertices f)
        (boundedEdgeLabellings K edges) :=
  ClusteringImpliesGap.lt_of_lt_of_le hvac
    (vertexCartesianSum_vacuum_floor edges hnodup vertices f hf)

/-- The normalized vacuum fraction of the complete finite graph sum is at
most one, with denominator positivity derived from the vacuum term. -/
theorem graphVacuumFraction_le_one
    {K : Nat} (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) (f : GraphPacket)
    (hf : ∀ label, (0 : Q') ≤ f label)
    (hvac : (0 : Q') < f zeroEdgeLabelling) :
    Q'.divPos (f zeroEdgeLabelling)
        (listQSum (graphVertexProject vertices f)
          (boundedEdgeLabellings K edges))
        (vertexCartesianSum_pos edges hnodup vertices f hf hvac) ≤
      (1 : Q') := by
  apply Q'.divPos_le_of_le_mul _ _
    (vertexCartesianSum_pos edges hnodup vertices f hf hvac)
  exact Q'.le_trans' _ _ _
    (vertexCartesianSum_vacuum_floor edges hnodup vertices f hf)
    (Q'.ge_of_eqv (Q'.one_mul_eqv _))

/-- The normalized vacuum fraction is strictly positive. -/
theorem graphVacuumFraction_pos
    {K : Nat} (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) (f : GraphPacket)
    (hf : ∀ label, (0 : Q') ≤ f label)
    (hvac : (0 : Q') < f zeroEdgeLabelling) :
    (0 : Q') <
      Q'.divPos (f zeroEdgeLabelling)
        (listQSum (graphVertexProject vertices f)
          (boundedEdgeLabellings K edges))
        (vertexCartesianSum_pos edges hnodup vertices f hf hvac) :=
  Q'.divPos_pos _ _
    (vertexCartesianSum_pos edges hnodup vertices f hf hvac) hvac

/-- Restoring the derived graph partition recovers the bare vacuum amplitude
exactly. -/
theorem graphVacuumFraction_mul_partition
    {K : Nat} (edges : List Nat) (hnodup : edges.Nodup)
    (vertices : List TrivalentVertex) (f : GraphPacket)
    (hf : ∀ label, (0 : Q') ≤ f label)
    (hvac : (0 : Q') < f zeroEdgeLabelling) :
    Q'.divPos (f zeroEdgeLabelling)
        (listQSum (graphVertexProject vertices f)
          (boundedEdgeLabellings K edges))
        (vertexCartesianSum_pos edges hnodup vertices f hf hvac) *
      listQSum (graphVertexProject vertices f)
        (boundedEdgeLabellings K edges) ≈
      f zeroEdgeLabelling :=
  Q'.divPos_mul_eqv _ _
    (vertexCartesianSum_pos edges hnodup vertices f hf hvac)

/-- The repaired `6K` packet's actual finite-box vertex-Cartesian partition.
The edge and vertex lists are the production graph enumerations, rather than
an abstract surrogate. -/
def fusionCompleteVertexPartition (K n : Nat) : Q' :=
  listQSum
    (graphVertexProject (resolutionVertices n)
      (packetGraphBareAmplitude (usedResolutionEdges n)
        (gaugeHeatKernelBoxPacketsFusionComplete K n)))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K) (usedResolutionEdges n))

/-- The explicit vacuum labelling gives a uniform unit floor for the repaired
finite-box vertex-Cartesian partition. -/
theorem fusionCompleteVertexPartition_one_le (K n : Nat) :
    (1 : Q') ≤ fusionCompleteVertexPartition K n := by
  unfold fusionCompleteVertexPartition
  refine Q'.le_trans' _
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (gaugeHeatKernelBoxPacketsFusionComplete K n) zeroEdgeLabelling) _ ?_ ?_
  · exact Q'.ge_of_eqv
      (gaugeHeatKernelBoxFusionCompleteBareAmplitude_zero_eqv_one K n)
  · exact vertexCartesianSum_vacuum_floor
      (K := linkAuxiliaryCutoff K)
      (usedResolutionEdges n) (usedResolutionEdges_nodup n)
      (resolutionVertices n)
      (packetGraphBareAmplitude (usedResolutionEdges n)
        (gaugeHeatKernelBoxPacketsFusionComplete K n))
      (gaugeHeatKernelBoxFusionCompleteBareAmplitude_nonneg K n)

/-- In particular, the repaired production graph has a constructively
positive finite-box normalization denominator. -/
theorem fusionCompleteVertexPartition_pos (K n : Nat) :
    (0 : Q') < fusionCompleteVertexPartition K n :=
  ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < 1)
    (fusionCompleteVertexPartition_one_le K n)

/-- The derived vacuum fraction for the repaired production graph. -/
def fusionCompleteVertexVacuumFraction (K n : Nat) : Q' :=
  Q'.divPos
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (gaugeHeatKernelBoxPacketsFusionComplete K n) zeroEdgeLabelling)
    (fusionCompleteVertexPartition K n)
    (fusionCompleteVertexPartition_pos K n)

theorem fusionCompleteVertexVacuumFraction_le_one (K n : Nat) :
    fusionCompleteVertexVacuumFraction K n ≤ (1 : Q') := by
  unfold fusionCompleteVertexVacuumFraction fusionCompleteVertexPartition
  exact graphVacuumFraction_le_one
    (K := linkAuxiliaryCutoff K)
    (usedResolutionEdges n) (usedResolutionEdges_nodup n)
    (resolutionVertices n)
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (gaugeHeatKernelBoxPacketsFusionComplete K n))
    (gaugeHeatKernelBoxFusionCompleteBareAmplitude_nonneg K n)
    (ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.ge_of_eqv
        (gaugeHeatKernelBoxFusionCompleteBareAmplitude_zero_eqv_one K n)))

theorem fusionCompleteVertexVacuumFraction_pos (K n : Nat) :
    (0 : Q') < fusionCompleteVertexVacuumFraction K n := by
  unfold fusionCompleteVertexVacuumFraction fusionCompleteVertexPartition
  exact graphVacuumFraction_pos
    (K := linkAuxiliaryCutoff K)
    (usedResolutionEdges n) (usedResolutionEdges_nodup n)
    (resolutionVertices n)
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (gaugeHeatKernelBoxPacketsFusionComplete K n))
    (gaugeHeatKernelBoxFusionCompleteBareAmplitude_nonneg K n)
    (ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.ge_of_eqv
        (gaugeHeatKernelBoxFusionCompleteBareAmplitude_zero_eqv_one K n)))

theorem fusionCompleteVertexVacuumFraction_mul_partition (K n : Nat) :
    fusionCompleteVertexVacuumFraction K n *
        fusionCompleteVertexPartition K n ≈
      packetGraphBareAmplitude (usedResolutionEdges n)
        (gaugeHeatKernelBoxPacketsFusionComplete K n) zeroEdgeLabelling := by
  unfold fusionCompleteVertexVacuumFraction fusionCompleteVertexPartition
  exact graphVacuumFraction_mul_partition
    (K := linkAuxiliaryCutoff K)
    (usedResolutionEdges n) (usedResolutionEdges_nodup n)
    (resolutionVertices n)
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (gaugeHeatKernelBoxPacketsFusionComplete K n))
    (gaugeHeatKernelBoxFusionCompleteBareAmplitude_nonneg K n)
    (ClusteringImpliesGap.lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.ge_of_eqv
        (gaugeHeatKernelBoxFusionCompleteBareAmplitude_zero_eqv_one K n)))

/-- With the derived unit vacuum amplitude inserted, the normalized vacuum
fraction restores exactly one when multiplied by the production partition. -/
theorem fusionCompleteVertexVacuumFraction_mul_partition_eqv_one (K n : Nat) :
    fusionCompleteVertexVacuumFraction K n *
        fusionCompleteVertexPartition K n ≈ (1 : Q') :=
  Q'.eqv_trans _
    (packetGraphBareAmplitude (usedResolutionEdges n)
      (gaugeHeatKernelBoxPacketsFusionComplete K n) zeroEdgeLabelling) _
    (fusionCompleteVertexVacuumFraction_mul_partition K n)
    (gaugeHeatKernelBoxFusionCompleteBareAmplitude_zero_eqv_one K n)

#print axioms graphGaugeVacuumProject_nonneg
#print axioms graphVertexProject_nonneg
#print axioms gaugeHeatKernelBoxPacket_coeff_nonneg
#print axioms gaugeHeatKernelBoxBareAmplitude_nonneg
#print axioms gaugeHeatKernelBoxBareAmplitude_zero_eqv_one
#print axioms gaugeHeatKernelBoxFusionComplete_coeff_nonneg
#print axioms gaugeHeatKernelBoxFusionCompleteBareAmplitude_nonneg
#print axioms gaugeHeatKernelBoxFusionCompleteBareAmplitude_zero_eqv_one
#print axioms usedResolutionEdges_nodup
#print axioms vertexCartesianSum_vacuum_floor
#print axioms vertexCartesianSum_pos
#print axioms graphVacuumFraction_le_one
#print axioms graphVacuumFraction_pos
#print axioms graphVacuumFraction_mul_partition
#print axioms fusionCompleteVertexPartition_one_le
#print axioms fusionCompleteVertexPartition_pos
#print axioms fusionCompleteVertexVacuumFraction_le_one
#print axioms fusionCompleteVertexVacuumFraction_pos
#print axioms fusionCompleteVertexVacuumFraction_mul_partition
#print axioms fusionCompleteVertexVacuumFraction_mul_partition_eqv_one

end YMGap.Continuum.Z4FiniteGraphVacuumFloor
