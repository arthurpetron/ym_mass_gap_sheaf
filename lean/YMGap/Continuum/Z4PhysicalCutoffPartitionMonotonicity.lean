/-
# Exact monotonicity of the interacting finite-box cutoff partition

The growing-character envelope is useful only after it is connected to the
actual Haar/spin-foam partition.  This file supplies the first exact part of
that connection.  When the physical cutoff is enlarged from `K` to `L`, every
old physical labelling has exactly the same face coefficient product and the
same fusion-complete link multiplicity product.  The larger interacting
partition therefore splits as the old partition plus the explicit finite sum
over genuinely new physical labellings.

No estimate is used here.  In particular, the remaining cutoff-removal task is
now the concrete analytic problem of bounding the nonnegative increment
defined below by a derived character-tail majorant.
-/

import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4ExplicitSpinFoamBounds
import YMGap.Continuum.Z4FinitePartitionRelativeNormalization

namespace YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitPhysicalCutoffReduction
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumFloor
open YMGap.Continuum.Z4FinitePartitionRelativeNormalization
open YMGap.Continuum.Z4FuseChainIdentifierTransport
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

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

/-- The literal interacting spin-foam summand at physical cutoff `K`. -/
def fusionCompletePhysicalTerm (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  explicitPhysicalFaceFactor K n physical *
    explicitLinkMultiplicityProduct K n physical
      (enumerate (distinctBoxLinks n))

/-- The genuinely new sector appearing between physical cutoffs `K` and `L`.
It is defined for all `K,L`; the decomposition theorem assumes `K ≤ L`. -/
def fusionCompleteCutoffIncrement (K L n : Nat) : Q' :=
  listQSum (fusionCompletePhysicalTerm L n)
    ((boundedEdgeLabellings L (List.range (plaquetteEdgeCount n))).filter
      (fun physical =>
        !(labelWithinB K (List.range (plaquetteEdgeCount n)) physical)))

/-! ## 1. Exact stability of every retained summand -/

theorem explicitPhysicalFaceFactor_cutoff_stable
    {K L n : Nat} {physical : EdgeLabelling}
    (hKL : K ≤ L)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    explicitPhysicalFaceFactor L n physical =
      explicitPhysicalFaceFactor K n physical := by
  unfold explicitPhysicalFaceFactor
  apply eliminateLinks_congr_eq
  intro edge hedge
  have hsound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) physical hphysical
  have hspinK : physical edge < K + 1 := hsound.1 edge hedge
  have hspinL : physical edge < L + 1 := by omega
  rw [coeffAt_heatKernelPacket hspinL,
    coeffAt_heatKernelPacket hspinK]

theorem explicitLinkMultiplicityProduct_cutoff_stable
    {K L n : Nat} {physical : EdgeLabelling}
    (hKL : K ≤ L)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    ∀ links : List (Nat ×
      YMGap.Continuum.ClusterCount4DProgress.Z4Link),
      explicitLinkMultiplicityProduct L n physical links =
        explicitLinkMultiplicityProduct K n physical links
  | [] => rfl
  | indexed :: rest => by
      have haux : linkAuxiliaryCutoff K ≤ linkAuxiliaryCutoff L := by
        unfold linkAuxiliaryCutoff linkIncidenceBound
        omega
      have hdegree := incidentPlaqIds_length_le_six n indexed.2
      have hfactor := explicitValenceMultiplicity_cutoff_independent
        (fun position => physical
          (localIdentifierRename (incidentPlaqIds n indexed.2)
            (linkBlockBase n indexed.1) position))
        haux hdegree (actualExternalSpinsBounded hphysical)
      unfold explicitLinkMultiplicityProduct
      rw [hfactor,
        explicitLinkMultiplicityProduct_cutoff_stable
          hKL hphysical rest]

theorem fusionCompletePhysicalTerm_cutoff_stable
    {K L n : Nat} {physical : EdgeLabelling}
    (hKL : K ≤ L)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    fusionCompletePhysicalTerm L n physical =
      fusionCompletePhysicalTerm K n physical := by
  unfold fusionCompletePhysicalTerm
  rw [explicitPhysicalFaceFactor_cutoff_stable hKL hphysical,
    explicitLinkMultiplicityProduct_cutoff_stable hKL hphysical]

theorem fusionCompletePhysicalTerm_nonnegative
    (K n : Nat) (physical : EdgeLabelling) :
    (0 : Q') ≤ fusionCompletePhysicalTerm K n physical := by
  unfold fusionCompletePhysicalTerm
  exact explicitSpinFoamSummand_nonnegative K n physical

/-! ## 2. The graph partition and the explicit physical sum -/

theorem fusionCompleteVertexPartition_eq_physicalSum (K n : Nat) :
    fusionCompleteVertexPartition K n ≈
      listQSum (fusionCompletePhysicalTerm K n)
        (boundedEdgeLabellings K
          (List.range (plaquetteEdgeCount n))) := by
  simpa [fusionCompleteVertexPartition,
    fusionCompleteBoxVertexCartesianSum,
    fusionCompleteBoxVertexIntegrand,
    fusionCompletePhysicalTerm] using
      (fusionCompleteBoxVertexCartesianSum_eq_physicalCutoffSpinFoam K n)

private theorem listQSum_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs : List A, (0 : Q') ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail => Q'.zero_le_add _ _ (hvalue head)
      (listQSum_nonnegative_local value hvalue tail)

theorem fusionCompleteCutoffIncrement_nonnegative (K L n : Nat) :
    (0 : Q') ≤ fusionCompleteCutoffIncrement K L n := by
  unfold fusionCompleteCutoffIncrement
  exact listQSum_nonnegative_local _
    (fusionCompletePhysicalTerm_nonnegative L n) _

/-! ## 3. Exact cutoff-sector decomposition and monotonicity -/

/-- **Exact interacting cutoff decomposition.**  The larger production
partition is the smaller one plus precisely the sum over physical labellings
which violate the old cutoff. -/
theorem fusionCompleteVertexPartition_eq_base_add_increment
    {K L n : Nat} (hKL : K ≤ L) :
    fusionCompleteVertexPartition L n ≈
      fusionCompleteVertexPartition K n +
        fusionCompleteCutoffIncrement K L n := by
  let edges := List.range (plaquetteEdgeCount n)
  let oldTest := labelWithinB K edges
  let largeSupport := boundedEdgeLabellings L edges
  let smallSupport := boundedEdgeLabellings K edges
  have hfilter : largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, edges]
    exact boundedEdgeLabellings_filter_cutoff hKL _
      (range_nodup_local _)
  have hcommon :
      listQSum (fusionCompletePhysicalTerm L n)
          (largeSupport.filter oldTest) ≈
        listQSum (fusionCompletePhysicalTerm K n) smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro physical hphysical
    exact Q'.eqv_of_eq
      (fusionCompletePhysicalTerm_cutoff_stable hKL hphysical)
  have hsplit :
      listQSum (fusionCompletePhysicalTerm L n) largeSupport ≈
        listQSum (fusionCompletePhysicalTerm L n)
            (largeSupport.filter oldTest) +
          fusionCompleteCutoffIncrement K L n := by
    have h := listQSum_filter_partition
      (fusionCompletePhysicalTerm L n) oldTest largeSupport
    simpa [fusionCompleteCutoffIncrement, largeSupport, oldTest, edges] using h
  have hsmall :
      listQSum (fusionCompletePhysicalTerm L n)
          (largeSupport.filter oldTest) ≈
        fusionCompleteVertexPartition K n :=
    Q'.eqv_trans _ _ _ hcommon
      (Q'.eqv_symm (fusionCompleteVertexPartition_eq_physicalSum K n))
  have hlarge :
      fusionCompleteVertexPartition L n ≈
        listQSum (fusionCompletePhysicalTerm L n) largeSupport := by
    simpa [largeSupport, edges] using
      (fusionCompleteVertexPartition_eq_physicalSum L n)
  exact Q'.eqv_trans _ _ _ hlarge
    (Q'.eqv_trans _ _ _ hsplit
      (Q'.add_eqv_congr' hsmall (Q'.eqv_refl _)))

/-- Enlarging the external representation cutoff can only add nonnegative
interacting spin-foam sectors. -/
theorem fusionCompleteVertexPartition_mono
    {K L n : Nat} (hKL : K ≤ L) :
    fusionCompleteVertexPartition K n ≤
      fusionCompleteVertexPartition L n := by
  have hinc := fusionCompleteCutoffIncrement_nonnegative K L n
  have hadd : fusionCompleteVertexPartition K n ≤
      fusionCompleteVertexPartition K n +
        fusionCompleteCutoffIncrement K L n :=
    Q'.add_le_self_of_nonneg _ _ hinc
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv
      (fusionCompleteVertexPartition_eq_base_add_increment hKL))

/-! ## 4. Exact additive and relative errors -/

/-- The signed cutoff difference is exactly the new physical sector. -/
theorem fusionCompleteVertexPartition_difference_eq_increment
    {K L n : Nat} (hKL : K ≤ L) :
    fusionCompleteVertexPartition L n +
        -fusionCompleteVertexPartition K n ≈
      fusionCompleteCutoffIncrement K L n := by
  let ZK := fusionCompleteVertexPartition K n
  let ZL := fusionCompleteVertexPartition L n
  let increment := fusionCompleteCutoffIncrement K L n
  have hdecomp : ZL ≈ ZK + increment :=
    fusionCompleteVertexPartition_eq_base_add_increment hKL
  refine Q'.eqv_trans _ ((ZK + increment) + -ZK) _
    (Q'.add_eqv_congr' hdecomp (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _ (ZK + (increment + -ZK)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (ZK + (-ZK + increment)) _
    (Q'.add_eqv_congr_left ZK _ _
      (Q'.add_comm_eqv increment (-ZK))) ?_
  refine Q'.eqv_trans _ ((ZK + -ZK) + increment) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + increment) _
    (Q'.add_eqv_congr_right _ _ increment
      (Q'.add_neg_self_eqv ZK)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' increment)

theorem fusionCompleteVertexPartition_difference_nonnegative
    {K L n : Nat} (hKL : K ≤ L) :
    (0 : Q') ≤ fusionCompleteVertexPartition L n +
      -fusionCompleteVertexPartition K n := by
  exact Q'.le_trans' _ (fusionCompleteCutoffIncrement K L n) _
    (fusionCompleteCutoffIncrement_nonnegative K L n)
    (Q'.ge_of_eqv
      (fusionCompleteVertexPartition_difference_eq_increment hKL))

private theorem absQ_of_nonnegative_local (x : Q')
    (hx : (0 : Q') ≤ x) : absQ x = x := by
  unfold absQ
  have hnum : (0 : Int) ≤ x.num := by
    rw [Q'.zero_le_iff_num_nonneg] at hx
    exact hx
  rw [if_pos hnum]

/-- Because cutoff extension is monotone, its absolute additive error is
exactly the nonnegative new-sector sum. -/
theorem fusionCompleteVertexPartition_abs_difference_eq_increment
    {K L n : Nat} (hKL : K ≤ L) :
    absQ (fusionCompleteVertexPartition L n +
        -fusionCompleteVertexPartition K n) ≈
      fusionCompleteCutoffIncrement K L n := by
  rw [absQ_of_nonnegative_local _
    (fusionCompleteVertexPartition_difference_nonnegative hKL)]
  exact fusionCompleteVertexPartition_difference_eq_increment hKL

/-- The existing unit vacuum floor turns the exact additive increment into a
relative normalization bound with no volume-dependent denominator loss. -/
theorem fusionCompleteVertexPartition_relative_cutoff_increment
    {K L n : Nat} (hKL : K ≤ L) :
    absQ
        (Q'.divPos
            (fusionCompleteVertexPartition L n)
            (fusionCompleteVertexPartition K n)
            (fusionCompleteVertexPartition_pos K n) +
          -(1 : Q')) ≤
      fusionCompleteCutoffIncrement K L n := by
  exact fusionCompleteVertexPartition_relative_cutoff
    (fusionCompleteCutoffIncrement_nonnegative K L n)
    (Q'.le_of_eqv
      (fusionCompleteVertexPartition_abs_difference_eq_increment hKL))

end YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.explicitPhysicalFaceFactor_cutoff_stable
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.explicitLinkMultiplicityProduct_cutoff_stable
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.fusionCompletePhysicalTerm_cutoff_stable
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.fusionCompleteVertexPartition_eq_physicalSum
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.fusionCompleteCutoffIncrement_nonnegative
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.fusionCompleteVertexPartition_eq_base_add_increment
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.fusionCompleteVertexPartition_mono
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.fusionCompleteVertexPartition_difference_eq_increment
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.fusionCompleteVertexPartition_abs_difference_eq_increment
#print axioms YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity.fusionCompleteVertexPartition_relative_cutoff_increment
