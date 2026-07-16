/-
# Coupling-parametric physical-cutoff spin-foam partition

This module places the arbitrary physical cutoff and the strong-coupling
anchor in one formula.  The local fusion multiplicities are independent of
the heat-kernel coupling, so only the face product is parameterized by `w`.

The resulting finite spin-foam partition has an exact cutoff-sector
decomposition for every nonnegative coupling.  If `0 <= w <= 1/2`, every
parametric summand is dominated termwise by the already machine-checked
`w = 1/2` summand.  Thus the complete interacting dyadic cutoff modulus also
holds at the derived anchor `w = 1/400`.  At physical cutoff one the new
partition is exactly the existing parameterized graph/polymer partition.

The remaining graph-theoretic interface is sharply isolated: for general
`w` and general `K`, the parameterized spin-foam partition below still has to
be identified with a literal parameterized packet-graph Cartesian sum.
-/

import YMGap.Continuum.FusedAmplitudeDerivation
import YMGap.Continuum.Z4InteractingCutoffCofinal
import YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity

namespace YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteCharacterPacketDirectedSystem
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.Z4AdjacentCutoffDyadicSchedule
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4ExplicitSpinFoamBounds
open YMGap.Continuum.Z4ExplicitSupportMultiplicityBound
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumFloor
open YMGap.Continuum.Z4FinitePartitionRelativeNormalization
open YMGap.Continuum.Z4InteractingCutoffCofinal
open YMGap.Continuum.Z4ParametricCutoffOneSpinFoamIdentity
open YMGap.Continuum.Z4PhysicalCutoffPartitionMonotonicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The common coupling/cutoff partition -/

def parametricKPhysicalFaceFactor (w : Q') (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  eliminateLinks
    (fun edge => coeffAt (heatKernelPacket K w) (physical edge))
    (List.range (plaquetteEdgeCount n))

def parametricKPhysicalTerm (w : Q') (K n : Nat)
    (physical : EdgeLabelling) : Q' :=
  parametricKPhysicalFaceFactor w K n physical *
    explicitLinkMultiplicityProduct K n physical
      (enumerate (distinctBoxLinks n))

def parametricKPhysicalPartition (w : Q') (K n : Nat) : Q' :=
  listQSum (parametricKPhysicalTerm w K n)
    (boundedEdgeLabellings K (List.range (plaquetteEdgeCount n)))

def parametricKCutoffIncrement (w : Q') (K L n : Nat) : Q' :=
  listQSum (parametricKPhysicalTerm w L n)
    ((boundedEdgeLabellings L (List.range (plaquetteEdgeCount n))).filter
      (fun physical =>
        !(labelWithinB K (List.range (plaquetteEdgeCount n)) physical)))

private theorem parametricCoefficient_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K spin : Nat) :
    (0 : Q') ≤ coeffAt (heatKernelPacket K w) spin := by
  by_cases hspin : spin < K + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg hw spin
  · have hlarge : K < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket K w) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_nonnegative_local
    (value : Nat → Q') (hvalue : ∀ edge, (0 : Q') ≤ value edge) :
    ∀ edges : List Nat, (0 : Q') ≤ eliminateLinks value edges
  | [] => Q'.zero_le_one
  | edge :: rest => Q'.mul_nonneg _ _ (hvalue edge)
      (eliminateLinks_nonnegative_local value hvalue rest)

private theorem listQSum_nonnegative_local {A : Type}
    (value : A → Q') (hvalue : ∀ x, (0 : Q') ≤ value x) :
    ∀ xs : List A, (0 : Q') ≤ listQSum value xs
  | [] => Q'.le_refl' 0
  | head :: tail => Q'.zero_le_add _ _ (hvalue head)
      (listQSum_nonnegative_local value hvalue tail)

theorem parametricKPhysicalTerm_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K n : Nat)
    (physical : EdgeLabelling) :
    (0 : Q') ≤ parametricKPhysicalTerm w K n physical := by
  unfold parametricKPhysicalTerm parametricKPhysicalFaceFactor
  exact Q'.mul_nonneg _ _
    (eliminateLinks_nonnegative_local _
      (fun edge => parametricCoefficient_nonnegative hw K (physical edge)) _)
    (explicitLinkMultiplicityProduct_nonnegative K n physical _)

theorem parametricKCutoffIncrement_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w) (K L n : Nat) :
    (0 : Q') ≤ parametricKCutoffIncrement w K L n := by
  unfold parametricKCutoffIncrement
  exact listQSum_nonnegative_local _
    (parametricKPhysicalTerm_nonnegative hw L n) _

/-! ## 2. Exact cutoff stability and decomposition -/

theorem parametricKPhysicalFaceFactor_cutoff_stable
    {w : Q'} {K L n : Nat} {physical : EdgeLabelling}
    (hKL : K ≤ L)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalFaceFactor w L n physical =
      parametricKPhysicalFaceFactor w K n physical := by
  unfold parametricKPhysicalFaceFactor
  apply eliminateLinks_congr_eq
  intro edge hedge
  have hsound := boundedEdgeLabellings_sound K
    (List.range (plaquetteEdgeCount n)) physical hphysical
  have hspinK : physical edge < K + 1 := hsound.1 edge hedge
  have hspinL : physical edge < L + 1 := by omega
  rw [coeffAt_heatKernelPacket hspinL,
    coeffAt_heatKernelPacket hspinK]

theorem parametricKPhysicalTerm_cutoff_stable
    {w : Q'} {K L n : Nat} {physical : EdgeLabelling}
    (hKL : K ≤ L)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalTerm w L n physical =
      parametricKPhysicalTerm w K n physical := by
  unfold parametricKPhysicalTerm
  rw [parametricKPhysicalFaceFactor_cutoff_stable hKL hphysical,
    explicitLinkMultiplicityProduct_cutoff_stable hKL hphysical]

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

theorem parametricKPhysicalPartition_eq_base_add_increment
    {w : Q'} {K L n : Nat} (hKL : K ≤ L) :
    parametricKPhysicalPartition w L n ≈
      parametricKPhysicalPartition w K n +
        parametricKCutoffIncrement w K L n := by
  let edges := List.range (plaquetteEdgeCount n)
  let oldTest := labelWithinB K edges
  let largeSupport := boundedEdgeLabellings L edges
  let smallSupport := boundedEdgeLabellings K edges
  have hfilter : largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, edges]
    exact boundedEdgeLabellings_filter_cutoff hKL _ (range_nodup_local _)
  have hcommon :
      listQSum (parametricKPhysicalTerm w L n)
          (largeSupport.filter oldTest) ≈
        listQSum (parametricKPhysicalTerm w K n) smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro physical hphysical
    exact Q'.eqv_of_eq
      (parametricKPhysicalTerm_cutoff_stable hKL hphysical)
  have hsplit :
      listQSum (parametricKPhysicalTerm w L n) largeSupport ≈
        listQSum (parametricKPhysicalTerm w L n)
            (largeSupport.filter oldTest) +
          parametricKCutoffIncrement w K L n := by
    have h := listQSum_filter_partition
      (parametricKPhysicalTerm w L n) oldTest largeSupport
    simpa [parametricKCutoffIncrement, largeSupport, oldTest, edges] using h
  unfold parametricKPhysicalPartition
  dsimp only [largeSupport, smallSupport, edges] at hcommon hsplit ⊢
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr' hcommon (Q'.eqv_refl _))

theorem parametricKPhysicalPartition_mono
    {w : Q'} (hw : (0 : Q') ≤ w) {K L n : Nat} (hKL : K ≤ L) :
    parametricKPhysicalPartition w K n ≤
      parametricKPhysicalPartition w L n := by
  have hinc := parametricKCutoffIncrement_nonnegative hw K L n
  have hadd : parametricKPhysicalPartition w K n ≤
      parametricKPhysicalPartition w K n +
        parametricKCutoffIncrement w K L n :=
    Q'.add_le_self_of_nonneg _ _ hinc
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv (parametricKPhysicalPartition_eq_base_add_increment hKL))

theorem parametricKPhysicalPartition_difference_eq_increment
    {w : Q'} {K L n : Nat} (hKL : K ≤ L) :
    parametricKPhysicalPartition w L n +
        -parametricKPhysicalPartition w K n ≈
      parametricKCutoffIncrement w K L n := by
  let ZK := parametricKPhysicalPartition w K n
  let ZL := parametricKPhysicalPartition w L n
  let increment := parametricKCutoffIncrement w K L n
  have hdecomp : ZL ≈ ZK + increment :=
    parametricKPhysicalPartition_eq_base_add_increment hKL
  refine Q'.eqv_trans _ ((ZK + increment) + -ZK) _
    (Q'.add_eqv_congr' hdecomp (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _ (ZK + (increment + -ZK)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (ZK + (-ZK + increment)) _
    (Q'.add_eqv_congr_left ZK _ _ (Q'.add_comm_eqv increment (-ZK))) ?_
  refine Q'.eqv_trans _ ((ZK + -ZK) + increment) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + increment) _
    (Q'.add_eqv_congr_right _ _ increment (Q'.add_neg_self_eqv ZK)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' increment)

private theorem absQ_of_nonnegative_local (x : Q')
    (hx : (0 : Q') ≤ x) : absQ x = x := by
  unfold absQ
  have hnum : (0 : Int) ≤ x.num := by
    rw [Q'.zero_le_iff_num_nonneg] at hx
    exact hx
  rw [if_pos hnum]

theorem parametricKPhysicalPartition_abs_difference_eq_increment
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K L n : Nat} (hKL : K ≤ L) :
    absQ
        (parametricKPhysicalPartition w L n +
          -parametricKPhysicalPartition w K n) ≈
      parametricKCutoffIncrement w K L n := by
  have hdiff0 : (0 : Q') ≤
      parametricKPhysicalPartition w L n +
        -parametricKPhysicalPartition w K n :=
    Q'.le_trans' _ (parametricKCutoffIncrement w K L n) _
      (parametricKCutoffIncrement_nonnegative hw K L n)
      (Q'.ge_of_eqv
        (parametricKPhysicalPartition_difference_eq_increment hKL))
  rw [absQ_of_nonnegative_local _ hdiff0]
  exact parametricKPhysicalPartition_difference_eq_increment hKL

/-! ## 3. Domination by the checked coupling-one-half partition -/

private theorem eliminateLinks_le_local
    (left right : Nat → Q')
    (hleft0 : ∀ edge, (0 : Q') ≤ left edge)
    (hright0 : ∀ edge, (0 : Q') ≤ right edge) :
    ∀ edges : List Nat,
      (∀ edge, edge ∈ edges → left edge ≤ right edge) →
      eliminateLinks left edges ≤ eliminateLinks right edges
  | [], _ => Q'.le_refl' 1
  | edge :: rest, hle => by
      have htail := eliminateLinks_le_local left right hleft0 hright0 rest
        (fun item hitem => hle item (List.mem_cons_of_mem edge hitem))
      have htail0 := eliminateLinks_nonnegative_local left
        hleft0 rest
      have hrightHead0 := hright0 edge
      have hfirst : left edge * eliminateLinks left rest ≤
          right edge * eliminateLinks left rest :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (hle edge List.mem_cons_self) htail0
      have hsecond : right edge * eliminateLinks left rest ≤
          right edge * eliminateLinks right rest :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ htail hrightHead0
      exact Q'.le_trans' _ _ _ hfirst hsecond

theorem parametricKPhysicalFaceFactor_le_coupling
    {w : Q'} (hw : (0 : Q') ≤ w) (hwc : w ≤ coupling)
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalFaceFactor w K n physical ≤
      explicitPhysicalFaceFactor K n physical := by
  unfold parametricKPhysicalFaceFactor explicitPhysicalFaceFactor
  apply eliminateLinks_le_local
  · intro edge
    exact parametricCoefficient_nonnegative hw K (physical edge)
  · intro edge
    exact heatKernelPacketCoefficient_nonnegative K (physical edge)
  · intro edge hedge
    have hsound := boundedEdgeLabellings_sound K
      (List.range (plaquetteEdgeCount n)) physical hphysical
    have hspin := hsound.1 edge hedge
    rw [coeffAt_heatKernelPacket hspin, coeffAt_heatKernelPacket hspin]
    exact coeffW_mono_w hw hwc (physical edge)

theorem parametricKPhysicalTerm_le_coupling
    {w : Q'} (hw : (0 : Q') ≤ w) (hwc : w ≤ coupling)
    {K n : Nat} {physical : EdgeLabelling}
    (hphysical : physical ∈ boundedEdgeLabellings K
      (List.range (plaquetteEdgeCount n))) :
    parametricKPhysicalTerm w K n physical ≤
      fusionCompletePhysicalTerm K n physical := by
  have hface := parametricKPhysicalFaceFactor_le_coupling hw hwc hphysical
  have hlink0 := explicitLinkMultiplicityProduct_nonnegative K n physical
    (enumerate (distinctBoxLinks n))
  unfold parametricKPhysicalTerm fusionCompletePhysicalTerm
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hface hlink0

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ xs : List A,
      (∀ x, x ∈ xs → left x ≤ right x) →
      listQSum left xs ≤ listQSum right xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun x hx => hle x (List.mem_cons_of_mem head hx)))

theorem parametricKCutoffIncrement_le_coupling
    {w : Q'} (hw : (0 : Q') ≤ w) (hwc : w ≤ coupling)
    (K L n : Nat) :
    parametricKCutoffIncrement w K L n ≤
      fusionCompleteCutoffIncrement K L n := by
  unfold parametricKCutoffIncrement fusionCompleteCutoffIncrement
  apply listQSum_le_termwise_local
  intro physical hphysical
  exact parametricKPhysicalTerm_le_coupling hw hwc
    (List.mem_filter.mp hphysical).1

/-! ## 4. Exact endpoint identifications -/

theorem parametricKPhysicalTerm_one_eqv_localized
    (w : Q') (n : Nat) (physical : EdgeLabelling) :
    parametricKPhysicalTerm w 1 n physical ≈
      parametricLocalizedSpinFoamWeight w n physical := by
  unfold parametricKPhysicalTerm parametricKPhysicalFaceFactor
  change
    parametricPhysicalFaceFactor w n physical *
        explicitLinkMultiplicityProduct 1 n physical
          (enumerate (distinctBoxLinks n)) ≈
      parametricLocalizedSpinFoamWeight w n physical
  exact parametricSpinFoamWeight_eq_localized w n physical

theorem parametricKPhysicalPartition_one_eqv_localized
    (w : Q') (n : Nat) :
    parametricKPhysicalPartition w 1 n ≈
      parametricLocalizedSpinFoamPartition w n := by
  unfold parametricKPhysicalPartition parametricLocalizedSpinFoamPartition
    explicitPhysicalLabellings physicalFaceEdges
  apply listQSum_congr
  intro physical
  exact parametricKPhysicalTerm_one_eqv_localized w n physical

theorem parametricKPhysicalPartition_coupling_eqv_graph (K n : Nat) :
    parametricKPhysicalPartition coupling K n ≈
      fusionCompleteVertexPartition K n := by
  refine Q'.eqv_trans _
    (listQSum (fusionCompletePhysicalTerm K n)
      (boundedEdgeLabellings K
        (List.range (plaquetteEdgeCount n)))) _ ?_ ?_
  · apply listQSum_congr
    intro physical
    exact Q'.eqv_refl _
  · exact Q'.eqv_symm
      (fusionCompleteVertexPartition_eq_physicalSum K n)

theorem anchorParametricPartition_one_eqv_graph (n : Nat) :
    parametricKPhysicalPartition anchorCoupling 1 n ≈
      parametricGaugeBoxVertexCartesianSum anchorCoupling n := by
  exact Q'.eqv_trans _
    (parametricLocalizedSpinFoamPartition anchorCoupling n) _
    (parametricKPhysicalPartition_one_eqv_localized anchorCoupling n)
    (Q'.eqv_symm
      (parametricGaugeBoxVertexCartesianSum_eq_localizedSpinFoam
        anchorCoupling n))

theorem anchorParametricPartition_one_le
    {K : Nat} (hK : 1 ≤ K) (n : Nat) :
    (1 : Q') ≤ parametricKPhysicalPartition anchorCoupling K n := by
  have hone : (1 : Q') ≤
      parametricKPhysicalPartition anchorCoupling 1 n :=
    Q'.le_trans' _ _ _
      (one_le_anchorGaugeBoxVertexCartesianSum n)
      (Q'.ge_of_eqv
        (anchorParametricPartition_one_eqv_graph n))
  exact Q'.le_trans' _ _ _ hone
    (parametricKPhysicalPartition_mono (by decide) hK)

theorem anchorParametricPartition_pos
    {K : Nat} (hK : 1 ≤ K) (n : Nat) :
    (0 : Q') < parametricKPhysicalPartition anchorCoupling K n :=
  ClusteringImpliesGap.lt_of_lt_of_le (by decide)
    (anchorParametricPartition_one_le hK n)

/-! ## 5. Anchor-coupling cutoff modulus and constructive limit -/

theorem anchorParametricCutoffIncrement_le_two_halfPow
    (stage depth n : Nat) :
    parametricKCutoffIncrement anchorCoupling
        (interactingAdjacentCutoff stage n)
        (interactingAdjacentCutoff stage n + depth) n ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  exact Q'.le_trans' _ _ _
    (parametricKCutoffIncrement_le_coupling (by decide) (by decide) _ _ _)
    (scheduledCutoffIncrement_le_two_halfPow stage depth n)

theorem anchorParametricAdjacentIncrement_le_halfPow
    (stage n : Nat) :
    parametricKCutoffIncrement anchorCoupling
        (interactingAdjacentCutoff stage n)
        (interactingAdjacentCutoff stage n + 1) n ≤
      HalfPow.half ^ stage := by
  exact Q'.le_trans' _ _ _
    (parametricKCutoffIncrement_le_coupling (by decide) (by decide) _ _ _)
    (interactingAdjacentCutoff_increment_le_halfPow stage n)

theorem anchorParametricPartition_abs_cutoff_difference_le_two_halfPow
    (stage depth n : Nat) :
    absQ
        (parametricKPhysicalPartition anchorCoupling
            (interactingAdjacentCutoff stage n + depth) n +
          -parametricKPhysicalPartition anchorCoupling
            (interactingAdjacentCutoff stage n) n) ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  have habs := parametricKPhysicalPartition_abs_difference_eq_increment
    (w := anchorCoupling) (by decide)
    (K := interactingAdjacentCutoff stage n)
    (L := interactingAdjacentCutoff stage n + depth)
    (n := n) (by omega)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv habs)
    (anchorParametricCutoffIncrement_le_two_halfPow stage depth n)

theorem anchorParametricPartition_relative_cutoff_le_two_halfPow
    (stage depth n : Nat) :
    absQ
        (Q'.divPos
            (parametricKPhysicalPartition anchorCoupling
              (interactingAdjacentCutoff stage n + depth) n)
            (parametricKPhysicalPartition anchorCoupling
              (interactingAdjacentCutoff stage n) n)
            (anchorParametricPartition_pos (by
              unfold interactingAdjacentCutoff
              omega) n) +
          -(1 : Q')) ≤
      Q'.ofNat 2 * (HalfPow.half ^ stage) := by
  exact additive_partition_error_to_relative
    (anchorParametricPartition_one_le (by
      unfold interactingAdjacentCutoff
      omega) n)
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.pow_nonneg _ HalfPow.half_nonneg stage))
    (anchorParametricPartition_abs_cutoff_difference_le_two_halfPow
      stage depth n)

def anchorParametricCutoffPartitionSequence (n stage : Nat) : Q' :=
  parametricKPhysicalPartition anchorCoupling
    (interactingAdjacentCutoff stage n) n

theorem anchorParametricCutoffPartitionSequence_step_eqv
    (n stage : Nat) :
    anchorParametricCutoffPartitionSequence n (stage + 1) ≈
      anchorParametricCutoffPartitionSequence n stage +
        parametricKCutoffIncrement anchorCoupling
          (interactingAdjacentCutoff stage n)
          (interactingAdjacentCutoff stage n + 1) n := by
  have hcutoff : interactingAdjacentCutoff (stage + 1) n =
      interactingAdjacentCutoff stage n + 1 := by
    unfold interactingAdjacentCutoff
    omega
  unfold anchorParametricCutoffPartitionSequence
  rw [hcutoff]
  exact parametricKPhysicalPartition_eq_base_add_increment (by omega)

theorem anchorParametricCutoffPartitionSequence_step_upper
    (n stage : Nat) :
    anchorParametricCutoffPartitionSequence n (stage + 1) ≤
      anchorParametricCutoffPartitionSequence n stage + geoIncr 1 stage := by
  have heq := anchorParametricCutoffPartitionSequence_step_eqv n stage
  have hinc := anchorParametricAdjacentIncrement_le_halfPow stage n
  have hgeo : HalfPow.half ^ stage ≤ geoIncr 1 stage :=
    Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.add_le_add_left _ _ _ (Q'.le_trans' _ _ _ hinc hgeo))

theorem anchorParametricCutoffPartitionSequence_step_lower
    (n stage : Nat) :
    anchorParametricCutoffPartitionSequence n stage ≤
      anchorParametricCutoffPartitionSequence n (stage + 1) +
        geoIncr 1 stage := by
  have hcutoff : interactingAdjacentCutoff stage n ≤
      interactingAdjacentCutoff (stage + 1) n := by
    unfold interactingAdjacentCutoff
    omega
  have hmono : anchorParametricCutoffPartitionSequence n stage ≤
      anchorParametricCutoffPartitionSequence n (stage + 1) := by
    unfold anchorParametricCutoffPartitionSequence
    exact parametricKPhysicalPartition_mono (by decide) hcutoff
  exact Q'.le_trans' _ _ _ hmono
    (Q'.add_le_self_of_nonneg _ _ (geoIncr_nonneg 1 Q'.zero_le_one stage))

/-- For each fixed finite box, the same coupling as the proved polymer anchor
has a constructive representation-cutoff limit. -/
def anchorParametricCutoffPartitionLimit (n : Nat) : CReal :=
  crealOfGeoIncrement (anchorParametricCutoffPartitionSequence n)
    1 Q'.zero_le_one
    (anchorParametricCutoffPartitionSequence_step_upper n)
    (anchorParametricCutoffPartitionSequence_step_lower n)
    (fun ε hε => by
      refine ⟨HalfPow.half * ε, ExpNeg.half_mul_pos ε hε, ?_⟩
      show (Q'.ofNat 2 * 1) * (HalfPow.half * ε) ≤ ε
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ (Q'.ofNat 2 * (HalfPow.half * ε)) _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_one_eqv (Q'.ofNat 2))) ?_
      refine Q'.eqv_trans _ ((Q'.ofNat 2 * HalfPow.half) * ε) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (Q'.ofNat 2) HalfPow.half ε)) ?_
      refine Q'.eqv_trans _ ((1 : Q') * ε) _
        (Q'.mul_eqv_congr_right _ _ _ (by decide)) ?_
      exact Q'.one_mul_eqv ε)

@[simp] theorem anchorParametricCutoffPartitionLimit_approx
    (n stage : Nat) :
    (anchorParametricCutoffPartitionLimit n).approx stage =
      anchorParametricCutoffPartitionSequence n stage := rfl

end YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ParametricPhysicalCutoffPartition.parametricKPhysicalPartition_eq_base_add_increment
#print axioms YMGap.Continuum.Z4ParametricPhysicalCutoffPartition.parametricKCutoffIncrement_le_coupling
#print axioms YMGap.Continuum.Z4ParametricPhysicalCutoffPartition.parametricKPhysicalPartition_one_eqv_localized
#print axioms YMGap.Continuum.Z4ParametricPhysicalCutoffPartition.parametricKPhysicalPartition_coupling_eqv_graph
#print axioms YMGap.Continuum.Z4ParametricPhysicalCutoffPartition.anchorParametricPartition_one_eqv_graph
#print axioms YMGap.Continuum.Z4ParametricPhysicalCutoffPartition.anchorParametricCutoffIncrement_le_two_halfPow
#print axioms YMGap.Continuum.Z4ParametricPhysicalCutoffPartition.anchorParametricPartition_relative_cutoff_le_two_halfPow
#print axioms YMGap.Continuum.Z4ParametricPhysicalCutoffPartition.anchorParametricCutoffPartitionLimit
