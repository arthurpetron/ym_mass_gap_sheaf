/-
# Fine-coupling reference perturbation for the literal pushed columns

The cancellation-preserving receiver reduction leaves one aggregate
comparison between coarse Gibbs four-cell masses and products of literal
one-replica pushed columns.  This module exposes exactly how the fine heat
nome enters those columns.

For every bounded corrected-slab physical labelling, the complete production
summand at coupling `w` is the coupling-one summand multiplied by

  w ^ (sum of the face Casimirs).

On `0 <= w <= 1`, Bernoulli's inequality therefore bounds the loss from the
coupling-one reference by `(1-w)` times an explicit Casimir-weighted reference
summand.  Positivity of the literal finite block kernel transports that
estimate to every pushed receiver column and to the total fine partition.

This is a genuine finite perturbation theorem, not the missing uniform
analytic estimate.  The exposed Casimir moment can grow with the slab volume,
and no coupling-one stationarity identity is asserted.  Consequently this
module proves neither the aggregate receiver raw-column `K*g^2` calibration,
all-cutoff persistence, a continuum measure, OS/GNS reconstruction, a
Hamiltonian gap, nor the Yang--Mills mass gap.

Constructive contract: structural induction over finite products and sums,
exact rational algebra, positivity, and Bernoulli's inequality only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration
import YMGap.Continuum.R1CornerAtoms

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.R1CornerAtoms
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_four_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  ring_qeqv

private theorem margin_casimir_regroup_local (margin casimir term : Q') :
    (casimir * margin) * term ≈ margin * (casimir * term) := by
  ring_qeqv

private theorem listQSum_neg_local {A : Type}
    (value : A → Q') : ∀ items : List A,
    listQSum (fun item => -(value item)) items ≈
      -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local value tail)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum left items - listQSum right items ≈
      listQSum (fun item => left item - right item) items := by
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (listQSum left items +
        listQSum (fun item => -(right item)) items) _
      (listQSum_add left (fun item => -(right item)) items)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (listQSum_neg_local right items)))

private theorem listQSum_mono_local {A : Type}
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. Exact coupling factorization of one corrected-slab term -/

/-- Total heat-kernel Casimir exponent on a displayed list of slab faces. -/
def slabPhysicalCasimirExponentOn
    (physical : EdgeLabelling) : List Nat → Nat
  | [] => 0
  | faceId :: rest =>
      c4 (physical faceId) +
        slabPhysicalCasimirExponentOn physical rest

/-- Total heat-kernel Casimir exponent of a corrected-slab labelling. -/
def slabPhysicalCasimirExponent
    (extent : Nat) (physical : EdgeLabelling) : Nat :=
  slabPhysicalCasimirExponentOn physical
    (slabPhysicalFaceEdges extent)

private theorem qpow_one_eqv_one_local : ∀ exponent : Nat,
    qpow (1 : Q') exponent ≈ 1
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      change qpow (1 : Q') exponent * 1 ≈ 1
      exact Q'.eqv_trans _ _ _
        (Q'.mul_one_eqv (qpow (1 : Q') exponent))
        (qpow_one_eqv_one_local exponent)

private theorem slabCoefficient_eqv_power_mul_atOne
    (w : Q') (K : Nat) (physical : EdgeLabelling)
    {faceId : Nat} (hspin : physical faceId < K + 1) :
    coeffAt (heatKernelPacket K w) (physical faceId) ≈
      qpow w (c4 (physical faceId)) *
        coeffAt (heatKernelPacket K 1) (physical faceId) := by
  rw [coeffAt_heatKernelPacket hspin,
    coeffAt_heatKernelPacket hspin]
  show dimQ (physical faceId) * qpow w (c4 (physical faceId)) ≈
    qpow w (c4 (physical faceId)) *
      (dimQ (physical faceId) *
        qpow (1 : Q') (c4 (physical faceId)))
  have href :
      dimQ (physical faceId) *
          qpow (1 : Q') (c4 (physical faceId)) ≈
        dimQ (physical faceId) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (dimQ (physical faceId)) _ _
        (qpow_one_eqv_one_local (c4 (physical faceId))))
      (Q'.mul_one_eqv (dimQ (physical faceId)))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (dimQ (physical faceId))
      (qpow w (c4 (physical faceId))))
    (Q'.mul_eqv_congr_left
      (qpow w (c4 (physical faceId))) _ _
      (Q'.eqv_symm href))

private theorem slabFaceProduct_eqv_power_mul_atOne
    (w : Q') (K : Nat) (physical : EdgeLabelling) :
    ∀ faces : List Nat,
    (∀ faceId, faceId ∈ faces → physical faceId < K + 1) →
      eliminateLinks
          (fun faceId =>
            coeffAt (heatKernelPacket K w) (physical faceId))
          faces ≈
        qpow w (slabPhysicalCasimirExponentOn physical faces) *
          eliminateLinks
            (fun faceId =>
              coeffAt (heatKernelPacket K 1) (physical faceId))
            faces
  | [], _ => by
      change (1 : Q') ≈ qpow w 0 * 1
      rw [qpow_zero]
      exact Q'.eqv_symm (Q'.one_mul_eqv 1)
  | faceId :: rest, hbounded => by
      change
        coeffAt (heatKernelPacket K w) (physical faceId) *
            eliminateLinks
              (fun id => coeffAt (heatKernelPacket K w) (physical id)) rest ≈
          qpow w
              (c4 (physical faceId) +
                slabPhysicalCasimirExponentOn physical rest) *
            (coeffAt (heatKernelPacket K 1) (physical faceId) *
              eliminateLinks
                (fun id => coeffAt (heatKernelPacket K 1) (physical id)) rest)
      have hhead := slabCoefficient_eqv_power_mul_atOne
        w K physical
        (hbounded faceId List.mem_cons_self)
      have htail := slabFaceProduct_eqv_power_mul_atOne
        w K physical rest
        (fun id hid => hbounded id (List.mem_cons_of_mem faceId hid))
      refine Q'.eqv_trans _
        ((qpow w (c4 (physical faceId)) *
            coeffAt (heatKernelPacket K 1) (physical faceId)) *
          (qpow w (slabPhysicalCasimirExponentOn physical rest) *
            eliminateLinks
              (fun id => coeffAt (heatKernelPacket K 1) (physical id)) rest)) _
        (qmul_congr_local hhead htail) ?_
      refine Q'.eqv_trans _
        ((qpow w (c4 (physical faceId)) *
            qpow w (slabPhysicalCasimirExponentOn physical rest)) *
          (coeffAt (heatKernelPacket K 1) (physical faceId) *
            eliminateLinks
              (fun id => coeffAt (heatKernelPacket K 1) (physical id)) rest)) _
        (mul_four_regroup_local _ _ _ _) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (YMGap.Continuum.HeatKernelRGStep.qpow_add w
            (c4 (physical faceId))
            (slabPhysicalCasimirExponentOn physical rest)))

/-- A bounded corrected-slab production term factors exactly into its
coupling-one value and one heat power carrying the sum of all face Casimirs. -/
theorem slabParametricKPhysicalTerm_eqv_power_mul_atOne
    (w : Q') (K extent : Nat) (physical : EdgeLabelling)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) :
    slabParametricKPhysicalTerm w K extent physical ≈
      qpow w (slabPhysicalCasimirExponent extent physical) *
        slabParametricKPhysicalTerm 1 K extent physical := by
  have hsound := boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges extent) physical hphysical
  have hfaces := slabFaceProduct_eqv_power_mul_atOne
    w K physical (slabPhysicalFaceEdges extent) hsound.1
  unfold slabParametricKPhysicalTerm
    slabParametricKPhysicalFaceFactor
    slabPhysicalCasimirExponent
  refine Q'.eqv_trans _
    ((qpow w
        (slabPhysicalCasimirExponentOn physical
          (slabPhysicalFaceEdges extent)) *
        eliminateLinks
          (fun faceId =>
            coeffAt (heatKernelPacket K 1) (physical faceId))
          (slabPhysicalFaceEdges extent)) *
      Q'.ofNat
        (slabExplicitLinkMultiplicityProduct K extent physical)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hfaces
  · exact Q'.mul_assoc_eqv _ _ _

/-! ## 2. First-order loss from the coupling-one reference -/

/-- Bernoulli's inequality converts the exact heat-power factorization into
a termwise first-order coupling-loss bound.  The coefficient is the explicit
total face Casimir of the labelling. -/
theorem slabParametricKPhysicalTerm_atOne_sub_le_casimirMargin
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (K extent : Nat) (physical : EdgeLabelling)
    (hphysical : physical ∈ boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent)) :
    slabParametricKPhysicalTerm 1 K extent physical -
        slabParametricKPhysicalTerm w K extent physical ≤
      (Q'.ofNat (slabPhysicalCasimirExponent extent physical) *
          (1 + -w)) *
        slabParametricKPhysicalTerm 1 K extent physical := by
  let exponent := slabPhysicalCasimirExponent extent physical
  let reference := slabParametricKPhysicalTerm 1 K extent physical
  have hfactor :
      slabParametricKPhysicalTerm w K extent physical ≈
        qpow w exponent * reference := by
    simpa only [exponent, reference] using
      (slabParametricKPhysicalTerm_eqv_power_mul_atOne
        w K extent physical hphysical)
  have hdiff :
      reference - slabParametricKPhysicalTerm w K extent physical ≈
        (1 + -(qpow w exponent)) * reference := by
    refine Q'.eqv_trans _
      (reference - qpow w exponent * reference) _
      (sub_eqv_both_local (Q'.eqv_refl _) hfactor) ?_
    refine Q'.eqv_symm
      (Q'.eqv_trans _
        ((1 : Q') * reference +
          (-(qpow w exponent)) * reference) _
        (Q'.add_mul_eqv
          (1 : Q') (-(qpow w exponent)) reference) ?_)
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv reference)
      (Q'.neg_mul_eqv (qpow w exponent) reference)
  have hreference0 : (0 : Q') ≤ reference :=
    slabParametricKPhysicalTerm_nonnegative
      (by decide : (0 : Q') ≤ (1 : Q')) K extent physical
  have hbernoulli := oneSub_qpow_le hw0 hw1 exponent
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hdiff)
    (Q'.mul_le_mul_of_nonneg_right _ _ reference
      hbernoulli hreference0)

/-! ## 3. Literal pushed-column reference and Casimir moment -/

/-- The fine corrected-slab summand with the same cutoff and geometry but
with heat nome set to one. -/
def fineUnitCouplingPhysicalTerm
    (S : SlabScalePair) (source : EdgeLabelling) : Q' :=
  slabParametricKPhysicalTerm
    1 S.fine.cutoff S.fine.extent source

/-- The corresponding finite coupling-one reference partition on the
literal fine Cartesian carrier. -/
def fineUnitCouplingPhysicalPartition (S : SlabScalePair) : Q' :=
  listQSum (fineUnitCouplingPhysicalTerm S)
    S.fine.physicalLabellings

/-- Coupling-one reference mass pushed through the same literal finite block
kernel to one coarse target. -/
def fineUnitCouplingPushedTargetRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (target : EdgeLabelling) : Q' :=
  listQSum
    (fun source =>
      fineUnitCouplingPhysicalTerm S source * K.kernel source target)
    S.fine.physicalLabellings

/-- Casimir-weighted coupling-one reference mass delivered to one coarse
target.  This is the explicit finite moment exposed by the perturbation
argument; no volume-uniform ceiling is asserted. -/
def fineUnitCouplingPushedTargetCasimirMoment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (target : EdgeLabelling) : Q' :=
  listQSum
    (fun source =>
      (Q'.ofNat
          (slabPhysicalCasimirExponent S.fine.extent source) *
        fineUnitCouplingPhysicalTerm S source) *
          K.kernel source target)
    S.fine.physicalLabellings

/-- Total Casimir-weighted coupling-one reference mass on the fine carrier. -/
def fineUnitCouplingPhysicalCasimirMoment
    (S : SlabScalePair) : Q' :=
  listQSum
    (fun source =>
      Q'.ofNat
          (slabPhysicalCasimirExponent S.fine.extent source) *
        fineUnitCouplingPhysicalTerm S source)
    S.fine.physicalLabellings

/-- The unit-coupling pushed reference has the unit-coupling fine partition
as its total mass. -/
theorem fineUnitCouplingPushedTargetRawMass_total
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    listQSum (fineUnitCouplingPushedTargetRawMass K)
        S.coarse.physicalLabellings ≈
      fineUnitCouplingPhysicalPartition S := by
  unfold fineUnitCouplingPushedTargetRawMass
    fineUnitCouplingPhysicalPartition
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            fineUnitCouplingPhysicalTerm S source *
              K.kernel source target)
          S.coarse.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_swap
      (fun source target =>
        fineUnitCouplingPhysicalTerm S source * K.kernel source target)
      S.fine.physicalLabellings S.coarse.physicalLabellings
  · apply listQSum_congr_on
    intro source hsource
    exact Q'.eqv_trans _
      (fineUnitCouplingPhysicalTerm S source *
        listQSum (K.kernel source) S.coarse.physicalLabellings) _
      (listQSum_mul_left
        (fineUnitCouplingPhysicalTerm S source)
        (K.kernel source) S.coarse.physicalLabellings)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (fineUnitCouplingPhysicalTerm S source) _ _
          (K.row_normalized source hsource))
        (Q'.mul_one_eqv
          (fineUnitCouplingPhysicalTerm S source)))

/-- Positivity of the literal kernel transports the first-order loss bound
to each actual pushed receiver column. -/
theorem fineUnitCouplingPushedTargetRawMass_sub_actual_le_margin_mul_moment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    {target : EdgeLabelling}
    (htarget : target ∈ S.coarse.physicalLabellings) :
    fineUnitCouplingPushedTargetRawMass K target -
        pushedPhysicalTargetRawMass K target ≤
      (1 + -S.fine.coupling) *
        fineUnitCouplingPushedTargetCasimirMoment K target := by
  let referenceTerm := fun source : EdgeLabelling =>
    fineUnitCouplingPhysicalTerm S source * K.kernel source target
  let actualTerm := fun source : EdgeLabelling =>
    S.fine.physicalTerm source * K.kernel source target
  let momentTerm := fun source : EdgeLabelling =>
    (Q'.ofNat
        (slabPhysicalCasimirExponent S.fine.extent source) *
      fineUnitCouplingPhysicalTerm S source) *
        K.kernel source target
  have hsum :
      listQSum (fun source => referenceTerm source - actualTerm source)
          S.fine.physicalLabellings ≤
        listQSum
          (fun source =>
            (1 + -S.fine.coupling) * momentTerm source)
          S.fine.physicalLabellings := by
    apply listQSum_mono_local
    intro source hsource
    have hsourceBound :=
      slabParametricKPhysicalTerm_atOne_sub_le_casimirMargin
        (w := S.fine.coupling) S.fine.coupling_nonnegative
        hfineCoupling_le_one S.fine.cutoff S.fine.extent source
        (by simpa only [SlabPhysicalData.physicalLabellings,
            SlabPhysicalData.faceEdges] using hsource)
    have hkernel0 := K.nonnegative source target hsource htarget
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
      (K.kernel source target) hsourceBound hkernel0
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by
        simp only [referenceTerm, actualTerm,
          fineUnitCouplingPhysicalTerm,
          SlabPhysicalData.physicalTerm]
        exact Q'.eqv_symm (Q'.sub_mul_eqv _ _ _)))
      (Q'.le_trans' _ _ _ hscaled
        (Q'.le_of_eqv (by
          simp only [momentTerm, fineUnitCouplingPhysicalTerm]
          ring_qeqv)))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _
      (listQSum (fun source => referenceTerm source - actualTerm source)
        S.fine.physicalLabellings) _ ?_ ?_))
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv ?_))
  · unfold fineUnitCouplingPushedTargetRawMass
      pushedPhysicalTargetRawMass
    exact listQSum_sub_local referenceTerm actualTerm
      S.fine.physicalLabellings
  · exact Q'.eqv_refl _
  · exact Q'.eqv_trans _
      ((1 + -S.fine.coupling) *
        listQSum momentTerm S.fine.physicalLabellings) _
      (listQSum_mul_left
        (1 + -S.fine.coupling) momentTerm
        S.fine.physicalLabellings)
      (by
        unfold fineUnitCouplingPushedTargetCasimirMoment
        exact Q'.mul_eqv_congr_left _ _ _
          (listQSum_congr_on momentTerm
            (fun source =>
              (Q'.ofNat
                  (slabPhysicalCasimirExponent S.fine.extent source) *
                fineUnitCouplingPhysicalTerm S source) *
                  K.kernel source target)
            S.fine.physicalLabellings
            (fun _ _ => Q'.eqv_refl _)))

/-- Summing the same termwise estimate gives the fine partition loss from its
coupling-one reference. -/
theorem fineUnitCouplingPhysicalPartition_sub_actual_le_margin_mul_moment
    (S : SlabScalePair)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1) :
    fineUnitCouplingPhysicalPartition S -
        S.fine.physicalPartition ≤
      (1 + -S.fine.coupling) *
        fineUnitCouplingPhysicalCasimirMoment S := by
  let referenceTerm := fineUnitCouplingPhysicalTerm S
  let actualTerm := S.fine.physicalTerm
  let momentTerm := fun source : EdgeLabelling =>
    Q'.ofNat
        (slabPhysicalCasimirExponent S.fine.extent source) *
      fineUnitCouplingPhysicalTerm S source
  have hsum :
      listQSum (fun source => referenceTerm source - actualTerm source)
          S.fine.physicalLabellings ≤
        listQSum
          (fun source =>
            (1 + -S.fine.coupling) * momentTerm source)
          S.fine.physicalLabellings := by
    apply listQSum_mono_local
    intro source hsource
    have hsourceBound :=
      slabParametricKPhysicalTerm_atOne_sub_le_casimirMargin
        (w := S.fine.coupling) S.fine.coupling_nonnegative
        hfineCoupling_le_one S.fine.cutoff S.fine.extent source
        (by simpa only [SlabPhysicalData.physicalLabellings,
            SlabPhysicalData.faceEdges] using hsource)
    exact Q'.le_trans' _ _ _ hsourceBound
      (Q'.le_of_eqv (by
        simp only [momentTerm, fineUnitCouplingPhysicalTerm]
        exact margin_casimir_regroup_local _ _ _))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _
      (listQSum (fun source => referenceTerm source - actualTerm source)
        S.fine.physicalLabellings) _ ?_ ?_))
    (Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv ?_))
  · unfold fineUnitCouplingPhysicalPartition
      SlabPhysicalData.physicalPartition
      YMGap.Continuum.Z4HalfTimeReflectionPartition.slabParametricKPhysicalPartition
      SlabPhysicalData.physicalLabellings
      SlabPhysicalData.faceEdges
    exact listQSum_sub_local referenceTerm actualTerm
      (boundedEdgeLabellings S.fine.cutoff
        (slabPhysicalFaceEdges S.fine.extent))
  · exact Q'.eqv_refl _
  · refine Q'.eqv_trans _
      ((1 + -S.fine.coupling) *
        listQSum momentTerm S.fine.physicalLabellings) _
      (listQSum_mul_left
        (1 + -S.fine.coupling) momentTerm
        S.fine.physicalLabellings) ?_
    unfold fineUnitCouplingPhysicalCasimirMoment
    exact Q'.mul_eqv_congr_left _ _ _
      (listQSum_congr_on momentTerm
        (fun source =>
          Q'.ofNat
              (slabPhysicalCasimirExponent S.fine.extent source) *
            fineUnitCouplingPhysicalTerm S source)
        S.fine.physicalLabellings
        (fun _ _ => Q'.eqv_refl _))

#print axioms slabPhysicalCasimirExponent
#print axioms slabParametricKPhysicalTerm_eqv_power_mul_atOne
#print axioms slabParametricKPhysicalTerm_atOne_sub_le_casimirMargin
#print axioms fineUnitCouplingPushedTargetRawMass_total
#print axioms fineUnitCouplingPushedTargetRawMass_sub_actual_le_margin_mul_moment
#print axioms fineUnitCouplingPhysicalPartition_sub_actual_le_margin_mul_moment

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
