/-
# Exact coupling-margin factorization of the normalized centered change

The cancellation-preserving normalized recentering leaves one signed raw
numerator.  This module factors its entire dependence on the change from
fine coupling one to the actual fine coupling before any absolute value or
finite-sum estimate is taken:

  centeredChangeNumerator
    = (1 - fineCoupling) * centeredMarginNumerator.

The proof propagates the exact finite geometric identity

  1 - w^n = (1 - w) * geomSum w n

through the corrected-slab term, partition, pushed receiver column, target
pair, signed four-cell cross, and partition square.  The residual centered
margin numerator retains the cross/normalization cancellation and is the
right object for a future volume-uniform quotient estimate.

No bound on that residual numerator is proved here.  In particular, this
does not prove a cutoff- or volume-uniform estimate, an all-cutoff limit, a
continuum measure, OS/GNS reconstruction, a Hamiltonian gap, or the
Yang--Mills mass gap.

Constructive contract: exact finite rational algebra and finite list
congruence only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
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
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering

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

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem one_sub_mul_local (power reference : Q') :
    reference - power * reference ≈
      (1 + -power) * reference := by
  refine Q'.eqv_trans _
    ((1 : Q') * reference + (-power) * reference) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.one_mul_eqv reference))
      (Q'.eqv_symm (Q'.neg_mul_eqv power reference))
  · exact Q'.eqv_symm
      (Q'.add_mul_eqv (1 : Q') (-power) reference)

private theorem sub_mul_right_local (left right factor : Q') :
    left * factor - right * factor ≈
      (left - right) * factor := by
  refine Q'.eqv_trans _
    (left * factor + (-right) * factor) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.neg_mul_eqv right factor))
  · exact Q'.eqv_symm
      (Q'.add_mul_eqv left (-right) factor)

private theorem cross_sub_cross_eqv_loss_difference_local
    (unitSource unitTarget actualSource actualTarget : Q') :
    (unitSource - unitTarget) -
        (actualSource - actualTarget) ≈
      (unitSource - actualSource) -
        (unitTarget - actualTarget) := by
  change
    ((unitSource + -unitTarget) +
        -(actualSource + -actualTarget)) ≈
      (unitSource + -actualSource) +
        -(unitTarget + -actualTarget)
  ring_qeqv

private theorem mul_sub_expand_local (factor left right : Q') :
    factor * (left - right) ≈
      factor * left - factor * right := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _
    (Q'.mul_add_eqv factor left (-right)) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv factor right)

private theorem sub_self_eqv_zero_local (value : Q') :
    value - value ≈ 0 := by
  refine Q'.eqv_trans _ (-value + value) _
    (Q'.add_comm_eqv value (-value)) ?_
  exact Q'.neg_add_self_eqv value

private theorem sum_of_margin_products_eqv_margin_mul_sum_local
    (left actualRight margin rightQuotient leftQuotient : Q') :
    left * (margin * rightQuotient) +
        actualRight * (margin * leftQuotient) ≈
      margin *
        (left * rightQuotient + actualRight * leftQuotient) := by
  ring_qeqv

private theorem centered_change_decomposition_local
    (unitCross actualCross unitSquare actualSquare : Q') :
    unitCross * actualSquare - actualCross * unitSquare ≈
      (unitCross - actualCross) * actualSquare -
        actualCross * (unitSquare - actualSquare) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    ((unitCross * actualSquare - actualCross * actualSquare) -
      (actualCross * unitSquare - actualCross * actualSquare)) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.eqv_symm
        (sub_mul_right_local unitCross actualCross actualSquare))
      (mul_sub_expand_local actualCross unitSquare actualSquare)
  refine Q'.eqv_trans _
    ((unitCross * actualSquare - actualCross * unitSquare) -
      (actualCross * actualSquare - actualCross * actualSquare)) _
    (cross_sub_cross_eqv_loss_difference_local _ _ _ _) ?_
  refine Q'.eqv_trans _
    ((unitCross * actualSquare - actualCross * unitSquare) - 0) _
    (sub_eqv_both_local (Q'.eqv_refl _)
      (sub_self_eqv_zero_local (actualCross * actualSquare))) ?_
  exact Q'.eqv_of_eq
    (Q'.sub_zero'
      (unitCross * actualSquare - actualCross * unitSquare))

private theorem centered_margin_factor_local
    (margin crossQuotient actualSquare actualCross squareQuotient : Q') :
    (margin * crossQuotient) * actualSquare -
        actualCross * (margin * squareQuotient) ≈
      margin *
        (crossQuotient * actualSquare -
          actualCross * squareQuotient) := by
  have hright :
      actualCross * (margin * squareQuotient) ≈
        margin * (actualCross * squareQuotient) := by
    refine Q'.eqv_trans _
      ((actualCross * margin) * squareQuotient) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv actualCross margin squareQuotient)) ?_
    refine Q'.eqv_trans _
      ((margin * actualCross) * squareQuotient) _
      (Q'.mul_eqv_congr_right _ _ squareQuotient
        (Q'.mul_comm_eqv actualCross margin)) ?_
    exact Q'.mul_assoc_eqv margin actualCross squareQuotient
  refine Q'.eqv_trans _
    (margin * (crossQuotient * actualSquare) -
      margin * (actualCross * squareQuotient)) _
    (sub_eqv_both_local
      (Q'.mul_assoc_eqv margin crossQuotient actualSquare)
      hright) ?_
  exact Q'.eqv_symm
    (mul_sub_expand_local margin
      (crossQuotient * actualSquare)
      (actualCross * squareQuotient))

private theorem quadratic_ceiling_regroup_local
    (two g ceiling denominator : Q') :
    (two * (g * g)) * (ceiling * denominator) ≈
      ((two * ceiling) * (g * g)) * denominator := by
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

/-! ## 1. Exact loss of one corrected-slab term -/

/-- The geometric quotient left after removing the common scalar fine
coupling margin from one corrected-slab physical summand. -/
def fineCouplingPhysicalMarginTerm
    (S : SlabScalePair) (source : EdgeLabelling) : Q' :=
  geomSum S.fine.coupling
      (slabPhysicalCasimirExponent S.fine.extent source) *
    fineUnitCouplingPhysicalTerm S source

/-- Exact termwise factorization of the loss from coupling one to the actual
fine coupling.  No sign or small-coupling hypothesis is needed. -/
theorem fineUnitCouplingPhysicalTerm_sub_actual_eqv_margin_mul
    (S : SlabScalePair) (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    fineUnitCouplingPhysicalTerm S source -
        S.fine.physicalTerm source ≈
      (1 + -S.fine.coupling) *
        fineCouplingPhysicalMarginTerm S source := by
  let exponent := slabPhysicalCasimirExponent S.fine.extent source
  let reference := fineUnitCouplingPhysicalTerm S source
  have hbounded : source ∈ boundedEdgeLabellings S.fine.cutoff
      (slabPhysicalFaceEdges S.fine.extent) := by
    simpa only [SlabPhysicalData.physicalLabellings,
      SlabPhysicalData.faceEdges] using hsource
  have hactual :
      S.fine.physicalTerm source ≈
        qpow S.fine.coupling exponent * reference := by
    simpa only [SlabPhysicalData.physicalTerm, exponent, reference,
      fineUnitCouplingPhysicalTerm] using
      (slabParametricKPhysicalTerm_eqv_power_mul_atOne
        S.fine.coupling S.fine.cutoff S.fine.extent source hbounded)
  refine Q'.eqv_trans _
    (reference - qpow S.fine.coupling exponent * reference) _
    (sub_eqv_both_local (Q'.eqv_refl _) hactual) ?_
  refine Q'.eqv_trans _
    ((1 + -(qpow S.fine.coupling exponent)) * reference) _ ?_ ?_
  · exact one_sub_mul_local
      (qpow S.fine.coupling exponent) reference
  refine Q'.eqv_trans _
    (((1 + -S.fine.coupling) *
        geomSum S.fine.coupling exponent) * reference) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ reference
      (oneSub_pow_factor S.fine.coupling exponent)
  · unfold fineCouplingPhysicalMarginTerm
    simp only [exponent, reference]
    exact Q'.mul_assoc_eqv _ _ _

/-! ## 2. Exact partition and pushed-column losses -/

/-- Sum of the termwise geometric quotients on the literal fine carrier. -/
def fineCouplingPhysicalPartitionMarginSum (S : SlabScalePair) : Q' :=
  listQSum (fineCouplingPhysicalMarginTerm S)
    S.fine.physicalLabellings

theorem fineUnitCouplingPhysicalPartition_sub_actual_eqv_margin_mul
    (S : SlabScalePair) :
    fineUnitCouplingPhysicalPartition S -
        S.fine.physicalPartition ≈
      (1 + -S.fine.coupling) *
        fineCouplingPhysicalPartitionMarginSum S := by
  unfold fineUnitCouplingPhysicalPartition
    SlabPhysicalData.physicalPartition
    slabParametricKPhysicalPartition
  refine Q'.eqv_trans _
    (listQSum
      (fun source => fineUnitCouplingPhysicalTerm S source -
        S.fine.physicalTerm source)
      S.fine.physicalLabellings) _
    (listQSum_sub_local _ _ _) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (1 + -S.fine.coupling) *
          fineCouplingPhysicalMarginTerm S source)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_congr_on _ _ _
      (fun source hsource =>
        fineUnitCouplingPhysicalTerm_sub_actual_eqv_margin_mul
          S source hsource)
  · exact Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (1 + -S.fine.coupling)
        (fineCouplingPhysicalMarginTerm S)
        S.fine.physicalLabellings)
      (Q'.eqv_refl _)

/-- Geometric-quotient raw mass delivered to one coarse target. -/
def fineCouplingPushedTargetMarginRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (target : EdgeLabelling) : Q' :=
  listQSum
    (fun source =>
      fineCouplingPhysicalMarginTerm S source * K.kernel source target)
    S.fine.physicalLabellings

theorem fineUnitCouplingPushedTargetRawMass_sub_actual_eqv_margin_mul
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (target : EdgeLabelling) :
    fineUnitCouplingPushedTargetRawMass K target -
        pushedPhysicalTargetRawMass K target ≈
      (1 + -S.fine.coupling) *
        fineCouplingPushedTargetMarginRawMass K target := by
  unfold fineUnitCouplingPushedTargetRawMass
    pushedPhysicalTargetRawMass
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        fineUnitCouplingPhysicalTerm S source * K.kernel source target -
          S.fine.physicalTerm source * K.kernel source target)
      S.fine.physicalLabellings) _
    (listQSum_sub_local _ _ _) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (1 + -S.fine.coupling) *
          (fineCouplingPhysicalMarginTerm S source *
            K.kernel source target))
      S.fine.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    refine Q'.eqv_trans _
      ((fineUnitCouplingPhysicalTerm S source -
          S.fine.physicalTerm source) * K.kernel source target) _ ?_ ?_
    · exact sub_mul_right_local _ _ _
    · refine Q'.eqv_trans _
        (((1 + -S.fine.coupling) *
            fineCouplingPhysicalMarginTerm S source) *
          K.kernel source target) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (fineUnitCouplingPhysicalTerm_sub_actual_eqv_margin_mul
            S source hsource)
      · exact Q'.mul_assoc_eqv _ _ _
  · exact Q'.eqv_trans _ _ _
      (listQSum_mul_left
        (1 + -S.fine.coupling)
        (fun source =>
          fineCouplingPhysicalMarginTerm S source *
            K.kernel source target)
        S.fine.physicalLabellings)
      (Q'.eqv_refl _)

/-! ## 3. Exact pair and four-cell cross losses -/

/-- Product-rule quotient for the loss in one pushed target-pair mass. -/
def fineCouplingPushedTargetPairMarginRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  fineUnitCouplingPushedTargetRawMass K pair.1 *
      fineCouplingPushedTargetMarginRawMass K pair.2 +
    pushedPhysicalTargetRawMass K pair.2 *
      fineCouplingPushedTargetMarginRawMass K pair.1

theorem fineUnitCouplingPushedTargetPairRawMass_sub_actual_eqv_margin_mul
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (pair : EdgeLabelling × EdgeLabelling) :
    fineUnitCouplingPushedTargetPairRawMass K pair -
        pushedPhysicalTargetPairRawMass K pair ≈
      (1 + -S.fine.coupling) *
        fineCouplingPushedTargetPairMarginRawMass K pair := by
  let unitLeft := fineUnitCouplingPushedTargetRawMass K pair.1
  let unitRight := fineUnitCouplingPushedTargetRawMass K pair.2
  let actualLeft := pushedPhysicalTargetRawMass K pair.1
  let actualRight := pushedPhysicalTargetRawMass K pair.2
  let margin := 1 + -S.fine.coupling
  let leftQuotient := fineCouplingPushedTargetMarginRawMass K pair.1
  let rightQuotient := fineCouplingPushedTargetMarginRawMass K pair.2
  have hleft : unitLeft - actualLeft ≈ margin * leftQuotient := by
    simpa only [unitLeft, actualLeft, margin, leftQuotient] using
      (fineUnitCouplingPushedTargetRawMass_sub_actual_eqv_margin_mul
        K pair.1)
  have hright : unitRight - actualRight ≈ margin * rightQuotient := by
    simpa only [unitRight, actualRight, margin, rightQuotient] using
      (fineUnitCouplingPushedTargetRawMass_sub_actual_eqv_margin_mul
        K pair.2)
  refine Q'.eqv_trans _
    (unitLeft * (unitRight - actualRight) +
      actualRight * (unitLeft - actualLeft)) _ ?_ ?_
  · simpa only [fineUnitCouplingPushedTargetPairRawMass,
        pushedPhysicalTargetPairRawMass, unitLeft, unitRight,
        actualLeft, actualRight] using
      (CReal.mul_sub_decomp unitLeft unitRight actualLeft actualRight)
  refine Q'.eqv_trans _
    (unitLeft * (margin * rightQuotient) +
      actualRight * (margin * leftQuotient)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left unitLeft _ _ hright)
      (Q'.mul_eqv_congr_left actualRight _ _ hleft)
  · unfold fineCouplingPushedTargetPairMarginRawMass
    simp only [unitLeft, actualRight, margin, leftQuotient, rightQuotient]
    exact sum_of_margin_products_eqv_margin_mul_sum_local
      unitLeft actualRight margin rightQuotient leftQuotient

/-- Four-cell quotient on the source (`TT x FF`) pair carrier. -/
def fineCouplingPushedFourCellSourceMarginRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (fineCouplingPushedTargetPairMarginRawMass K)
    (pushedFaceRawFourCellSourcePairs (S := S) root target)

/-- Four-cell quotient on the opposite (`FT x TF`) pair carrier. -/
def fineCouplingPushedFourCellTargetMarginRawMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (fineCouplingPushedTargetPairMarginRawMass K)
    (pushedFaceRawFourCellTargetPairs (S := S) root target)

theorem fineUnitCouplingPushedFourCellSourceRawMass_sub_actual_eqv_margin_mul
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingPushedFourCellSourceRawMass K root target -
        listQSum (pushedPhysicalTargetPairRawMass K)
          (pushedFaceRawFourCellSourcePairs (S := S) root target) ≈
      (1 + -S.fine.coupling) *
        fineCouplingPushedFourCellSourceMarginRawMass K root target := by
  unfold fineUnitCouplingPushedFourCellSourceRawMass
    fineCouplingPushedFourCellSourceMarginRawMass
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        fineUnitCouplingPushedTargetPairRawMass K pair -
          pushedPhysicalTargetPairRawMass K pair)
      (pushedFaceRawFourCellSourcePairs (S := S) root target)) _
    (listQSum_sub_local _ _ _) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        (1 + -S.fine.coupling) *
          fineCouplingPushedTargetPairMarginRawMass K pair)
      (pushedFaceRawFourCellSourcePairs (S := S) root target)) _ ?_ ?_
  · apply listQSum_congr_on
    intro pair _
    exact fineUnitCouplingPushedTargetPairRawMass_sub_actual_eqv_margin_mul
      K pair
  · exact listQSum_mul_left _ _ _

theorem fineUnitCouplingPushedFourCellTargetRawMass_sub_actual_eqv_margin_mul
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingPushedFourCellTargetRawMass K root target -
        listQSum (pushedPhysicalTargetPairRawMass K)
          (pushedFaceRawFourCellTargetPairs (S := S) root target) ≈
      (1 + -S.fine.coupling) *
        fineCouplingPushedFourCellTargetMarginRawMass K root target := by
  unfold fineUnitCouplingPushedFourCellTargetRawMass
    fineCouplingPushedFourCellTargetMarginRawMass
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        fineUnitCouplingPushedTargetPairRawMass K pair -
          pushedPhysicalTargetPairRawMass K pair)
      (pushedFaceRawFourCellTargetPairs (S := S) root target)) _
    (listQSum_sub_local _ _ _) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        (1 + -S.fine.coupling) *
          fineCouplingPushedTargetPairMarginRawMass K pair)
      (pushedFaceRawFourCellTargetPairs (S := S) root target)) _ ?_ ?_
  · apply listQSum_congr_on
    intro pair _
    exact fineUnitCouplingPushedTargetPairRawMass_sub_actual_eqv_margin_mul
      K pair
  · exact listQSum_mul_left _ _ _

/-- Signed quotient for the exact loss of the pushed four-cell cross. -/
def fineCouplingPushedRawColumnCrossMargin
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  fineCouplingPushedFourCellSourceMarginRawMass K root target -
    fineCouplingPushedFourCellTargetMarginRawMass K root target

theorem fineUnitCouplingPushedRawColumnCross_sub_actual_eqv_margin_mul
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingPushedRawColumnCross K root target -
        pushedFaceRawFourCellCross K root target ≈
      (1 + -S.fine.coupling) *
        fineCouplingPushedRawColumnCrossMargin K root target := by
  let sourceActual :=
    listQSum (pushedPhysicalTargetPairRawMass K)
      (pushedFaceRawFourCellSourcePairs (S := S) root target)
  let targetActual :=
    listQSum (pushedPhysicalTargetPairRawMass K)
      (pushedFaceRawFourCellTargetPairs (S := S) root target)
  have hactual : pushedFaceRawFourCellCross K root target ≈
      sourceActual - targetActual := by
    simpa only [sourceActual, targetActual] using
      (pushedFaceRawFourCellCross_eqv_pair_mass_difference
        K root target)
  have hsource :
      fineUnitCouplingPushedFourCellSourceRawMass K root target -
          sourceActual ≈
        (1 + -S.fine.coupling) *
          fineCouplingPushedFourCellSourceMarginRawMass K root target := by
    simpa only [sourceActual] using
      (fineUnitCouplingPushedFourCellSourceRawMass_sub_actual_eqv_margin_mul
        K root target)
  have htarget :
      fineUnitCouplingPushedFourCellTargetRawMass K root target -
          targetActual ≈
        (1 + -S.fine.coupling) *
          fineCouplingPushedFourCellTargetMarginRawMass K root target := by
    simpa only [targetActual] using
      (fineUnitCouplingPushedFourCellTargetRawMass_sub_actual_eqv_margin_mul
        K root target)
  refine Q'.eqv_trans _
    ((fineUnitCouplingPushedFourCellSourceRawMass K root target -
        sourceActual) -
      (fineUnitCouplingPushedFourCellTargetRawMass K root target -
        targetActual)) _ ?_ ?_
  · unfold fineUnitCouplingPushedRawColumnCross
    refine Q'.eqv_trans _
      ((fineUnitCouplingPushedFourCellSourceRawMass K root target -
          fineUnitCouplingPushedFourCellTargetRawMass K root target) -
        (sourceActual - targetActual)) _
      (sub_eqv_both_local (Q'.eqv_refl _) hactual) ?_
    exact cross_sub_cross_eqv_loss_difference_local _ _ _ _
  refine Q'.eqv_trans _
    (((1 + -S.fine.coupling) *
        fineCouplingPushedFourCellSourceMarginRawMass K root target) -
      ((1 + -S.fine.coupling) *
        fineCouplingPushedFourCellTargetMarginRawMass K root target)) _
    (sub_eqv_both_local hsource htarget) ?_
  · unfold fineCouplingPushedRawColumnCrossMargin
    exact Q'.eqv_symm
      (mul_sub_expand_local
        (1 + -S.fine.coupling)
        (fineCouplingPushedFourCellSourceMarginRawMass K root target)
        (fineCouplingPushedFourCellTargetMarginRawMass K root target))

/-! ## 4. The normalized centered numerator -/

/-- Product-rule quotient for the exact loss of the fine partition square. -/
def fineCouplingPhysicalPartitionSquareMargin (S : SlabScalePair) : Q' :=
  fineUnitCouplingPhysicalPartition S *
      fineCouplingPhysicalPartitionMarginSum S +
    S.fine.physicalPartition *
      fineCouplingPhysicalPartitionMarginSum S

theorem fineUnitCouplingPhysicalPartitionSquare_sub_actual_eqv_margin_mul
    (S : SlabScalePair) :
    fineUnitCouplingPhysicalPartition S *
          fineUnitCouplingPhysicalPartition S -
        S.fine.physicalPartition * S.fine.physicalPartition ≈
      (1 + -S.fine.coupling) *
        fineCouplingPhysicalPartitionSquareMargin S := by
  let unitPartition := fineUnitCouplingPhysicalPartition S
  let actualPartition := S.fine.physicalPartition
  let margin := 1 + -S.fine.coupling
  let quotient := fineCouplingPhysicalPartitionMarginSum S
  have hpartition : unitPartition - actualPartition ≈
      margin * quotient := by
    simpa only [unitPartition, actualPartition, margin, quotient] using
      (fineUnitCouplingPhysicalPartition_sub_actual_eqv_margin_mul S)
  refine Q'.eqv_trans _
    (unitPartition * (unitPartition - actualPartition) +
      actualPartition * (unitPartition - actualPartition)) _ ?_ ?_
  · exact CReal.mul_sub_decomp
      unitPartition unitPartition actualPartition actualPartition
  refine Q'.eqv_trans _
    (unitPartition * (margin * quotient) +
      actualPartition * (margin * quotient)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left unitPartition _ _ hpartition)
      (Q'.mul_eqv_congr_left actualPartition _ _ hpartition)
  · unfold fineCouplingPhysicalPartitionSquareMargin
    simp only [unitPartition, actualPartition, margin, quotient]
    exact sum_of_margin_products_eqv_margin_mul_sum_local
      unitPartition actualPartition margin quotient quotient

/-- Cancellation-preserving quotient left after extracting the common fine
coupling margin from the normalized centered change numerator. -/
def fineUnitCouplingCenteredNormalizedMarginNumerator
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  fineCouplingPushedRawColumnCrossMargin K root target *
      (S.fine.physicalPartition * S.fine.physicalPartition) -
    pushedFaceRawFourCellCross K root target *
      fineCouplingPhysicalPartitionSquareMargin S

/-- The full normalized centered change numerator has one exact scalar
factor `1 - fineCoupling`; all remaining cancellation stays inside the
displayed margin numerator. -/
theorem fineUnitCouplingCenteredNormalizedChangeNumerator_eqv_margin_mul
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingCenteredNormalizedChangeNumerator K root target ≈
      (1 + -S.fine.coupling) *
        fineUnitCouplingCenteredNormalizedMarginNumerator
          K root target := by
  let unitCross := fineUnitCouplingPushedRawColumnCross K root target
  let actualCross := pushedFaceRawFourCellCross K root target
  let unitSquare := fineUnitCouplingPhysicalPartition S *
    fineUnitCouplingPhysicalPartition S
  let actualSquare := S.fine.physicalPartition *
    S.fine.physicalPartition
  let margin := 1 + -S.fine.coupling
  let crossQuotient :=
    fineCouplingPushedRawColumnCrossMargin K root target
  let squareQuotient := fineCouplingPhysicalPartitionSquareMargin S
  have hcross : unitCross - actualCross ≈
      margin * crossQuotient := by
    simpa only [unitCross, actualCross, margin, crossQuotient] using
      (fineUnitCouplingPushedRawColumnCross_sub_actual_eqv_margin_mul
        K root target)
  have hsquare : unitSquare - actualSquare ≈
      margin * squareQuotient := by
    simpa only [unitSquare, actualSquare, margin, squareQuotient] using
      (fineUnitCouplingPhysicalPartitionSquare_sub_actual_eqv_margin_mul S)
  unfold fineUnitCouplingCenteredNormalizedChangeNumerator
  change unitCross * actualSquare - actualCross * unitSquare ≈ _
  refine Q'.eqv_trans _
    ((unitCross - actualCross) * actualSquare -
      actualCross * (unitSquare - actualSquare)) _ ?_ ?_
  · exact centered_change_decomposition_local
      unitCross actualCross unitSquare actualSquare
  refine Q'.eqv_trans _
    ((margin * crossQuotient) * actualSquare -
      actualCross * (margin * squareQuotient)) _
    (sub_eqv_both_local
      (Q'.mul_eqv_congr_right _ _ actualSquare hcross)
      (Q'.mul_eqv_congr_left actualCross _ _ hsquare)) ?_
  unfold fineUnitCouplingCenteredNormalizedMarginNumerator
  simp only [actualCross, actualSquare, margin, crossQuotient,
    squareQuotient]
  exact centered_margin_factor_local
    margin crossQuotient actualSquare actualCross squareQuotient

/-! ## 5. The remaining quotient calibration and matched-AF compiler -/

/-- A dimensionless bound on the cancellation-preserving margin numerator,
relative to the positive common normalization denominator.  This is the
remaining analytic producer: no inhabitant or volume-uniform ceiling is
asserted by the definition. -/
def FineUnitCouplingCenteredNormalizedMarginRawCalibration
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (marginCeiling : Q') : Prop :=
  Q'.abs
      (fineUnitCouplingCenteredNormalizedMarginNumerator
        K M.coarseRoot M.coarseTarget) ≤
    marginCeiling *
      fineUnitCouplingCenteredNormalizedChangeDenominator S

/-- Once the residual quotient has a nonnegative ceiling, the physical
matched-AF upper margin `1 - w <= 2 g^2` compiles it into the existing raw
quadratic centered-change calibration.  The theorem exposes exactly which
uniform estimate remains missing. -/
theorem fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_margin
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g marginCeiling : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (hmarginCeiling : (0 : Q') ≤ marginCeiling)
    (hcalibration :
      FineUnitCouplingCenteredNormalizedMarginRawCalibration
        K M marginCeiling) :
    FineUnitCouplingCenteredNormalizedChangeRawCalibration
      K M g (Q'.ofNat 2 * marginCeiling) := by
  let margin := 1 + -S.fine.coupling
  let quotient :=
    fineUnitCouplingCenteredNormalizedMarginNumerator
      K M.coarseRoot M.coarseTarget
  let denominator :=
    fineUnitCouplingCenteredNormalizedChangeDenominator S
  have hg0 : (0 : Q') ≤ g := Q'.le_of_lt hg
  have hsquare0 : (0 : Q') ≤ g * g :=
    Q'.mul_nonneg g g hg0 hg0
  have hhalfSquare0 : (0 : Q') ≤ half * (g * g) :=
    Q'.mul_nonneg half (g * g) (by decide) hsquare0
  have hlower : half * (g * g) ≤ margin := by
    simpa only [margin, blockedMargin, hcoupling] using
      (blockedMargin_ge_half_square family law g hg hgle)
  have hmargin0 : (0 : Q') ≤ margin :=
    Q'.le_trans' _ _ _ hhalfSquare0 hlower
  have hupper : margin ≤ Q'.ofNat 2 * (g * g) := by
    simpa only [margin, blockedMargin, hcoupling] using
      (blockedMargin_le_two_square family law g hg hgle)
  have hdenominator0 : (0 : Q') ≤ denominator :=
    Q'.le_of_lt
      (by simpa only [denominator] using
        (fineUnitCouplingCenteredNormalizedChangeDenominator_pos S))
  have hbudget0 : (0 : Q') ≤ marginCeiling * denominator :=
    Q'.mul_nonneg marginCeiling denominator
      hmarginCeiling hdenominator0
  have hquotient : Q'.abs quotient ≤ marginCeiling * denominator := by
    simpa only [quotient, denominator,
      FineUnitCouplingCenteredNormalizedMarginRawCalibration] using
      hcalibration
  have habsProduct :
      Q'.abs (margin * quotient) ≤ margin * Q'.abs quotient := by
    refine Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le margin quotient) ?_
    exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ (Q'.abs quotient)
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hmargin0))
  have hmarginTimesQuotient :
      margin * Q'.abs quotient ≤
        margin * (marginCeiling * denominator) :=
    Q'.mul_le_mul_of_nonneg_left _ _ margin
      hquotient hmargin0
  have hquadratic :
      margin * (marginCeiling * denominator) ≤
        (Q'.ofNat 2 * (g * g)) *
          (marginCeiling * denominator) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hupper hbudget0
  unfold FineUnitCouplingCenteredNormalizedChangeRawCalibration
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (fineUnitCouplingCenteredNormalizedChangeNumerator_eqv_margin_mul
          K M.coarseRoot M.coarseTarget))) ?_
  refine Q'.le_trans' _ _ _ habsProduct ?_
  refine Q'.le_trans' _ _ _ hmarginTimesQuotient ?_
  refine Q'.le_trans' _ _ _ hquadratic ?_
  exact Q'.le_of_eqv
    (quadratic_ceiling_regroup_local
      (Q'.ofNat 2) g marginCeiling denominator)

#print axioms fineUnitCouplingPhysicalTerm_sub_actual_eqv_margin_mul
#print axioms fineUnitCouplingPhysicalPartition_sub_actual_eqv_margin_mul
#print axioms fineUnitCouplingPushedTargetRawMass_sub_actual_eqv_margin_mul
#print axioms fineUnitCouplingPushedTargetPairRawMass_sub_actual_eqv_margin_mul
#print axioms fineUnitCouplingPushedFourCellSourceRawMass_sub_actual_eqv_margin_mul
#print axioms fineUnitCouplingPushedFourCellTargetRawMass_sub_actual_eqv_margin_mul
#print axioms fineUnitCouplingPushedRawColumnCross_sub_actual_eqv_margin_mul
#print axioms fineUnitCouplingPhysicalPartitionSquare_sub_actual_eqv_margin_mul
#print axioms fineUnitCouplingCenteredNormalizedChangeNumerator_eqv_margin_mul
#print axioms FineUnitCouplingCenteredNormalizedMarginRawCalibration
#print axioms fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_margin

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
