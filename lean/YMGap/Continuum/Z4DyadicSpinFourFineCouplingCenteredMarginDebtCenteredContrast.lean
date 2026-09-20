/-
# Constant-shift compiler for centered fine-source debt

The centered source debt has exact total mass zero.  This module isolates the
generic algebraic consequence that any constant reference level may be
subtracted from the output contrast before estimating the signed average.
The concrete four-cell adapter keeps the literal pushed source-pair carrier
and the same source debt; it does not supply a nonconstant oscillation bound.

Constructive contract: finite list sums and rational setoid algebra only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtPullback

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtCenteredContrast

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtPullback

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
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

private theorem mul_sub_factor_local (factor left right : Q') :
    factor * left - factor * right ≈ factor * (left - right) := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_neg_eqv factor right))
  · exact Q'.eqv_symm (Q'.mul_add_eqv factor left (-right))

/-- Generic exact shift invariance for a zero-total signed source weight. -/
theorem listQSum_mul_contrast_eqv_centered
    {A : Type} (items : List A) (debt contrast : A → Q')
    (constant : Q')
    (hzero : listQSum debt items ≈ 0) :
    listQSum (fun item => debt item * contrast item) items ≈
      listQSum (fun item => debt item * (contrast item - constant)) items := by
  have hconstant :
      listQSum (fun item => debt item * constant) items ≈ 0 := by
    exact Q'.eqv_trans _ (listQSum debt items * constant) _
      (listQSum_mul_right debt constant items)
      (Q'.eqv_trans _ (0 * constant) _
        (Q'.mul_eqv_congr_right _ _ constant hzero)
        (Q'.zero_mul_eqv constant))
  have hsub :
      listQSum (fun item => debt item * contrast item) items -
          listQSum (fun item => debt item * constant) items ≈
        listQSum
          (fun item => debt item * contrast item -
            debt item * constant) items := by
    exact listQSum_sub_local _ _ items
  have hresidual :
      listQSum
          (fun item => debt item * contrast item -
            debt item * constant) items ≈
        listQSum
          (fun item => debt item * (contrast item - constant)) items := by
    apply listQSum_congr_on
    intro item _
    exact mul_sub_factor_local (debt item) (contrast item) constant
  have hremove :
      listQSum (fun item => debt item * contrast item) items ≈
        listQSum (fun item => debt item * contrast item) items -
          listQSum (fun item => debt item * constant) items := by
    have hsubtract :
        listQSum (fun item => debt item * contrast item) items -
            listQSum (fun item => debt item * constant) items ≈
          listQSum (fun item => debt item * contrast item) items := by
      change
        listQSum (fun item => debt item * contrast item) items +
            -(listQSum (fun item => debt item * constant) items) ≈
          listQSum (fun item => debt item * contrast item) items
      refine Q'.eqv_trans _
        (listQSum (fun item => debt item * contrast item) items + (-0)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _ hconstant)
      · exact Q'.eqv_of_eq (Q'.add_zero' _)
    exact Q'.eqv_symm hsubtract
  exact Q'.eqv_trans _
    (listQSum (fun item => debt item * contrast item) items -
      listQSum (fun item => debt item * constant) items) _
    (Q'.eqv_trans _ _ _ hremove (Q'.eqv_refl _))
    (Q'.eqv_trans _ _ _ hsub hresidual)

/-- The centered four-cell output contrast on the literal pushed source-pair
carrier. -/
def fineCouplingPhysicalSourcePairCenteredMarginDebtCenteredContrast
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) (constant : Q') : Q' :=
  listQSum
    (fun sourcePair =>
      fineCouplingPhysicalSourcePairCenteredMarginRawDebt S sourcePair *
        (fineCouplingTwoReplicaFourCellOutputContrast
          K root target sourcePair - constant))
    (pushedPhysicalSourcePairs S)

/-- The physical source-pair cross-average is invariant under subtracting a
constant contrast level. -/
theorem fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_eqv_centered_contrast
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) (constant : Q') :
    fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
        K root target ≈
      fineCouplingPhysicalSourcePairCenteredMarginDebtCenteredContrast
        K root target constant := by
  let sources := pushedPhysicalSourcePairs S
  let debt := fineCouplingPhysicalSourcePairCenteredMarginRawDebt S
  let contrast := fun sourcePair =>
    fineCouplingTwoReplicaFourCellOutputContrast K root target sourcePair
  have hzero : listQSum debt sources ≈ 0 := by
    simpa only [sources, debt] using
      (fineCouplingPhysicalSourcePairCenteredMarginRawDebt_total_eqv_zero S)
  have hgeneric := listQSum_mul_contrast_eqv_centered
    sources debt contrast constant hzero
  simpa only [sources, debt, contrast,
    fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage,
    fineCouplingPhysicalSourcePairCenteredMarginDebtCenteredContrast] using
    hgeneric

#print axioms listQSum_mul_contrast_eqv_centered
#print axioms fineCouplingPhysicalSourcePairCenteredMarginDebtCenteredContrast
#print axioms fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_eqv_centered_contrast

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtCenteredContrast
