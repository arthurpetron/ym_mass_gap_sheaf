/-
# Symmetric two-face gradient of the connected refresh observable

The connected refresh observable is not three unrelated cylinders.  If

  `F(a,b) = -a*b + beta*a + gamma*b`,

then its exact denominator-cleared two-point difference is

  `2 * (F(a,b) - F(a',b'))`
    `= (a-a') * (2*beta - b-b')`
    `+ (b-b') * (2*gamma - a-a')`.

The two symmetric doubled gradients have absolute value at most two because
the moments and Boolean sums lie in `[0,2]`.  This preserves the three-term
vacuum cancellation while reducing the observable variation to the two
one-face differences already controlled by the connected packet geometry.

This is the pointwise algebraic bridge only.  No finite-source summation,
posterior-variance bound for the connected observable, dense form bound,
completed gap, thermodynamic limit, continuum theory, or Clay theorem is
asserted here.

Constructive contract: rational order and the kernel-proved reflective
polynomial normalizer only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalPosteriorVarianceFraction
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Symmetric doubled Boolean gradients -/

/-- The symmetric sum of the two target-face bits. -/
def connectedRemainderTargetBitSum
    {S : SlabScalePair} (M : SlabFaceBlockMap S)
    (left right : SlabLabelling) : Q' :=
  booleanEventIndicator
      (slabPhysicalFacePositiveB M.coarseTarget) left +
    booleanEventIndicator
      (slabPhysicalFacePositiveB M.coarseTarget) right

/-- The symmetric sum of the two root-face bits. -/
def connectedRemainderRootBitSum
    {S : SlabScalePair} (M : SlabFaceBlockMap S)
    (left right : SlabLabelling) : Q' :=
  booleanEventIndicator
      (slabPhysicalFacePositiveB M.coarseRoot) left +
    booleanEventIndicator
      (slabPhysicalFacePositiveB M.coarseRoot) right

/-- Denominator-cleared symmetric gradient in the root-face coordinate. -/
def connectedRemainderRootDoubledSymmetricGradient
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (left right : SlabLabelling) : Q' :=
  (2 : Q') * blockedFaceMoment K M.coarseTarget +
    -(connectedRemainderTargetBitSum M left right)

/-- Denominator-cleared symmetric gradient in the target-face coordinate. -/
def connectedRemainderTargetDoubledSymmetricGradient
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (left right : SlabLabelling) : Q' :=
  (2 : Q') * coarseFaceMoment K M.coarseRoot +
    -(connectedRemainderRootBitSum M left right)

private theorem symmetricBooleanSum_twoInterval
    {A : Type} (event : A → Bool) (left right : A) :
    (0 : Q') ≤
        booleanEventIndicator event left +
          booleanEventIndicator event right ∧
      booleanEventIndicator event left +
          booleanEventIndicator event right ≤ (2 : Q') := by
  cases hleft : event left <;> cases hright : event right <;>
    simp only [booleanEventIndicator, hleft, hright,
      Bool.false_eq_true, if_false, if_true] <;> decide

private theorem twice_unitInterval
    (value : Q') (hvalue : (0 : Q') ≤ value ∧ value ≤ (1 : Q')) :
    (0 : Q') ≤ (2 : Q') * value ∧
      (2 : Q') * value ≤ (2 : Q') := by
  constructor
  · exact Q'.mul_nonneg _ _ (by decide) hvalue.1
  · exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hvalue.2 (by decide))
      (Q'.le_of_eqv (Q'.mul_one_eqv (2 : Q')))

private theorem difference_twoInterval
    (left right : Q')
    (hleft : (0 : Q') ≤ left ∧ left ≤ (2 : Q'))
    (hright : (0 : Q') ≤ right ∧ right ≤ (2 : Q')) :
    (-(2 : Q')) ≤ left + (-right) ∧
      left + (-right) ≤ (2 : Q') := by
  constructor
  · have hadd := Q'.add_le_add
      (Q'.neg_le_neg hright.2) hleft.1
    rw [Q'.add_zero'] at hadd
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (Q'.add_comm_eqv (-right) left))
  · have hadd := Q'.add_le_add hleft.2
      (Q'.nonpos_neg_of_nonneg hright.1)
    rwa [Q'.add_zero'] at hadd

theorem connectedRemainderRootDoubledSymmetricGradient_abs_le_two
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (left right : SlabLabelling) :
    Q'.abs
        (connectedRemainderRootDoubledSymmetricGradient K M left right) ≤
      (2 : Q') := by
  unfold connectedRemainderRootDoubledSymmetricGradient
  have hbounds := difference_twoInterval
    ((2 : Q') * blockedFaceMoment K M.coarseTarget)
    (connectedRemainderTargetBitSum M left right)
    (twice_unitInterval
      (blockedFaceMoment K M.coarseTarget)
      ⟨blockedFaceMoment_nonnegative K M.coarseTarget,
        blockedFaceMoment_le_one K M.coarseTarget⟩)
    (symmetricBooleanSum_twoInterval
      (slabPhysicalFacePositiveB M.coarseTarget) left right)
  exact Q'.abs_le_of_bounds hbounds.1 hbounds.2

theorem connectedRemainderTargetDoubledSymmetricGradient_abs_le_two
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (left right : SlabLabelling) :
    Q'.abs
        (connectedRemainderTargetDoubledSymmetricGradient K M left right) ≤
      (2 : Q') := by
  unfold connectedRemainderTargetDoubledSymmetricGradient
  have hbounds := difference_twoInterval
    ((2 : Q') * coarseFaceMoment K M.coarseRoot)
    (connectedRemainderRootBitSum M left right)
    (twice_unitInterval
      (coarseFaceMoment K M.coarseRoot)
      ⟨coarseFaceMoment_nonnegative K M.coarseRoot,
        coarseFaceMoment_le_one K M.coarseRoot⟩)
    (symmetricBooleanSum_twoInterval
      (slabPhysicalFacePositiveB M.coarseRoot) left right)
  exact Q'.abs_le_of_bounds hbounds.1 hbounds.2

/-! ## 2. Kernel-checked polynomial identity -/

private def connectedBinaryPolynomial
    (root target beta gamma : PolyExpr) : PolyExpr :=
  .add (.neg (.mul root target))
    (.add (.mul beta root) (.mul gamma target))

private def connectedDoubledGradientLHS : PolyExpr :=
  .mul (.const 2)
    (.add
      (connectedBinaryPolynomial (.var 0) (.var 2) (.var 4) (.var 5))
      (.neg
        (connectedBinaryPolynomial (.var 1) (.var 3) (.var 4) (.var 5))))

private def connectedDoubledGradientRHS : PolyExpr :=
  .add
    (.mul
      (.add (.var 0) (.neg (.var 1)))
      (.add
        (.mul (.const 2) (.var 4))
        (.neg (.add (.var 2) (.var 3)))))
    (.mul
      (.add (.var 2) (.neg (.var 3)))
      (.add
        (.mul (.const 2) (.var 5))
        (.neg (.add (.var 0) (.var 1)))))

private theorem connectedDoubledGradient_normal_eq :
    normalize connectedDoubledGradientLHS =
      normalize connectedDoubledGradientRHS := by decide

private theorem doubledSymmetricBinaryGradientIdentity
    (rootLeft rootRight targetLeft targetRight beta gamma : Q') :
    (2 : Q') *
        ((-(rootLeft * targetLeft) +
            (beta * rootLeft + gamma * targetLeft)) +
          -(-(rootRight * targetRight) +
            (beta * rootRight + gamma * targetRight))) ≈
      (rootLeft + (-rootRight)) *
          ((2 : Q') * beta + -(targetLeft + targetRight)) +
        (targetLeft + (-targetRight)) *
          ((2 : Q') * gamma + -(rootLeft + rootRight)) := by
  let environment : Nat → Q' := fun index =>
    match index with
    | 0 => rootLeft
    | 1 => rootRight
    | 2 => targetLeft
    | 3 => targetRight
    | 4 => beta
    | _ => gamma
  have hid := poly_identity_of_normal_eq
    connectedDoubledGradientLHS connectedDoubledGradientRHS
    connectedDoubledGradient_normal_eq environment
  simpa [eval, connectedDoubledGradientLHS,
    connectedDoubledGradientRHS, connectedBinaryPolynomial,
    qpow, environment] using hid

/-! ## 3. Identify the concrete three-cylinder observable -/

private theorem weightedCylinderObservable_eqv_coefficient_mul_indicator
    (event : SlabLabelling → Bool) (coefficient : Q')
    (state : SlabLabelling) :
    weightedCylinderObservable event coefficient state ≈
      coefficient * booleanEventIndicator event state := by
  cases hevent : event state
  · simp only [weightedCylinderObservable, booleanEventIndicator, hevent,
      Bool.false_eq_true, if_false]
    exact Q'.eqv_symm (Q'.mul_zero_eqv coefficient)
  · simp only [weightedCylinderObservable, booleanEventIndicator, hevent,
      if_true]
    exact Q'.eqv_symm (Q'.mul_one_eqv coefficient)

private theorem facePairIndicator_eqv_mul
    (rootFaceId targetFaceId : Nat) (state : SlabLabelling) :
    booleanEventIndicator
        (slabPhysicalFacePairPositiveB rootFaceId targetFaceId) state ≈
      booleanEventIndicator
          (slabPhysicalFacePositiveB rootFaceId) state *
        booleanEventIndicator
          (slabPhysicalFacePositiveB targetFaceId) state := by
  cases hroot : slabPhysicalFacePositiveB rootFaceId state <;>
    cases htarget : slabPhysicalFacePositiveB targetFaceId state <;>
    simp only [booleanEventIndicator, slabPhysicalFacePairPositiveB,
      hroot, htarget, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, if_false, if_true] <;> decide

private def connectedRemainderBooleanPolynomial
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (state : SlabLabelling) : Q' :=
  -(booleanEventIndicator
        (slabPhysicalFacePositiveB M.coarseRoot) state *
      booleanEventIndicator
        (slabPhysicalFacePositiveB M.coarseTarget) state) +
    (blockedFaceMoment K M.coarseTarget *
        booleanEventIndicator
          (slabPhysicalFacePositiveB M.coarseRoot) state +
      coarseFaceMoment K M.coarseRoot *
        booleanEventIndicator
          (slabPhysicalFacePositiveB M.coarseTarget) state)

private theorem connectedRemainderObservable_eqv_booleanPolynomial
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (state : SlabLabelling) :
    connectedRemainderObservable K M state ≈
      connectedRemainderBooleanPolynomial K M state := by
  let pairEvent := slabPhysicalFacePairPositiveB
    M.coarseRoot M.coarseTarget
  let rootEvent := slabPhysicalFacePositiveB M.coarseRoot
  let targetEvent := slabPhysicalFacePositiveB M.coarseTarget
  let rootBit := booleanEventIndicator rootEvent state
  let targetBit := booleanEventIndicator targetEvent state
  unfold connectedRemainderObservable connectedRemainderBooleanPolynomial
  refine Q'.add_eqv_congr' ?_ (Q'.add_eqv_congr' ?_ ?_)
  · refine Q'.eqv_trans _ ((-1 : Q') *
      booleanEventIndicator pairEvent state) _ ?_ ?_
    · exact weightedCylinderObservable_eqv_coefficient_mul_indicator
        pairEvent (-1) state
    refine Q'.eqv_trans _ ((-1 : Q') * (rootBit * targetBit)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (-1) _ _
        (facePairIndicator_eqv_mul
          M.coarseRoot M.coarseTarget state)
    exact Q'.eqv_trans _ (-(1 * (rootBit * targetBit))) _
      (Q'.neg_mul_eqv 1 (rootBit * targetBit))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))
  · exact weightedCylinderObservable_eqv_coefficient_mul_indicator
      rootEvent (blockedFaceMoment K M.coarseTarget) state
  · exact weightedCylinderObservable_eqv_coefficient_mul_indicator
      targetEvent (coarseFaceMoment K M.coarseRoot) state

/-! ## 4. Exact cancellation-preserving factorization -/

/-- The doubled three-cylinder connected observable difference is exactly the
sum of two symmetric one-face gradients.  No absolute value has been taken
across its joint and marginal cylinder terms. -/
theorem two_mul_connectedRemainderObservable_sub_eqv_symmetricFaceGradients
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (left right : SlabLabelling) :
    (2 : Q') *
        (connectedRemainderObservable K M left +
          -(connectedRemainderObservable K M right)) ≈
      (booleanEventIndicator
            (slabPhysicalFacePositiveB M.coarseRoot) left +
          -(booleanEventIndicator
            (slabPhysicalFacePositiveB M.coarseRoot) right)) *
        connectedRemainderRootDoubledSymmetricGradient K M left right +
      (booleanEventIndicator
            (slabPhysicalFacePositiveB M.coarseTarget) left +
          -(booleanEventIndicator
            (slabPhysicalFacePositiveB M.coarseTarget) right)) *
        connectedRemainderTargetDoubledSymmetricGradient K M left right := by
  unfold connectedRemainderRootDoubledSymmetricGradient
    connectedRemainderTargetDoubledSymmetricGradient
    connectedRemainderTargetBitSum connectedRemainderRootBitSum
  refine Q'.eqv_trans _
    ((2 : Q') *
      (connectedRemainderBooleanPolynomial K M left +
        -(connectedRemainderBooleanPolynomial K M right))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (2 : Q') _ _
      (Q'.add_eqv_congr'
        (connectedRemainderObservable_eqv_booleanPolynomial K M left)
        (Q'.neg_eqv_congr _ _
          (connectedRemainderObservable_eqv_booleanPolynomial K M right)))
  · unfold connectedRemainderBooleanPolynomial
    exact doubledSymmetricBinaryGradientIdentity
      (booleanEventIndicator
        (slabPhysicalFacePositiveB M.coarseRoot) left)
      (booleanEventIndicator
        (slabPhysicalFacePositiveB M.coarseRoot) right)
      (booleanEventIndicator
        (slabPhysicalFacePositiveB M.coarseTarget) left)
      (booleanEventIndicator
        (slabPhysicalFacePositiveB M.coarseTarget) right)
      (blockedFaceMoment K M.coarseTarget)
      (coarseFaceMoment K M.coarseRoot)

/-- If both selected face bits agree, the connected observable agrees.  This
is the exact two-coordinate support statement needed by the later active
carrier split. -/
theorem connectedRemainderObservable_sub_eqv_zero_of_faceBits_eq
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (left right : SlabLabelling)
    (hroot : slabPhysicalFacePositiveB M.coarseRoot left =
      slabPhysicalFacePositiveB M.coarseRoot right)
    (htarget : slabPhysicalFacePositiveB M.coarseTarget left =
      slabPhysicalFacePositiveB M.coarseTarget right) :
    connectedRemainderObservable K M left +
        -(connectedRemainderObservable K M right) ≈ 0 := by
  have htwice :=
    two_mul_connectedRemainderObservable_sub_eqv_symmetricFaceGradients
      K M left right
  have hrootIndicator :
      booleanEventIndicator
          (slabPhysicalFacePositiveB M.coarseRoot) left =
        booleanEventIndicator
          (slabPhysicalFacePositiveB M.coarseRoot) right := by
    unfold booleanEventIndicator
    rw [hroot]
  have htargetIndicator :
      booleanEventIndicator
          (slabPhysicalFacePositiveB M.coarseTarget) left =
        booleanEventIndicator
          (slabPhysicalFacePositiveB M.coarseTarget) right := by
    unfold booleanEventIndicator
    rw [htarget]
  rw [hrootIndicator, htargetIndicator] at htwice
  have hrootZero := Q'.add_neg_self_eqv
    (booleanEventIndicator
      (slabPhysicalFacePositiveB M.coarseRoot) right)
  have htargetZero := Q'.add_neg_self_eqv
    (booleanEventIndicator
      (slabPhysicalFacePositiveB M.coarseTarget) right)
  have hrhsZero :
      (booleanEventIndicator
            (slabPhysicalFacePositiveB M.coarseRoot) right +
          -(booleanEventIndicator
            (slabPhysicalFacePositiveB M.coarseRoot) right)) *
          connectedRemainderRootDoubledSymmetricGradient K M left right +
        (booleanEventIndicator
            (slabPhysicalFacePositiveB M.coarseTarget) right +
          -(booleanEventIndicator
            (slabPhysicalFacePositiveB M.coarseTarget) right)) *
          connectedRemainderTargetDoubledSymmetricGradient K M left right ≈
        0 := by
    refine Q'.eqv_trans _ (0 *
        connectedRemainderRootDoubledSymmetricGradient K M left right +
      0 * connectedRemainderTargetDoubledSymmetricGradient K M left right) _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ hrootZero)
        (Q'.mul_eqv_congr_right _ _ _ htargetZero)) ?_
    refine Q'.eqv_trans _ (0 + 0) _
      (Q'.add_eqv_congr'
        (Q'.zero_mul_eqv _)
        (Q'.zero_mul_eqv _)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' 0)
  apply Q'.mul_eqv_zero_of_pos (Q'.ofNat_succ_pos 1)
  exact Q'.eqv_trans _ _ _ htwice hrhsZero

/-! ## 5. Axiom audit -/

#print axioms connectedRemainderTargetBitSum
#print axioms connectedRemainderRootBitSum
#print axioms connectedRemainderRootDoubledSymmetricGradient
#print axioms connectedRemainderTargetDoubledSymmetricGradient
#print axioms connectedRemainderRootDoubledSymmetricGradient_abs_le_two
#print axioms connectedRemainderTargetDoubledSymmetricGradient_abs_le_two
#print axioms two_mul_connectedRemainderObservable_sub_eqv_symmetricFaceGradients
#print axioms connectedRemainderObservable_sub_eqv_zero_of_faceBits_eq

end YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradient
