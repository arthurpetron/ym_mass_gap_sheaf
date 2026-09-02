/-
# Bound the connected pushed-law remainder by the actual physical L1 norm

The exact centered pushed-law remainder is the signed combination

  -r_joint + r_root * blockedTarget + coarseRoot * r_target.

Both face moments lie in the unit interval, while each selected cylinder
remainder is bounded by the literal total-variation quantity `remainderL1`.
Triangle inequality therefore proves

  |centeredCylinderRemainder| <= 3 * remainderL1.

This separates the active physical transport tail into two standard-looking
producers: the actual raw pullback mismatch and the actual pushed-law `L1`
remainder.  It does not prove that either producer decays with lattice spacing.

Constructive contract: finite rational probability bounds and triangle
inequalities only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalRemainderLocality
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

private theorem abs_mul_le_of_right_unit_interval
    (value probability : Q')
    (hprobabilityNonnegative : (0 : Q') ≤ probability)
    (hprobabilityLeOne : probability ≤ (1 : Q')) :
    Q'.abs (value * probability) ≤ Q'.abs value := by
  refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le value probability) ?_
  refine Q'.le_trans' _
    (Q'.abs value * probability) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.mul_eqv_congr_left (Q'.abs value) _ _
        (Q'.eqv_of_eq
          (ExpNeg.abs_of_nonneg hprobabilityNonnegative)))
  refine Q'.le_trans' _ (Q'.abs value * 1) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg_left _ _ _
      hprobabilityLeOne (Q'.abs_nonneg value)
  exact Q'.le_of_eqv (Q'.mul_one_eqv (Q'.abs value))

/-! ## 1. The two multiplying face moments lie in the unit interval -/

theorem blockedFaceMoment_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (faceId : Nat) :
    (0 : Q') ≤ blockedFaceMoment K faceId := by
  unfold blockedFaceMoment PhysicalKernel.blockedCylinderMass
  exact finiteEventMass_nonnegative
    K.blockedMass S.coarse.physicalLabellings
    (slabPhysicalFacePositiveB faceId)
    (fun _ htarget => K.blockedMass_nonnegative htarget)

theorem blockedFaceMoment_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (faceId : Nat) :
    blockedFaceMoment K faceId ≤ (1 : Q') := by
  unfold blockedFaceMoment PhysicalKernel.blockedCylinderMass
  exact finiteEventMass_le_one
    K.blockedMass S.coarse.physicalLabellings
    (slabPhysicalFacePositiveB faceId)
    (fun _ htarget => K.blockedMass_nonnegative htarget)
    K.blockedMass_total

theorem coarseFaceMoment_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (faceId : Nat) :
    (0 : Q') ≤ coarseFaceMoment K faceId := by
  unfold coarseFaceMoment PhysicalKernel.coarseCylinderMass
  exact finiteEventMass_nonnegative
    S.coarse.normalizedMass S.coarse.physicalLabellings
    (slabPhysicalFacePositiveB faceId)
    (fun target _ => S.coarse.normalizedMass_nonnegative target)

theorem coarseFaceMoment_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (faceId : Nat) :
    coarseFaceMoment K faceId ≤ (1 : Q') := by
  unfold coarseFaceMoment PhysicalKernel.coarseCylinderMass
  exact finiteEventMass_le_one
    S.coarse.normalizedMass S.coarse.physicalLabellings
    (slabPhysicalFacePositiveB faceId)
    (fun target _ => S.coarse.normalizedMass_nonnegative target)
    S.coarse.normalizedMass_total

/-! ## 2. Connected cylinder remainder versus total variation -/

/-- The exact centered pushed-law remainder is bounded by three copies of the
literal physical `L1` remainder.  Retaining the exact signed version upstream
still permits a future cancellation-aware estimate to improve this bound. -/
theorem centeredCylinderRemainder_abs_le_threePhysicalRemainderCost
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    Q'.abs (centeredCylinderRemainder K M) ≤
      threePhysicalRemainderCost K := by
  let joint := facePairCylinderRemainder K M.coarseRoot M.coarseTarget
  let root := faceCylinderRemainder K M.coarseRoot
  let target := faceCylinderRemainder K M.coarseTarget
  let blockedTarget := blockedFaceMoment K M.coarseTarget
  let coarseRoot := coarseFaceMoment K M.coarseRoot
  have hjoint : Q'.abs (-joint) ≤ K.remainderL1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' joint))
      (PhysicalKernel.cylinderRemainder_abs_le_remainderL1 K
        (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget))
  have hroot : Q'.abs (root * blockedTarget) ≤ K.remainderL1 :=
    Q'.le_trans' _ _ _
      (abs_mul_le_of_right_unit_interval root blockedTarget
        (blockedFaceMoment_nonnegative K M.coarseTarget)
        (blockedFaceMoment_le_one K M.coarseTarget))
      (PhysicalKernel.cylinderRemainder_abs_le_remainderL1 K
        (slabPhysicalFacePositiveB M.coarseRoot))
  have htarget : Q'.abs (coarseRoot * target) ≤ K.remainderL1 :=
    Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le coarseRoot target) (by
        refine Q'.le_trans' _
          (coarseRoot * Q'.abs target) _ ?_ ?_
        · exact Q'.le_of_eqv
            (Q'.mul_eqv_congr_right _ _ (Q'.abs target)
              (Q'.eqv_of_eq
                (ExpNeg.abs_of_nonneg
                  (coarseFaceMoment_nonnegative K M.coarseRoot))))
        refine Q'.le_trans' _ (1 * Q'.abs target) _ ?_ ?_
        · exact Q'.mul_le_mul_of_nonneg_right _ _ _
            (coarseFaceMoment_le_one K M.coarseRoot)
            (Q'.abs_nonneg target)
        refine Q'.le_trans' _ (Q'.abs target) _ ?_ ?_
        · exact Q'.le_of_eqv (Q'.one_mul_eqv (Q'.abs target))
        exact PhysicalKernel.cylinderRemainder_abs_le_remainderL1 K
          (slabPhysicalFacePositiveB M.coarseTarget))
  unfold centeredCylinderRemainder threePhysicalRemainderCost
  exact Q'.le_trans' _ _ _
    (Q'.abs_add_le' (-joint)
      (root * blockedTarget + coarseRoot * target))
    (Q'.add_le_add hjoint
      (Q'.le_trans' _ _ _
        (Q'.abs_add_le' (root * blockedTarget) (coarseRoot * target))
        (Q'.add_le_add hroot htarget)))

#print axioms blockedFaceMoment_nonnegative
#print axioms blockedFaceMoment_le_one
#print axioms coarseFaceMoment_nonnegative
#print axioms coarseFaceMoment_le_one
#print axioms centeredCylinderRemainder_abs_le_threePhysicalRemainderCost

end YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderL1Bound
