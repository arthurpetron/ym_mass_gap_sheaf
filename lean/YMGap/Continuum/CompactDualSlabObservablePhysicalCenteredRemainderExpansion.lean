/-
# Exact connected expansion of the centered physical slab remainder

The centered blocking theorem isolates the covariance discrepancy between the
actual pushed fine law and the coarse Gibbs law.  Paying three copies of the
full physical `L¹` remainder is safe, but it discards the centering
cancellation that a separation-decay argument must exploit.

This module computes that discrepancy exactly.  For the coarse root, target,
and joint face cylinders, write the selected signed remainders as

  r_root, r_target, r_joint.

Then finite rational algebra and the exact pushforward decomposition give

  coarseCovariance - blockedCovariance
    = -r_joint
        + r_root * blockedTargetMoment
        + coarseRootMoment * r_target.

Thus the physical centered remainder defect is the absolute value of one
explicit connected signed combination, rather than an opaque norm payment.

No smallness or decay estimate is asserted.  The exact connected combination
is the new producer on which geometric locality and refining-trajectory
estimates must act.

Constructive contract: finite exact-rational probability algebra and the
existing physical kernel only; no choice, `Classical`, `native_decide`,
`sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalRemainderLocality
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ac_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem add_then_sub_left_local (left residual : Q') :
    (left + residual) - left ≈ residual := by
  change (left + residual) + (-left) ≈ residual
  refine Q'.eqv_trans _
    (left + (residual + (-left))) _
    (Q'.add_assoc_eqv left residual (-left)) ?_
  refine Q'.eqv_trans _
    (left + ((-left) + residual)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left left _ _
      (Q'.add_comm_eqv residual (-left))
  refine Q'.eqv_trans _
    ((left + (-left)) + residual) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.add_assoc_eqv left (-left) residual)
  refine Q'.eqv_trans _ (0 + residual) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ residual
      (Q'.add_neg_self_eqv left)
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem productDifference_decompose_local
    (blockedRoot blockedTarget coarseRoot coarseTarget : Q') :
    blockedRoot * blockedTarget - coarseRoot * coarseTarget ≈
      (blockedRoot - coarseRoot) * blockedTarget +
        coarseRoot * (blockedTarget - coarseTarget) := by
  change
    blockedRoot * blockedTarget + (-(coarseRoot * coarseTarget)) ≈
      (blockedRoot + (-coarseRoot)) * blockedTarget +
        coarseRoot * (blockedTarget + (-coarseTarget))
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    ((blockedRoot * blockedTarget +
        (-(coarseRoot * blockedTarget))) +
      (coarseRoot * blockedTarget +
        (-(coarseRoot * coarseTarget)))) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _
        (Q'.add_mul_eqv blockedRoot (-coarseRoot) blockedTarget)
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.neg_mul_eqv coarseRoot blockedTarget)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv coarseRoot blockedTarget (-coarseTarget))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (Q'.mul_neg_eqv coarseRoot coarseTarget)))
  · refine Q'.eqv_trans _
      (blockedRoot * blockedTarget +
        ((-(coarseRoot * blockedTarget)) +
          (coarseRoot * blockedTarget +
            (-(coarseRoot * coarseTarget))))) _ ?_ ?_
    · exact Q'.add_assoc_eqv _ _ _
    refine Q'.eqv_trans _
      (blockedRoot * blockedTarget +
        (((-(coarseRoot * blockedTarget)) +
            coarseRoot * blockedTarget) +
          (-(coarseRoot * coarseTarget)))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
    refine Q'.eqv_trans _
      (blockedRoot * blockedTarget +
        (0 + (-(coarseRoot * coarseTarget)))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.neg_add_self_eqv (coarseRoot * blockedTarget)))
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_of_eq (Q'.zero_add' (-(coarseRoot * coarseTarget))))

private theorem covarianceDifference_decompose_local
    (blockedJoint blockedRoot blockedTarget
      coarseJoint coarseRoot coarseTarget : Q') :
    (coarseJoint - coarseRoot * coarseTarget) -
        (blockedJoint - blockedRoot * blockedTarget) ≈
      -(blockedJoint - coarseJoint) +
        (blockedRoot * blockedTarget - coarseRoot * coarseTarget) := by
  have hbase :
      (coarseJoint - coarseRoot * coarseTarget) +
          (-(blockedJoint - blockedRoot * blockedTarget)) ≈
        (coarseJoint - blockedJoint) +
          (blockedRoot * blockedTarget - coarseRoot * coarseTarget) := by
    change
      (coarseJoint + (-(coarseRoot * coarseTarget))) +
          (-(blockedJoint + (-(blockedRoot * blockedTarget)))) ≈
        (coarseJoint + (-blockedJoint)) +
          (blockedRoot * blockedTarget + (-(coarseRoot * coarseTarget)))
    refine Q'.eqv_trans _
      ((coarseJoint + (-(coarseRoot * coarseTarget))) +
        ((-blockedJoint) + (-(-(blockedRoot * blockedTarget))))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_eqv blockedJoint (-(blockedRoot * blockedTarget)))
    refine Q'.eqv_trans _
      ((coarseJoint + (-(coarseRoot * coarseTarget))) +
        ((-blockedJoint) + (blockedRoot * blockedTarget))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.add_eqv_congr_left (-blockedJoint) _ _
          (Q'.neg_neg_eqv (blockedRoot * blockedTarget)))
    refine Q'.eqv_trans _
      ((coarseJoint + (-blockedJoint)) +
        ((-(coarseRoot * coarseTarget)) +
          blockedRoot * blockedTarget)) _ ?_ ?_
    · exact Q'.add_swap_inner coarseJoint (-(coarseRoot * coarseTarget))
        (-blockedJoint) (blockedRoot * blockedTarget)
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_comm_eqv (-(coarseRoot * coarseTarget))
        (blockedRoot * blockedTarget))
  have hswap :
      coarseJoint - blockedJoint ≈
        -(blockedJoint - coarseJoint) := by
    change coarseJoint + (-blockedJoint) ≈
      -(blockedJoint + (-coarseJoint))
    apply Q'.eqv_symm
    refine Q'.eqv_trans _
      ((-blockedJoint) + (-(-coarseJoint))) _
      (Q'.neg_add_eqv blockedJoint (-coarseJoint)) ?_
    refine Q'.eqv_trans _
      ((-blockedJoint) + coarseJoint) _ ?_ ?_
    · exact Q'.add_eqv_congr_left (-blockedJoint) _ _
        (Q'.neg_neg_eqv coarseJoint)
    exact Q'.add_comm_eqv (-blockedJoint) coarseJoint
  exact Q'.eqv_trans _ _ _ hbase
    (Q'.add_eqv_congr_right _ _ _ hswap)

/-! ## 1. Selected signed cylinder remainders -/

/-- Signed physical remainder selected by one coarse face cylinder. -/
def faceCylinderRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (coarseFaceId : Nat) : Q' :=
  PhysicalKernel.cylinderRemainder K
    (slabPhysicalFacePositiveB coarseFaceId)

/-- Signed physical remainder selected by the joint coarse two-face
cylinder. -/
def facePairCylinderRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (coarseRoot coarseTarget : Nat) : Q' :=
  PhysicalKernel.cylinderRemainder K
    (slabPhysicalFacePairPositiveB coarseRoot coarseTarget)

/-- The exact connected signed remainder correcting the blocked covariance
to the coarse Gibbs covariance.  Retaining the signs is essential: taking
absolute values termwise here would erase the centering cancellation. -/
def centeredCylinderRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  -(facePairCylinderRemainder K M.coarseRoot M.coarseTarget) +
    (faceCylinderRemainder K M.coarseRoot *
        blockedFaceMoment K M.coarseTarget +
      coarseFaceMoment K M.coarseRoot *
        faceCylinderRemainder K M.coarseTarget)

/-! ## 2. Exact covariance expansion -/

/-- Generic exact covariance comparison when each new moment is a reference
moment plus a signed remainder.  This is public so the Markov-pullback and
pushed-law remainder sides can share one algebraic seam. -/
theorem covariance_sub_covariance_eqv_signedMomentRemainders
    (blockedJoint blockedRoot blockedTarget
      coarseJoint coarseRoot coarseTarget
      jointRemainder rootRemainder targetRemainder : Q')
    (hjoint : blockedJoint ≈ coarseJoint + jointRemainder)
    (hroot : blockedRoot ≈ coarseRoot + rootRemainder)
    (htarget : blockedTarget ≈ coarseTarget + targetRemainder) :
    (coarseJoint - coarseRoot * coarseTarget) -
        (blockedJoint - blockedRoot * blockedTarget) ≈
      -jointRemainder +
        (rootRemainder * blockedTarget +
          coarseRoot * targetRemainder) := by
  have hjointSub : blockedJoint - coarseJoint ≈ jointRemainder := by
    refine Q'.eqv_trans _
      ((coarseJoint + jointRemainder) - coarseJoint) _ ?_ ?_
    · exact sub_eqv_both_local hjoint (Q'.eqv_refl _)
    · exact add_then_sub_left_local coarseJoint jointRemainder
  have hrootSub : blockedRoot - coarseRoot ≈ rootRemainder := by
    refine Q'.eqv_trans _
      ((coarseRoot + rootRemainder) - coarseRoot) _ ?_ ?_
    · exact sub_eqv_both_local hroot (Q'.eqv_refl _)
    · exact add_then_sub_left_local coarseRoot rootRemainder
  have htargetSub : blockedTarget - coarseTarget ≈ targetRemainder := by
    refine Q'.eqv_trans _
      ((coarseTarget + targetRemainder) - coarseTarget) _ ?_ ?_
    · exact sub_eqv_both_local htarget (Q'.eqv_refl _)
    · exact add_then_sub_left_local coarseTarget targetRemainder
  have hproduct :
      blockedRoot * blockedTarget - coarseRoot * coarseTarget ≈
        rootRemainder * blockedTarget + coarseRoot * targetRemainder := by
    refine Q'.eqv_trans _
      ((blockedRoot - coarseRoot) * blockedTarget +
        coarseRoot * (blockedTarget - coarseTarget)) _ ?_ ?_
    · exact productDifference_decompose_local
        blockedRoot blockedTarget coarseRoot coarseTarget
    · exact Q'.add_eqv_congr'
        (mul_eqv_both_local hrootSub (Q'.eqv_refl _))
        (mul_eqv_both_local (Q'.eqv_refl _) htargetSub)
  refine Q'.eqv_trans _
    (-(blockedJoint - coarseJoint) +
      (blockedRoot * blockedTarget - coarseRoot * coarseTarget)) _ ?_ ?_
  · exact covarianceDifference_decompose_local
      blockedJoint blockedRoot blockedTarget
      coarseJoint coarseRoot coarseTarget
  · exact Q'.add_eqv_congr'
      (Q'.neg_eqv_congr _ _ hjointSub) hproduct

/-- Exact covariance-level pushforward decomposition for the two literal
coarse face events. -/
theorem coarse_sub_blocked_covariance_eqv_centeredCylinderRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget -
        blockedSlabFaceBooleanCovariance K M ≈
      centeredCylinderRemainder K M := by
  have hjoint :
      blockedFacePairMoment K M.coarseRoot M.coarseTarget ≈
        coarseFacePairMoment K M.coarseRoot M.coarseTarget +
          facePairCylinderRemainder K M.coarseRoot M.coarseTarget := by
    exact PhysicalKernel.blockedCylinderMass_decomposition K
      (slabPhysicalFacePairPositiveB M.coarseRoot M.coarseTarget)
  have hroot :
      blockedFaceMoment K M.coarseRoot ≈
        coarseFaceMoment K M.coarseRoot +
          faceCylinderRemainder K M.coarseRoot := by
    exact PhysicalKernel.blockedCylinderMass_decomposition K
      (slabPhysicalFacePositiveB M.coarseRoot)
  have htarget :
      blockedFaceMoment K M.coarseTarget ≈
        coarseFaceMoment K M.coarseTarget +
          faceCylinderRemainder K M.coarseTarget := by
    exact PhysicalKernel.blockedCylinderMass_decomposition K
      (slabPhysicalFacePositiveB M.coarseTarget)
  exact covariance_sub_covariance_eqv_signedMomentRemainders
    (blockedFacePairMoment K M.coarseRoot M.coarseTarget)
    (blockedFaceMoment K M.coarseRoot)
    (blockedFaceMoment K M.coarseTarget)
    (coarseFacePairMoment K M.coarseRoot M.coarseTarget)
    (coarseFaceMoment K M.coarseRoot)
    (coarseFaceMoment K M.coarseTarget)
    (facePairCylinderRemainder K M.coarseRoot M.coarseTarget)
    (faceCylinderRemainder K M.coarseRoot)
    (faceCylinderRemainder K M.coarseTarget)
    hjoint hroot htarget

/-- The previously isolated centered physical remainder defect is exactly
the absolute value of the connected signed cylinder remainder. -/
theorem centeredPhysicalRemainderDefect_eqv_abs_centeredCylinderRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    centeredPhysicalRemainderDefect K M ≈
      Q'.abs (centeredCylinderRemainder K M) := by
  unfold centeredPhysicalRemainderDefect
  exact Q'.abs_eqv_congr
    (coarse_sub_blocked_covariance_eqv_centeredCylinderRemainder K M)

#print axioms faceCylinderRemainder
#print axioms facePairCylinderRemainder
#print axioms centeredCylinderRemainder
#print axioms covariance_sub_covariance_eqv_signedMomentRemainders
#print axioms coarse_sub_blocked_covariance_eqv_centeredCylinderRemainder
#print axioms centeredPhysicalRemainderDefect_eqv_abs_centeredCylinderRemainder

end YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
