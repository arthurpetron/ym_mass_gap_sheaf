/-
# Exact connected expansion of the centered observable pullback defect

The actual physical block kernel is stochastic, so a coarse Boolean face
cylinder pulls back to a conditional probability rather than to a Boolean
fine cylinder.  The centered blocking interface records the resulting
covariance discrepancy as `centeredObservablePullbackDefect`.

This module exposes the cancellation inside that defect.  Let the signed
root, target, and joint pullback remainders be the blocked moments minus the
corresponding fine moments.  Exact finite rational algebra gives

  fineCovariance - blockedCovariance
    = -jointPullbackRemainder
        + rootPullbackRemainder * blockedTargetMoment
        + fineRootMoment * targetPullbackRemainder.

The centered pullback defect is therefore exactly the absolute value of this
one signed combination.  Together with the connected physical-remainder
expansion, this leaves two explicit cancellation-aware quantities for the
refining-corridor decay estimate.

No smallness or decay estimate is asserted here.

Constructive contract: finite exact-rational covariance algebra and the
existing physical kernel only; no choice, `Classical`, `native_decide`,
`sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredPullbackExpansion

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Signed Markov-pullback moment remainders -/

/-- Signed one-face pullback remainder: pushed coarse event mass minus the
selected fine Boolean event mass. -/
def facePullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineFaceId coarseFaceId : Nat) : Q' :=
  blockedFaceMoment K coarseFaceId - fineFaceMoment K fineFaceId

/-- Signed two-face pullback remainder. -/
def facePairPullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (fineRoot fineTarget coarseRoot coarseTarget : Nat) : Q' :=
  blockedFacePairMoment K coarseRoot coarseTarget -
    fineFacePairMoment K fineRoot fineTarget

/-- The exact connected signed Markov-pullback remainder, oriented as fine
covariance minus blocked covariance. -/
def centeredObservablePullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  -(facePairPullbackRemainder K
      M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget) +
    (facePullbackRemainder K M.fineRoot M.coarseRoot *
        blockedFaceMoment K M.coarseTarget +
      fineFaceMoment K M.fineRoot *
        facePullbackRemainder K M.fineTarget M.coarseTarget)

/-! ## 2. Exact covariance expansion -/

/-- Exact covariance-level expansion of the stochastic observable pullback. -/
theorem fine_sub_blocked_covariance_eqv_centeredObservablePullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    normalizedSlabFaceBooleanCovariance
          S.fine M.fineRoot M.fineTarget -
        blockedSlabFaceBooleanCovariance K M ≈
      centeredObservablePullbackRemainder K M := by
  have hjoint :
      blockedFacePairMoment K M.coarseRoot M.coarseTarget ≈
        fineFacePairMoment K M.fineRoot M.fineTarget +
          facePairPullbackRemainder K
            M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget := by
    unfold facePairPullbackRemainder
    exact Q'.add_sub_cancel_eqv
      (blockedFacePairMoment K M.coarseRoot M.coarseTarget)
      (fineFacePairMoment K M.fineRoot M.fineTarget)
  have hroot :
      blockedFaceMoment K M.coarseRoot ≈
        fineFaceMoment K M.fineRoot +
          facePullbackRemainder K M.fineRoot M.coarseRoot := by
    unfold facePullbackRemainder
    exact Q'.add_sub_cancel_eqv
      (blockedFaceMoment K M.coarseRoot)
      (fineFaceMoment K M.fineRoot)
  have htarget :
      blockedFaceMoment K M.coarseTarget ≈
        fineFaceMoment K M.fineTarget +
          facePullbackRemainder K M.fineTarget M.coarseTarget := by
    unfold facePullbackRemainder
    exact Q'.add_sub_cancel_eqv
      (blockedFaceMoment K M.coarseTarget)
      (fineFaceMoment K M.fineTarget)
  exact covariance_sub_covariance_eqv_signedMomentRemainders
    (blockedFacePairMoment K M.coarseRoot M.coarseTarget)
    (blockedFaceMoment K M.coarseRoot)
    (blockedFaceMoment K M.coarseTarget)
    (fineFacePairMoment K M.fineRoot M.fineTarget)
    (fineFaceMoment K M.fineRoot)
    (fineFaceMoment K M.fineTarget)
    (facePairPullbackRemainder K
      M.fineRoot M.fineTarget M.coarseRoot M.coarseTarget)
    (facePullbackRemainder K M.fineRoot M.coarseRoot)
    (facePullbackRemainder K M.fineTarget M.coarseTarget)
    hjoint hroot htarget

/-- The centered observable pullback defect is exactly the absolute value of
the connected signed pullback remainder. -/
theorem centeredObservablePullbackDefect_eqv_abs_centeredPullbackRemainder
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    centeredObservablePullbackDefect K M ≈
      Q'.abs (centeredObservablePullbackRemainder K M) := by
  let fine := normalizedSlabFaceBooleanCovariance
    S.fine M.fineRoot M.fineTarget
  let blocked := blockedSlabFaceBooleanCovariance K M
  have hconnected :
      fine - blocked ≈ centeredObservablePullbackRemainder K M :=
    fine_sub_blocked_covariance_eqv_centeredObservablePullbackRemainder K M
  unfold centeredObservablePullbackDefect
  exact Q'.eqv_trans _ (Q'.abs (fine - blocked)) _
    (Q'.eqv_symm (ExpNeg.abs_sub_comm fine blocked))
    (Q'.abs_eqv_congr hconnected)

#print axioms facePullbackRemainder
#print axioms facePairPullbackRemainder
#print axioms centeredObservablePullbackRemainder
#print axioms fine_sub_blocked_covariance_eqv_centeredObservablePullbackRemainder
#print axioms centeredObservablePullbackDefect_eqv_abs_centeredPullbackRemainder

end YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredPullbackExpansion
