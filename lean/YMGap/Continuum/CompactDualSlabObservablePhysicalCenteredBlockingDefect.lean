/-
# Centered physical blocking defects for the literal slab covariance

The first physical transport theorem safely controls covariance by separately
paying the root, target, and joint moment errors.  That interface is general,
but its one-point payments obscure the centering cancellation needed for a
separation-decay theorem.

This module retains covariance throughout the comparison.  It defines the
blocked covariance of the two coarse Boolean events under the actual pushed
fine law, then isolates exactly two computed quantities:

* the centered defect from the fine literal covariance to that blocked
  covariance;
* the centered remainder from the blocked covariance to the coarse Gibbs
  covariance.

Finite ordered-field algebra proves

  fine covariance
    <= coarse covariance
       + centered pullback defect
       + centered physical remainder defect.

Coefficient capture then replaces the coarse covariance by the established
global-anchor rate, and the final theorem specializes to the actual globally
link-glued cutoff-one physical kernel.

No decay estimate for either centered defect is asserted here.  These are the
sharper interacting four-dimensional quantities on which a connected/local
blocking estimate should act.

Constructive contract: finite exact-rational covariance algebra and the
existing physical kernel only; no choice, `Classical`, `native_decide`,
`sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem le_add_of_sub_le_local {a b error : Q'}
    (h : a + (-b) ≤ error) : a ≤ b + error := by
  have hstep := Q'.add_le_add_right (a + (-b)) error b h
  have hcancel : ((a + (-b)) + b).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a (-b) b) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left a ((-b) + b) 0
        (Q'.neg_add_self_eqv b)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hcancel)
    (Q'.le_trans' _ _ _ hstep
      (Q'.le_of_eqv (Q'.add_comm_eqv error b)))

private theorem difference_through_middle
    (left middle right : Q') :
    left - right ≈ (left - middle) + (middle - right) := by
  change left + (-right) ≈
    (left + (-middle)) + (middle + (-right))
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv left (-middle) (middle + (-right))) ?_
  refine Q'.add_eqv_congr_left left
    ((-middle) + (middle + (-right))) (-right) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle (-right))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 (-right)
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (-right))

/-! ## 1. The actual blocked covariance and the two centered defects -/

/-- Covariance of the two coarse face events under the pushed fine law. -/
def blockedSlabFaceBooleanCovariance
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  blockedFacePairMoment K M.coarseRoot M.coarseTarget -
    blockedFaceMoment K M.coarseRoot *
      blockedFaceMoment K M.coarseTarget

/-- Centered observable distortion introduced by the stochastic Markov
pullback itself. -/
def centeredObservablePullbackDefect
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.abs
    (blockedSlabFaceBooleanCovariance K M -
      normalizedSlabFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget)

/-- Centered covariance distortion caused by replacing the pushed law with
the coarse Gibbs law. -/
def centeredPhysicalRemainderDefect
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.abs
    (normalizedSlabFaceBooleanCovariance
        S.coarse M.coarseRoot M.coarseTarget -
      blockedSlabFaceBooleanCovariance K M)

/-- The exact two-stage centered physical transport budget. -/
def centeredPhysicalTransportBudget
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) : Q' :=
  centeredObservablePullbackDefect K M +
    centeredPhysicalRemainderDefect K M

theorem centeredObservablePullbackDefect_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    (0 : Q') ≤ centeredObservablePullbackDefect K M :=
  by
    unfold centeredObservablePullbackDefect
    exact Q'.abs_nonneg _

theorem centeredPhysicalRemainderDefect_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    (0 : Q') ≤ centeredPhysicalRemainderDefect K M :=
  by
    unfold centeredPhysicalRemainderDefect
    exact Q'.abs_nonneg _

/-! ## 2. Exact centered covariance transport -/

/-- The fine normalized covariance is controlled by the coarse normalized
covariance plus exactly the two centered defects. -/
theorem normalizedSlabFaceBooleanCovariance_le_add_centeredTransportBudget
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    normalizedSlabFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget +
        centeredPhysicalTransportBudget K M := by
  let fine := normalizedSlabFaceBooleanCovariance
    S.fine M.fineRoot M.fineTarget
  let blocked := blockedSlabFaceBooleanCovariance K M
  let coarse := normalizedSlabFaceBooleanCovariance
    S.coarse M.coarseRoot M.coarseTarget
  have hfineBlocked : fine - blocked ≤
      centeredObservablePullbackDefect K M := by
    refine Q'.le_trans' _ _ _ (Q'.le_abs_self (fine - blocked)) ?_
    unfold centeredObservablePullbackDefect
    exact Q'.le_of_eqv (ExpNeg.abs_sub_comm fine blocked)
  have hblockedCoarse : blocked - coarse ≤
      centeredPhysicalRemainderDefect K M := by
    refine Q'.le_trans' _ _ _ (Q'.le_abs_self (blocked - coarse)) ?_
    unfold centeredPhysicalRemainderDefect
    exact Q'.le_of_eqv (ExpNeg.abs_sub_comm blocked coarse)
  have hsum :
      (fine - blocked) + (blocked - coarse) ≤
        centeredPhysicalTransportBudget K M := by
    unfold centeredPhysicalTransportBudget
    exact Q'.add_le_add hfineBlocked hblockedCoarse
  have hfineCoarse : fine - coarse ≤
      centeredPhysicalTransportBudget K M := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (difference_through_middle fine blocked coarse)) hsum
  exact le_add_of_sub_le_local hfineCoarse

/-! ## 3. Coefficient capture and the actual physical kernel -/

/-- Once the coarse datum lies in the proved coefficient corridor, only the
two exact centered physical defects remain above the global-anchor rate. -/
theorem slabPhysicalFaceBooleanCovariance_le_blockedRate_add_centeredBudget
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S)
    (hcoarsePositive : (0 : Q') < S.coarse.coupling)
    (hcoarseLtOne : S.coarse.coupling < (1 : Q'))
    (hcoefficient :
      exteriorFaceCoefficient S.coarse.coupling 0 ≤ anchorFaceCoefficient) :
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        centeredPhysicalTransportBudget K M := by
  have hfine :=
    normalizedSlabFaceBooleanCovariance_le_add_centeredTransportBudget K M
  have hcoarseObservable :=
    slabObservableFaceBooleanCovariance_le_of_zeroCoefficient_le
      S.coarse hcoarsePositive hcoarseLtOne hcoefficient
      M.coarseRoot M.coarseTarget M.coarseTarget_mem
  have hcoarsePhysical :
      normalizedSlabFaceBooleanCovariance
          S.coarse M.coarseRoot M.coarseTarget ≤
        slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (slabPhysicalFaceBooleanCovariance_eqv_normalized
          S.coarse M.coarseRoot M.coarseTarget))
      (Q'.le_trans' _ _ _
        (Q'.ge_of_eqv
          (slabObservableFaceBooleanCovariance_eqv_physical
            S.coarse M.coarseRoot M.coarseTarget))
        hcoarseObservable)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabPhysicalFaceBooleanCovariance_eqv_normalized
        S.fine M.fineRoot M.fineTarget))
    (Q'.le_trans' _ _ _ hfine
      (Q'.add_le_add hcoarsePhysical (Q'.le_refl' _)))

/-- The centered theorem for the actual globally link-glued cutoff-one
physical slab kernel. -/
theorem cutoffOnePhysicalSlabFaceBooleanCovariance_le_blockedRate_add_centeredBudget
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarsePositive : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S)
    (hcoarseLtOne : S.coarse.coupling < (1 : Q'))
    (hcoefficient :
      exteriorFaceCoefficient S.coarse.coupling 0 ≤ anchorFaceCoefficient) :
    let K := physicalKernel S hfineCutoff hcoarsePositive
    slabPhysicalFaceBooleanCovariance
        S.fine M.fineRoot M.fineTarget ≤
      slabObservablePairedSupportGlobalAnchorRate
          S.coarse M.coarseRoot M.coarseTarget +
        centeredPhysicalTransportBudget K M := by
  let K := physicalKernel S hfineCutoff hcoarsePositive
  exact slabPhysicalFaceBooleanCovariance_le_blockedRate_add_centeredBudget
    K M hcoarsePositive hcoarseLtOne hcoefficient

#print axioms blockedSlabFaceBooleanCovariance
#print axioms centeredObservablePullbackDefect
#print axioms centeredPhysicalRemainderDefect
#print axioms centeredPhysicalTransportBudget
#print axioms normalizedSlabFaceBooleanCovariance_le_add_centeredTransportBudget
#print axioms slabPhysicalFaceBooleanCovariance_le_blockedRate_add_centeredBudget
#print axioms cutoffOnePhysicalSlabFaceBooleanCovariance_le_blockedRate_add_centeredBudget

end YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredBlockingDefect
