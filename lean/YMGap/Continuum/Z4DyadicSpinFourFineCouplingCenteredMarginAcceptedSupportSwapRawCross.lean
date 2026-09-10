/-
# Clearing the four accepted support-swap row denominators

The actual support-swap response defect is a difference of four positive-row
raw event ratios.  This module multiplies that defect by the positive product
of its four complete row partitions and obtains one division-free raw cross
polynomial.  Vanishing of that polynomial is therefore sufficient for exact
pair-response invariance, without requiring the two individual rows to be
separately invariant.

This is the normalization-aware target for a graphical component
factorization: numerator and partition contributions from all four rows now
occur in one exact polynomial.  No such factorization or estimate is claimed
here.

Constructive contract: exact rational setoid algebra over explicit positive
finite-row partitions only; no choice, proof hole, classical witness erasure,
trusted external computation, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapRawCross

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRealization
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalTargetPair
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportRecouplingProduct
open YMGap.Continuum.CompactDualSlabObservablePhysicalPullbackRawMismatch
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapCocycle
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapResponseDefect
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

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

/-! ## 1. Generic four-ratio denominator clearing -/

/-- Difference of two differences of four ratios with positive
denominators. -/
def fourPositiveRatioResponseDefect
    (a b c d A B C D : Q')
    (hA : (0 : Q') < A) (hB : (0 : Q') < B)
    (hC : (0 : Q') < C) (hD : (0 : Q') < D) : Q' :=
  (Q'.divPos a A hA - Q'.divPos b B hB) -
    (Q'.divPos c C hC - Q'.divPos d D hD)

/-- Common positive denominator for the four-row response defect. -/
def fourPositiveRatioResponseDenominator
    (A B C D : Q') : Q' :=
  A * (B * (C * D))

/-- Division-free cross polynomial obtained from the four normalized rows. -/
def fourPositiveRatioResponseCrossNumerator
    (a b c d A B C D : Q') : Q' :=
  (a * (B * (C * D)) - b * (A * (C * D))) -
    (c * (A * (B * D)) - d * (A * (B * C)))

theorem fourPositiveRatioResponseDenominator_pos
    {A B C D : Q'}
    (hA : (0 : Q') < A) (hB : (0 : Q') < B)
    (hC : (0 : Q') < C) (hD : (0 : Q') < D) :
    (0 : Q') < fourPositiveRatioResponseDenominator A B C D := by
  unfold fourPositiveRatioResponseDenominator
  exact Q'.mul_pos hA (Q'.mul_pos hB (Q'.mul_pos hC hD))

private theorem divPos_mul_denominator_tail_eqv
    (numerator denominator tail : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos numerator denominator hdenominator *
        (denominator * tail) ≈
      numerator * tail := by
  refine Q'.eqv_trans _
    ((Q'.divPos numerator denominator hdenominator * denominator) * tail)
    _ ?_ ?_
  · ring_qeqv
  · exact Q'.mul_eqv_congr_right _ _ tail
      (Q'.divPos_mul_eqv numerator denominator hdenominator)

/-- Multiplying the four-ratio defect by its common denominator produces
the division-free cross polynomial exactly. -/
theorem fourPositiveRatioResponseDefect_mul_denominator_eqv_crossNumerator
    (a b c d A B C D : Q')
    (hA : (0 : Q') < A) (hB : (0 : Q') < B)
    (hC : (0 : Q') < C) (hD : (0 : Q') < D) :
    fourPositiveRatioResponseDefect a b c d A B C D hA hB hC hD *
        fourPositiveRatioResponseDenominator A B C D ≈
      fourPositiveRatioResponseCrossNumerator a b c d A B C D := by
  let common := fourPositiveRatioResponseDenominator A B C D
  have ha : Q'.divPos a A hA * common ≈
      a * (B * (C * D)) := by
    unfold common fourPositiveRatioResponseDenominator
    exact divPos_mul_denominator_tail_eqv
      a A (B * (C * D)) hA
  have hb : Q'.divPos b B hB * common ≈
      b * (A * (C * D)) := by
    refine Q'.eqv_trans _
      (Q'.divPos b B hB * (B * (A * (C * D)))) _ ?_ ?_
    · unfold common fourPositiveRatioResponseDenominator
      ring_qeqv
    · exact divPos_mul_denominator_tail_eqv
        b B (A * (C * D)) hB
  have hc : Q'.divPos c C hC * common ≈
      c * (A * (B * D)) := by
    refine Q'.eqv_trans _
      (Q'.divPos c C hC * (C * (A * (B * D)))) _ ?_ ?_
    · unfold common fourPositiveRatioResponseDenominator
      ring_qeqv
    · exact divPos_mul_denominator_tail_eqv
        c C (A * (B * D)) hC
  have hd : Q'.divPos d D hD * common ≈
      d * (A * (B * C)) := by
    refine Q'.eqv_trans _
      (Q'.divPos d D hD * (D * (A * (B * C)))) _ ?_ ?_
    · unfold common fourPositiveRatioResponseDenominator
      ring_qeqv
    · exact divPos_mul_denominator_tail_eqv
        d D (A * (B * C)) hD
  unfold fourPositiveRatioResponseDefect
    fourPositiveRatioResponseCrossNumerator
  refine Q'.eqv_trans _
    ((Q'.divPos a A hA * common - Q'.divPos b B hB * common) -
      (Q'.divPos c C hC * common -
        Q'.divPos d D hD * common)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.sub_mul_eqv
        (Q'.divPos a A hA - Q'.divPos b B hB)
        (Q'.divPos c C hC - Q'.divPos d D hD)
        common)
      (sub_eqv_both_local
        (Q'.sub_mul_eqv
          (Q'.divPos a A hA) (Q'.divPos b B hB) common)
        (Q'.sub_mul_eqv
          (Q'.divPos c C hC) (Q'.divPos d D hD) common))
  · exact sub_eqv_both_local
      (sub_eqv_both_local ha hb)
      (sub_eqv_both_local hc hd)

/-! ## 2. The four literal accepted positive raw rows -/

def fineCouplingAcceptedSourceLeftRawRow
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    CoherentSlabRecouplingSource S :=
  positiveCoherentSource S hfineCutoff hcoarseCoupling
    source.1.1.1.1 source.1.1.physical_mem
    (fineCouplingAcceptedSeparated_left_physicalTerm_pos
      S hfineCoupling rootFaceId targetFaceId source)

def fineCouplingAcceptedSourceRightRawRow
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    CoherentSlabRecouplingSource S :=
  positiveCoherentSource S hfineCutoff hcoarseCoupling
    source.1.2.1.1
    (mem_slabExpandedFineSources_iff.mp source.1.2.2).1
    (fineCouplingAcceptedSeparated_right_physicalTerm_pos
      S hfineCoupling rootFaceId targetFaceId source)

def fineCouplingAcceptedSwappedLeftRawRow
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    CoherentSlabRecouplingSource S :=
  positiveCoherentSource S hfineCutoff hcoarseCoupling
    (slabObservablePairSupportSwitchedLeftPhysical
      S.fine targetFaceId source.1)
    (slabObservablePairedSupportSwitchedLeftPhysical_mem
      S.fine source)
    (fineCouplingAcceptedSeparated_swappedLeft_physicalTerm_pos
      S hfineCoupling rootFaceId targetFaceId htarget source)

def fineCouplingAcceptedSwappedRightRawRow
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    CoherentSlabRecouplingSource S :=
  positiveCoherentSource S hfineCutoff hcoarseCoupling
    (slabObservablePairSupportSwitchedRightPhysical
      S.fine targetFaceId source.1)
    (slabObservablePairedSupportSwitchedRightPhysical_mem
      S.fine source)
    (fineCouplingAcceptedSeparated_swappedRight_physicalTerm_pos
      S hfineCoupling rootFaceId targetFaceId htarget source)

/-! ## 3. The accepted division-free raw cross -/

def fineCouplingAcceptedRawRatioResponseDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) : Q' :=
  (wholeSlabRecouplingRawCylinderRatio
      (fineCouplingAcceptedSourceLeftRawRow S hfineCutoff
        hfineCoupling hcoarseCoupling rootFaceId targetFaceId source) event -
    wholeSlabRecouplingRawCylinderRatio
      (fineCouplingAcceptedSourceRightRawRow S hfineCutoff
        hfineCoupling hcoarseCoupling rootFaceId targetFaceId source) event) -
  (wholeSlabRecouplingRawCylinderRatio
      (fineCouplingAcceptedSwappedLeftRawRow S hfineCutoff
        hfineCoupling hcoarseCoupling rootFaceId targetFaceId
        htarget source) event -
    wholeSlabRecouplingRawCylinderRatio
      (fineCouplingAcceptedSwappedRightRawRow S hfineCutoff
        hfineCoupling hcoarseCoupling rootFaceId targetFaceId
        htarget source) event)

def fineCouplingAcceptedRawResponseDenominator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) : Q' :=
  fourPositiveRatioResponseDenominator
    (wholeSlabRecouplingPartition
      (fineCouplingAcceptedSourceLeftRawRow S hfineCutoff
        hfineCoupling hcoarseCoupling rootFaceId targetFaceId source))
    (wholeSlabRecouplingPartition
      (fineCouplingAcceptedSourceRightRawRow S hfineCutoff
        hfineCoupling hcoarseCoupling rootFaceId targetFaceId source))
    (wholeSlabRecouplingPartition
      (fineCouplingAcceptedSwappedLeftRawRow S hfineCutoff
        hfineCoupling hcoarseCoupling rootFaceId targetFaceId
        htarget source))
    (wholeSlabRecouplingPartition
      (fineCouplingAcceptedSwappedRightRawRow S hfineCutoff
        hfineCoupling hcoarseCoupling rootFaceId targetFaceId
        htarget source))

def fineCouplingAcceptedRawResponseCrossNumerator
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) : Q' :=
  let sourceLeft := fineCouplingAcceptedSourceLeftRawRow S hfineCutoff
    hfineCoupling hcoarseCoupling rootFaceId targetFaceId source
  let sourceRight := fineCouplingAcceptedSourceRightRawRow S hfineCutoff
    hfineCoupling hcoarseCoupling rootFaceId targetFaceId source
  let swappedLeft := fineCouplingAcceptedSwappedLeftRawRow S hfineCutoff
    hfineCoupling hcoarseCoupling rootFaceId targetFaceId htarget source
  let swappedRight := fineCouplingAcceptedSwappedRightRawRow S hfineCutoff
    hfineCoupling hcoarseCoupling rootFaceId targetFaceId htarget source
  fourPositiveRatioResponseCrossNumerator
    (wholeSlabRecouplingRawCylinderMass sourceLeft event)
    (wholeSlabRecouplingRawCylinderMass sourceRight event)
    (wholeSlabRecouplingRawCylinderMass swappedLeft event)
    (wholeSlabRecouplingRawCylinderMass swappedRight event)
    (wholeSlabRecouplingPartition sourceLeft)
    (wholeSlabRecouplingPartition sourceRight)
    (wholeSlabRecouplingPartition swappedLeft)
    (wholeSlabRecouplingPartition swappedRight)

theorem fineCouplingAcceptedRawResponseDenominator_pos
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId) :
    (0 : Q') < fineCouplingAcceptedRawResponseDenominator
      S hfineCutoff hfineCoupling hcoarseCoupling
        rootFaceId targetFaceId htarget source := by
  unfold fineCouplingAcceptedRawResponseDenominator
  exact fourPositiveRatioResponseDenominator_pos
    (wholeSlabRecouplingPartition_pos _)
    (wholeSlabRecouplingPartition_pos _)
    (wholeSlabRecouplingPartition_pos _)
    (wholeSlabRecouplingPartition_pos _)

theorem fineCouplingAcceptedSeparated_actualResponseDefect_eqv_rawRatioDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalSupportSwapResponseDefect
        (physicalKernel S hfineCutoff hcoarseCoupling) event targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source) ≈
      fineCouplingAcceptedRawRatioResponseDefect
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source event := by
  simpa only [fineCouplingAcceptedRawRatioResponseDefect,
    fineCouplingAcceptedSourceLeftRawRow,
    fineCouplingAcceptedSourceRightRawRow,
    fineCouplingAcceptedSwappedLeftRawRow,
    fineCouplingAcceptedSwappedRightRawRow,
    positivePhysicalRawEventRatio] using
    fineCouplingAcceptedSeparated_actualResponseDefect_eqv_rawRatios
      S hfineCutoff hfineCoupling hcoarseCoupling
        rootFaceId targetFaceId htarget source event

/-- **Accepted raw-cross identity.**  The actual production-kernel response
defect times one explicit positive denominator is the division-free four-row
raw cross. -/
theorem fineCouplingAcceptedSeparated_actualResponseDefect_mul_denominator_eqv_rawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool) :
    fineCouplingPhysicalSupportSwapResponseDefect
          (physicalKernel S hfineCutoff hcoarseCoupling)
          event targetFaceId
          (fineCouplingAcceptedSeparatedPhysicalPair
            S rootFaceId targetFaceId source) *
        fineCouplingAcceptedRawResponseDenominator
          S hfineCutoff hfineCoupling hcoarseCoupling
            rootFaceId targetFaceId htarget source ≈
      fineCouplingAcceptedRawResponseCrossNumerator
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source event := by
  let sourceLeft := fineCouplingAcceptedSourceLeftRawRow S hfineCutoff
    hfineCoupling hcoarseCoupling rootFaceId targetFaceId source
  let sourceRight := fineCouplingAcceptedSourceRightRawRow S hfineCutoff
    hfineCoupling hcoarseCoupling rootFaceId targetFaceId source
  let swappedLeft := fineCouplingAcceptedSwappedLeftRawRow S hfineCutoff
    hfineCoupling hcoarseCoupling rootFaceId targetFaceId htarget source
  let swappedRight := fineCouplingAcceptedSwappedRightRawRow S hfineCutoff
    hfineCoupling hcoarseCoupling rootFaceId targetFaceId htarget source
  refine Q'.eqv_trans _
    (fineCouplingAcceptedRawRatioResponseDefect
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source event *
      fineCouplingAcceptedRawResponseDenominator
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (fineCouplingAcceptedSeparated_actualResponseDefect_eqv_rawRatioDefect
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source event)
  simpa only [fineCouplingAcceptedRawRatioResponseDefect,
    fineCouplingAcceptedRawResponseDenominator,
    fineCouplingAcceptedRawResponseCrossNumerator,
    wholeSlabRecouplingRawCylinderRatio,
    sourceLeft, sourceRight, swappedLeft, swappedRight] using
    fourPositiveRatioResponseDefect_mul_denominator_eqv_crossNumerator
      (wholeSlabRecouplingRawCylinderMass sourceLeft event)
      (wholeSlabRecouplingRawCylinderMass sourceRight event)
      (wholeSlabRecouplingRawCylinderMass swappedLeft event)
      (wholeSlabRecouplingRawCylinderMass swappedRight event)
      (wholeSlabRecouplingPartition sourceLeft)
      (wholeSlabRecouplingPartition sourceRight)
      (wholeSlabRecouplingPartition swappedLeft)
      (wholeSlabRecouplingPartition swappedRight)
      (wholeSlabRecouplingPartition_pos sourceLeft)
      (wholeSlabRecouplingPartition_pos sourceRight)
      (wholeSlabRecouplingPartition_pos swappedLeft)
      (wholeSlabRecouplingPartition_pos swappedRight)

/-- Vanishing of the single division-free raw cross is enough to discharge
the response defect.  This condition is strictly weaker than separately
equating both switched rows. -/
theorem fineCouplingAcceptedSeparated_actualResponseDefect_eqv_zero_of_rawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool)
    (hcross : fineCouplingAcceptedRawResponseCrossNumerator
      S hfineCutoff hfineCoupling hcoarseCoupling
        rootFaceId targetFaceId htarget source event ≈ 0) :
    fineCouplingPhysicalSupportSwapResponseDefect
        (physicalKernel S hfineCutoff hcoarseCoupling)
        event targetFaceId
        (fineCouplingAcceptedSeparatedPhysicalPair
          S rootFaceId targetFaceId source) ≈ 0 := by
  let defect := fineCouplingPhysicalSupportSwapResponseDefect
    (physicalKernel S hfineCutoff hcoarseCoupling)
    event targetFaceId
    (fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source)
  let denominator := fineCouplingAcceptedRawResponseDenominator
    S hfineCutoff hfineCoupling hcoarseCoupling
      rootFaceId targetFaceId htarget source
  have hmul : defect * denominator ≈ 0 :=
    Q'.eqv_trans _ _ _
      (fineCouplingAcceptedSeparated_actualResponseDefect_mul_denominator_eqv_rawCross
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source event)
      hcross
  have hleft : denominator * defect ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv denominator defect) hmul
  exact Q'.mul_eqv_zero_of_pos
    (fineCouplingAcceptedRawResponseDenominator_pos
      S hfineCutoff hfineCoupling hcoarseCoupling
        rootFaceId targetFaceId htarget source)
    hleft

/-- A vanishing division-free raw cross discharges the response term in the
literal accepted occupation decomposition directly.  No separate equality of
the two switched rows is required. -/
theorem fineCouplingAcceptedSeparatedOccupationResponse_decomposition_of_rawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineCoupling : (0 : Q') < S.fine.coupling)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (event : EdgeLabelling → Bool) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (choice : SlabObservablePairedSupportRecouplingChoice
      S.fine rootFaceId targetFaceId source)
    (hcross : fineCouplingAcceptedRawResponseCrossNumerator
      S hfineCutoff hfineCoupling hcoarseCoupling
        rootFaceId targetFaceId htarget source event ≈ 0) :
    let pair := fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source
    let swapped := fineCouplingAcceptedRecoupledPhysicalPair
      S rootFaceId targetFaceId htarget source choice
    let sourceAssignments := fineCouplingAcceptedSeparatedAssignmentPair
      S rootFaceId targetFaceId source
    let targetAssignments := fineCouplingAcceptedRecoupledAssignmentPair
      S rootFaceId targetFaceId htarget source choice
    fineCouplingExpandedOccupationResponseTerm
        (physicalKernel S hfineCutoff hcoarseCoupling)
        event pair sourceAssignments ≈
      fineCouplingExpandedOccupationResponseTerm
          (physicalKernel S hfineCutoff hcoarseCoupling)
          event swapped targetAssignments +
        ((qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.1) +
            qpow S.fine.coupling
              (3 * fineCouplingPhysicalOutsideOccupiedFaceCount
                S targetFaceId pair pair.2)) *
          fineCouplingPhysicalComponentOccupationSkewCoefficient
            S targetFaceId pair) *
          (fineUnitCouplingExpandedFiberPairWeight
              S pair sourceAssignments *
            fineCouplingPhysicalPairEventResponseDifference
              (physicalKernel S hfineCutoff hcoarseCoupling)
              event pair) := by
  exact
    fineCouplingAcceptedSeparatedOccupationResponse_decomposition_of_responseDefect_eqv_zero
      (physicalKernel S hfineCutoff hcoarseCoupling)
      event rootFaceId targetFaceId htarget source choice
      (fineCouplingAcceptedSeparated_actualResponseDefect_eqv_zero_of_rawCross
        S hfineCutoff hfineCoupling hcoarseCoupling
          rootFaceId targetFaceId htarget source event hcross)

#print axioms fourPositiveRatioResponseDefect
#print axioms fourPositiveRatioResponseDenominator
#print axioms fourPositiveRatioResponseCrossNumerator
#print axioms fourPositiveRatioResponseDenominator_pos
#print axioms fourPositiveRatioResponseDefect_mul_denominator_eqv_crossNumerator
#print axioms fineCouplingAcceptedSourceLeftRawRow
#print axioms fineCouplingAcceptedSourceRightRawRow
#print axioms fineCouplingAcceptedSwappedLeftRawRow
#print axioms fineCouplingAcceptedSwappedRightRawRow
#print axioms fineCouplingAcceptedRawRatioResponseDefect
#print axioms fineCouplingAcceptedRawResponseDenominator
#print axioms fineCouplingAcceptedRawResponseCrossNumerator
#print axioms fineCouplingAcceptedRawResponseDenominator_pos
#print axioms fineCouplingAcceptedSeparated_actualResponseDefect_eqv_rawRatioDefect
#print axioms fineCouplingAcceptedSeparated_actualResponseDefect_mul_denominator_eqv_rawCross
#print axioms fineCouplingAcceptedSeparated_actualResponseDefect_eqv_zero_of_rawCross
#print axioms fineCouplingAcceptedSeparatedOccupationResponse_decomposition_of_rawCross

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapRawCross
