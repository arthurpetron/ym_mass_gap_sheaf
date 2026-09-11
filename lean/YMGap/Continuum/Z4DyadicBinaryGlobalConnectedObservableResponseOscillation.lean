/-
# Global oscillation of the actual connected-observable response

The normalized connected response has two causal face gradients.  Its
pairwise absolute difference is bounded by the sum of the root- and
target-face connected-envelope fractions.  This file averages that exact
pointwise statement over the physical fine-source pair law and proves

  global connected-response oscillation
    <= global root envelope fraction + global target envelope fraction.

Each face envelope is separately bounded by the SU(2)-specific anchor rate
`1449/1700`.  Their unhalved sum need not be below one; no strict global
oscillation claim is made here.  The exact factor one half in posterior
variance is the next contraction.

No centered variance, production/refresh form, dense spectral bound,
completed gap, thermodynamic limit, continuum theory, or Clay theorem is
asserted here.

Constructive contract: finite rational sums, explicit positive division,
and previously proved SU(2)-specific envelope estimates only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
trusted external computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedObservableResponseOscillation

namespace YMGap.Continuum.Z4DyadicBinaryGlobalConnectedObservableResponseOscillation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableResponseOscillation
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedResponseOscillation
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem finePhysicalPartitionSquare_pos (S : SlabScalePair) :
    (0 : Q') < S.fine.physicalPartition * S.fine.physicalPartition :=
  Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)

private theorem finePositiveSourcePairWeight_nonnegative
    (S : SlabScalePair) (pair : PositivePhysicalSourcePair S) :
    (0 : Q') ≤ finePacketFineSourceRawPairWeight
      S pair.1.1 pair.2.1 := by
  unfold finePacketFineSourceRawPairWeight
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt pair.1.2.2)
    (Q'.le_of_lt pair.2.2.2)

private theorem divPos_add_eqv_add_divPos
    (left right denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (left + right) denominator hdenominator ≈
      Q'.divPos left denominator hdenominator +
        Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.add_mul_eqv left right
    (Q'.recipPos denominator hdenominator)

/-! ## 1. Weighted global oscillation and its two-face envelope -/

/-- Fine-source-pair-weighted absolute oscillation of the normalized actual
connected-observable response. -/
def finePacketGlobalTiltedGibbsConnectedResponseOscillationMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  listQSum
    (fun pair : PositivePhysicalSourcePair S =>
      finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
        Q'.abs
          (positivePhysicalSourceTiltedGibbsConnectedResponse
              K hfineCutoff hcoarseCoupling M pair.1 -
            positivePhysicalSourceTiltedGibbsConnectedResponse
              K hfineCutoff hcoarseCoupling M pair.2))
    (positivePhysicalSourcePairs S)

def finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.divPos
    (finePacketGlobalTiltedGibbsConnectedResponseOscillationMass
      K hfineCutoff hcoarseCoupling M)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

/-- The weighted sum of both face-envelope fractions on every source pair. -/
def finePacketGlobalConnectedObservableResponseEnvelopeMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  listQSum
    (fun pair : PositivePhysicalSourcePair S =>
      finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
        (finePacketConnectedEnvelopeFraction
            S hfineCutoff hcoarseCoupling pair.1 pair.2 M.coarseRoot +
          finePacketConnectedEnvelopeFraction
            S hfineCutoff hcoarseCoupling pair.1 pair.2 M.coarseTarget))
    (positivePhysicalSourcePairs S)

def finePacketGlobalConnectedObservableResponseEnvelopeFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  Q'.divPos
    (finePacketGlobalConnectedObservableResponseEnvelopeMass
      S hfineCutoff hcoarseCoupling M)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (finePhysicalPartitionSquare_pos S)

theorem finePacketGlobalTiltedGibbsConnectedResponseOscillationMass_le_envelopeMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponseOscillationMass
        K hfineCutoff hcoarseCoupling M ≤
      finePacketGlobalConnectedObservableResponseEnvelopeMass
        S hfineCutoff hcoarseCoupling M := by
  unfold finePacketGlobalTiltedGibbsConnectedResponseOscillationMass
    finePacketGlobalConnectedObservableResponseEnvelopeMass
  apply listQSum_mono_local
  intro pair _
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (positivePhysicalTiltedGibbsConnectedResponseDifference_abs_le_envelopeFractions
      K hfineCutoff hcoarseCoupling M pair.1 pair.2)
    (finePositiveSourcePairWeight_nonnegative S pair)

theorem finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction_le_envelopeFraction
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction
        K hfineCutoff hcoarseCoupling M ≤
      finePacketGlobalConnectedObservableResponseEnvelopeFraction
        S hfineCutoff hcoarseCoupling M := by
  unfold finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction
    finePacketGlobalConnectedObservableResponseEnvelopeFraction Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (finePacketGlobalTiltedGibbsConnectedResponseOscillationMass_le_envelopeMass
      K hfineCutoff hcoarseCoupling M)
    (Q'.le_of_lt
      (Q'.recipPos_pos _ (finePhysicalPartitionSquare_pos S)))

/-! ## 2. Exact contraction into the two existing one-face envelopes -/

theorem finePacketGlobalConnectedObservableResponseEnvelopeMass_eqv_faceSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalConnectedObservableResponseEnvelopeMass
        S hfineCutoff hcoarseCoupling M ≈
      finePacketGlobalConnectedResponseEnvelopeMass
          S hfineCutoff hcoarseCoupling M.coarseRoot +
        finePacketGlobalConnectedResponseEnvelopeMass
          S hfineCutoff hcoarseCoupling M.coarseTarget := by
  unfold finePacketGlobalConnectedObservableResponseEnvelopeMass
    finePacketGlobalConnectedResponseEnvelopeMass
  refine Q'.eqv_trans _
    (listQSum
      (fun pair : PositivePhysicalSourcePair S =>
        finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
            finePacketConnectedEnvelopeFraction
              S hfineCutoff hcoarseCoupling pair.1 pair.2 M.coarseRoot +
          finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1 *
            finePacketConnectedEnvelopeFraction
              S hfineCutoff hcoarseCoupling pair.1 pair.2 M.coarseTarget)
      (positivePhysicalSourcePairs S)) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    exact Q'.mul_add_eqv
      (finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1)
      (finePacketConnectedEnvelopeFraction
        S hfineCutoff hcoarseCoupling pair.1 pair.2 M.coarseRoot)
      (finePacketConnectedEnvelopeFraction
        S hfineCutoff hcoarseCoupling pair.1 pair.2 M.coarseTarget)
  · exact listQSum_add _ _ (positivePhysicalSourcePairs S)

theorem finePacketGlobalConnectedObservableResponseEnvelopeFraction_eqv_faceSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalConnectedObservableResponseEnvelopeFraction
        S hfineCutoff hcoarseCoupling M ≈
      finePacketGlobalConnectedResponseEnvelopeFraction
          S hfineCutoff hcoarseCoupling M.coarseRoot +
        finePacketGlobalConnectedResponseEnvelopeFraction
          S hfineCutoff hcoarseCoupling M.coarseTarget := by
  unfold finePacketGlobalConnectedObservableResponseEnvelopeFraction
    finePacketGlobalConnectedResponseEnvelopeFraction
  refine Q'.eqv_trans _
    (Q'.divPos
      (finePacketGlobalConnectedResponseEnvelopeMass
          S hfineCutoff hcoarseCoupling M.coarseRoot +
        finePacketGlobalConnectedResponseEnvelopeMass
          S hfineCutoff hcoarseCoupling M.coarseTarget)
      (S.fine.physicalPartition * S.fine.physicalPartition)
      (finePhysicalPartitionSquare_pos S)) _ ?_ ?_
  · unfold Q'.divPos
    exact Q'.mul_eqv_congr_right _ _ _
      (finePacketGlobalConnectedObservableResponseEnvelopeMass_eqv_faceSum
        S hfineCutoff hcoarseCoupling M)
  · exact divPos_add_eqv_add_divPos _ _ _
      (finePhysicalPartitionSquare_pos S)

/-- The actual connected-response oscillation is bounded by the sum of the
two already-normalized one-face connected envelopes. -/
theorem finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction_le_faceEnvelopes
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction
        K hfineCutoff hcoarseCoupling M ≤
      finePacketGlobalConnectedResponseEnvelopeFraction
          S hfineCutoff hcoarseCoupling M.coarseRoot +
        finePacketGlobalConnectedResponseEnvelopeFraction
          S hfineCutoff hcoarseCoupling M.coarseTarget := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction_le_envelopeFraction
      K hfineCutoff hcoarseCoupling M)
    (Q'.le_of_eqv
      (finePacketGlobalConnectedObservableResponseEnvelopeFraction_eqv_faceSum
        S hfineCutoff hcoarseCoupling M))

/-! ## 3. SU(2)-specific anchor bounds for each causal face -/

theorem finePacketGlobalConnectedResponseEnvelopeFraction_le_anchorVacuumPacketRate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (cutoff half observableFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalConnectedResponseEnvelopeFraction
        S hfineCutoff hcoarseCoupling observableFaceId ≤
      finePacketAnchorVacuumPacketStrictRate := by
  have hforward :=
    finePacketGlobalNormalizedConnectedJointFraction_le_anchorVacuumPacketRate
      S hfineCutoff hcoarseCoupling .forward cutoff half observableFaceId
        hfine hobservableFace
  have hreverse :=
    finePacketGlobalNormalizedConnectedJointFraction_le_anchorVacuumPacketRate
      S hfineCutoff hcoarseCoupling .reverse cutoff half observableFaceId
        hfine hobservableFace
  have hsum := Q'.add_le_add hforward hreverse
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    hsum HalfPow.half_nonneg
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (finePacketGlobalConnectedResponseEnvelopeFraction_eqv_orientedAverage
        S hfineCutoff hcoarseCoupling observableFaceId))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (by
        refine Q'.eqv_trans _
          (HalfPow.half * finePacketAnchorVacuumPacketStrictRate +
            HalfPow.half * finePacketAnchorVacuumPacketStrictRate) _
          (Q'.mul_add_eqv HalfPow.half
            finePacketAnchorVacuumPacketStrictRate
            finePacketAnchorVacuumPacketStrictRate) ?_
        exact YMGap.Constructive.ExpNeg.two_halves
          finePacketAnchorVacuumPacketStrictRate)))

/-- At the named anchor, the connected response has two face contributions.
This deliberately records their sum without claiming that the sum is below
one. -/
theorem finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction_le_two_anchorRates
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (cutoff half : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half) :
    finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction
        K hfineCutoff hcoarseCoupling M ≤
      finePacketAnchorVacuumPacketStrictRate +
        finePacketAnchorVacuumPacketStrictRate := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction_le_faceEnvelopes
      K hfineCutoff hcoarseCoupling M)
    (Q'.add_le_add
      (finePacketGlobalConnectedResponseEnvelopeFraction_le_anchorVacuumPacketRate
        S hfineCutoff hcoarseCoupling cutoff half M.coarseRoot
          hfine M.coarseRoot_mem)
      (finePacketGlobalConnectedResponseEnvelopeFraction_le_anchorVacuumPacketRate
        S hfineCutoff hcoarseCoupling cutoff half M.coarseTarget
          hfine M.coarseTarget_mem))

/-! ## Axiom audit -/

#print axioms finePacketGlobalTiltedGibbsConnectedResponseOscillationMass
#print axioms finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction
#print axioms finePacketGlobalConnectedObservableResponseEnvelopeMass
#print axioms finePacketGlobalConnectedObservableResponseEnvelopeFraction
#print axioms finePacketGlobalTiltedGibbsConnectedResponseOscillationMass_le_envelopeMass
#print axioms finePacketGlobalConnectedObservableResponseEnvelopeMass_eqv_faceSum
#print axioms finePacketGlobalConnectedObservableResponseEnvelopeFraction_eqv_faceSum
#print axioms finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction_le_faceEnvelopes
#print axioms finePacketGlobalConnectedResponseEnvelopeFraction_le_anchorVacuumPacketRate
#print axioms finePacketGlobalTiltedGibbsConnectedResponseOscillationFraction_le_two_anchorRates

end YMGap.Continuum.Z4DyadicBinaryGlobalConnectedObservableResponseOscillation
