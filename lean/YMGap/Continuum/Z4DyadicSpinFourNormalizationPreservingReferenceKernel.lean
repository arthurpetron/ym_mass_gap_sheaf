/-
# Normalization-preserving reference-kernel decomposition

The preceding coupling-one audit showed that changing the fine Gibbs
coupling globally also changes the fine partition and introduces a
whole-slab Casimir payment.  A different reference route is available at
the level of block transport: compare two finite slab kernels while keeping
the actual fine Gibbs source law fixed.

Every `FiniteSlabKernel` is row-normalized, so its pushed raw target law has
total mass exactly equal to the actual fine physical partition.  This module
uses that fact to recenter the signed raw-column scale defect at an arbitrary
reference kernel.  The exact split is

  referenceKernelScaleDefect
    + coarsePartition^2 * (referenceKernelCross - actualKernelCross).

No fine-partition drift appears: both pushed crosses use the same actual
fine physical weights.  The remaining obligations are stated honestly as
a reference blocking calibration and a quadratic signed-cross comparison.
Those two inputs compile to the aggregate raw-column calibration already
consumed by the finite connected-covariance theorem.

This is an interface theorem, not a construction of the desired reference
kernel.  It does not prove that either calibration is volume-uniform, build
an all-cutoff family, take a continuum limit, perform OS/GNS reconstruction,
or prove the Yang--Mills mass gap.

Constructive contract: finite rational sums, row normalization, and exact
rational algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingPartitionDrift

namespace YMGap.Continuum.Z4DyadicSpinFourNormalizationPreservingReferenceKernel

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

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

private theorem scale_cross_reference_decomposition
    (fineSquare coarseCross coarseSquare referenceCross actualCross : Q') :
    fineSquare * coarseCross - coarseSquare * actualCross ≈
      (fineSquare * coarseCross - coarseSquare * referenceCross) +
        coarseSquare * (referenceCross - actualCross) := by
  let A := fineSquare * coarseCross
  let B := coarseSquare * actualCross
  let C := coarseSquare * referenceCross
  have hscaled :
      coarseSquare * (referenceCross + -actualCross) ≈ C + -B := by
    refine Q'.eqv_trans _
      (coarseSquare * referenceCross + coarseSquare * (-actualCross)) _
      (Q'.mul_add_eqv coarseSquare referenceCross (-actualCross)) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_neg_eqv coarseSquare actualCross)
  have hcancel : -C + (C + -B) ≈ -B := by
    refine Q'.eqv_trans _ ((-C + C) + -B) _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-C) C (-B))) ?_
    refine Q'.eqv_trans _ ((0 : Q') + -B) _
      (Q'.add_eqv_congr_right _ _ (-B) (Q'.neg_add_self_eqv C)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' (-B))
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ ((A + -C) + (C + -B)) _
    (Q'.add_eqv_congr_left _ _ _ hscaled) ?_
  refine Q'.eqv_trans _ (A + (-C + (C + -B))) _
    (Q'.add_assoc_eqv A (-C) (C + -B)) ?_
  exact Q'.add_eqv_congr_left A _ _ hcancel

private theorem physicalPartitionSquare_nonnegative
    (D : SlabPhysicalData) :
    (0 : Q') ≤ D.physicalPartition * D.physicalPartition :=
  Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
    (Q'.le_of_lt
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))

/-! ## 1. The same fine normalization -/

/-- Any proposed reference kernel pushes the same actual fine Gibbs raw
mass as the production kernel.  Its total target mass is therefore exactly
the actual fine physical partition. -/
theorem referenceKernelPushedRawMass_total_eqv_actualFinePartition
    {S : SlabScalePair} (referenceKernel : S.FiniteSlabKernel) :
    listQSum (pushedPhysicalTargetRawMass referenceKernel)
        S.coarse.physicalLabellings ≈
      S.fine.physicalPartition :=
  pushedPhysicalTargetRawMass_total referenceKernel

/-- The production kernel has the same actual fine raw normalization. -/
theorem physicalKernelPushedRawMass_total_eqv_actualFinePartition
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling) :
    listQSum
        (pushedPhysicalTargetRawMass
          (physicalKernel S hfineCutoff hcoarseCoupling))
        S.coarse.physicalLabellings ≈
      S.fine.physicalPartition :=
  pushedPhysicalTargetRawMass_total
    (physicalKernel S hfineCutoff hcoarseCoupling)

/-! ## 2. Exact kernel-to-kernel recentering -/

/-- Raw-column scale defect recentered at a reference block kernel.  The
fine and coarse physical partitions are the actual partitions from `S`;
only the pushed signed four-cell cross is replaced. -/
def normalizationPreservingReferenceKernelRawColumnScaleDefect
    (S : SlabScalePair) (referenceKernel : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  (S.fine.physicalPartition * S.fine.physicalPartition) *
      coarseObservableFourCellRawColumnCross S root target -
    (S.coarse.physicalPartition * S.coarse.physicalPartition) *
      pushedFaceRawFourCellCross referenceKernel root target

/-- The signed receiver cross is the generic pushed cross of the production
physical kernel.  This form makes the common fine normalization on both
sides of the comparison explicit. -/
theorem receiverRawColumnCross_eqv_physicalKernelPushedCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    positiveExpandedAssignmentSaturatedReceiverRawColumnCross
        S hfineCutoff hcoarseCoupling root target ≈
      pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target := by
  exact Q'.eqv_trans _ _ _
    (positiveExpandedAssignmentSaturatedReceiverRawColumnCross_eqv_actualPushed
      S hfineCutoff hcoarseCoupling root target)
    (Q'.eqv_symm
      (pushedFaceRawFourCellCross_physicalKernel_eqv_actualRaw
        S hfineCutoff hcoarseCoupling root target))

/-- Exact normalization-preserving reference-plus-kernel-discrepancy split
of the aggregate raw-column scale defect. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_normalizationPreservingReference_add
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (referenceKernel : S.FiniteSlabKernel)
    (root target : Nat) :
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
        S hfineCutoff hcoarseCoupling root target ≈
      normalizationPreservingReferenceKernelRawColumnScaleDefect
          S referenceKernel root target +
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          (pushedFaceRawFourCellCross referenceKernel root target -
            pushedFaceRawFourCellCross
              (physicalKernel S hfineCutoff hcoarseCoupling)
              root target) := by
  let fineSquare := S.fine.physicalPartition * S.fine.physicalPartition
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let coarseCross := coarseObservableFourCellRawColumnCross S root target
  let receiverCross :=
    positiveExpandedAssignmentSaturatedReceiverRawColumnCross
      S hfineCutoff hcoarseCoupling root target
  let actualCross :=
    pushedFaceRawFourCellCross
      (physicalKernel S hfineCutoff hcoarseCoupling) root target
  let referenceCross :=
    pushedFaceRawFourCellCross referenceKernel root target
  have hcrosses :
      positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
          S hfineCutoff hcoarseCoupling root target ≈
        fineSquare * coarseCross - coarseSquare * receiverCross := by
    simpa only [fineSquare, coarseSquare, coarseCross, receiverCross] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_crosses
        S hfineCutoff hcoarseCoupling root target)
  have hreceiver : receiverCross ≈ actualCross := by
    simpa only [receiverCross, actualCross] using
      (receiverRawColumnCross_eqv_physicalKernelPushedCross
        S hfineCutoff hcoarseCoupling root target)
  refine Q'.eqv_trans _
    (fineSquare * coarseCross - coarseSquare * receiverCross) _
    hcrosses ?_
  refine Q'.eqv_trans _
    (fineSquare * coarseCross - coarseSquare * actualCross) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left coarseSquare _ _ hreceiver)
  · simpa only [normalizationPreservingReferenceKernelRawColumnScaleDefect,
      fineSquare, coarseSquare, coarseCross, referenceCross, actualCross] using
      (scale_cross_reference_decomposition
        fineSquare coarseCross coarseSquare referenceCross actualCross)

/-- Absolute form of the exact split.  Unlike the global coupling-one
reference, this bound contains no partition-drift term. -/
theorem positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_normalizationPreservingReference_add
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (referenceKernel : S.FiniteSlabKernel)
    (root target : Nat) :
    Q'.abs
        (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
          S hfineCutoff hcoarseCoupling root target) ≤
      Q'.abs
          (normalizationPreservingReferenceKernelRawColumnScaleDefect
            S referenceKernel root target) +
        (S.coarse.physicalPartition * S.coarse.physicalPartition) *
          Q'.abs
            (pushedFaceRawFourCellCross referenceKernel root target -
              pushedFaceRawFourCellCross
                (physicalKernel S hfineCutoff hcoarseCoupling)
                root target) := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let reference :=
    normalizationPreservingReferenceKernelRawColumnScaleDefect
      S referenceKernel root target
  let discrepancy :=
    pushedFaceRawFourCellCross referenceKernel root target -
      pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target
  have hsplit :
      positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross
          S hfineCutoff hcoarseCoupling root target ≈
        reference + coarseSquare * discrepancy := by
    simpa only [reference, coarseSquare, discrepancy] using
      (positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_normalizationPreservingReference_add
        S hfineCutoff hcoarseCoupling referenceKernel root target)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _
      (Q'.abs_add_le' reference (coarseSquare * discrepancy)) ?_)
  apply Q'.add_le_add_left
  refine Q'.le_trans' _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le coarseSquare discrepancy)
    (Q'.le_of_eqv ?_)
  exact Q'.mul_eqv_congr_right _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg
      (by
        simpa only [coarseSquare] using
          (physicalPartitionSquare_nonnegative S.coarse)))

/-! ## 3. Honest calibration interfaces and compiler -/

/-- Blocking-law input for the normalization-preserving reference kernel. -/
def NormalizationPreservingReferenceKernelRawColumnScaleDefectCalibration
    (S : SlabScalePair) (referenceKernel : S.FiniteSlabKernel)
    (root target : Nat) (g referenceCeiling : Q') : Prop :=
  Q'.abs
      (normalizationPreservingReferenceKernelRawColumnScaleDefect
        S referenceKernel root target) ≤
    (referenceCeiling * (g * g)) *
      ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
        (S.fine.physicalPartition * S.fine.physicalPartition))

/-- Signed-cross comparison between the reference and production kernels.
Both crosses are pushed from the same actual fine Gibbs raw law. -/
def NormalizationPreservingReferenceKernelCrossCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (referenceKernel : S.FiniteSlabKernel)
    (root target : Nat) (g kernelCeiling : Q') : Prop :=
  Q'.abs
      (pushedFaceRawFourCellCross referenceKernel root target -
        pushedFaceRawFourCellCross
          (physicalKernel S hfineCutoff hcoarseCoupling) root target) ≤
    (kernelCeiling * (g * g)) *
      (S.fine.physicalPartition * S.fine.physicalPartition)

/-- The two normalization-preserving reference inputs compile to the exact
aggregate raw-column calibration required by the finite covariance theorem. -/
theorem positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_normalizationPreservingReference
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (referenceKernel : S.FiniteSlabKernel)
    (root target : Nat) (g referenceCeiling kernelCeiling : Q')
    (hreference :
      NormalizationPreservingReferenceKernelRawColumnScaleDefectCalibration
        S referenceKernel root target g referenceCeiling)
    (hkernel :
      NormalizationPreservingReferenceKernelCrossCalibration
        S hfineCutoff hcoarseCoupling referenceKernel root target
          g kernelCeiling) :
    PositiveExpandedAssignmentSaturatedRawColumnCrossCalibration
      S hfineCutoff hcoarseCoupling root target
        ((referenceCeiling + kernelCeiling) * (g * g)) := by
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let fineSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let reference :=
    normalizationPreservingReferenceKernelRawColumnScaleDefect
      S referenceKernel root target
  let discrepancy :=
    pushedFaceRawFourCellCross referenceKernel root target -
      pushedFaceRawFourCellCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target
  have hbase :=
    positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_normalizationPreservingReference_add
      S hfineCutoff hcoarseCoupling referenceKernel root target
  have hkernelScaled :
      coarseSquare * Q'.abs discrepancy ≤
        coarseSquare * ((kernelCeiling * (g * g)) * fineSquare) :=
    Q'.mul_le_mul_of_nonneg_left _ _ coarseSquare
      (by simpa only [NormalizationPreservingReferenceKernelCrossCalibration,
          discrepancy, fineSquare] using hkernel)
      (by
        simpa only [coarseSquare] using
          (physicalPartitionSquare_nonnegative S.coarse))
  have hsum := Q'.add_le_add
    (by simpa only
        [NormalizationPreservingReferenceKernelRawColumnScaleDefectCalibration,
          reference, coarseSquare, fineSquare] using hreference)
    hkernelScaled
  refine Q'.le_trans' _ _ _ hbase
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv ?_))
  simp only [coarseSquare, fineSquare]
  ring_qeqv

#print axioms referenceKernelPushedRawMass_total_eqv_actualFinePartition
#print axioms physicalKernelPushedRawMass_total_eqv_actualFinePartition
#print axioms normalizationPreservingReferenceKernelRawColumnScaleDefect
#print axioms receiverRawColumnCross_eqv_physicalKernelPushedCross
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_eqv_normalizationPreservingReference_add
#print axioms positiveExpandedAssignmentSaturatedRawColumnScaleDefectCross_abs_le_normalizationPreservingReference_add
#print axioms NormalizationPreservingReferenceKernelRawColumnScaleDefectCalibration
#print axioms NormalizationPreservingReferenceKernelCrossCalibration
#print axioms positiveExpandedAssignmentSaturatedRawColumnCrossCalibration_of_normalizationPreservingReference

end YMGap.Continuum.Z4DyadicSpinFourNormalizationPreservingReferenceKernel
