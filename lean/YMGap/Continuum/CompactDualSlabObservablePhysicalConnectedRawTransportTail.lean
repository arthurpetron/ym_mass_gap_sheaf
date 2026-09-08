/-
# Preserve the connected pushed-law remainder in the physical transport tail

The exact physical raw-transport budget is already

  raw event-mismatch cost + |connected pushed-law remainder|.

The later `remainderL1` bound is conservative: it replaces the connected term
by three copies of total variation.  This module keeps the exact connected
quantity and splits its linear-in-spacing estimate from the raw-mismatch
estimate.  Separate bounds with coefficients `C_m` and `C_c` compile to the
existing complete tail with coefficient `C_m + C_c`.

This is the cancellation-preserving analytic branch.  No estimate is
inhabited here.  In particular, this module proves no refining-scale decay,
continuum measure, OS/GNS reconstruction, or physical mass gap.

Constructive contract: exact rational identities, inequalities, and
Type-valued witnesses only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverDensity
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
import YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross
import YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
import YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail

namespace YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverDensity
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualPhysicalConnectedObservableRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalRawTransportTail.PhysicalObservableRefinementSchedule
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail
open YMGap.Continuum.CompactDualSlabObservablePhysicalSeparatedRawTransportTail.PhysicalObservableRefinementSchedule

local infix:50 " ≈ " => Q'.eqv

namespace PhysicalObservableRefinementSchedule

/-! ## 1. Exact connected budget split -/

/-- The cancellation-preserving pushed-law term in the exact transport
budget. -/
def connectedRemainderBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  Q'.abs
    (centeredCylinderRemainder
      (schedule.kernel scale) (schedule.faceMap scale))

/-- The sharp second budget is exactly the matching defect of the explicit
pointwise-unit-bounded connected observable. -/
theorem connectedRemainderBudget_eqv_structuredObservableMatchDefect
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    connectedRemainderBudget schedule scale ≈
      finiteKernelObservableMatchDefect
        (schedule.kernel scale)
        (connectedRemainderObservable
          (schedule.kernel scale) (schedule.faceMap scale)) := by
  unfold connectedRemainderBudget
  exact Q'.eqv_symm
    (connectedObservableMatchDefect_eqv_abs_centeredCylinderRemainder
      (schedule.kernel scale) (schedule.faceMap scale))

/-- Pointwise unit boundedness of the structured observable improves the
old universal factor three to one copy of the pushed-law `L1` remainder. -/
theorem connectedRemainderBudget_le_remainderL1
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    connectedRemainderBudget schedule scale ≤
      (schedule.kernel scale).remainderL1 := by
  unfold connectedRemainderBudget
  exact centeredCylinderRemainder_abs_le_remainderL1
    (schedule.kernel scale) (schedule.faceMap scale)

/-- The exact transport budget displayed as its raw and connected parts. -/
def connectedSeparatedRawTransportBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) : Q' :=
  rawMismatchBudget schedule scale +
    connectedRemainderBudget schedule scale

/-- This split is exact; unlike the `remainderL1` branch, it introduces no
majorization factor. -/
theorem rawTransportBudget_eq_connectedSeparatedRawTransportBudget
    (schedule : PhysicalObservableRefinementSchedule)
    (scale : Nat) :
    schedule.rawTransportBudget scale =
      connectedSeparatedRawTransportBudget schedule scale :=
  rfl

/-! ## 2. Separate linear producers and exact compilation -/

/-- The two sharp physical estimates: raw event mismatch and the exact
connected pushed-law remainder are each linear in the same physical spacing.
No inhabitant is supplied. -/
structure ConnectedSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  connectedRemainder_le : ∀ scale : Nat, start ≤ scale →
    connectedRemainderBudget schedule scale ≤
      connectedCeiling * schedule.spacing.spacing scale

namespace ConnectedSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- No factor three is paid on the cancellation-preserving branch. -/
def combinedCeiling
    (tail : ConnectedSeparatedLinearRawTransportTail schedule) : Q' :=
  tail.mismatchCeiling + tail.connectedCeiling

theorem combinedCeiling_pos
    (tail : ConnectedSeparatedLinearRawTransportTail schedule) :
    (0 : Q') < tail.combinedCeiling :=
  Q'.add_pos tail.mismatchCeiling_pos tail.connectedCeiling_pos

/-- The two sharp producers imply the exact complete raw-transport tail. -/
theorem rawTransportBudget_le_combinedCeiling_mul_spacing
    (tail : ConnectedSeparatedLinearRawTransportTail schedule)
    (scale : Nat) (hscale : tail.start ≤ scale) :
    schedule.rawTransportBudget scale ≤
      tail.combinedCeiling * schedule.spacing.spacing scale := by
  let spacing := schedule.spacing.spacing scale
  have hmismatch :
      rawMismatchBudget schedule scale ≤
        tail.mismatchCeiling * spacing :=
    tail.mismatch_le scale hscale
  have hconnected :
      connectedRemainderBudget schedule scale ≤
        tail.connectedCeiling * spacing :=
    tail.connectedRemainder_le scale hscale
  have hsum :
      connectedSeparatedRawTransportBudget schedule scale ≤
        tail.mismatchCeiling * spacing +
          tail.connectedCeiling * spacing := by
    unfold connectedSeparatedRawTransportBudget
    exact Q'.add_le_add hmismatch hconnected
  rw [rawTransportBudget_eq_connectedSeparatedRawTransportBudget]
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          tail.mismatchCeiling tail.connectedCeiling spacing)))

/-- Compile the cancellation-preserving split into the existing complete
budget tail. -/
def toLinearRawTransportTail
    (tail : ConnectedSeparatedLinearRawTransportTail schedule) :
    LinearRawTransportTail schedule where
  start := tail.start
  ceiling := tail.combinedCeiling
  ceiling_pos := tail.combinedCeiling_pos
  budget_le := fun scale hscale =>
    tail.rawTransportBudget_le_combinedCeiling_mul_spacing scale hscale

/-- Final scale consumer for the sharp connected formulation. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : ConnectedSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale : tail.toLinearRawTransportTail.eventualStart epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ConnectedSeparatedLinearRawTransportTail

/-! ## 3. Division-free raw-cross producer -/

/-- The cancellation-preserving tail stated entirely before normalization.
The connected hypothesis is a raw cross-determinant estimate relative to the
exact fine/coarse product partition. -/
structure RawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  connectedRawCross_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (physicalObservableRawCrossDefect
          (schedule.kernel scale)
          (connectedRemainderObservable
            (schedule.kernel scale) (schedule.faceMap scale))) ≤
      (connectedCeiling * schedule.spacing.spacing scale) *
        ((schedule.scalePair scale).fine.physicalPartition *
          (schedule.scalePair scale).coarse.physicalPartition)

namespace RawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Clearing the positive product partition compiles the raw cross estimate
to the exact connected tail with no coefficient loss. -/
def toConnectedSeparatedLinearRawTransportTail
    (tail : RawCrossSeparatedLinearRawTransportTail schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedRemainder_le := fun scale hscale => by
    unfold connectedRemainderBudget
    exact connectedRemainder_abs_le_of_rawCross
      (schedule.kernel scale) (schedule.faceMap scale)
      (tail.connectedCeiling * schedule.spacing.spacing scale)
      (tail.connectedRawCross_le scale hscale)

theorem combinedCeiling_eq
    (tail : RawCrossSeparatedLinearRawTransportTail schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the division-free raw-cross producer. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : RawCrossSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end RawCrossSeparatedLinearRawTransportTail

/-! ## 4. Fully raw covariance-cross producer -/

/-- The cancellation-preserving tail with every normalized face moment
cleared.  Its connected input contains only raw joint/root/target event
numerators and the fine/coarse physical partitions. -/
structure CovarianceRawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  connectedCovarianceRawCross_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (connectedCovarianceRawCrossDefect
          (schedule.kernel scale) (schedule.faceMap scale)) ≤
      (connectedCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator
          (schedule.scalePair scale)

namespace CovarianceRawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Clearing the positive cubic partition product compiles the fully raw
covariance cross to the exact connected tail without coefficient loss. -/
def toConnectedSeparatedLinearRawTransportTail
    (tail : CovarianceRawCrossSeparatedLinearRawTransportTail schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedRemainder_le := fun scale hscale => by
    unfold connectedRemainderBudget
    exact centeredCylinderRemainder_abs_le_of_covarianceRawCross
      (schedule.kernel scale) (schedule.faceMap scale)
      (tail.connectedCeiling * schedule.spacing.spacing scale)
      (tail.connectedCovarianceRawCross_le scale hscale)

theorem combinedCeiling_eq
    (tail : CovarianceRawCrossSeparatedLinearRawTransportTail schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the fully raw covariance-cross producer. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : CovarianceRawCrossSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end CovarianceRawCrossSeparatedLinearRawTransportTail

/-! ## 5. Receiver-density-weighted paired-path producer -/

/-- The receiver-weighted production tail.  Every surviving accepted-fiber
path has been written exactly as a density times its oriented coarse receiver
pair weight.  The field below is the remaining analytic estimate: this
structure does not manufacture a density or congestion bound. -/
structure ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  actualPositiveExpandedReceiverWeightedRawCross_le :
    ∀ scale : Nat, start ≤ scale →
      Q'.abs
          (physicalConnectedCovariancePositiveExpandedReceiverWeightedRawCrossDefect
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale)) ≤
        (connectedCeiling * schedule.spacing.spacing scale) *
          connectedCovarianceRawCrossDenominator
            (schedule.scalePair scale)

namespace ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Actual-kernel specialization followed by the exact receiver-density
factorization compiles to the generic raw covariance-cross tail with no
coefficient loss. -/
def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail
        schedule) :
    CovarianceRawCrossSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedCovarianceRawCross_le := fun scale hscale => by
    have hspecialization :=
      connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    have hdensity :=
      physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedReceiverWeighted
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (by
          simpa only [kernel] using
            (Q'.eqv_trans _ _ _ hspecialization hdensity))))
      (tail.actualPositiveExpandedReceiverWeightedRawCross_le scale hscale)

def toConnectedSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the receiver-density-weighted path-cross
producer. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail

/-! ## 6. Strict-support receiver-orientable paired-path producer -/

/-- The strongest carrier-respecting production tail.  Every path carries
accepted fine fibers, strict positivity of both raw transitions, and the
constructive coarse receiver-cell orientations. -/
structure ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  actualPositiveExpandedSupportedPathRawCross_le :
    ∀ scale : Nat, start ≤ scale →
      Q'.abs
          (physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
            (schedule.scalePair scale) rfl
            (schedule.effectiveCoupling_pos scale)
            (schedule.faceMap scale)) ≤
        (connectedCeiling * schedule.spacing.spacing scale) *
          connectedCovarianceRawCrossDenominator
            (schedule.scalePair scale)

namespace ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Actual-kernel specialization followed by exact deletion of zero-raw paths
compiles to the generic raw covariance-cross tail with no coefficient loss. -/
def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail
        schedule) :
    CovarianceRawCrossSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedCovarianceRawCross_le := fun scale hscale => by
    have hspecialization :=
      connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    have hsupport :=
      physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedSupported
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (by
          simpa only [kernel] using
            (Q'.eqv_trans _ _ _ hspecialization hsupport))))
      (tail.actualPositiveExpandedSupportedPathRawCross_le scale hscale)

def toConnectedSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the strict-support receiver-orientable path
cross producer. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail

/-! ## 7. Accepted-fiber positive paired-path producer -/

/-- The strongest carrier-respecting production tail.  Every positive fine
physical source has been disintegrated over its proof-carrying accepted
intertwiner fiber, and each such endpoint projects to the same expanded
source universe used by the successful receiver-column theory. -/
structure ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  actualPositiveExpandedPathRawCross_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale)) ≤
      (connectedCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator
          (schedule.scalePair scale)

namespace ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Actual-kernel specialization followed by exact accepted-fiber summation
compiles to the generic raw covariance-cross tail with no coefficient loss. -/
def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail
        schedule) :
    CovarianceRawCrossSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedCovarianceRawCross_le := fun scale hscale => by
    have hspecialization :=
      connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    have hexpansion :=
      physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedPathRawCross
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (by
          simpa only [kernel] using
            (Q'.eqv_trans _ _ _ hspecialization hexpansion))))
      (tail.actualPositiveExpandedPathRawCross_le scale hscale)

def toConnectedSeparatedLinearRawTransportTail
    (tail :
      ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail
        schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail :
      ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail
        schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the accepted-fiber positive paired-path raw
cross producer. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail :
      ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail
        schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail

/-! ## 8. Positive paired source-to-target path producer -/

/-- The preferred carrier-respecting production tail.  Gibbs-null fine-source
paths have been deleted, every surviving source carries its positivity proof,
and its kernel entries are literal conditional recoupling raw ratios. -/
structure ActualPositivePathRawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  actualPositivePathRawCross_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (physicalConnectedCovariancePositivePathRawCrossDefect
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale)) ≤
      (connectedCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator
          (schedule.scalePair scale)

namespace ActualPositivePathRawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Actual-kernel specialization and constructive deletion of every null path
compile to the generic raw covariance-cross tail without loss. -/
def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (tail : ActualPositivePathRawCrossSeparatedLinearRawTransportTail schedule) :
    CovarianceRawCrossSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedCovarianceRawCross_le := fun scale hscale => by
    have hpositivePath := tail.actualPositivePathRawCross_le scale hscale
    have hspecialization :=
      connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    have hpositiveExpansion :=
      physicalConnectedCovarianceRawCrossDefect_eqv_positivePathRawCross
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (by
          simpa only [kernel] using
            (Q'.eqv_trans _ _ _ hspecialization hpositiveExpansion))))
      hpositivePath

def toConnectedSeparatedLinearRawTransportTail
    (tail : ActualPositivePathRawCrossSeparatedLinearRawTransportTail schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail : ActualPositivePathRawCrossSeparatedLinearRawTransportTail schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the proof-carrying positive paired-path raw
cross producer. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : ActualPositivePathRawCrossSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPositivePathRawCrossSeparatedLinearRawTransportTail

/-! ## 9. Literal all-source paired path producer -/

/-- The carrier-respecting production tail.  Its connected input is the exact
coarse-versus-pushed covariance cross after every pushed coarse-output pair
mass has been expanded into pairs of literal fine-source to coarse-target
kernel paths.  Both endpoints are therefore present for the next
receiver-column comparison. -/
structure ActualPathRawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  actualPathRawCross_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (physicalConnectedCovariancePathRawCrossDefect
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale)) ≤
      (connectedCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator
          (schedule.scalePair scale)

namespace ActualPathRawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Actual-kernel specialization followed by the exact finite Fubini path
expansion compiles to the generic raw covariance-cross tail without loss. -/
def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (tail : ActualPathRawCrossSeparatedLinearRawTransportTail schedule) :
    CovarianceRawCrossSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedCovarianceRawCross_le := fun scale hscale => by
    have hpath := tail.actualPathRawCross_le scale hscale
    have hspecialization :=
      connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    have hpathExpansion :=
      physicalConnectedCovarianceRawCrossDefect_eqv_pathRawCross
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (by
          simpa only [kernel] using
            (Q'.eqv_trans _ _ _ hspecialization hpathExpansion))))
      hpath

def toConnectedSeparatedLinearRawTransportTail
    (tail : ActualPathRawCrossSeparatedLinearRawTransportTail schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail : ActualPathRawCrossSeparatedLinearRawTransportTail schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the literal paired-path raw-cross
producer. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : ActualPathRawCrossSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualPathRawCrossSeparatedLinearRawTransportTail

/-! ## 10. Actual two-replica four-cell producer -/

/-- The four-cell production tail.  Its connected input is the exact
coarse-versus-pushed four-cell raw cross.  The pushed determinant consists of
the four positive-row raw-ratio event masses and is literally a difference of
two coarse-output pair masses. -/
structure ActualFourCellRawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  actualFourCellRawCross_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (physicalConnectedCovarianceFourCellRawCrossDefect
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale)) ≤
      (connectedCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator
          (schedule.scalePair scale)

namespace ActualFourCellRawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Exact specialization and four-cell factorization compile to the generic
raw covariance-cross tail with no coefficient loss. -/
def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (tail : ActualFourCellRawCrossSeparatedLinearRawTransportTail schedule) :
    CovarianceRawCrossSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedCovarianceRawCross_le := fun scale hscale => by
    have hfour := tail.actualFourCellRawCross_le scale hscale
    have hspecialization :=
      connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    have hfactorization :=
      physicalConnectedCovarianceRawCrossDefect_eqv_fourCellRawCross
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (by
          simpa only [kernel] using
            (Q'.eqv_trans _ _ _ hspecialization hfactorization))))
      hfour

def toConnectedSeparatedLinearRawTransportTail
    (tail : ActualFourCellRawCrossSeparatedLinearRawTransportTail schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail : ActualFourCellRawCrossSeparatedLinearRawTransportTail schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the actual four-cell raw-cross producer. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : ActualFourCellRawCrossSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualFourCellRawCrossSeparatedLinearRawTransportTail

/-! ## 11. Actual-kernel raw covariance-cross producer -/

/-- The preferred production tail.  Its connected input is the fully raw
covariance determinant specialized to the actual globally link-glued kernel,
with null fine Gibbs rows removed and every positive row exposed through its
literal recoupling raw-event ratio. -/
structure ActualCovarianceRawCrossSeparatedLinearRawTransportTail
    (schedule : PhysicalObservableRefinementSchedule) : Type where
  start : Nat
  mismatchCeiling : Q'
  mismatchCeiling_pos : (0 : Q') < mismatchCeiling
  connectedCeiling : Q'
  connectedCeiling_pos : (0 : Q') < connectedCeiling
  mismatch_le : ∀ scale : Nat, start ≤ scale →
    rawMismatchBudget schedule scale ≤
      mismatchCeiling * schedule.spacing.spacing scale
  actualConnectedCovarianceRawCross_le : ∀ scale : Nat, start ≤ scale →
    Q'.abs
        (physicalConnectedCovarianceRawCrossDefect
          (schedule.scalePair scale) rfl
          (schedule.effectiveCoupling_pos scale)
          (schedule.faceMap scale)) ≤
      (connectedCeiling * schedule.spacing.spacing scale) *
        connectedCovarianceRawCrossDenominator
          (schedule.scalePair scale)

namespace ActualCovarianceRawCrossSeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- Exact specialization of the production-kernel determinant compiles to
the generic fully raw covariance-cross tail with no coefficient loss. -/
def toCovarianceRawCrossSeparatedLinearRawTransportTail
    (tail : ActualCovarianceRawCrossSeparatedLinearRawTransportTail schedule) :
    CovarianceRawCrossSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.connectedCeiling
  connectedCeiling_pos := tail.connectedCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedCovarianceRawCross_le := fun scale hscale => by
    have hactual := tail.actualConnectedCovarianceRawCross_le scale hscale
    have hspecialization :=
      connectedCovarianceRawCrossDefect_physicalKernel_eqv_actualRaw
        (schedule.scalePair scale) rfl
        (schedule.effectiveCoupling_pos scale) (schedule.faceMap scale)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.abs_eqv_congr (by
          simpa only [kernel] using hspecialization)))
      hactual

def toConnectedSeparatedLinearRawTransportTail
    (tail : ActualCovarianceRawCrossSeparatedLinearRawTransportTail schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule :=
  tail.toCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail

theorem combinedCeiling_eq
    (tail : ActualCovarianceRawCrossSeparatedLinearRawTransportTail schedule) :
    tail.toConnectedSeparatedLinearRawTransportTail.combinedCeiling =
      tail.mismatchCeiling + tail.connectedCeiling :=
  rfl

/-- Final covariance consumer for the actual production-kernel raw cross. -/
theorem fineCovariance_le_anchorRate_add_epsilon
    (tail : ActualCovarianceRawCrossSeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      tail.toConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  tail.toConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end ActualCovarianceRawCrossSeparatedLinearRawTransportTail

/-! ## 12. Sharpen the existing raw/L1 producer without new hypotheses -/

namespace SeparatedLinearRawTransportTail

variable {schedule : PhysicalObservableRefinementSchedule}

/-- The existing raw-mismatch and `remainderL1` hypotheses compile into the
cancellation-preserving tail with coefficient `C_m + C_r`, rather than the
older conservative coefficient `C_m + 3*C_r`. -/
def toConnectedSeparatedLinearRawTransportTail
    (tail : SeparatedLinearRawTransportTail schedule) :
    ConnectedSeparatedLinearRawTransportTail schedule where
  start := tail.start
  mismatchCeiling := tail.mismatchCeiling
  mismatchCeiling_pos := tail.mismatchCeiling_pos
  connectedCeiling := tail.remainderCeiling
  connectedCeiling_pos := tail.remainderCeiling_pos
  mismatch_le := tail.mismatch_le
  connectedRemainder_le := fun scale hscale =>
    Q'.le_trans' _ _ _
      (connectedRemainderBudget_le_remainderL1 schedule scale)
      (tail.remainderL1_le scale hscale)

theorem connectedCombinedCeiling_eq
    (tail : SeparatedLinearRawTransportTail schedule) :
    (toConnectedSeparatedLinearRawTransportTail tail).combinedCeiling =
      tail.mismatchCeiling + tail.remainderCeiling :=
  rfl

/-- Final covariance consumer for the sharpened raw/L1 route. -/
theorem connectedFineCovariance_le_anchorRate_add_epsilon
    (tail : SeparatedLinearRawTransportTail schedule)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (scale : Nat)
    (hscale :
      (toConnectedSeparatedLinearRawTransportTail tail).toLinearRawTransportTail.eventualStart
        epsilon ≤ scale) :
    schedule.fineCovariance scale ≤
      schedule.anchorRate scale + epsilon :=
  (toConnectedSeparatedLinearRawTransportTail tail).fineCovariance_le_anchorRate_add_epsilon
    epsilon hepsilon scale hscale

end SeparatedLinearRawTransportTail
end PhysicalObservableRefinementSchedule

#print axioms PhysicalObservableRefinementSchedule.connectedRemainderBudget
#print axioms PhysicalObservableRefinementSchedule.connectedRemainderBudget_eqv_structuredObservableMatchDefect
#print axioms PhysicalObservableRefinementSchedule.connectedRemainderBudget_le_remainderL1
#print axioms PhysicalObservableRefinementSchedule.connectedSeparatedRawTransportBudget
#print axioms PhysicalObservableRefinementSchedule.rawTransportBudget_eq_connectedSeparatedRawTransportBudget
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail.combinedCeiling_pos
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail.rawTransportBudget_le_combinedCeiling_mul_spacing
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail.toLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ConnectedSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.RawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.RawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.RawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.RawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.CovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.CovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.CovarianceRawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.CovarianceRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail.toCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedReceiverWeightedRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail.toCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedSupportedPathRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail.toCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositiveExpandedPathRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualPositivePathRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositivePathRawCrossSeparatedLinearRawTransportTail.toCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositivePathRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPositivePathRawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPositivePathRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualPathRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPathRawCrossSeparatedLinearRawTransportTail.toCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPathRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualPathRawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualPathRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualFourCellRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualFourCellRawCrossSeparatedLinearRawTransportTail.toCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualFourCellRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualFourCellRawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualFourCellRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.ActualCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualCovarianceRawCrossSeparatedLinearRawTransportTail.toCovarianceRawCrossSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualCovarianceRawCrossSeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.ActualCovarianceRawCrossSeparatedLinearRawTransportTail.combinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.ActualCovarianceRawCrossSeparatedLinearRawTransportTail.fineCovariance_le_anchorRate_add_epsilon
#print axioms PhysicalObservableRefinementSchedule.SeparatedLinearRawTransportTail.toConnectedSeparatedLinearRawTransportTail
#print axioms PhysicalObservableRefinementSchedule.SeparatedLinearRawTransportTail.connectedCombinedCeiling_eq
#print axioms PhysicalObservableRefinementSchedule.SeparatedLinearRawTransportTail.connectedFineCovariance_le_anchorRate_add_epsilon

end YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRawTransportTail
