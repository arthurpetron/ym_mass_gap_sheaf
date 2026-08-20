/-
M4b -- specialize the same-object continuum contract to the wired
BF4/Faraut `SpectralMarginInput` certificate.

The AF trajectory already proves that the producer's physical spacing tends to
zero.  Consequently this adapter removes spacing cofinality from the M4
residuals.  It does not construct the remaining rate-limit modulus,
projective-correlator identification, continuum Yang--Mills existence, or
OS/GNS exact-log rate binding.
-/

import YMGap.Continuum.BF4FarautSpectralPhysicalMarginIdentification
import YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare
import YMGap.Continuum.CRealRationalProxyTracking
import YMGap.Continuum.ContinuumMassClusteringEndpoint
import YMGap.Continuum.ContinuumExactMassClusteringTarget
import YMGap.Continuum.ContinuumCorrectedExactMassTarget
import YMGap.Continuum.ContinuumExactMassScalingWindow
import YMGap.Continuum.ContinuumExactMassDecayEndpoint
import YMGap.Continuum.ContinuumSelectedExactMassDecayTarget
import YMGap.Continuum.ContinuumSelectedTheoryPins
import YMGap.Continuum.ContinuumSquaredClusteringHandoff
import YMGap.Continuum.DirectLogQuadraticRemainder
import YMGap.Continuum.ExactRateReconstructionHandoff
import YMGap.Continuum.FullLogRateInnerRegularity
import YMGap.Continuum.InverseSquareAntitoneTailControl
import YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
import YMGap.Continuum.PhysicalSeparatorContinuumRealization
import YMGap.Continuum.ProjectiveOSCorrelationHandoff
import YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff
import YMGap.Continuum.SummableCRealEventualStepVariation
import YMGap.Continuum.WilsonExactRateGapHandoff
import YMGap.Continuum.WilsonLinkedOSReconstruction
import YMGap.Continuum.WilsonBoundedMassGapHandoff
import YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
import YMGap.Continuum.WilsonIteratedNormDecayHandoff
import YMGap.Continuum.WilsonOSConnectedDecayHandoff

namespace YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AsymptoticSpectralLoc
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.CRealRationalProxyTracking
open YMGap.Continuum.ContinuumMassClusteringEndpoint
open YMGap.Continuum.ContinuumExactMassClusteringTarget
open YMGap.Continuum.ContinuumCorrectedExactMassTarget
open YMGap.Continuum.ContinuumExactMassScalingWindow
open YMGap.Continuum.ContinuumExactMassDecayEndpoint
open YMGap.Continuum.ContinuumSelectedExactMassDecayTarget
open YMGap.Continuum.ContinuumSelectedTheoryPins
open YMGap.Continuum.ContinuumSelectedTheoryPins.SelectedTheoryPins
open YMGap.Continuum.ContinuumSquaredClusteringHandoff
open YMGap.Continuum.DirectLogQuadraticRemainder
open YMGap.Continuum.EventualCRealRationalProxyTracking
open YMGap.Continuum.ExactRateReconstructionHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.FullLogRateInnerRegularity
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.InverseSquareAntitoneTailControl
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorHalfWindow
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SummableCRealEventualStepVariation
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.UnifiedContinuumFloor
open YMGap.Continuum.UniformCorrelationDecay
open YMGap.Continuum.WilsonExactRateGapHandoff
open YMGap.Continuum.WilsonLinkedOSReconstruction
open YMGap.Continuum.WilsonBoundedMassGapHandoff
open YMGap.Continuum.WilsonOperatorNormGapHandoff
open YMGap.Continuum.WilsonQuadraticFormGapHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonOSConnectedDecayHandoff

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}
    {b : Nat} {afr : AFRateModulus} {N0 : Nat}

namespace BF4FarautSpectralMarginInputExactFlow

/-- Name the exact finite-scale certificate used by the M4 specialization. -/
def continuumSourceCertificate
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  flow.fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK
    anchorDominates AF trajectory comparison bare

/-- The BF4/Faraut exact logarithmic rate family inhabits the canonical
spacing-uniform constructive-real floor interface.  This is the currency-correct
canonical frontier export: the bounded quantity is `-log(separator)/spacing`,
not the legacy rational survival product. -/
def continuumExactRateCRealFloor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    CRealFloor
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate :=
  (continuumSourceCertificate flow
    anchorDominates AF trajectory comparison bare).exactRateCRealFloor

/-- The renormalized bare comparison already carries the linear physical
margin estimate used by both the exact-log half-window and its quadratic
remainder bound. -/
def continuumLinearMarginTail
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    LinearMarginTail
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).separator
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing := by
  exact bare.toPhysicalLinearMarginTail

/-- The common tail start computed from the linear margin estimate and the
proved AF spacing-to-zero modulus. -/
def continuumExactRateStart
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) : Nat :=
  (continuumLinearMarginTail flow
    anchorDominates AF trajectory comparison bare).eventualStart
      (producer.physicalSpacingToZeroOfAFTrajectory AF trajectory)

/-- The same AF trajectory supplies the inverse-square spacing majorant on
the exact-rate family's physical spacing. -/
def continuumSpacingInverseSquare
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    InverseSquareSpacingTail
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing 0 := by
  exact producer.physicalSpacingInverseSquareOfAFTrajectory AF trajectory

/-- The proved AF spacing-to-zero modulus constructs the fixed-physical-time
sampling; it is not an independent continuum residual. -/
def continuumPhysicalSampling
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    PhysicalSeparationSampling
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing :=
  physicalSeparationSamplingOfSpacingToZero _
    (producer.physicalSpacingToZeroOfAFTrajectory AF trajectory)

/-- The computed Type-level inner regularity of one exact logarithmic rate in
the finite-scale certificate. -/
def continuumRateInnerRegularity
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (j : Nat) :
    CReal.InnerRegularity
      ((continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate j) :=
  fullMassRateInnerRegularity
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing j

/-- Exact logarithmic rates tracked by the already-proved inverse-square
normalized-loss budget of the same `SpectralMarginInput` flow.

The summability theorem is not repeated here: the wired inverse-square control
supplies both its budget and a representation-invariant antitone tail rate.
The approximation-index regularity of each exact rate is computed above.  The
only remaining analytic content here is the two-sided consecutive exact-rate
comparison. -/
structure ExactRateLossTracking
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) : Type 1 where
  /-- Computed rational-approximation threshold for the physical comparison
  of two consecutive exact rates at the requested extra tolerance. -/
  stepRate : Nat -> Q' -> Nat
  /-- The genuine physical input: consecutive represented exact rates differ
  by at most the already-summable normalized-loss allowance.  At the rational
  representation level this is required only after `stepRate`, with the
  requested extra tolerance. -/
  stepBound : forall j : Nat, forall epsilon : Q',
    (0 : Q') < epsilon -> forall k : Nat, stepRate j epsilon <= k ->
    ((continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate
          (j + 1)).approx k <=
      (((continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate j).approx k +
        flow.input.toMassNormalizedLossFlow.rateLoss j) + epsilon /\
    ((continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate j).approx k <=
      (((continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate
          (j + 1)).approx k +
        flow.input.toMassNormalizedLossFlow.rateLoss j) + epsilon

namespace ExactRateLossTracking

/-- Assemble eventual local step tracking from the computed inner modulus and
the remaining two-sided represented-real cutoff-step estimate. -/
def toCRealEventualStepTracking
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (tracking : ExactRateLossTracking flow anchorDominates AF trajectory comparison bare) :
    CRealEventualStepTracking
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate
      flow.input.toMassNormalizedLossFlow.rateLoss where
  innerRate j :=
    (continuumRateInnerRegularity flow
      anchorDominates AF trajectory comparison bare j).rate
  innerRegular := by
    intro j epsilon hepsilon p q hp hq
    exact (continuumRateInnerRegularity flow
      anchorDominates AF trajectory comparison bare j).regular
        epsilon hepsilon p q hp hq
  stepRate := tracking.stepRate
  stepBound := tracking.stepBound

/-- Reuse the wired inverse-square loss budget to construct the exact-rate
summable step-variation package. -/
def rateVariation
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (tracking : ExactRateLossTracking flow anchorDominates AF trajectory comparison bare) :
    SummableCRealEventualStepVariation
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate :=
  tracking.toCRealEventualStepTracking.withSummableBudget
    flow.input.lossBudget
    (inverseSquareTailControl flow.input.toInverseSquareControl)

end ExactRateLossTracking

/-! ## A factored sufficient route to exact-rate tracking

The existing `SpectralMarginInput` already proves the forward rational step

  g_j <= g_(j+1) + rateLoss_j.

It does not prove the reverse step, and its current `mass_certificate` is only a
one-sided lower comparison with the exact logarithmic rate.  The next structure
states precisely the two missing facts needed to obtain
`ExactRateLossTracking`: a modulus-carrying identification of `g_j` with the
exact rate, and the reverse rational step. -/

/-- A transparent sufficient factorization of the remaining exact-rate step
estimate into a same-object proxy identification and reverse rational
stability.  Neither field is supplied by the present `SpectralMarginInput`. -/
structure ExactRateProxyTracking
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) : Type 1 where
  /-- Computed two-sided identification of the exact logarithmic rate with the
  rational physical-margin proxy already carried by `SpectralMarginInput`. -/
  proxyIdentification : CRealRationalProxyIdentification
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).rateFamily.rate
    flow.input.g
  /-- The rational step direction not supplied by the existing multiplicative
  descent theorem.  The opposite direction is `additive_step`. -/
  reverseStep : forall j : Nat,
    flow.input.g (j + 1) <=
      flow.input.g j +
        flow.input.toMassNormalizedLossFlow.rateLoss j

namespace ExactRateProxyTracking

/-- The reverse residual plus the already-proved forward additive-loss step
give a two-sided rational proxy estimate. -/
def rationalTwoSidedStep
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (tracking : ExactRateProxyTracking flow
      anchorDominates AF trajectory comparison bare) :
    RationalTwoSidedStep flow.input.g
      flow.input.toMassNormalizedLossFlow.rateLoss where
  step j :=
    ⟨tracking.reverseStep j,
      flow.input.toMassNormalizedLossFlow.step_rateLoss j⟩

/-- The factored proxy route constructs the canonical minimal exact-rate
tracking residual.  Endpoint approximation errors are budgeted at half the
requested tolerance by `CRealRationalProxyTracking`. -/
def toExactRateLossTracking
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (tracking : ExactRateProxyTracking flow
      anchorDominates AF trajectory comparison bare) :
    ExactRateLossTracking flow
      anchorDominates AF trajectory comparison bare := by
  let localTracking := tracking.proxyIdentification.toCRealEventualStepTracking
    (fun j => continuumRateInnerRegularity flow
      anchorDominates AF trajectory comparison bare j)
    tracking.rationalTwoSidedStep
  exact
    { stepRate := localTracking.stepRate
      stepBound := localTracking.stepBound }

end ExactRateProxyTracking

/-! ## A physically realistic proxy route with a finite-spacing remainder

The exact logarithmic rate and the linear margin proxy need not coincide at a
finite spacing.  The next structure exposes that discrepancy as its own
nonnegative, summably controlled error stream.  This is the natural target for
a constructive logarithmic-remainder estimate. -/

/-- Sufficient data for exact-rate convergence when the rational margin proxy
approximates, rather than equals, the finite-spacing exact logarithmic rate.
The present `SpectralMarginInput` supplies the forward proxy step and the
inverse-square proxy-loss tail; it does not yet supply these four fields. -/
structure ExactRateProxyErrorTracking
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) : Type 1 where
  /-- Explicit finite-spacing discrepancy between logarithmic rate and linear
  margin proxy. -/
  error : Nat -> Q'
  proxyApproximation : CRealRationalProxyApproximation
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).rateFamily.rate
    flow.input.g error
  /-- The rational step direction not supplied by `additive_step`. -/
  reverseStep : forall j : Nat,
    flow.input.g (j + 1) <=
      flow.input.g j +
        flow.input.toMassNormalizedLossFlow.rateLoss j
  error_nonnegative : forall j : Nat, (0 : Q') <= error j
  /-- Representation-invariant constructive tail modulus for the remainder. -/
  errorTailControl : AntitoneTailControl error

/-- A concrete specialization of `ExactRateProxyErrorTracking` through the
physical linear margin.  The logarithmic comparison and its error are no
longer opaque: they are the proved bound

`marginRate <= fullMassRate <= marginRate + 3 * physMargin^2 / spacing`.

The remaining hypotheses say that the BF4 input proxy is the same rational
physical margin, that its missing reverse step holds, and that the explicit
quadratic rate error has a constructive summable tail. -/
structure ExactRatePhysicalMarginTracking
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) : Type 1 where
  halfWindow : SeparatorHalfWindow
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator
  marginProxyEqv : forall j : Nat,
    (marginRate
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).separator
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing
      j).eqv (flow.input.g j)
  reverseStep : forall j : Nat,
    flow.input.g (j + 1) <=
      flow.input.g j +
        flow.input.toMassNormalizedLossFlow.rateLoss j
  errorTailControl : AntitoneTailControl
    (quadraticRateError
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).separator
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing)

namespace ExactRatePhysicalMarginTracking

/-- The direct logarithmic remainder theorem fills the formerly opaque proxy
approximation and nonnegativity fields of `ExactRateProxyErrorTracking`. -/
def toExactRateProxyErrorTracking
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (tracking : ExactRatePhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare) :
    ExactRateProxyErrorTracking flow
      anchorDominates AF trajectory comparison bare := by
  let source := continuumSourceCertificate flow
    anchorDominates AF trajectory comparison bare
  let approximation := fullMassRateMarginProxyApproximation
    source.separator source.rateFamily.physicalSpacing tracking.halfWindow
  exact
    { error := quadraticRateError
        source.separator source.rateFamily.physicalSpacing
      proxyApproximation := approximation.proxyEqv tracking.marginProxyEqv
      reverseStep := tracking.reverseStep
      error_nonnegative := fun j =>
        quadraticRateError_nonneg
          source.separator source.rateFamily.physicalSpacing j
      errorTailControl := tracking.errorTailControl }

end ExactRatePhysicalMarginTracking

/-- The physically natural tail version of the margin factorization.  Its tail
start and half-window are computed from the renormalized bare linear-margin
estimate and AF spacing modulus; its quadratic error tail is computed from the
AF inverse-square spacing majorant.  Only the proxy identity and the missing
reverse proxy dynamics remain as fields. -/
structure ExactRateEventualPhysicalMarginTracking
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) : Type 1 where
  marginProxyEqv : forall j : Nat,
      continuumExactRateStart flow
        anchorDominates AF trajectory comparison bare <= j ->
    (marginRate
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).separator
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing
      j).eqv (flow.input.g j)
  reverseStep : forall j : Nat,
    continuumExactRateStart flow
      anchorDominates AF trajectory comparison bare <= j ->
    flow.input.g (j + 1) <=
      flow.input.g j +
        flow.input.toMassNormalizedLossFlow.rateLoss j

namespace ExactRateEventualPhysicalMarginTracking

/-- Assemble eventual exact-rate tracking from the two analytic statements at
the physical/spectral handoff.  All tail starts, logarithmic remainders, and
summability moduli are derived elsewhere in this file. -/
def ofPhysicalHandoff
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (identification :
      _root_.YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.PhysicalMarginIdentification flow)
    (upperDrift :
      _root_.YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.EventualUpperMarginDrift flow
      (continuumExactRateStart flow
        anchorDominates AF trajectory comparison bare)) :
    ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare where
  marginProxyEqv := fun j _ => by
    simpa only [continuumSourceCertificate] using
      identification.marginRate_eqv_input j
  reverseStep := upperDrift.reverseStep

/-- The preferred handoff constructor: the same-object floor identification
and the missing lower half of the spectral shift estimate imply all exact-rate
tracking fields. -/
def ofPhysicalIdentificationAndSymmetricShift
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (identification :
      _root_.YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.PhysicalMarginIdentification flow)
    (symmetric :
      _root_.YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.SymmetricSpectralShift flow) :
    ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare :=
  ofPhysicalHandoff identification
    (symmetric.toEventualUpperMarginDrift
      (continuumExactRateStart flow
        anchorDominates AF trajectory comparison bare))

/-- The eventual half-window logarithmic comparison constructs the exact
full-range rate family's global modulus-Cauchy datum.  Its outer modulus is
shifted past the start computed from the physical linear-margin tail and the
AF spacing-to-zero modulus; no estimate is asserted on the finite prefix. -/
def rateCauchy
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare) :
    CReal.ModCauchyEv
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate := by
  let source := continuumSourceCertificate flow
    anchorDominates AF trajectory comparison bare
  let linear := continuumLinearMarginTail flow
    anchorDominates AF trajectory comparison bare
  let spacingToZero := producer.physicalSpacingToZeroOfAFTrajectory AF trajectory
  let start := continuumExactRateStart flow
    anchorDominates AF trajectory comparison bare
  let approximation := eventualFullMassRateMarginProxyApproximation
    source.separator source.rateFamily.physicalSpacing start
    (linear.toEventualHalfWindow spacingToZero)
  let inputApproximation := approximation.proxyEqv tracking.marginProxyEqv
  let tailStep : RationalTwoSidedTailStep
      flow.input.g flow.input.toMassNormalizedLossFlow.rateLoss
      start :=
    { step := fun j hj =>
        ⟨tracking.reverseStep j hj,
          flow.input.toMassNormalizedLossFlow.step_rateLoss j⟩ }
  let spacingTail :=
    (continuumSpacingInverseSquare flow
      anchorDominates AF trajectory comparison bare).shifted start
  let errorTail :=
    QuadraticRateErrorTailControl.LinearMarginTail.quadraticRateErrorTailControl
      linear start (by
        unfold start continuumExactRateStart
        exact Nat.le_max_left _ _)
      (by simpa only [Nat.zero_add] using spacingTail)
  exact inputApproximation.toModCauchyEv
    (fun j => continuumRateInnerRegularity flow
      anchorDominates AF trajectory comparison bare j)
    tailStep
    flow.input.toMassNormalizedLossFlow.rateLoss_nonnegative
    (fun j => quadraticRateError_nonneg
      source.separator source.rateFamily.physicalSpacing j)
    (shiftedTailControl
      (inverseSquareTailControl flow.input.toInverseSquareControl)
      start)
    errorTail

end ExactRateEventualPhysicalMarginTracking

namespace ExactRateProxyErrorTracking

/-- Combine the residual reverse proxy step with the already-proved forward
normalized-loss step. -/
def rationalTwoSidedStep
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (tracking : ExactRateProxyErrorTracking flow
      anchorDominates AF trajectory comparison bare) :
    RationalTwoSidedStep flow.input.g
      flow.input.toMassNormalizedLossFlow.rateLoss where
  step j :=
    ⟨tracking.reverseStep j,
      flow.input.toMassNormalizedLossFlow.step_rateLoss j⟩

/-- The wired inverse-square proxy-loss control and the separately summable
finite-spacing remainder construct the exact logarithmic rate's cutoff-Cauchy
package. -/
def rateVariation
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    (tracking : ExactRateProxyErrorTracking flow
      anchorDominates AF trajectory comparison bare) :
    SummableCRealEventualStepVariation
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate :=
  tracking.proxyApproximation.toSummableCRealEventualStepVariation
    (fun j => continuumRateInnerRegularity flow
      anchorDominates AF trajectory comparison bare j)
    tracking.rationalTwoSidedStep
    flow.input.toMassNormalizedLossFlow.rateLoss_nonnegative
    tracking.error_nonnegative
    (inverseSquareTailControl flow.input.toInverseSquareControl)
    tracking.errorTailControl

end ExactRateProxyErrorTracking

/-- The still-open M4 data after the AF trajectory has already supplied the
spacing-to-zero modulus. -/
structure ContinuumResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  /-- The minimal remaining analytic rate-limit package.  It can be
  constructed from a global summable step variation or from the eventual
  physical-margin route, whose shift bridge deliberately ignores the
  irrelevant finite prefix. -/
  exactRateCauchy : CReal.ModCauchyEv
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).rateFamily.rate
  /-- The externally fixed interpretation of observables on stage measures. -/
  stageCorrelators : StageCorrelationSemantics
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator M
  /-- The physical correlators are those of the selected projective thread. -/
  projectiveIdentification : ProjectiveCorrIdentification
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator mu
    stageCorrelators
  /-- Physically rescaled continuum limits of the selected-stage correlators. -/
  continuumCorrelators : ContinuumCorrelationSemantics
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator mu
    stageCorrelators
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing
    (continuumPhysicalSampling flow
      anchorDominates AF trajectory comparison bare)
  /-- Genuine continuum Yang--Mills existence on this same measure. -/
  existence : ContinuumYMExistence mu
  /-- Measure-linked OS functional and reconstruction using the same OS4
  spectral model and separator. -/
  osGNS : MeasureLinkedOSGNSData existence
  /-- The reconstructed nonzero spectral channel is the limit of the same
  physically sampled separator-controlled correlator. -/
  reconstructionCorrelators : ReconstructionCorrIdentification
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator
    osGNS.reconstruction continuumCorrelators
  /-- Fixed connected-two-point insertion semantics in the OS algebra. -/
  osConnectedTwoPoint : OSConnectedTwoPointSemantics existence
  /-- Identification of the OS functional's connected gap correlator with the
  continuum and reconstructed spectral correlator. -/
  osGapCorrelation : OSGapCorrelationIdentification
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator
    existence osConnectedTwoPoint continuumCorrelators
    reconstructionCorrelators
  /-- Identification of the exact rate limit with the reconstruction's
  computed logarithmic Hamiltonian gap. -/
  exactGap : ExactLogGapAt osGNS.reconstruction
    (CReal.completeLimitCauchy
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate
      exactRateCauchy)

/-- The residual continuum/OS data after the exact-rate Cauchy modulus has
already been constructed from physical-margin tracking.  This separates the
two finite-scale physical/spectral inputs from the genuinely continuum
same-object obligations. -/
structure ContinuumSameObjectResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  stageCorrelators : StageCorrelationSemantics
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator M
  projectiveIdentification : ProjectiveCorrIdentification
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator mu
    stageCorrelators
  continuumCorrelators : ContinuumCorrelationSemantics
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator mu
    stageCorrelators
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing
    (continuumPhysicalSampling flow
      anchorDominates AF trajectory comparison bare)
  existence : ContinuumYMExistence mu
  osGNS : MeasureLinkedOSGNSData existence
  reconstructionCorrelators : ReconstructionCorrIdentification
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator
    osGNS.reconstruction continuumCorrelators
  osConnectedTwoPoint : OSConnectedTwoPointSemantics existence
  osGapCorrelation : OSGapCorrelationIdentification
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator
    existence osConnectedTwoPoint continuumCorrelators
    reconstructionCorrelators
  exactGap : ExactLogGapAt osGNS.reconstruction
    (CReal.completeLimitCauchy
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate
      tracking.rateCauchy)

/-- The compressed M4 residual after both the exact-rate cutoff removal and
the formal consequences of projective OS-functional convergence have been
discharged.

Compared with `ContinuumSameObjectResidualData`, the stage correlator,
projective identification, continuum correlator limit, connected OS
semantics, and OS gap-correlation identification are supplied through the
single `projectiveOS` handoff.  The OS/GNS field is strengthened to select a
concrete Wilson completion and time translation whose operator-form gap uses
the same OS4 model and separator.  Continuum YM existence, that strengthened
GNS construction, the genuine continuum spectral-channel identification, and
exact-rate convergence to the reconstructed logarithmic gap remain explicit. -/
structure ContinuumProjectiveOSResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  /-- Genuine continuum Yang--Mills existence on the selected measure. -/
  existence : ContinuumYMExistence mu
  /-- The OS functional is the limit of the selected measure thread, its
  reconstruction uses the same OS4 spectral data, and a concrete Wilson GNS
  time translation realizes that model through an operator-form gap. -/
  osGNS : WilsonLinkedOSGNSData existence
  /-- One physical-sampling handoff from the separator correlators to the
  fixed projective OS functional. -/
  projectiveOS : ProjectiveOSCorrelationHandoff
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator
    existence osGNS.measureLinked
    (continuumPhysicalSampling flow
      anchorDominates AF trajectory comparison bare)
  /-- The remaining GNS/spectral-theorem identification for the nonzero gap
  channel fixed by `projectiveOS`. -/
  spectralChannel :
    ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
      projectiveOS osGNS.reconstruction
  /-- The same finite exact-rate sequence converges to the reconstruction's
  computed logarithmic Hamiltonian gap.  Limit uniqueness will derive the
  completed-rate equality. -/
  rateReconstruction : ExactRateReconstructionHandoff
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare)
    osGNS.reconstruction

/-- The smaller residual sufficient for the bounded-transfer mass-gap
endpoint.  Unlike `ContinuumProjectiveOSResidualData`, it does not request the
projective correlator handoff or the reconstruction spectral-channel
identification, because neither enters the exact-rate/operator-norm argument.
-/
structure ContinuumWilsonBoundedResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  /-- Genuine continuum Yang--Mills existence on the selected measure. -/
  existence : ContinuumYMExistence mu
  /-- The same-measure Wilson completion, selected time translation, and
  canonical linear form gap. -/
  osGNS : WilsonLinkedOSGNSData existence
  /-- Convergence of the finite exact-rate family to the selected
  reconstruction's logarithmic separator. -/
  rateReconstruction : ExactRateReconstructionHandoff
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare)
    osGNS.reconstruction
  /-- The minimal quadratic form inequality on the selected vacuum
  complement. -/
  quadraticFormGap : WilsonQuadraticFormGapPin osGNS

/-- The irreducible BF4 residual for a bounded transfer gap supplied directly.
It omits the projective correlator channel, the canonical linear form gap, and
the quadratic-form bridge. -/
structure ContinuumWilsonMinimalBoundedResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  /-- Genuine continuum Yang--Mills existence on the selected measure. -/
  existence : ContinuumYMExistence mu
  /-- The same-measure Wilson completion and selected time translation, before
  any linear or quadratic form-gap field is imposed. -/
  osGNS : WilsonSelectedOSGNSData existence
  /-- Convergence of the finite exact-rate family to the selected
  reconstruction's logarithmic separator. -/
  rateReconstruction : ExactRateReconstructionHandoff
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare)
    osGNS.reconstruction
  /-- The direct bounded transfer-operator norm gap on the selected vacuum
  complement. -/
  operatorNormGap : WilsonOperatorNormGapPin osGNS

/-- The minimal BF4 bounded residual together with the vacuum stationarity
needed to iterate its one-step contraction. -/
structure ContinuumWilsonIteratedBoundedResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  bounded : ContinuumWilsonMinimalBoundedResidualData flow
    anchorDominates AF trajectory comparison bare tracking mu
  stationarity : WilsonVacuumStationarityPin bounded.osGNS

/-- The iterated BF4 bounded residual together with the separate same-object
identification needed to read a selected Wilson autocorrelation as an OS
connected two-point function.  This correlation package is not a premise of
the bounded mass-gap endpoint. -/
structure ContinuumWilsonOSConnectedDecayResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  iterated : ContinuumWilsonIteratedBoundedResidualData flow
    anchorDominates AF trajectory comparison bare tracking mu
  connectedPin : WilsonOSConnectedMatrixCoefficientPin iterated.bounded.osGNS

/-- The projective BF4/OS residual plus exactly the direct Wilson data needed
to prove decay of the physical continuum gap correlator it constructs. -/
structure ContinuumProjectiveWilsonDecayResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  projective : ContinuumProjectiveOSResidualData flow
    anchorDominates AF trajectory comparison bare tracking mu
  operatorNormGap : WilsonOperatorNormGapPin
    (WilsonSelectedOSGNSData.ofLinked projective.osGNS)
  stationarity : WilsonVacuumStationarityPin
    (WilsonSelectedOSGNSData.ofLinked projective.osGNS)
  continuumMatrixPin : ProjectiveWilsonOSMatrixCoefficientPin
    projective.projectiveOS
    (WilsonSelectedOSGNSData.ofLinked projective.osGNS)

namespace ContinuumSameObjectResidualData

/-- Restore the general residual package by filling its rate-Cauchy field from
the physical tracking theorem. -/
def toContinuumResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumSameObjectResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumResidualData flow
      anchorDominates AF trajectory comparison bare mu where
  exactRateCauchy := tracking.rateCauchy
  stageCorrelators := D.stageCorrelators
  projectiveIdentification := D.projectiveIdentification
  continuumCorrelators := D.continuumCorrelators
  existence := D.existence
  osGNS := D.osGNS
  reconstructionCorrelators := D.reconstructionCorrelators
  osConnectedTwoPoint := D.osConnectedTwoPoint
  osGapCorrelation := D.osGapCorrelation
  exactGap := D.exactGap

end ContinuumSameObjectResidualData

namespace ContinuumProjectiveOSResidualData

/-- Expand the compressed projective/OS boundary into the standard
same-object residual package.  All continuum-correlator convergence and OS
gap-correlation fields are theorems derived from `projectiveOS`. -/
def toContinuumSameObjectResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumSameObjectResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  stageCorrelators := D.projectiveOS.stageCorrelators
  projectiveIdentification := D.projectiveOS.projectiveIdentification
  continuumCorrelators := D.projectiveOS.continuumCorrelators
  existence := D.existence
  osGNS := D.osGNS.measureLinked
  reconstructionCorrelators :=
    D.projectiveOS.reconstructionCorrelators
      D.osGNS.reconstruction D.spectralChannel
  osConnectedTwoPoint := D.projectiveOS.osConnectedTwoPoint
  osGapCorrelation :=
    D.projectiveOS.osGapCorrelation
      D.osGNS.reconstruction D.spectralChannel
  exactGap := D.rateReconstruction.exactLogGapAt tracking.rateCauchy

end ContinuumProjectiveOSResidualData

namespace ContinuumResidualData

/-- The global exact-rate Cauchy modulus derived from the residual's local
summable two-sided step variation. -/
def rateCauchy
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumResidualData flow anchorDominates AF trajectory comparison bare mu) :
    CReal.ModCauchyEv
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare).rateFamily.rate :=
  D.exactRateCauchy

/-- The AF trajectory fills the only non-analytic field of
`ExactRateCutoffRemoval`: physical spacing cofinality. -/
def toContinuumRealization
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumResidualData flow anchorDominates AF trajectory comparison bare mu) :
    PhysicalSeparatorContinuumRealization
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare) mu where
  stageCorrelators := D.stageCorrelators
  projectiveIdentification := D.projectiveIdentification
  cutoffRemoval :=
    (ExactRateLimitData.ofRateCauchy
      D.exactRateCauchy).withSpacing
      (producer.physicalSpacingToZeroOfAFTrajectory AF trajectory)
  physicalSampling := continuumPhysicalSampling flow
    anchorDominates AF trajectory comparison bare
  continuumCorrelators := D.continuumCorrelators
  existence := D.existence
  osGNS := D.osGNS
  reconstructionCorrelators := D.reconstructionCorrelators
  osConnectedTwoPoint := D.osConnectedTwoPoint
  osGapCorrelation := D.osGapCorrelation
  exactGap := D.exactGap

/-- The exact-log conditional endpoint for the BF4/Faraut spectral-input
route. -/
def toContinuumYMWithExactLogGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumResidualData flow anchorDominates AF trajectory comparison bare mu) :
    ContinuumYMWithExactLogGap
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare) mu :=
  D.toContinuumRealization.toContinuumYMWithExactLogGap

/-- The reconstructed Hamiltonian has an exact logarithmic gap at a positive
physical rate, conditional on exactly the residual data displayed by
`ContinuumResidualData`. -/
def continuumYangMillsExactLogGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumResidualData flow anchorDominates AF trajectory comparison bare mu) :
    PositiveExactLogGapWitness D.osGNS.reconstruction :=
  PhysicalSeparatorContinuumRealization.continuumYangMillsExactLogGap
    D.toContinuumRealization

end ContinuumResidualData

namespace ContinuumSameObjectResidualData

/-- Assemble the full same-object realization after the rate-Cauchy field has
been discharged by physical tracking. -/
def toContinuumRealization
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumSameObjectResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    PhysicalSeparatorContinuumRealization
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare) mu :=
  D.toContinuumResidualData.toContinuumRealization

/-- Conditional endpoint with rate cutoff removal no longer present among the
downstream continuum assumptions. -/
def continuumYangMillsExactLogGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumSameObjectResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    PositiveExactLogGapWitness D.osGNS.reconstruction :=
  D.toContinuumResidualData.continuumYangMillsExactLogGap

end ContinuumSameObjectResidualData

namespace ContinuumProjectiveOSResidualData

/-- Assemble the full same-object realization from the compressed
projective/OS handoff. -/
def toContinuumRealization
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    PhysicalSeparatorContinuumRealization
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare) mu :=
  D.toContinuumSameObjectResidualData.toContinuumRealization

/-- The exact-log Hamiltonian-gap endpoint with the projective correlator and
OS-functional consequences compressed into one analytic handoff. -/
def continuumYangMillsExactLogGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    PositiveExactLogGapWitness D.osGNS.reconstruction :=
  D.toContinuumSameObjectResidualData.continuumYangMillsExactLogGap

/-- The exact-rate endpoint attached to the same concrete completed Wilson GNS
and selected transfer operator carried by the compressed residual. -/
def continuumWilsonExactLogGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonPositiveExactLogGapWitness D.osGNS :=
  WilsonPositiveExactLogGapWitness.ofReconstructionWitness D.osGNS
    D.continuumYangMillsExactLogGap

/-- The bounded-transfer mass-gap endpoint on the same BF4 residual datum,
conditional only on the square Schur identity for a finite-character/OS4 pin.
The exact logarithmic rate is supplied by the already-constructed cutoff
limit and reconstruction handoff. -/
def continuumWilsonBoundedMassGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    {w t : Q'} {ht : (0 : Q') <= t} {N : Nat}
    {hw0 : (0 : Q') <= w} {hw1 : w < (1 : Q')}
    {B : WilsonLinkedOSGNSData.WilsonCharacterOS4Pin
      D.osGNS.measureLinked D.osGNS.timeTranslation ht N hw0 hw1}
    (S : WilsonCharacterSquarePin B) : WilsonBoundedMassGap D.osGNS :=
  WilsonBoundedMassGap.ofCharacterSquarePin D.osGNS
    D.continuumWilsonExactLogGap S

/-- The same bounded-transfer endpoint from the minimal quadratic-form
inequality, without requiring a finite-character square resolution. -/
def continuumWilsonBoundedMassGapOfQuadraticFormGapPin
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (Q : WilsonQuadraticFormGapPin D.osGNS) : WilsonBoundedMassGap D.osGNS :=
  WilsonBoundedMassGap.ofQuadraticFormGapPin D.osGNS
    D.continuumWilsonExactLogGap Q

end ContinuumProjectiveOSResidualData

namespace ContinuumWilsonBoundedResidualData

/-- Forget the correlator and spectral-channel fields of the stronger
projective residual once a minimal quadratic-form pin has been supplied. -/
def ofProjectiveOSResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (Q : WilsonQuadraticFormGapPin D.osGNS) :
    ContinuumWilsonBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  existence := D.existence
  osGNS := D.osGNS
  rateReconstruction := D.rateReconstruction
  quadraticFormGap := Q

/-- The exact-rate cutoff removal already follows from physical tracking and
the AF spacing cofinality; it does not use continuum correlator semantics. -/
def cutoffRemoval
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (_D : ContinuumWilsonBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ExactRateCutoffRemoval
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare) :=
  (ExactRateLimitData.ofRateCauchy tracking.rateCauchy).withSpacing
    (producer.physicalSpacingToZeroOfAFTrajectory AF trajectory)

/-- The positive exact logarithmic rate needs only cutoff removal and the
same-reconstruction rate convergence, not a selected correlator channel. -/
def positiveExactLogGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    PositiveExactLogGapWitness D.osGNS.reconstruction where
  rate := D.cutoffRemoval.continuumRate
  rate_posEv := D.cutoffRemoval.continuumRate_posEv
  exactGap := D.rateReconstruction.exactLogGapAt tracking.rateCauchy

/-- Attach the reduced exact-rate witness to the same concrete Wilson datum. -/
def wilsonExactLogGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonPositiveExactLogGapWitness D.osGNS :=
  WilsonPositiveExactLogGapWitness.ofReconstructionWitness D.osGNS
    D.positiveExactLogGap

/-- The reduced residual directly yields the bounded-transfer mass-gap
endpoint. -/
def continuumWilsonBoundedMassGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonBoundedMassGap D.osGNS :=
  WilsonBoundedMassGap.ofQuadraticFormGapPin D.osGNS
    D.wilsonExactLogGap D.quadraticFormGap

end ContinuumWilsonBoundedResidualData

namespace ContinuumWilsonMinimalBoundedResidualData

/-- Forget the correlator, spectral-channel, and canonical form-gap fields of
the stronger projective residual once a direct operator-norm gap is supplied.
-/
def ofProjectiveOSResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveOSResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (N : WilsonOperatorNormGapPin
      (WilsonSelectedOSGNSData.ofLinked D.osGNS)) :
    ContinuumWilsonMinimalBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  existence := D.existence
  osGNS := WilsonSelectedOSGNSData.ofLinked D.osGNS
  rateReconstruction := D.rateReconstruction
  operatorNormGap := N

/-- The quadratic-form residual projects to the direct-norm residual.  This is
the sufficient route; the target itself does not retain either form-gap
field. -/
def ofBoundedResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumWilsonMinimalBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  existence := D.existence
  osGNS := WilsonSelectedOSGNSData.ofLinked D.osGNS
  rateReconstruction := D.rateReconstruction
  operatorNormGap := {
    normGap := fun hx => D.quadraticFormGap.selectedOperatorNormGap hx
  }

/-- Exact-rate cutoff removal from tracking and AF spacing cofinality; no
correlator or form-gap input is used. -/
def cutoffRemoval
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (_D : ContinuumWilsonMinimalBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ExactRateCutoffRemoval
      (continuumSourceCertificate flow
        anchorDominates AF trajectory comparison bare) :=
  (ExactRateLimitData.ofRateCauchy tracking.rateCauchy).withSpacing
    (producer.physicalSpacingToZeroOfAFTrajectory AF trajectory)

/-- The positive exact logarithmic rate on the selected reconstruction. -/
def positiveExactLogGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonMinimalBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    PositiveExactLogGapWitness D.osGNS.reconstruction where
  rate := D.cutoffRemoval.continuumRate
  rate_posEv := D.cutoffRemoval.continuumRate_posEv
  exactGap := D.rateReconstruction.exactLogGapAt tracking.rateCauchy

/-- The irreducible BF4 residual yields the minimal same-object bounded
mass-gap endpoint directly. -/
def continuumWilsonMinimalBoundedMassGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonMinimalBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonMinimalBoundedMassGap D.osGNS where
  exactRate := D.positiveExactLogGap
  operatorGap := D.operatorNormGap

end ContinuumWilsonMinimalBoundedResidualData

namespace ContinuumWilsonIteratedBoundedResidualData

/-- Add the one extra stationarity pin to the irreducible bounded residual. -/
def ofMinimalBoundedResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonMinimalBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (S : WilsonVacuumStationarityPin D.osGNS) :
    ContinuumWilsonIteratedBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  bounded := D
  stationarity := S

/-- The BF4 exact-rate reduction, direct norm gap, and vacuum stationarity
yield the iterated bounded-transfer endpoint. -/
def continuumWilsonIteratedBoundedMassGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonIteratedBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonIteratedBoundedMassGap D.bounded.osGNS where
  boundedGap := D.bounded.continuumWilsonMinimalBoundedMassGap
  stationarity := D.stationarity

end ContinuumWilsonIteratedBoundedResidualData

namespace ContinuumWilsonOSConnectedDecayResidualData

/-- Add the OS connected same-object pin to the iterated bounded residual
without making it part of the mass-gap endpoint itself. -/
def ofIteratedBoundedResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonIteratedBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (C : WilsonOSConnectedMatrixCoefficientPin D.bounded.osGNS) :
    ContinuumWilsonOSConnectedDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  iterated := D
  connectedPin := C

/-- The BF4 exact-rate reduction, direct norm gap, and stationarity remain the
bounded-transfer endpoint after the optional correlation data are added. -/
def continuumWilsonIteratedBoundedMassGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonOSConnectedDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonIteratedBoundedMassGap D.iterated.bounded.osGNS :=
  D.iterated.continuumWilsonIteratedBoundedMassGap

/-- Once the separate same-object OS pin is inhabited, the selected BF4
continuum branch has geometric squared decay of its connected two-point
function. -/
theorem connectedCorrelationSqDecay
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumWilsonOSConnectedDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (n : Nat) :
    RCle
      (RCmul (D.connectedPin.connectedCorrRC n)
        (D.connectedPin.connectedCorrRC n))
      (RCmul
        (RCscale
          ((D.iterated.bounded.osGNS.selectedSpectralData.gap.sep *
              D.iterated.bounded.osGNS.selectedSpectralData.gap.sep) ^ n)
          (D.iterated.bounded.osGNS.wilson.toGNSData.gnsComplete.hilbert.cinner
            D.connectedPin.gapState D.connectedPin.gapState))
        (D.iterated.bounded.osGNS.wilson.toGNSData.gnsComplete.hilbert.cinner
          D.connectedPin.gapState D.connectedPin.gapState)) :=
  D.connectedPin.connectedCorrelationSqDecay
    D.continuumWilsonIteratedBoundedMassGap n

end ContinuumWilsonOSConnectedDecayResidualData

namespace ContinuumProjectiveWilsonDecayResidualData

/-- Forget the projective correlation fields when constructing the minimal
bounded endpoint; they remain available for the separate decay theorem. -/
def minimalBoundedResidual
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveWilsonDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumWilsonMinimalBoundedResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu :=
  ContinuumWilsonMinimalBoundedResidualData.ofProjectiveOSResidualData
    D.projective D.operatorNormGap

/-- The projective correlation package retains the same minimal bounded gap
and adds the stationarity required for transfer iteration. -/
def continuumWilsonIteratedBoundedMassGap
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveWilsonDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    WilsonIteratedBoundedMassGap
      (WilsonSelectedOSGNSData.ofLinked D.projective.osGNS) where
  boundedGap := D.minimalBoundedResidual.continuumWilsonMinimalBoundedMassGap
  stationarity := D.stationarity

/-- The BF4 projective continuum gap correlator inherits the Wilson transfer's
squared geometric decay after the one explicitly named same-object pin. -/
theorem continuumGapCorrelationSqDecay
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveWilsonDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (n : Nat) :
    let W := WilsonSelectedOSGNSData.ofLinked D.projective.osGNS
    RCle
      (RCmul (D.continuumMatrixPin.continuumGapCorrRC n)
        (D.continuumMatrixPin.continuumGapCorrRC n))
      (RCmul
        (RCscale
          ((W.selectedSpectralData.gap.sep *
              W.selectedSpectralData.gap.sep) ^ n)
          (W.wilson.toGNSData.gnsComplete.hilbert.cinner
            D.continuumMatrixPin.gapState
            D.continuumMatrixPin.gapState))
        (W.wilson.toGNSData.gnsComplete.hilbert.cinner
          D.continuumMatrixPin.gapState
          D.continuumMatrixPin.gapState)) := by
  exact D.continuumMatrixPin.continuumGapCorrelationSqDecay
    D.continuumWilsonIteratedBoundedMassGap n

/-- The same BF4 endpoint is a nonvacuous constructive-real squared
clustering witness: its ratio is strictly below one and the reconstruction's
positive time-zero spectral channel supplies the nonzero floor. -/
def continuumNontrivialSquaredGeometricClustering
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveWilsonDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    NontrivialRCSquaredGeometricClustering
      D.continuumMatrixPin.continuumGapCorrRC :=
  ContinuumSquaredClusteringHandoff.ProjectiveWilsonOSMatrixCoefficientPin.continuumNontrivialSquaredGeometricClustering
    D.continuumMatrixPin D.continuumWilsonIteratedBoundedMassGap
    D.projective.spectralChannel

/-- Package the exact positive BF4 physical mass and the nontrivial projective
continuum clustering witness on the same selected Wilson object.  The fields
left in `D` remain the honest continuum/Wilson residuals. -/
def continuumMassClusteringEndpoint
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveWilsonDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumMassClusteringEndpoint
      (WilsonSelectedOSGNSData.ofLinked D.projective.osGNS)
      D.projective.projectiveOS where
  iteratedGap := D.continuumWilsonIteratedBoundedMassGap
  correlationPin := D.continuumMatrixPin
  spectralChannel := D.projective.spectralChannel

/-- Bundle the BF4 conditional endpoint as one target-facing continuum object.
This is still an export from the explicit residual `D`, not an inhabitant of
that residual for four-dimensional Yang--Mills. -/
def continuumExactMassClusteringTarget
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumProjectiveWilsonDecayResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumExactMassClusteringTarget mu where
  existence := D.projective.existence
  separator :=
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).separator
  physicalSpacing :=
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing
  sampling := continuumPhysicalSampling flow
    anchorDominates AF trajectory comparison bare
  wilson := WilsonSelectedOSGNSData.ofLinked D.projective.osGNS
  projective := D.projective.projectiveOS
  endpoint := D.continuumMassClusteringEndpoint

end ContinuumProjectiveWilsonDecayResidualData

/-- The complete BF4 projective/Wilson residual together with the one
remaining corrected continuum input: spacing-uniform physical correlation
decay whose mass is the same exact logarithmic mass exported by the BF4
endpoint.  This structure is deliberately uninhabited. -/
structure ContinuumCorrectedExactMassResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 3 where
  projectiveWilson : ContinuumProjectiveWilsonDecayResidualData flow
    anchorDominates AF trajectory comparison bare tracking mu
  uniform : ExactMassUniformDecayExtension
    projectiveWilson.continuumExactMassClusteringTarget

namespace ContinuumCorrectedExactMassResidualData

/-- Export the BF4 conditional chain directly to the corrected exact-mass,
full-O(4), spacing-uniform target.  This consumes, rather than constructs, the
explicit residual `D`. -/
def continuumCorrectedExactMassTarget
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumCorrectedExactMassResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumCorrectedExactMassTarget mu where
  exact := D.projectiveWilson.continuumExactMassClusteringTarget
  uniform := D.uniform

end ContinuumCorrectedExactMassResidualData

/-- Build the physical-volume package from exactly its genuine IR input.
Canonical floor sampling proves the no-overshoot bound; the caller supplies
only divergence of the same finite-volume correlator's physical extent. -/
def continuumPhysicalVolumeGrowthOf
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (corrected : ContinuumCorrectedExactMassResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (physicalLinearExtentDiverges :
      SelectedPhysicalLinearExtentDivergence
        corrected.continuumCorrectedExactMassTarget) :
    SelectedPhysicalVolumeGrowthPins
      corrected.continuumCorrectedExactMassTarget :=
  SelectedPhysicalVolumeGrowthPins.ofLinearExtentDivergence
    physicalLinearExtentDiverges (by
      intro j t
      exact sampledDistance_le
        (continuumSourceCertificate flow
          anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing
        j (t + 1))

/-- The BF4 corrected target together with the irreducible scaling-window
inputs needed to transport its finite-spacing physical decay estimate to its
selected continuum correlator.  The UV ratio window is omitted: canonical
floor sampling and the proved AF spacing-to-zero modulus construct it below.
This record is deliberately uninhabited; it does not manufacture continuum
existence or the thermodynamic IR window.
The source error sign and canonical floor-sampler UV/no-overshoot facts are
derived rather than repeated as residual fields.  Generic exponential
continuity, exact chunking, and fixed-power continuity reconstruct the full
physical-envelope limit. -/
structure ContinuumExactMassScalingResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 3 where
  corrected : ContinuumCorrectedExactMassResidualData flow
    anchorDominates AF trajectory comparison bare tracking mu
  physicalLinearExtentDiverges : SelectedPhysicalLinearExtentDivergence
    corrected.continuumCorrectedExactMassTarget

namespace ContinuumExactMassScalingResidualData

/-- Construct the BF4 scaling residual from the purely discrete sufficient
volume schedule `L_j+1 >= j*den(a_j)`.  All conversions from that natural
inequality to physical cofinality and then to the IR window are generic
theorems. -/
def ofLatticeExtentDenominatorSchedule
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (corrected : ContinuumCorrectedExactMassResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (schedule : SelectedLatticeExtentDenominatorSchedule
      corrected.continuumCorrectedExactMassTarget) :
    ContinuumExactMassScalingResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu where
  corrected := corrected
  physicalLinearExtentDiverges :=
    SelectedPhysicalLinearExtentDivergence.ofDiagonalGrowth
      (SelectedPhysicalLinearExtentDiagonalGrowth.ofLatticeDenominatorSchedule
        schedule)

/-- BF4's canonical floor sampling and already-proved AF spacing-to-zero
modulus construct the UV half of the physical scaling window.  This theorem
does not use any analytic window field of `D`; cofinal physical-volume growth
is its only scaling-window input. -/
def continuumPhysicalUVWindow
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumExactMassScalingResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (t : Nat) (δ : Q') (hδ : (0 : Q') < δ) :
    { J : Nat // forall j : Nat, J <= j ->
      latticeUVRatio
        (D.corrected.continuumCorrectedExactMassTarget.exact.sampling.latticeSteps
          j (t + 1)) <= δ } :=
  floorLatticeUVWindow
    (continuumSourceCertificate flow
      anchorDominates AF trajectory comparison bare).rateFamily.physicalSpacing
    (producer.physicalSpacingToZeroOfAFTrajectory AF trajectory)
    t δ hδ

/-- Specialize the standalone physical-volume constructor to the BF4
scaling residual's single thermodynamic field. -/
def continuumPhysicalVolumeGrowth
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumExactMassScalingResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    SelectedPhysicalVolumeGrowthPins
      D.corrected.continuumCorrectedExactMassTarget :=
  continuumPhysicalVolumeGrowthOf D.corrected D.physicalLinearExtentDiverges

/-- Assemble the concrete physical scaling windows.  Its UV field and
no-overshoot field are theorems; only genuine physical-volume growth is read
from `D`. -/
def physicalWindows
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumExactMassScalingResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    SelectedPhysicalScalingWindows
      D.corrected.continuumCorrectedExactMassTarget where
  uvWindow := D.continuumPhysicalUVWindow
  physicalVolume := D.continuumPhysicalVolumeGrowth

/-- Reconstruct the complete generic scaling window from the reduced BF4
residual and its derived UV cutoff.  Exponential and envelope convergence are
now generic theorems, not residual fields. -/
def scaling
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumExactMassScalingResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ExactMassUniformDecayScalingWindow
      D.corrected.continuumCorrectedExactMassTarget where
  physicalWindows := D.physicalWindows

/-- The BF4 chain reaches continuum exponential decay for the same selected
correlator and the same quotient-pinned exact logarithmic mass once the
explicit scaling residual is supplied. -/
theorem continuumExactMassDecay
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumExactMassScalingResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (t : Nat) :
    CReal.leEv
      (CReal.abs
        (D.corrected.continuumCorrectedExactMassTarget.exact.projective.continuumCorr
          D.corrected.continuumCorrectedExactMassTarget.exact.projective.gapObservable
            (t + 1)))
      (exactMassContinuumEnvelope
        D.corrected.continuumCorrectedExactMassTarget (t + 1)) :=
  D.scaling.continuumExactMassDecay t

/-- Package the BF4 endpoint as one nontrivial continuum clustering channel
with an unsquared exponential bound at the quotient-pinned exact physical
mass.  The result remains conditional on the explicit residual `D`. -/
def continuumNontrivialExactMassClustering
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumExactMassScalingResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    NontrivialExactMassContinuumClustering
      (fun t =>
        D.corrected.continuumCorrectedExactMassTarget.exact.projective.continuumCorr
          D.corrected.continuumCorrectedExactMassTarget.exact.projective.gapObservable t) :=
  ofScalingWindow D.corrected.continuumCorrectedExactMassTarget D.scaling

/-- Export the entire BF4 conditional endpoint as one target for the selected
continuum measure.  This is a packaging map only: `D` still contains every
continuum and scaling hypothesis, and the target is not quantified over compact
simple gauge groups. -/
def continuumSelectedExactMassDecayTarget
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : ContinuumExactMassScalingResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    ContinuumSelectedExactMassDecayTarget mu where
  corrected := D.corrected.continuumCorrectedExactMassTarget
  scaling := D.scaling

end ContinuumExactMassScalingResidualData

/-! ## BF4 specialization of the selected same-theory pins

The generic selected-theory interface permits any classified compact-simple
Cartan type.  BF4 is the SU(2) branch, so this final residual forces the group
type to `A₁` in the type of its UV datum.  The record remains deliberately
uninhabited: it neither manufactures the scaling residual nor any rotation,
gauge, UV, or non-Gaussianity pin. -/

/-- The conditional BF4 exact-mass endpoint together with same-theory pins
whose group-dependent UV trajectory is definitionally specialized to
`CartanType.A 1`, i.e. the SU(2) Lie type used by BF4. -/
structure BF4SU2SelectedTheoryPinResidualData
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (AF : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling AF)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison)
    (tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 3 where
  scalingResidual : ContinuumExactMassScalingResidualData flow
    anchorDominates AF trajectory comparison bare tracking mu
  rotations : SelectedRotationActionPins
    scalingResidual.continuumSelectedExactMassDecayTarget
  gauge : SelectedGaugeProjectionPins
    scalingResidual.continuumSelectedExactMassDecayTarget
  uv : SelectedGroupUVPins
    scalingResidual.continuumSelectedExactMassDecayTarget (.A 1)
  nonGaussian : SelectedCorrelationNonGaussianPin
    scalingResidual.continuumSelectedExactMassDecayTarget

namespace BF4SU2SelectedTheoryPinResidualData

/-- Assemble the generic same-theory package with group type definitionally
equal to `A₁`.  This is packaging of explicit residual fields, not a
construction of the fields. -/
def selectedTheoryPins
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : BF4SU2SelectedTheoryPinResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    SelectedTheoryPins
      D.scalingResidual.continuumSelectedExactMassDecayTarget where
  groupType := .A 1
  simpleRank := Nat.le_refl 1
  rotations := D.rotations
  gauge := D.gauge
  uv := D.uv
  nonGaussian := D.nonGaussian

/-- The assembled BF4 theory pin carries SU(2), not an arbitrary member of the
compact-simple classification. -/
theorem selectedTheoryGroupIsSU2
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : BF4SU2SelectedTheoryPinResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu) :
    D.selectedTheoryPins.groupType = .A 1 :=
  rfl

/-- Along the exact BF4-selected measure thread, the SU(2)-Casimir inverse
coupling is strictly increasing at consecutive stages. -/
theorem selectedSU2InverseCouplingStrictMono
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {flow : BF4FarautSpectralMarginInputExactFlow producer b afr N0}
    {anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N0 flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N0 flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0}
    {AF : AFTrajectoryCertificate}
    {trajectory : producer.ShiftedAFCoupling AF}
    {comparison : producer.RenormalizedPhysicalComparison}
    {bare : producer.RenormalizedBareTail comparison}
    {tracking : ExactRateEventualPhysicalMarginTracking flow
      anchorDominates AF trajectory comparison bare}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (D : BF4SU2SelectedTheoryPinResidualData flow
      anchorDominates AF trajectory comparison bare tracking mu)
    (j : Nat) :
    D.uv.stageInverseCoupling j (mu.pick j) <
      D.uv.stageInverseCoupling (j + 1) (mu.pick (j + 1)) :=
  D.selectedTheoryPins.selectedInverseCouplingStrictMono j

end BF4SU2SelectedTheoryPinResidualData

end BF4FarautSpectralMarginInputExactFlow

end YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization

#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.continuumSourceCertificate
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.continuumExactRateCRealFloor
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.continuumLinearMarginTail
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.continuumExactRateStart
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.continuumSpacingInverseSquare
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.continuumPhysicalSampling
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.continuumRateInnerRegularity
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateLossTracking.toCRealEventualStepTracking
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateLossTracking.rateVariation
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateProxyTracking.rationalTwoSidedStep
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateProxyTracking.toExactRateLossTracking
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateProxyErrorTracking.rationalTwoSidedStep
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateProxyErrorTracking.rateVariation
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRatePhysicalMarginTracking.toExactRateProxyErrorTracking
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateEventualPhysicalMarginTracking.ofPhysicalHandoff
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateEventualPhysicalMarginTracking.ofPhysicalIdentificationAndSymmetricShift
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ExactRateEventualPhysicalMarginTracking.rateCauchy
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumSameObjectResidualData.toContinuumResidualData
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumSameObjectResidualData.toContinuumRealization
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumSameObjectResidualData.continuumYangMillsExactLogGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveOSResidualData.toContinuumSameObjectResidualData
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveOSResidualData.toContinuumRealization
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveOSResidualData.continuumYangMillsExactLogGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveOSResidualData.continuumWilsonExactLogGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveOSResidualData.continuumWilsonBoundedMassGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveOSResidualData.continuumWilsonBoundedMassGapOfQuadraticFormGapPin
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonBoundedResidualData.cutoffRemoval
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonBoundedResidualData.ofProjectiveOSResidualData
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonBoundedResidualData.positiveExactLogGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonBoundedResidualData.wilsonExactLogGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonBoundedResidualData.continuumWilsonBoundedMassGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonMinimalBoundedResidualData.ofProjectiveOSResidualData
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonMinimalBoundedResidualData.ofBoundedResidualData
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonMinimalBoundedResidualData.cutoffRemoval
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonMinimalBoundedResidualData.positiveExactLogGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonMinimalBoundedResidualData.continuumWilsonMinimalBoundedMassGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonIteratedBoundedResidualData.ofMinimalBoundedResidualData
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonIteratedBoundedResidualData.continuumWilsonIteratedBoundedMassGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonOSConnectedDecayResidualData.ofIteratedBoundedResidualData
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonOSConnectedDecayResidualData.continuumWilsonIteratedBoundedMassGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumWilsonOSConnectedDecayResidualData.connectedCorrelationSqDecay
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveWilsonDecayResidualData.minimalBoundedResidual
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveWilsonDecayResidualData.continuumWilsonIteratedBoundedMassGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveWilsonDecayResidualData.continuumGapCorrelationSqDecay
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveWilsonDecayResidualData.continuumNontrivialSquaredGeometricClustering
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveWilsonDecayResidualData.continuumMassClusteringEndpoint
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumProjectiveWilsonDecayResidualData.continuumExactMassClusteringTarget
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumCorrectedExactMassResidualData.continuumCorrectedExactMassTarget
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.continuumPhysicalVolumeGrowthOf
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumExactMassScalingResidualData.ofLatticeExtentDenominatorSchedule
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumExactMassScalingResidualData.continuumPhysicalUVWindow
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumExactMassScalingResidualData.continuumPhysicalVolumeGrowth
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumExactMassScalingResidualData.physicalWindows
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumExactMassScalingResidualData.scaling
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumExactMassScalingResidualData.continuumExactMassDecay
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumExactMassScalingResidualData.continuumNontrivialExactMassClustering
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumExactMassScalingResidualData.continuumSelectedExactMassDecayTarget
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.BF4SU2SelectedTheoryPinResidualData.selectedTheoryPins
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.BF4SU2SelectedTheoryPinResidualData.selectedTheoryGroupIsSU2
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.BF4SU2SelectedTheoryPinResidualData.selectedSU2InverseCouplingStrictMono
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumResidualData.rateCauchy
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumResidualData.toContinuumRealization
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumResidualData.toContinuumYMWithExactLogGap
#print axioms YMGap.Continuum.BF4FarautSpectralMarginInputContinuumRealization.BF4FarautSpectralMarginInputExactFlow.ContinuumResidualData.continuumYangMillsExactLogGap
