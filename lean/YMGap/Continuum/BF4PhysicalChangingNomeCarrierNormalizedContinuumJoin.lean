/-
# Join the repaired carrier calibration to the normalized continuum route

This module records the exact same-family meeting point between the B04
cofinal-prefix calibration and the A05 variation/continuum compilers.  The
join is deliberately a certificate type rather than an inhabitant: its four
fields are the remaining analytic inputs.  Once supplied, the downstream
objects are definitionally tied to the repaired changing-nome completed
family, the normalized moving-cube observable, and the exact scheduled rate
factor.

No asymptotic witness, physical-exponential identification, OS reconstruction,
continuum Yang--Mills theory, or Clay conclusion is asserted here.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialModulusCertificate
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
import YMGap.Constructive.CRealExplicitSqueeze
import YMGap.Continuum.SummableCRealExplicitConvergenceCertificate

namespace YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw
open YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFinitePrefixResponse
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorMovingCubeNormalizationTailCeilingCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialModulusCertificate
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.WindowedSpacingFloor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariation

/-! ## The four-input meeting point -/

/-- Raw same-observable representative variation for the repaired family. -/
def RawVariation : Type 1 :=
  MovingCubeRawScheduledRepresentativeVariation
    changingNomeCarrierNormalizedDynamicFamily

/-- Rational reciprocal-square normalization-debt variation for the repaired
family. -/
def NormDebtVariation : Type 1 :=
  MovingCubeNormalizationNormDebtRationalVariation
    changingNomeCarrierNormalizedDynamicFamily

/-- Rational variation of the exact scheduled squared-rate power for the
repaired family. -/
def RatePowerVariation : Type 1 :=
  NormalizedMovingCubeSampledRatePowerRationalVariation
    changingNomeCarrierNormalizedDynamicFamily

/- The time-zero branch of the exact scheduled rate is definitionally one and
   is compiled automatically below.  This alias keeps the remaining input
   restricted to strictly positive physical times. -/
def PositiveRatePowerVariation : Type 1 :=
  ∀ time, 0 < time ->
    SummableRationalStepVariation
      (fun scale => normalizedMovingCubeSampledRatePower
        changingNomeCarrierNormalizedDynamicFamily scale time)

/-- The honest typed join of the B04 calibration and the A05 same-observable
variation inputs.  It is intentionally not inhabited in the current
development. -/
structure Join : Type 1 where
  calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration
  raw : RawVariation
  normDebt : NormDebtVariation
  ratePower : RatePowerVariation

/-! ## The response floor transported to the canonical carrier -/

/- The response-persistence channel is definitionally the same completed
   moving-cube carrier only after its bridge equalities are used.  This
   transport is therefore kept explicit: it does not identify an arbitrary
   response channel with the canonical one by type alone. -/
def responsePersistence_toCanonicalUniformRCNormFloor
    (persistence : ChangingNomeCarrierNormalizedResponsePersistence) :
    DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel
        changingNomeCarrierNormalizedDynamicFamily) where
  floor := persistence.floor
  floor_pos := persistence.floor_pos
  floor_le := by
    intro scale
    have hprefix : persistence.floor ≤
        finitePrefixResponseFloor
          persistence.channelBridge.channel scale :=
      persistence.floor_le_prefix scale
    have hmin : finitePrefixResponseFloor
        persistence.channelBridge.channel scale ≤
        persistence.channelBridge.channel.normFloor scale :=
      finMin_le persistence.channelBridge.channel.normFloor scale scale
        (Nat.le_refl scale)
    have hchannel : CReal.RCle
        (Quotient.mk CReal.crealSetoid
          (CReal.ofQ' persistence.floor))
        (persistence.channelBridge.channel.normSq scale) := by
      refine CReal.RCle_trans ?_ (persistence.channelBridge.channel.normFloor_le scale)
      rw [CReal.RCle_mk]
      exact CReal.leEv_of_le
        (CReal.ofQ'_le_ofQ' (Q'.le_trans' _ _ _ hprefix hmin))
    have hvector :
        persistence.channelBridge.channel.vectorAt scale =
          (centralPhysicalDynamicMovingCubeRCChannel
            changingNomeCarrierNormalizedDynamicFamily).vectorAt scale := by
      exact persistence.channelBridge.vectorAt_eq scale
    simpa [DynamicVacuumSectorSameObjectRCChannel.normSq, hvector] using hchannel

/- The same response-persistence witness consequently closes the raw
   continuum nontriviality field once the raw representative variation is
   supplied.  The remaining raw variation is not hidden or weakened. -/
def rawContinuumNontrivialityOfResponsePersistence
    (persistence : ChangingNomeCarrierNormalizedResponsePersistence)
    (raw : RawVariation) :
    MovingCubeRawContinuumNontriviality
      changingNomeCarrierNormalizedDynamicFamily raw :=
  MovingCubeRawContinuumNontriviality.ofUniformNormFloor
    (responsePersistence_toCanonicalUniformRCNormFloor
      persistence)

/-! ## One same-carrier join including response persistence -/

/-- The normalized continuum inputs can be attached to the same cofinal
    concrete route that carries both response persistence and physical-gap
    calibration.  This stronger bundle prevents those two certificates from
    being supplied for unrelated presentations of the repaired family. -/
structure ConcreteJoin : Type 1 where
  cofinal : ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute
  raw : RawVariation
  normDebt : NormDebtVariation
  ratePower : RatePowerVariation

/- A uniform ceiling on the reciprocal normalization scale contracts the
   finite-prefix response floors into the exact response-persistence field.
   The finite-minimum induction is explicit; no all-scale floor is inferred
   from pointwise positivity alone. -/
private theorem changingNomeCarrierNormalizedResponseFloor_le_finMin_ofNormalizationScaleCeiling
    (bound : MovingCubeNormalizationScaleCeiling
      changingNomeCarrierNormalizedDynamicFamily)
    (window : Nat) :
    bound.rawFloor ≤
      finitePrefixResponseFloor
        changingNomeCarrierNormalizedConcreteChannelBridge.channel window := by
  change bound.rawFloor ≤
    finMin
      changingNomeCarrierNormalizedConcreteChannelBridge.channel.normFloor window
  induction window with
  | zero =>
      exact bound.rawFloor_le_channelFloor 0
  | succ window ih =>
      apply (Q'.le_min'_iff _ _ _).mpr
      exact ⟨bound.rawFloor_le_channelFloor (window + 1), ih⟩

def changingNomeCarrierNormalizedResponsePersistence_ofNormalizationScaleCeiling
    (bound : MovingCubeNormalizationScaleCeiling
      changingNomeCarrierNormalizedDynamicFamily) :
    ChangingNomeCarrierNormalizedResponsePersistence where
  channelBridge := changingNomeCarrierNormalizedConcreteChannelBridge
  floor := bound.rawFloor
  floor_pos := bound.rawFloor_pos
  floor_le_prefix :=
    changingNomeCarrierNormalizedResponseFloor_le_finMin_ofNormalizationScaleCeiling
      bound

def ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofCofinalGapCalibration
    (responsePersistence : ChangingNomeCarrierNormalizedResponsePersistence)
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration) :
    ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute where
  responsePersistence := responsePersistence
  calibration := calibration

def ConcreteJoin.ofCofinalGapCalibration
    (responsePersistence : ChangingNomeCarrierNormalizedResponsePersistence)
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration)
    (raw : RawVariation)
    (normDebt : NormDebtVariation)
    (ratePower : RatePowerVariation) :
    ConcreteJoin where
  cofinal :=
    ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofCofinalGapCalibration
      responsePersistence calibration
  raw := raw
  normDebt := normDebt
  ratePower := ratePower

/- A compatible constant physical-gap certificate can be recoded into the
   specialized cofinal calibration used by the repaired carrier.  The proof
   only transports its pointwise equality through the existing finite-min/max
   compiler; it does not construct the equality. -/
def changingNomeCarrierNormalizedPhysicalGapBounds_ofConstantPhysicalGapCalibration
    (calibration :
      DynamicVacuumSectorObservablePin.ConstantPhysicalGapCalibration
        changingNomeCarrierNormalizedDynamicFamily) :
    ChangingNomeCarrierNormalizedPhysicalGapBounds where
  floor := calibration.value
  floor_pos := calibration.value_pos
  ceiling := calibration.value
  ceiling_pos := calibration.value_pos
  floor_le_gap := by
    intro scale
    exact Q'.le_of_eqv (Q'.eqv_symm (calibration.physicalGap_eqv scale))
  gap_le_ceiling := by
    intro scale
    exact Q'.le_of_eqv (calibration.physicalGap_eqv scale)

def changingNomeCarrierNormalizedCofinalGapCalibration_ofConstantPhysicalGapCalibration
    (calibration :
      DynamicVacuumSectorObservablePin.ConstantPhysicalGapCalibration
        changingNomeCarrierNormalizedDynamicFamily) :
    ChangingNomeCarrierNormalizedCofinalGapCalibration :=
  (changingNomeCarrierNormalizedPhysicalGapBounds_ofConstantPhysicalGapCalibration
    calibration).toCofinalGapCalibration

def changingNomeCarrierNormalizedPhysicalGapBounds_ofHeadEnergyProductBand
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand) :
    ChangingNomeCarrierNormalizedPhysicalGapBounds where
  floor := band.floor
  floor_pos := band.floor_pos
  ceiling := band.ceiling
  ceiling_pos := band.ceiling_pos
  floor_le_gap := by
    intro scale
    exact DynamicVacuumSectorPhysicalRateBand.floor_le_physicalGap
      (band.toPhysicalRateBand) scale
  gap_le_ceiling := by
    intro scale
    exact DynamicVacuumSectorPhysicalRateBand.physicalGap_le_ceiling
      (band.toPhysicalRateBand) scale

def changingNomeCarrierNormalizedCofinalGapCalibration_ofHeadEnergyProductBand
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand) :
    ChangingNomeCarrierNormalizedCofinalGapCalibration :=
  (changingNomeCarrierNormalizedPhysicalGapBounds_ofHeadEnergyProductBand
    band).toCofinalGapCalibration

def ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofConstantPhysicalGapCalibration
    (responsePersistence : ChangingNomeCarrierNormalizedResponsePersistence)
    (calibration :
      DynamicVacuumSectorObservablePin.ConstantPhysicalGapCalibration
        changingNomeCarrierNormalizedDynamicFamily) :
    ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute :=
  ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofCofinalGapCalibration
    responsePersistence
    (changingNomeCarrierNormalizedCofinalGapCalibration_ofConstantPhysicalGapCalibration
      calibration)

def ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofHeadEnergyProductBand
    (responsePersistence : ChangingNomeCarrierNormalizedResponsePersistence)
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand) :
    ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute :=
  ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofCofinalGapCalibration
    responsePersistence
    (changingNomeCarrierNormalizedCofinalGapCalibration_ofHeadEnergyProductBand band)

def ConcreteJoin.ofConstantPhysicalGapCalibration
    (responsePersistence : ChangingNomeCarrierNormalizedResponsePersistence)
    (calibration :
      DynamicVacuumSectorObservablePin.ConstantPhysicalGapCalibration
        changingNomeCarrierNormalizedDynamicFamily)
    (raw : RawVariation)
    (normDebt : NormDebtVariation)
    (ratePower : RatePowerVariation) :
    ConcreteJoin where
  cofinal :=
    ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofConstantPhysicalGapCalibration
      responsePersistence calibration
  raw := raw
  normDebt := normDebt
  ratePower := ratePower

def ConcreteJoin.ofHeadEnergyProductBand
    (responsePersistence : ChangingNomeCarrierNormalizedResponsePersistence)
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand)
    (raw : RawVariation)
    (normDebt : NormDebtVariation)
    (ratePower : RatePowerVariation) :
    ConcreteJoin where
  cofinal :=
    ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofHeadEnergyProductBand
      responsePersistence band
  raw := raw
  normDebt := normDebt
  ratePower := ratePower

def ConcreteJoin.ofNormalizationScaleCeiling
    (bound : MovingCubeNormalizationScaleCeiling
      changingNomeCarrierNormalizedDynamicFamily)
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration)
    (raw : RawVariation)
    (normDebt : NormDebtVariation)
    (ratePower : RatePowerVariation) :
    ConcreteJoin :=
  ConcreteJoin.ofCofinalGapCalibration
    (changingNomeCarrierNormalizedResponsePersistence_ofNormalizationScaleCeiling
      bound)
    calibration raw normDebt ratePower

def ConcreteJoin.ofNormalizationScaleCeilingAndHeadEnergyProductBand
    (bound : MovingCubeNormalizationScaleCeiling
      changingNomeCarrierNormalizedDynamicFamily)
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand)
    (raw : RawVariation)
    (normDebt : NormDebtVariation)
    (ratePower : RatePowerVariation) :
    ConcreteJoin :=
  ConcreteJoin.ofNormalizationScaleCeiling
    bound
    (changingNomeCarrierNormalizedCofinalGapCalibration_ofHeadEnergyProductBand
      band)
    raw normDebt ratePower

def ConcreteJoin.ofNormalizationScaleVariation
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration)
    (raw : RawVariation)
    (ratePower : RatePowerVariation) :
    ConcreteJoin :=
  ConcreteJoin.ofNormalizationScaleCeiling
    (MovingCubeNormalizationScaleCeiling.ofScaleVariation scaleVariation)
    calibration raw
    (MovingCubeNormalizationScaleCeiling.normDebtRationalVariationOfScaleVariation
      scaleVariation)
    ratePower

def ConcreteJoin.ofNormalizationScaleVariationAndHeadEnergyProductBand
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand)
    (raw : RawVariation)
    (ratePower : RatePowerVariation) :
    ConcreteJoin :=
  ConcreteJoin.ofNormalizationScaleVariation
    scaleVariation
    (changingNomeCarrierNormalizedCofinalGapCalibration_ofHeadEnergyProductBand
      band)
    raw ratePower

def ConcreteJoin.ofNormalizationScaleVariationAndPositiveRatePower
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration)
    (raw : RawVariation)
    (positiveRatePower : PositiveRatePowerVariation) :
    ConcreteJoin :=
  ConcreteJoin.ofNormalizationScaleVariation
    scaleVariation calibration raw
    (normalizedMovingCubeSampledRatePowerRationalVariationOfPositive
      changingNomeCarrierNormalizedDynamicFamily positiveRatePower)

def ConcreteJoin.ofNormalizationScaleVariationAndHeadEnergyProductBandAndPositiveRatePower
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand)
    (raw : RawVariation)
    (positiveRatePower : PositiveRatePowerVariation) :
    ConcreteJoin :=
  ConcreteJoin.ofNormalizationScaleVariationAndPositiveRatePower
    scaleVariation
    (changingNomeCarrierNormalizedCofinalGapCalibration_ofHeadEnergyProductBand
      band)
    raw positiveRatePower

/-- Forget only the response-persistence field to reuse the existing
    calibration/raw/debt/rate contraction. -/
def ConcreteJoin.toJoin (data : ConcreteJoin) : Join where
  calibration := data.cofinal.calibration
  raw := data.raw
  normDebt := data.normDebt
  ratePower := data.ratePower

def ConcreteJoin.toCanonicalUniformRCNormFloor (data : ConcreteJoin) :
    DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel
        changingNomeCarrierNormalizedDynamicFamily) :=
  responsePersistence_toCanonicalUniformRCNormFloor
    data.cofinal.responsePersistence

def ConcreteJoin.toRawContinuumNontriviality (data : ConcreteJoin) :
    MovingCubeRawContinuumNontriviality
      changingNomeCarrierNormalizedDynamicFamily data.raw :=
  MovingCubeRawContinuumNontriviality.ofUniformNormFloor
    data.toCanonicalUniformRCNormFloor

/-! ## Exact downstream compilations -/

/-- The cofinal calibration gives the all-scale physical rate band on the
identical repaired completed family. -/
def Join.toPhysicalRateBand (data : Join) :
    DynamicVacuumSectorPhysicalRateBand
      changingNomeCarrierNormalizedDynamicFamily :=
  data.calibration.toPhysicalRateBand

/-- The raw and normalization-debt streams give the normalized continuum
same-observable RC limit. -/
def Join.toContinuumLimit (data : Join) :
    NormalizedMovingCubeScheduledRCContinuumLimit
      changingNomeCarrierNormalizedDynamicFamily :=
  normalizedMovingCubeLimitOfRationalDebtVariation
    changingNomeCarrierNormalizedDynamicFamily data.raw data.normDebt

/-- The scheduled-rate variation gives the exact constructive-real limit of the
finite squared-rate factor, without identifying it with a physical exponential.
-/
def Join.toRatePowerLimit (data : Join) :
    NormalizedMovingCubeSampledRatePowerLimit
      changingNomeCarrierNormalizedDynamicFamily :=
  normalizedMovingCubeSampledRatePowerLimitOfVariation
    changingNomeCarrierNormalizedDynamicFamily
    (normalizedMovingCubeSampledRatePowerVariationOfRational
      changingNomeCarrierNormalizedDynamicFamily data.ratePower)

/-- The scalar physical-gap interface produced by the joined calibration. -/
def Join.toContinuumGapTheorem (data : Join) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  data.toPhysicalRateBand.toContinuumGapTheorem

/-! ## Rejoined consequences -/

theorem Join.zero_isPositive (data : Join) :
    RCIsPositive
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        data.toContinuumLimit 0) :=
  normalizedMovingCubeLimitOfRationalDebtVariation_zero_isPositive
    changingNomeCarrierNormalizedDynamicFamily data.raw data.normDebt

/-- The normalized unit floor survives the joined cutoff limit.  This is
stronger than mere positivity: once the four-input join is supplied, the
same-object continuum response at time zero is at least one in the exact
constructive-real order. -/
theorem Join.zero_floor (data : Join) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        data.toContinuumLimit 0) :=
  NormalizedMovingCubeScheduledRCContinuumLimit.one_le_continuumConnectedAutocorrelation_zero
    data.toContinuumLimit

/-- The joined same-object limit and exact scheduled rate-power limit form the
direct rate-power clustering contract.  This retains the actual CReal rate
stream and does not identify it with a fixed rational ratio or a physical
exponential. -/
def Join.toRatePowerClustering (data : Join) :
    NontrivialRCSquaredRatePowerClustering
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        data.toContinuumLimit) :=
  NormalizedMovingCubeContinuumCertificate.toNontrivialRCSquaredRatePowerClusteringOfLimits
    changingNomeCarrierNormalizedDynamicFamily
    data.toContinuumLimit data.toRatePowerLimit

/-! ## The next physical-exponential handoff -/

/-- The repaired completed family has a strictly positive finite transfer rate
at every scale.  This is a finite-family fact; it is not a uniform physical
mass bound. -/
theorem carrierNormalized_rate_pos (scale : Nat) :
    (0 : Q') <
      (changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate := by
  rw [changingNomeCarrierNormalizedDynamicFamily_same_gap_rate]
  exact cutoffUniformRate_pos (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale))

/-- The physical-exponential corridor needs one additional exact variation
certificate: consecutive-scale variation of the same family's physical gap.
The existing `Join` supplies every other field, so this structure isolates the
remaining analytic input without weakening its identity. -/
structure PhysicalExponentialJoin : Type 1 where
  core : Join
  gapVariation : SummableRationalStepVariation
    changingNomeCarrierNormalizedDynamicFamily.physicalGap

def PhysicalExponentialJoin.ofNormalizationScaleVariationAndPositiveRatePower
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration)
    (raw : RawVariation)
    (positiveRatePower : PositiveRatePowerVariation)
    (gapVariation : SummableRationalStepVariation
      changingNomeCarrierNormalizedDynamicFamily.physicalGap) :
    PhysicalExponentialJoin where
  core :=
    (ConcreteJoin.ofNormalizationScaleVariationAndPositiveRatePower
      scaleVariation calibration raw positiveRatePower).toJoin
  gapVariation := gapVariation

def PhysicalExponentialJoin.ofNormalizationScaleVariationAndHeadEnergyProductBandAndPositiveRatePower
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand)
    (raw : RawVariation)
    (positiveRatePower : PositiveRatePowerVariation)
    (gapVariation : SummableRationalStepVariation
      changingNomeCarrierNormalizedDynamicFamily.physicalGap) :
    PhysicalExponentialJoin where
  core :=
    (ConcreteJoin.ofNormalizationScaleVariationAndHeadEnergyProductBandAndPositiveRatePower
      scaleVariation band raw positiveRatePower).toJoin
  gapVariation := gapVariation

def PhysicalExponentialJoin.ofNormalizationScaleVariationAndConstantPhysicalGapCalibrationAndPositiveRatePower
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (calibration :
      DynamicVacuumSectorObservablePin.ConstantPhysicalGapCalibration
        changingNomeCarrierNormalizedDynamicFamily)
    (raw : RawVariation)
    (positiveRatePower : PositiveRatePowerVariation) :
    PhysicalExponentialJoin where
  core :=
    (ConcreteJoin.ofNormalizationScaleVariationAndPositiveRatePower
      scaleVariation
      (changingNomeCarrierNormalizedCofinalGapCalibration_ofConstantPhysicalGapCalibration
        calibration)
      raw positiveRatePower).toJoin
  gapVariation := calibration.toVariation

/-- The lower physical-exponential handoff exposes the same primitive
    margin/reciprocal-spacing decomposition already available at the Wilson
    layer.  The reciprocal stream is deliberately an explicit backward input;
    it is not inferred from the repaired spacing schedule. -/
def PhysicalExponentialJoin.ofNormalizationScaleVariationAndMarginAndReciprocalSpacingAndPositiveRatePower
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration)
    (raw : RawVariation)
    (positiveRatePower : PositiveRatePowerVariation)
    (marginVariation : SummableRationalStepVariation
      changingNomeCarrierNormalizedDynamicFamily.latticeMargin)
    (reciprocalSpacingVariation : SummableRationalStepVariation
      (fun scale =>
        Q'.recipPos
          (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
          (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))) :
    PhysicalExponentialJoin where
  core :=
    (ConcreteJoin.ofNormalizationScaleVariationAndPositiveRatePower
      scaleVariation calibration raw positiveRatePower).toJoin
  gapVariation := physicalGapVariationOfMarginAndReciprocalSpacing
    changingNomeCarrierNormalizedDynamicFamily marginVariation
      reciprocalSpacingVariation

/-- Head-energy calibration specialization of the primitive physical-gap
    handoff.  All fields remain tied to the same repaired completed family. -/
def PhysicalExponentialJoin.ofNormalizationScaleVariationAndHeadEnergyProductBandAndMarginAndReciprocalSpacingAndPositiveRatePower
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (band : ChangingNomeCarrierNormalizedHeadEnergyProductBand)
    (raw : RawVariation)
    (positiveRatePower : PositiveRatePowerVariation)
    (marginVariation : SummableRationalStepVariation
      changingNomeCarrierNormalizedDynamicFamily.latticeMargin)
    (reciprocalSpacingVariation : SummableRationalStepVariation
      (fun scale =>
        Q'.recipPos
          (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
          (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))) :
    PhysicalExponentialJoin where
  core :=
    (ConcreteJoin.ofNormalizationScaleVariationAndHeadEnergyProductBandAndPositiveRatePower
      scaleVariation band raw positiveRatePower).toJoin
  gapVariation := physicalGapVariationOfMarginAndReciprocalSpacing
    changingNomeCarrierNormalizedDynamicFamily marginVariation
      reciprocalSpacingVariation

/-- The repaired spacing schedule has an explicit modulus to zero, so the
    bounded summable reciprocal-spacing interface is incompatible with it. -/
theorem noChangingNomeCarrierNormalizedReciprocalSpacingVariation
    (reciprocalSpacingVariation : SummableRationalStepVariation
      (fun scale =>
        Q'.recipPos
          (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing scale)
          (changingNomeCarrierNormalizedDynamicFamily.transferSpacing.spacing_pos scale))) :
    False :=
  YMGap.Continuum.SummableRationalReciprocalSpacingNoGo.noSummableReciprocalSpacingVariation
    changingNomeCarrierNormalizedDynamicFamily.transferSpacing
    changingNomeCarrierNormalizedDynamicFamily.transferSpacingToZero
    reciprocalSpacingVariation

/-- Compile the repaired-family join plus the single physical-gap variation
input into the existing same-object physical-exponential certificate. -/
def PhysicalExponentialJoin.toCertificate
    (data : PhysicalExponentialJoin) :
    NormalizedMovingCubePhysicalExponentialCertificate
      changingNomeCarrierNormalizedDynamicFamily :=
  NormalizedMovingCubePhysicalExponentialCertificate.ofRationalVariations
    changingNomeCarrierNormalizedDynamicFamily
    data.core.raw data.core.normDebt
    data.core.toPhysicalRateBand
    carrierNormalized_rate_pos
    data.gapVariation
    data.core.ratePower

/-- The rational scheduled-rate variation already carries an explicit CReal
convergence modulus for the exact middle stream used by the physical-
exponential corridor.  This projection exposes that witness without trying to
extract endpoint moduli from the propositional Euler squeeze. -/
def PhysicalExponentialJoin.ratePowerExplicitCertificate
    (data : PhysicalExponentialJoin) (time : Nat) :
    CReal.ExplicitConvergenceCertificate
      (fun scale => CReal.ofQ'
        (normalizedMovingCubeSampledRatePower
          changingNomeCarrierNormalizedDynamicFamily scale time))
      ((normalizedMovingCubePhysicalExponentialLimit
        changingNomeCarrierNormalizedDynamicFamily data.core.ratePower).limitRepresentative
        time) :=
  SummableCRealStepVariation.toExplicitConvergenceCertificate
    ((data.core.ratePower time).toSummableCRealStepVariation)

/-- Compile the physical-exponential join plus its explicit endpoint moduli
into the modulus-refined same-object certificate. -/
def PhysicalExponentialJoin.toModulusCertificate
    (data : PhysicalExponentialJoin)
    (upperModulus : ∀ time : Nat,
      CReal.ExplicitConvergenceCertificate
        (fun scale => scheduledSquaredRateUpperExponential
          changingNomeCarrierNormalizedDynamicFamily scale time)
        ((normalizedMovingCubePhysicalExponentialLimit
          changingNomeCarrierNormalizedDynamicFamily data.core.ratePower).limitRepresentative
          time))
    (lowerModulus : ∀ time : Nat,
      CReal.ExplicitConvergenceCertificate
        (fun scale => scheduledSquaredRateLowerExponential
          changingNomeCarrierNormalizedDynamicFamily carrierNormalized_rate_pos scale time)
        ((normalizedMovingCubePhysicalExponentialLimit
          changingNomeCarrierNormalizedDynamicFamily data.core.ratePower).limitRepresentative
          time)) :
    NormalizedMovingCubePhysicalExponentialModulusCertificate
      changingNomeCarrierNormalizedDynamicFamily :=
  NormalizedMovingCubePhysicalExponentialModulusCertificate.ofRationalVariations
    changingNomeCarrierNormalizedDynamicFamily
    data.core.raw data.core.normDebt
    data.core.toPhysicalRateBand
    carrierNormalized_rate_pos
    data.gapVariation
    data.core.ratePower
    upperModulus lowerModulus

/-! ## Explicit squeeze handoff -/

/--
The endpoint-modulus constructor after the Prop/Type wall has been factored
into its minimal typed inputs.  The supplied order witnesses and width
certificate are compiled against the exact middle certificate selected by
`ratePowerExplicitCertificate`; the resulting endpoint certificates are then
fed to the existing same-family modulus refinement.

This does not construct those order/width witnesses.  It makes their precise
remaining interface observable and prevents a later consumer from pairing an
endpoint modulus with a different rate-power limit.
-/
def PhysicalExponentialJoin.toModulusCertificateOfExplicitSandwich
    (data : PhysicalExponentialJoin)
    (lowerLeMiddle : ∀ time : Nat, ∀ scale : Nat,
      CReal.ExplicitLeEv
        (scheduledSquaredRateLowerExponential
          changingNomeCarrierNormalizedDynamicFamily carrierNormalized_rate_pos
            scale time)
        (CReal.ofQ'
          (normalizedMovingCubeSampledRatePower
            changingNomeCarrierNormalizedDynamicFamily scale time)))
    (middleLeUpper : ∀ time : Nat, ∀ scale : Nat,
      CReal.ExplicitLeEv
        (CReal.ofQ'
          (normalizedMovingCubeSampledRatePower
            changingNomeCarrierNormalizedDynamicFamily scale time))
        (scheduledSquaredRateUpperExponential
          changingNomeCarrierNormalizedDynamicFamily scale time))
    (width : ∀ time : Nat,
      CReal.ExplicitWidth
        (fun scale =>
          scheduledSquaredRateLowerExponential
            changingNomeCarrierNormalizedDynamicFamily carrierNormalized_rate_pos
              scale time)
        (fun scale =>
          scheduledSquaredRateUpperExponential
            changingNomeCarrierNormalizedDynamicFamily scale time)) :
    NormalizedMovingCubePhysicalExponentialModulusCertificate
      changingNomeCarrierNormalizedDynamicFamily :=
  data.toModulusCertificate
    (fun time =>
      (CReal.explicitEndpointsOfSandwich
        (data.ratePowerExplicitCertificate time)
        (fun scale => lowerLeMiddle time scale)
        (fun scale => middleLeUpper time scale)
        (width time)).1)
    (fun time =>
      (CReal.explicitEndpointsOfSandwich
        (data.ratePowerExplicitCertificate time)
        (fun scale => lowerLeMiddle time scale)
        (fun scale => middleLeUpper time scale)
        (width time)).2)

theorem Join.sq_decay (data : Join) (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit time)
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (data.toRatePowerLimit.limitRepresentative time))
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            data.toContinuumLimit 0))
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit 0)) :=
  normalizedMovingCubeLimitOfRationalVariations_sq_decay
    changingNomeCarrierNormalizedDynamicFamily data.raw data.normDebt
    data.ratePower time

def ConcreteJoin.toContinuumLimit (data : ConcreteJoin) :
    NormalizedMovingCubeScheduledRCContinuumLimit
      changingNomeCarrierNormalizedDynamicFamily :=
  data.toJoin.toContinuumLimit

def ConcreteJoin.toRatePowerLimit (data : ConcreteJoin) :
    NormalizedMovingCubeSampledRatePowerLimit
      changingNomeCarrierNormalizedDynamicFamily :=
  data.toJoin.toRatePowerLimit

theorem ConcreteJoin.zero_isPositive (data : ConcreteJoin) :
    RCIsPositive
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        data.toContinuumLimit 0) :=
  data.toJoin.zero_isPositive

theorem ConcreteJoin.sq_decay (data : ConcreteJoin) (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit time)
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (data.toRatePowerLimit.limitRepresentative time))
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            data.toContinuumLimit 0))
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit 0)) :=
  data.toJoin.sq_decay time

end YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toContinuumLimit
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toRatePowerLimit
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.zero_floor
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toRatePowerClustering
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.toModulusCertificateOfExplicitSandwich
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.carrierNormalized_rate_pos
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.toCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.ratePowerExplicitCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.toModulusCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.responsePersistence_toCanonicalUniformRCNormFloor
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.rawContinuumNontrivialityOfResponsePersistence
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.toJoin
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.changingNomeCarrierNormalizedResponsePersistence_ofNormalizationScaleCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofCofinalGapCalibration
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofCofinalGapCalibration
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.changingNomeCarrierNormalizedPhysicalGapBounds_ofConstantPhysicalGapCalibration
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.changingNomeCarrierNormalizedCofinalGapCalibration_ofConstantPhysicalGapCalibration
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.changingNomeCarrierNormalizedPhysicalGapBounds_ofHeadEnergyProductBand
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.changingNomeCarrierNormalizedCofinalGapCalibration_ofHeadEnergyProductBand
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofConstantPhysicalGapCalibration
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ChangingNomeCarrierNormalizedCofinalConcreteChannelRoute.ofHeadEnergyProductBand
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofConstantPhysicalGapCalibration
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofHeadEnergyProductBand
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofNormalizationScaleCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofNormalizationScaleCeilingAndHeadEnergyProductBand
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofNormalizationScaleVariation
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofNormalizationScaleVariationAndHeadEnergyProductBand
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofNormalizationScaleVariationAndPositiveRatePower
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.ofNormalizationScaleVariationAndHeadEnergyProductBandAndPositiveRatePower
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.ofNormalizationScaleVariationAndPositiveRatePower
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.ofNormalizationScaleVariationAndHeadEnergyProductBandAndPositiveRatePower
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.ofNormalizationScaleVariationAndConstantPhysicalGapCalibrationAndPositiveRatePower
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.ofNormalizationScaleVariationAndMarginAndReciprocalSpacingAndPositiveRatePower
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.ofNormalizationScaleVariationAndHeadEnergyProductBandAndMarginAndReciprocalSpacingAndPositiveRatePower
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.noChangingNomeCarrierNormalizedReciprocalSpacingVariation
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.toCanonicalUniformRCNormFloor
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.toRawContinuumNontriviality
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.toContinuumLimit
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.toRatePowerLimit
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.ConcreteJoin.sq_decay
