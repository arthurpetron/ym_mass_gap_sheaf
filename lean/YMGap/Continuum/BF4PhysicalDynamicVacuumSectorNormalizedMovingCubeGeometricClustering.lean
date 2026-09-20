/-
# Certificate bridge for the normalized moving-cube continuum channel

The normalized moving-cube route already carries the three constructive
ingredients needed for a continuum statement: explicit representatives,
convergence moduli, and a uniform unit floor.  Its decay compiler is phrased
with a time-indexed limit of scheduled rate powers, while the canonical
clustering interface uses one fixed rational ratio.

This module is the narrow bridge between those two currencies.  The fixed
ratio identification is a named Type-level input; it is not inferred from a
pointwise family of rates.  Once supplied, the same completed limit and the
same rate-power limit produce the canonical nontrivial squared-geometric
clustering certificate.  No new observable, limit, or vacuum sector is
selected here.

No rate-power identification, cutoff-limit inhabitant, adaptive producer,
projective measure, OS reconstruction, continuum Yang--Mills theory, or Clay
conclusion is inhabited here.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
import YMGap.Continuum.ContinuumSquaredClusteringHandoff

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ContinuumSquaredClusteringHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler

/-! ## 1. The missing fixed-ratio certificate -/

/-- A scheduled rate-power limit is identified with powers of one fixed
rational ratio.  The limit field itself carries the cutoff convergence modulus;
this structure adds only the fixed-ratio identification needed by the
canonical clustering interface. -/
structure NormalizedMovingCubeRatePowerGeometricIdentification
    (family : DynamicVacuumSectorCompletedFamily 0)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit family) : Type 1 where
  ratio : Q'
  ratio_nonneg : (0 : Q') <= ratio
  ratio_lt_one : ratio < (1 : Q')
  ratePower_eq_ratio_pow : forall time : Nat,
    Quotient.mk CReal.crealSetoid
        (ratePower.limitRepresentative time) =
      Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (ratio ^ time))

/-! ## 2. The certificate and its canonical projection -/

/-- One normalized moving-cube continuum certificate.  Its limit and rate
power are explicit approximation schemes, and the geometric identification is
an explicit same-currency equality rather than an erased existential. -/
structure NormalizedMovingCubeContinuumCertificate
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 2 where
  limit : NormalizedMovingCubeScheduledRCContinuumLimit family
  ratePower : NormalizedMovingCubeSampledRatePowerLimit family
  geometricRate :
    NormalizedMovingCubeRatePowerGeometricIdentification family ratePower

/-- Assemble the three explicit cross-cutoff variation certificates into one
same-observable continuum certificate.  The raw representative, reciprocal
normalization debt, and scheduled rate-power streams are converted to their
constructive limits by the existing variation compilers; the supplied
`geometricRate` is then checked against that exact rate-power limit. -/
def NormalizedMovingCubeContinuumCertificate.ofVariations
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtVariation family)
    (ratePower : NormalizedMovingCubeSampledRatePowerVariation family)
    (geometricRate :
      NormalizedMovingCubeRatePowerGeometricIdentification family
        (normalizedMovingCubeSampledRatePowerLimitOfVariation family ratePower)) :
    NormalizedMovingCubeContinuumCertificate family where
  limit := normalizedMovingCubeLimitOfVariations family raw normDebt
  ratePower := normalizedMovingCubeSampledRatePowerLimitOfVariation family ratePower
  geometricRate := geometricRate

namespace NormalizedMovingCubeContinuumCertificate

private theorem zero_le_one : CReal.RCle
    CReal.RCzero
    (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1)) := by
  change CReal.leEv CReal.czero (CReal.ofQ' 1)
  exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (by decide))

private theorem continuum_zero_nonneg
    {family : DynamicVacuumSectorCompletedFamily 0}
    (certificate : NormalizedMovingCubeContinuumCertificate family) :
    CReal.RCnonneg
      (certificate.limit.continuumConnectedAutocorrelation 0) := by
  exact CReal.RCle_trans zero_le_one
    certificate.limit.one_le_continuumConnectedAutocorrelation_zero

/-- Project the certificate to the canonical nontrivial squared-geometric
clustering contract.  The amplitude is the actual same-object time-zero
correlation, the ratio is the identified fixed rate, and the unit floor is
preserved verbatim. -/
def toNontrivialRCSquaredGeometricClustering
    {family : DynamicVacuumSectorCompletedFamily 0}
    (certificate : NormalizedMovingCubeContinuumCertificate family) :
    NontrivialRCSquaredGeometricClustering
      certificate.limit.continuumConnectedAutocorrelation where
  amplitude := certificate.limit.continuumConnectedAutocorrelation 0
  ratio := certificate.geometricRate.ratio
  amplitude_nonneg := continuum_zero_nonneg certificate
  ratio_nonneg := certificate.geometricRate.ratio_nonneg
  ratio_lt_one := certificate.geometricRate.ratio_lt_one
  decay := by
    intro time
    have hdecay := normalizedMovingCubeContinuumConnectedAutocorrelationSq_decay
      family certificate.limit certificate.ratePower time
    have hrate := certificate.geometricRate.ratePower_eq_ratio_pow time
    rw [hrate] at hdecay
    simpa [NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation]
      using hdecay
  zeroFloor := 1
  zeroFloor_pos := by decide
  zeroFloor_le := certificate.limit.one_le_continuumConnectedAutocorrelation_zero

end NormalizedMovingCubeContinuumCertificate

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering.NormalizedMovingCubeContinuumCertificate.ofVariations
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering.NormalizedMovingCubeContinuumCertificate.toNontrivialRCSquaredGeometricClustering
