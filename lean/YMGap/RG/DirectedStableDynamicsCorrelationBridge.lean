/-
Forward-only stable RG dynamics to finite spectral correlation decay.

This is the directed companion to `StableDynamicsCorrelationBridge`.  It
consumes `DirectedStableDynamicsCertificate` directly, so physical
coarse-graining never has to be upgraded to an interface equivalence merely to
reach the first finite spectral consumer.

The bridge remains deliberately explicit about the open physics.  Stable-state
contraction becomes correlator decay only through `readoutBound`, and becomes a
finite positive spectral statement only through `spectralMatches` and the
positive-weight side conditions.  It constructs neither a physical Wilson
readout nor any volume-uniform or continuum mass-gap input.

No state recovery, inverse transport, or interface equivalence is used.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.RG.DirectedStableDynamics
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.RG.DirectedStableDynamicsCorrelationBridge

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG.PolynomialTree
open YMGap.RG.DirectedStableDynamics
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ClusteringImpliesGap

universe u v

/-! ## Directed physical correlation readout -/

/-- Explicitly identify contraction of the forward-normalized orbit with a
geometric correlation envelope.

The comparison state lives in the same stable interface as the directed
pushforward orbit.  `readoutBound` is the named physical input; it is not
inferred from the abstract RG-state distance. -/
structure DirectedStableCorrelationReadout
    {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p) where
  comparisonState : RGState dynamics.stableTail.stableInterface
  comparisonAdmissible : dynamics.contraction.Admissible comparisonState
  correlation : QSeq
  rate : Q'
  ratePositive : (0 : Q') < rate
  rateBelowOne : rate < (1 : Q')
  contractionRate_le : dynamics.contraction.q <= rate
  envelope : Q'
  envelopePositive : (0 : Q') < envelope
  initialDistanceBound :
    dynamics.contraction.distance
        (dynamics.orbit dynamics.landing.offset) comparisonState <= envelope
  readoutBound : forall n,
    correlation n <=
      dynamics.contraction.distance
        (dynamics.orbit (dynamics.landing.offset + n))
        (dynamics.contraction.evolveFrom dynamics.landing.offset
          comparisonState n)

namespace DirectedStableCorrelationReadout

/-- Forward-normalized stable contraction plus the explicit readout gives the
geometric correlation estimate `correlation n <= envelope * rate^n`. -/
theorem correlation_decay
    {p : RGProgram.{u}}
    {dynamics : DirectedStableDynamicsCertificate.{u, v} p}
    (readout : DirectedStableCorrelationReadout dynamics) :
    forall n, readout.correlation n <= readout.envelope * readout.rate ^ n := by
  intro n
  have hcontract := dynamics.postLanding_contracts
    readout.comparisonAdmissible n
  have hinitial :
      dynamics.contraction.q ^ n *
          dynamics.contraction.distance
            (dynamics.orbit dynamics.landing.offset) readout.comparisonState <=
        dynamics.contraction.q ^ n * readout.envelope :=
    Q'.mul_le_mul_of_nonneg_left _ _ (dynamics.contraction.q ^ n)
      readout.initialDistanceBound
      (Q'.pow_nonneg dynamics.contraction.q
        dynamics.contraction.qNonnegative n)
  have hratePow : dynamics.contraction.q ^ n <= readout.rate ^ n :=
    pow_le_pow_left dynamics.contraction.qNonnegative
      readout.contractionRate_le n
  have hrate :
      dynamics.contraction.q ^ n * readout.envelope <=
        readout.envelope * readout.rate ^ n :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv (dynamics.contraction.q ^ n) readout.envelope))
      (Q'.mul_le_mul_of_nonneg_left _ _ readout.envelope hratePow
        (Q'.le_of_lt readout.envelopePositive))
  exact Q'.le_trans' _ _ _ (readout.readoutBound n)
    (Q'.le_trans' _ _ _ hcontract (Q'.le_trans' _ _ _ hinitial hrate))

end DirectedStableCorrelationReadout

/-! ## Finite positive spectral consumer -/

/-- Tie the directed correlation readout to a finite positive spectral model.

The equality and side conditions are the honest operator/spectral inputs used
by `clustering_implies_located`; no unrelated decaying sequence is substituted
for the spectral correlator. -/
structure DirectedStableSpectralReadout
    {p : RGProgram.{u}}
    (dynamics : DirectedStableDynamicsCertificate.{u, v} p)
    extends DirectedStableCorrelationReadout dynamics where
  spectralModel : SpectralModel
  spectralMatches : forall n,
    (corr spectralModel n).eqv (toDirectedStableCorrelationReadout.correlation n)
  liveWeightPositive : forall i, i < spectralModel.k ->
    (0 : Q') < spectralModel.w i
  unusedModeBound : forall i, spectralModel.k <= i ->
    spectralModel.lam i <= toDirectedStableCorrelationReadout.rate

namespace DirectedStableSpectralReadout

/-- The finite spectral correlator inherits the directed RG decay estimate. -/
theorem spectral_correlation_decay
    {p : RGProgram.{u}}
    {dynamics : DirectedStableDynamicsCertificate.{u, v} p}
    (readout : DirectedStableSpectralReadout dynamics) :
    forall n,
      corr readout.spectralModel n <= readout.envelope * readout.rate ^ n := by
  intro n
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (readout.spectralMatches n))
    (readout.toDirectedStableCorrelationReadout.correlation_decay n)

/-- Strongest honest single-volume consequence: a constructively located
separator for the supplied finite positive spectral model. -/
def locatedGap
    {p : RGProgram.{u}}
    {dynamics : DirectedStableDynamicsCertificate.{u, v} p}
    (readout : DirectedStableSpectralReadout dynamics) :
    LocatedSpectralGap readout.spectralModel :=
  clustering_implies_located readout.spectralModel
    readout.envelope readout.rate
    readout.envelopePositive readout.ratePositive readout.rateBelowOne
    readout.spectral_correlation_decay
    readout.liveWeightPositive readout.unusedModeBound

/-- The located separator is exactly the supplied geometric rate. -/
theorem locatedGap_sep
    {p : RGProgram.{u}}
    {dynamics : DirectedStableDynamicsCertificate.{u, v} p}
    (readout : DirectedStableSpectralReadout dynamics) :
    readout.locatedGap.sep = readout.rate := rfl

/-- The finite located gap carries a strictly positive exact-rational margin. -/
theorem locatedGap_margin_positive
    {p : RGProgram.{u}}
    {dynamics : DirectedStableDynamicsCertificate.{u, v} p}
    (readout : DirectedStableSpectralReadout dynamics) :
    (0 : Q') < readout.locatedGap.gapMargin :=
  readout.locatedGap.gapMargin_pos

/-- Located finite gap data together with its positive rational margin. -/
structure FiniteGapOutcome
    {p : RGProgram.{u}}
    {dynamics : DirectedStableDynamicsCertificate.{u, v} p}
    (readout : DirectedStableSpectralReadout dynamics) where
  gap : LocatedSpectralGap readout.spectralModel
  marginPositive : (0 : Q') < gap.gapMargin

/-- Return the directed bridge's finite gap and margin as Type-level data. -/
def finiteGapOutcome
    {p : RGProgram.{u}}
    {dynamics : DirectedStableDynamicsCertificate.{u, v} p}
    (readout : DirectedStableSpectralReadout dynamics) :
    FiniteGapOutcome readout where
  gap := readout.locatedGap
  marginPositive := readout.locatedGap_margin_positive

end DirectedStableSpectralReadout

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms DirectedStableCorrelationReadout
#print axioms DirectedStableCorrelationReadout.correlation_decay
#print axioms DirectedStableSpectralReadout
#print axioms DirectedStableSpectralReadout.spectral_correlation_decay
#print axioms DirectedStableSpectralReadout.locatedGap
#print axioms DirectedStableSpectralReadout.locatedGap_sep
#print axioms DirectedStableSpectralReadout.locatedGap_margin_positive
#print axioms DirectedStableSpectralReadout.FiniteGapOutcome
#print axioms DirectedStableSpectralReadout.finiteGapOutcome

end YMGap.RG.DirectedStableDynamicsCorrelationBridge
