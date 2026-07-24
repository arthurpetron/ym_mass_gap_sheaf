/-
Stable transported RG dynamics to finite spectral correlation decay.

This module audits and bridges the first honest downstream consumer of
`StableDynamicsCertificate`:

    transported stable-state contraction
      + explicit observable/spectral readout
      -> geometric correlator decay
      -> finite `LocatedSpectralGap` with positive rational margin.

The bridge deliberately stops at the finite positive spectral model from
`Continuum/ClusteringImpliesGap.lean`.  It does NOT claim that an RG-state
distance is automatically a Wilson connected correlator.  That missing
physical interpretation is the named `StableCorrelationReadout.readoutBound`
plus `StableSpectralReadout.spectralMatches` input below.  It also does not
construct the volume-uniform floor, inter-volume increment modulus, physical
spacing conversion, OS reconstruction, or continuum measure required by the
continuum mass-gap consumers.

The RG orbit remains pinned to the node-indexed physical states through the
`StableDynamicsCertificate.transportedOrbit` field introduced in
`StableDynamics.lean`.  No frontier or scorecard structure is inhabited.

Axiom gate (AGENTS.md Rules 1 and 8): no classical reasoning, sorry,
native_decide, quotient, or noncomputable declaration.
-/

import YMGap.RG.StableDynamics
import YMGap.Continuum.ClusteringImpliesGap

namespace YMGap.RG.StableDynamicsCorrelationBridge

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG.PolynomialTree
open YMGap.RG.StableDynamics
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.ClusteringImpliesGap

universe u v

/-! ## A named physical correlation readout -/

/-- The explicit input identifying stable-state contraction with a geometric
correlation envelope.

The comparison state may represent a vacuum/reference trajectory.  It is
evolved by the same stable-interface RG maps, so `readoutBound` compares the
claimed correlator with two states living in exactly the same transported
stable interface.  `rate` may be a convenient positive rational enlargement
of the certificate's contraction factor `q`; this also handles the exact
contraction case `q = 0` while satisfying the spectral converse's `0 < rate`
hypothesis. -/
structure StableCorrelationReadout
    {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p) where
  /-- Reference state in the SAME stable interface as the transported orbit. -/
  comparisonState : RGState dynamics.stableTail.stableInterface
  comparisonAdmissible : dynamics.contraction.Admissible comparisonState
  /-- Correlation quantity to be controlled. -/
  correlation : QSeq
  /-- Positive geometric rate used by downstream spectral consumers. -/
  rate : Q'
  ratePositive : (0 : Q') < rate
  rateBelowOne : rate < (1 : Q')
  contractionRate_le : dynamics.contraction.q <= rate
  /-- Correlation envelope constant. -/
  envelope : Q'
  envelopePositive : (0 : Q') < envelope
  /-- The initial post-landing separation fits the envelope. -/
  initialDistanceBound :
    dynamics.contraction.distance
        (dynamics.orbit dynamics.landing.offset) comparisonState <= envelope
  /-- THE physical readout input: the claimed correlator is dominated by the
  transported stable-state separation at every post-landing offset. -/
  readoutBound : forall n,
    correlation n <=
      dynamics.contraction.distance
        (dynamics.orbit (dynamics.landing.offset + n))
        (dynamics.contraction.evolveFrom dynamics.landing.offset
          comparisonState n)

namespace StableCorrelationReadout

/-- Stable contraction plus the explicit readout yields a genuine geometric
correlation bound `correlation n <= envelope * rate^n`. -/
theorem correlation_decay
    {p : RGProgram.{u}}
    {dynamics : StableDynamicsCertificate.{u, v} p}
    (readout : StableCorrelationReadout dynamics) :
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

end StableCorrelationReadout

/-! ## The finite positive spectral consumer -/

/-- The explicit input tying the correlation readout to an honest finite
positive Kallen--Lehmann spectral model.

`spectralMatches` is the observable/operator bridge: it says the finite
spectral model's connected correlator is the same quantity controlled by the
RG readout.  `liveWeightPositive` and `unusedModeBound` are precisely the two
honest side conditions required by `clustering_implies_located`; neither is
inferred from decay of an unrelated sequence. -/
structure StableSpectralReadout
    {p : RGProgram.{u}}
    (dynamics : StableDynamicsCertificate.{u, v} p)
    extends StableCorrelationReadout dynamics where
  spectralModel : SpectralModel
  spectralMatches : forall n,
    (corr spectralModel n).eqv (toStableCorrelationReadout.correlation n)
  liveWeightPositive : forall i, i < spectralModel.k ->
    (0 : Q') < spectralModel.w i
  unusedModeBound : forall i, spectralModel.k <= i ->
    spectralModel.lam i <= toStableCorrelationReadout.rate

namespace StableSpectralReadout

/-- The finite spectral correlator inherits the transported RG geometric
decay, with the SAME explicit envelope and rate. -/
theorem spectral_correlation_decay
    {p : RGProgram.{u}}
    {dynamics : StableDynamicsCertificate.{u, v} p}
    (readout : StableSpectralReadout dynamics) :
    forall n,
      corr readout.spectralModel n <= readout.envelope * readout.rate ^ n := by
  intro n
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (readout.spectralMatches n))
    (readout.toStableCorrelationReadout.correlation_decay n)

/-- **Strongest honest single-volume consequence.**

The finite positive spectral model has a located separator equal to the
geometric rate.  This is the existing constructive clustering-to-gap theorem,
fed by the RG-derived decay and the explicit coupling/tail conditions. -/
def locatedGap
    {p : RGProgram.{u}}
    {dynamics : StableDynamicsCertificate.{u, v} p}
    (readout : StableSpectralReadout dynamics) :
    LocatedSpectralGap readout.spectralModel :=
  clustering_implies_located readout.spectralModel
    readout.envelope readout.rate
    readout.envelopePositive readout.ratePositive readout.rateBelowOne
    readout.spectral_correlation_decay
    readout.liveWeightPositive readout.unusedModeBound

/-- The located separator is definitionally the supplied geometric rate. -/
theorem locatedGap_sep
    {p : RGProgram.{u}}
    {dynamics : StableDynamicsCertificate.{u, v} p}
    (readout : StableSpectralReadout dynamics) :
    readout.locatedGap.sep = readout.rate := rfl

/-- The resulting finite eigenvalue-gap margin is a strictly positive exact
rational. -/
theorem locatedGap_margin_positive
    {p : RGProgram.{u}}
    {dynamics : StableDynamicsCertificate.{u, v} p}
    (readout : StableSpectralReadout dynamics) :
    (0 : Q') < readout.locatedGap.gapMargin :=
  readout.locatedGap.gapMargin_pos

/-- Located gap data together with its positive rational margin certificate. -/
structure FiniteGapOutcome
    {p : RGProgram.{u}}
    {dynamics : StableDynamicsCertificate.{u, v} p}
    (readout : StableSpectralReadout dynamics) where
  gap : LocatedSpectralGap readout.spectralModel
  marginPositive : (0 : Q') < gap.gapMargin

/-- Return the located gap and positive margin as Type-level data. -/
def finiteGapOutcome
    {p : RGProgram.{u}}
    {dynamics : StableDynamicsCertificate.{u, v} p}
    (readout : StableSpectralReadout dynamics) : FiniteGapOutcome readout where
  gap := readout.locatedGap
  marginPositive := readout.locatedGap_margin_positive

end StableSpectralReadout

/-! ## A family of finite-volume consequences, stopping before uniformity -/

/-- Volume-indexed stable dynamics and their explicit spectral readouts.

This structure is intentionally weaker than
`ClusterGapReduction.UniformClusterBound`: it constructs the entire family of
finite located gaps, but carries no uniform positive floor or inter-volume
Cauchy modulus. -/
structure StableSpectralFamily (p : RGProgram.{u}) where
  dynamics : Nat -> StableDynamicsCertificate.{u, v} p
  readout : (volume : Nat) -> StableSpectralReadout (dynamics volume)

namespace StableSpectralFamily

/-- The finite spectral model at each volume. -/
def gaps
    {p : RGProgram.{u}}
    (family : StableSpectralFamily.{u, v} p) : Nat -> SpectralModel :=
  fun volume => (family.readout volume).spectralModel

/-- Every supplied volume has a constructively located positive gap.  This
constructs exactly the `located`-family portion of the downstream
`UniformClusterBound`, and no more. -/
def locatedFamily
    {p : RGProgram.{u}}
    (family : StableSpectralFamily.{u, v} p) :
    (volume : Nat) -> LocatedSpectralGap (family.gaps volume) :=
  fun volume => (family.readout volume).locatedGap

/-- Every member of the finite-volume family has a positive rational margin;
the theorem does NOT assert a single positive floor uniform in `volume`. -/
theorem marginPositive
    {p : RGProgram.{u}}
    (family : StableSpectralFamily.{u, v} p) :
    forall volume, (0 : Q') < (family.locatedFamily volume).gapMargin :=
  fun volume => (family.locatedFamily volume).gapMargin_pos

end StableSpectralFamily

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms StableCorrelationReadout
#print axioms StableCorrelationReadout.correlation_decay
#print axioms StableSpectralReadout
#print axioms StableSpectralReadout.spectral_correlation_decay
#print axioms StableSpectralReadout.locatedGap
#print axioms StableSpectralReadout.locatedGap_sep
#print axioms StableSpectralReadout.locatedGap_margin_positive
#print axioms StableSpectralReadout.FiniteGapOutcome
#print axioms StableSpectralReadout.finiteGapOutcome
#print axioms StableSpectralFamily
#print axioms StableSpectralFamily.locatedFamily
#print axioms StableSpectralFamily.marginPositive

end YMGap.RG.StableDynamicsCorrelationBridge
