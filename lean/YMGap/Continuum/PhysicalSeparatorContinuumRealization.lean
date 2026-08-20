/-
M4a -- an honest same-object contract from an exact physical separator band to
the reconstructed continuum Yang--Mills Hamiltonian.

The M2--M3 certificate supplies a positive, finite exact logarithmic rate at
every lattice spacing.  That finite-scale statement does not construct its own
continuum limit and does not identify a limiting rate with the transfer
semigroup obtained by Osterwalder--Schrader reconstruction.  This file records
those missing steps without collapsing them into an opaque final hypothesis.

There are three layers.

* `StageCorrelationSemantics` is an external interpretation of observables on
  the stage-measure carriers.  `ProjectiveCorrIdentification` identifies the
  correlators controlled by the physical separator with this fixed evaluator
  on the selected thread of one `ContinuumMeasure`.  This is the same-object
  pin; the identification cannot manufacture its own measure-ignoring
  evaluator.
* `ExactRateCutoffRemoval` supplies spacing cofinality and a Type-level Cauchy
  modulus for the exact physical-rate sequence.  Its limit and the survival of
  the finite lower/upper band are explicit.
* `PhysicalSeparatorContinuumRealization` adds genuine continuum Yang--Mills
  existence, OS reconstruction, and one dimensionally faithful binding: the
  limiting exact physical rate is the reconstruction's computed logarithmic
  gap `-log(mu)`.  The older `HasSpectralGapAt` endpoint is margin-valued
  (`1-mu`), so exporting to it requires a separately named compatibility
  hypothesis rather than silently identifying the two currencies.

No inhabitant is constructed.  In particular, an exact finite-scale band alone
does not produce a projective continuum measure, cutoff removal, OS axioms, or a
Hamiltonian spectral gap.
-/

import YMGap.Constructive.CRealCompleteCauchy
import YMGap.Continuum.FourDExistence
import YMGap.Continuum.MeasureLinkedOSReconstruction
import YMGap.Continuum.OSCanonicalMarginGap
import YMGap.Continuum.OSExactLogGap
import YMGap.Continuum.PhysicalSeparatorFullLogComparison
import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.SummableCRealEventualStepVariation
import YMGap.Continuum.SummableCRealStepVariation

namespace YMGap.Continuum.PhysicalSeparatorContinuumRealization

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.OSCanonicalMarginGap
open YMGap.Continuum.OSReconstruction
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.SummableCRealEventualStepVariation
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.TuranPositivity

/-! ## 1. Same-object identification with a projective measure thread -/

/-- External stage-measure semantics for the separator's observables.

This evaluator is deliberately a parameter of the identification below rather
than a field of it.  The concrete continuum-measure construction must supply
the interpretation; an equality witness cannot choose an evaluator that
ignores the measure. -/
structure StageCorrelationSemantics
    (P : PhysicalSeparator) (M : Nat -> Type) : Type 1 where
  /-- Evaluate a gauge-invariant connected correlator on a stage measure. -/
  corrFromStage : (j : Nat) -> M j -> P.corrIface.Obs -> Nat -> Q'

/-- Identify the physical separator's correlator interface with correlators
evaluated on the selected stage measures of one projectively consistent
continuum-measure thread.  The equality field prevents a separator attached to
one abstract correlator family from being silently reused for another measure. -/
structure ProjectiveCorrIdentification
    (P : PhysicalSeparator) {M : Nat -> Type}
    (mu : ContinuumMeasure M)
    (stageCorr : StageCorrelationSemantics P M) : Type 1 where
  /-- The selected projective-thread measure gives exactly the correlator
  controlled by `P` at every scale and separation. -/
  picked_corr_eq : forall (j : Nat) (O : P.corrIface.Obs) (n : Nat),
    stageCorr.corrFromStage j (mu.pick j) O n =
      P.corrIface.connectedCorr j O n

/-- The separator's geometric control transfers to the correlators evaluated
on the selected projective-measure thread. -/
def ProjectiveCorrIdentification.pickedCorrControl
    {P : PhysicalSeparator} {M : Nat -> Type}
    {mu : ContinuumMeasure M} {stageCorr : StageCorrelationSemantics P M}
    (I : ProjectiveCorrIdentification P mu stageCorr)
    (O : P.corrIface.Obs) (hO : P.corrIface.GaugeInvariantLocal O) :
    Σ' C : Q', (0 : Q') < C /\
      forall j n : Nat,
        stageCorr.corrFromStage j (mu.pick j) O n <= C * (P.sep j) ^ n := by
  let W := P.controlsGaugeInvariantCorr O hO
  refine ⟨W.1, W.2.1, fun j n => ?_⟩
  rw [I.picked_corr_eq j O n]
  exact W.2.2 j n

/-! ## 2. Physical rescaling and reconstruction-correlation identification -/

/-- A cofinal sampling of lattice separations at fixed integer physical time.

At cutoff index `j`, `latticeSteps j t` is the number of lattice time steps
used to represent continuum separation `t`.  The convergence field rules out
the dimensionally wrong fixed-step limit: it explicitly requires

    a_j * latticeSteps(j,t) -> t.

The integer target is enough for the present reconstructed spectral model,
whose correlator is indexed by `Nat`.  A future real-time OS interface can
refine this sampling object without changing the same-object boundary below. -/
structure PhysicalSeparationSampling (A : PhysicalSpacing) : Type where
  latticeSteps : Nat -> Nat -> Nat
  distanceConverges : forall t : Nat,
    CReal.ConvergesTo
      (fun j => CReal.ofQ'
        (PhysicalSpacing.spacing A j * Q'.ofNat (latticeSteps j t)))
      (CReal.ofQ' (Q'.ofNat t))

/-- Continuum correlators obtained as physically rescaled limits of the fixed
stage-measure semantics.

This record is parameterized by the already-fixed `stageCorr` and selected
projective thread `mu`: it cannot choose a new finite-stage evaluator or a new
measure.  Its convergence therefore records the actual cutoff-removal step for
the same correlators controlled by the physical separator. -/
structure ContinuumCorrelationSemantics
    (P : PhysicalSeparator) {M : Nat -> Type}
    (mu : ContinuumMeasure M)
    (stageCorr : StageCorrelationSemantics P M)
    (A : PhysicalSpacing)
    (sampling : PhysicalSeparationSampling A) : Type 1 where
  continuumCorr : P.corrIface.Obs -> Nat -> CReal
  rescaledStageConverges : forall (O : P.corrIface.Obs) (t : Nat),
    CReal.ConvergesTo
      (fun j => CReal.ofQ'
        (stageCorr.corrFromStage j (mu.pick j) O
          (sampling.latticeSteps j t)))
      (continuumCorr O t)

/-- Identify a nonzero gauge-invariant local continuum correlator with the
spectral correlator carried by the reconstruction.

The positive value at zero excludes the empty/zero spectral channel, which
would otherwise satisfy every decay inequality vacuously.  Together with
`ContinuumCorrelationSemantics`, this pins the reconstruction's spectral model
to the physically rescaled limit of the same finite-stage observable. -/
structure ReconstructionCorrIdentification
    (P : PhysicalSeparator)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu)
    {stageCorr : StageCorrelationSemantics P M}
    {A : PhysicalSpacing} {sampling : PhysicalSeparationSampling A}
    (continuumCorrs :
      ContinuumCorrelationSemantics P mu stageCorr A sampling) : Type 1 where
  gapObservable : P.corrIface.Obs
  gapObservable_local : P.corrIface.GaugeInvariantLocal gapObservable
  spectralCorr_eq : forall t : Nat,
    CReal.Equiv (continuumCorrs.continuumCorr gapObservable t)
      (CReal.ofQ' (SpectralGap.corr rec.spec t))
  spectralCorrZero_pos :
    (0 : Q') < SpectralGap.corr rec.spec 0

/-- External connected-two-point semantics inside the fixed OS observable
algebra.  As with the stage evaluators, this is supplied independently of the
identification proof so the latter cannot invent its own insertion map. -/
structure OSConnectedTwoPointSemantics
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu) : Type 1 where
  gapInsertion : H.os_axioms.A.carrier
  connectedInsertion :
    H.os_axioms.A.carrier -> Nat -> H.os_axioms.A.carrier

/-- The OS Schwinger functional's connected two-point function is the same
continuum correlator already identified with the reconstruction's nonzero
spectral channel.

Combined with `ProjectiveOSFunctionalIdentification`, this closes the chain

    selected stage measures -> OS functional -> continuum correlator
                            -> reconstructed spectral correlator.
-/
structure OSGapCorrelationIdentification
    (P : PhysicalSeparator)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (osCorr : OSConnectedTwoPointSemantics H)
    {stageCorr : StageCorrelationSemantics P M}
    {A : PhysicalSpacing} {sampling : PhysicalSeparationSampling A}
    (continuumCorrs :
      ContinuumCorrelationSemantics P mu stageCorr A sampling)
    {rec : OSReconstruction mu}
    (recCorrs : ReconstructionCorrIdentification P rec continuumCorrs) :
    Type 1 where
  gapCorr_eq : forall t : Nat,
    CReal.Equiv
      (CReal.ofQ' (H.os_axioms.E.E
        (osCorr.connectedInsertion osCorr.gapInsertion t)))
      (continuumCorrs.continuumCorr recCorrs.gapObservable t)

/-- The geometric separator estimate remains attached to the physically
sampled correlators on the selected projective-measure thread. -/
def ProjectiveCorrIdentification.rescaledPickedCorrControl
    {P : PhysicalSeparator} {M : Nat -> Type}
    {mu : ContinuumMeasure M} {stageCorr : StageCorrelationSemantics P M}
    (I : ProjectiveCorrIdentification P mu stageCorr)
    {A : PhysicalSpacing} (sampling : PhysicalSeparationSampling A)
    (O : P.corrIface.Obs) (hO : P.corrIface.GaugeInvariantLocal O) :
    Σ' C : Q', (0 : Q') < C /\
      forall j t : Nat,
        stageCorr.corrFromStage j (mu.pick j) O
            (sampling.latticeSteps j t) <=
          C * (P.sep j) ^ (sampling.latticeSteps j t) := by
  let W := I.pickedCorrControl O hO
  exact ⟨W.1, W.2.1,
    fun j t => W.2.2 j (sampling.latticeSteps j t)⟩

/-! ## 3. Exact-rate cutoff removal -/

/-! A termwise eventual-order bound passes through an explicitly Cauchy
sequence.  These two lemmas avoid strengthening the finite exact rate band to
pointwise bounds on every rational approximation. -/

/-- A common eventual lower bound on every term survives the constructive
`ModCauchyEv` limit. -/
theorem leEv_of_termwise_le_completeLimitCauchy
    (s : Nat -> CReal) (c : CReal.ModCauchyEv s) {x : CReal}
    (h : forall k : Nat, CReal.leEv x (s k)) :
    CReal.leEv x (CReal.completeLimitCauchy s c) := by
  intro ε hε
  let q : Q' := HalfPow.half * ε
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos ε hε
  obtain ⟨N, hN⟩ := CReal.convergesTo_completeLimitCauchy s c q hq
  obtain ⟨Kclose, hclose⟩ := hN N (Nat.le_refl N)
  obtain ⟨Korder, horder⟩ := h N q hq
  refine ⟨max Kclose Korder, fun n hn => ?_⟩
  have hnClose : Kclose ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnOrder : Korder ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hxo : x.approx n ≤ (s N).approx n + q := horder n hnOrder
  have hol : (s N).approx n ≤
      (CReal.completeLimitCauchy s c).approx n + q :=
    (hclose n hnClose).1
  refine Q'.le_trans' _ _ _ hxo ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ q hol) ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv
      ((CReal.completeLimitCauchy s c).approx n) q q) ?_)
  exact Q'.add_eqv_congr_left
    ((CReal.completeLimitCauchy s c).approx n) (q + q) ε
    (ExpNeg.two_halves ε)

/-- A common eventual upper bound on every term survives the constructive
`ModCauchyEv` limit. -/
theorem leEv_completeLimitCauchy_of_termwise_le
    (s : Nat -> CReal) (c : CReal.ModCauchyEv s) {x : CReal}
    (h : forall k : Nat, CReal.leEv (s k) x) :
    CReal.leEv (CReal.completeLimitCauchy s c) x := by
  intro ε hε
  let q : Q' := HalfPow.half * ε
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos ε hε
  obtain ⟨N, hN⟩ := CReal.convergesTo_completeLimitCauchy s c q hq
  obtain ⟨Kclose, hclose⟩ := hN N (Nat.le_refl N)
  obtain ⟨Korder, horder⟩ := h N q hq
  refine ⟨max Kclose Korder, fun n hn => ?_⟩
  have hnClose : Kclose ≤ n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnOrder : Korder ≤ n :=
    Nat.le_trans (Nat.le_max_right _ _) hn
  have hlo : (CReal.completeLimitCauchy s c).approx n ≤
      (s N).approx n + q :=
    (hclose n hnClose).2
  have hox : (s N).approx n ≤ x.approx n + q := horder n hnOrder
  refine Q'.le_trans' _ _ _ hlo ?_
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ q hox) ?_
  refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (x.approx n) q q) ?_)
  exact Q'.add_eqv_congr_left (x.approx n) (q + q) ε
    (ExpNeg.two_halves ε)

/-- The genuinely analytic rate-limit data, separated from spacing cofinality.
This factorization lets an AF-specific adapter discharge `a_j -> 0` from its
proved schedule.  The public structure records the limiting band, while
`ExactRateLimitData.ofRateCauchy` derives both survival fields from the sole
analytic input: a Type-level Cauchy modulus for the exact-rate sequence. -/
structure ExactRateLimitData
    (C : FullRangeExactPhysicalSeparatorCertificate) : Type 1 where
  /-- Type-level eventual Cauchy modulus for the exact physical-rate sequence. -/
  rateCauchy : CReal.ModCauchyEv C.rateFamily.rate
  /-- The positive finite-scale floor survives the constructed rate limit. -/
  floor_survives :
    CReal.leEv (CReal.ofQ' C.uniformFloor.floor)
      (CReal.completeLimitCauchy C.rateFamily.rate rateCauchy)
  /-- The finite-scale ceiling survives the constructed rate limit. -/
  ceiling_survives :
    CReal.leEv (CReal.completeLimitCauchy C.rateFamily.rate rateCauchy)
      (CReal.ofQ' C.finiteCeiling.ceiling)

namespace ExactRateLimitData

/-- A Type-level rate Cauchy modulus is sufficient: the exact certificate's
termwise lower and upper bands pass to its constructive limit. -/
def ofRateCauchy
    {C : FullRangeExactPhysicalSeparatorCertificate}
    (rateCauchy : CReal.ModCauchyEv C.rateFamily.rate) :
    ExactRateLimitData C where
  rateCauchy := rateCauchy
  floor_survives := leEv_of_termwise_le_completeLimitCauchy
    C.rateFamily.rate rateCauchy C.uniformFloor.floor_bound
  ceiling_survives := leEv_completeLimitCauchy_of_termwise_le
    C.rateFamily.rate rateCauchy C.finiteCeiling.ceiling_bound

/-- A summable two-sided single-step variation estimate is a sufficient local
analytic input for exact-rate cutoff removal.  The global Cauchy modulus is
constructed by telescoping its tail bound. -/
def ofSummableStepVariation
    {C : FullRangeExactPhysicalSeparatorCertificate}
    (variation : SummableCRealStepVariation C.rateFamily.rate) :
    ExactRateLimitData C :=
  ofRateCauchy variation.toModCauchyEv

/-- A summable two-sided consecutive-step estimate that holds eventually in
the rational approximation index is sufficient for exact-rate cutoff removal.
The approximation threshold for a finite cutoff interval is computed as the
maximum of its finitely many local thresholds. -/
def ofSummableEventualStepVariation
    {C : FullRangeExactPhysicalSeparatorCertificate}
    (variation : SummableCRealEventualStepVariation C.rateFamily.rate) :
    ExactRateLimitData C :=
  ofRateCauchy variation.toModCauchyEv

/-- The exact physical-rate limit represented by the supplied Cauchy data. -/
def continuumRate {C : FullRangeExactPhysicalSeparatorCertificate}
    (D : ExactRateLimitData C) : CReal :=
  CReal.completeLimitCauchy C.rateFamily.rate D.rateCauchy

end ExactRateLimitData

/-- Cutoff removal for one exact physical logarithmic rate family.

`rateCauchy` is the quantitative scale-removal input.  The lower and upper
survival fields expose the limiting band to downstream consumers; for an exact
certificate they are constructively generated by
`ExactRateLimitData.ofRateCauchy`. -/
structure ExactRateCutoffRemoval
    (C : FullRangeExactPhysicalSeparatorCertificate) : Type 1 where
  /-- The physical spacings are cofinal at zero. -/
  spacingToZero : SpacingToZero C.rateFamily.physicalSpacing
  /-- Type-level eventual Cauchy modulus for the exact physical-rate sequence. -/
  rateCauchy : CReal.ModCauchyEv C.rateFamily.rate
  /-- The positive finite-scale floor survives the constructed rate limit. -/
  floor_survives :
    CReal.leEv (CReal.ofQ' C.uniformFloor.floor)
      (CReal.completeLimitCauchy C.rateFamily.rate rateCauchy)
  /-- The finite-scale ceiling also survives, excluding an infinite-mass
  degeneration of the selected continuum rate. -/
  ceiling_survives :
    CReal.leEv (CReal.completeLimitCauchy C.rateFamily.rate rateCauchy)
      (CReal.ofQ' C.finiteCeiling.ceiling)

/-- Add a separately proved spacing-to-zero modulus to the analytic rate-limit
data. -/
def ExactRateLimitData.withSpacing
    {C : FullRangeExactPhysicalSeparatorCertificate}
    (D : ExactRateLimitData C)
    (Z : SpacingToZero C.rateFamily.physicalSpacing) :
    ExactRateCutoffRemoval C where
  spacingToZero := Z
  rateCauchy := D.rateCauchy
  floor_survives := D.floor_survives
  ceiling_survives := D.ceiling_survives

namespace ExactRateCutoffRemoval

/-- The continuum exact physical rate constructed from the supplied Cauchy
modulus. -/
def continuumRate {C : FullRangeExactPhysicalSeparatorCertificate}
    (R : ExactRateCutoffRemoval C) : CReal :=
  CReal.completeLimitCauchy C.rateFamily.rate R.rateCauchy

/-- The exact finite-scale floor survives to the continuum rate. -/
theorem continuumRate_ge_floor
    {C : FullRangeExactPhysicalSeparatorCertificate}
    (R : ExactRateCutoffRemoval C) :
    CReal.leEv (CReal.ofQ' C.uniformFloor.floor) R.continuumRate :=
  R.floor_survives

/-- The continuum rate remains below the exact finite-scale ceiling. -/
theorem continuumRate_le_ceiling
    {C : FullRangeExactPhysicalSeparatorCertificate}
    (R : ExactRateCutoffRemoval C) :
    CReal.leEv R.continuumRate
      (CReal.ofQ' C.finiteCeiling.ceiling) :=
  R.ceiling_survives

/-- The surviving lower bound is genuinely positive in the eventual order. -/
theorem continuumRate_eventuallyPositive
    {C : FullRangeExactPhysicalSeparatorCertificate}
    (R : ExactRateCutoffRemoval C) :
    (0 : Q') < C.uniformFloor.floor /\
      CReal.leEv (CReal.ofQ' C.uniformFloor.floor) R.continuumRate :=
  ⟨C.uniformFloor.floor_pos, R.continuumRate_ge_floor⟩

/-- The surviving rational floor makes the exact continuum rate strictly
positive in the equivalence-stable eventual order. -/
theorem continuumRate_posEv
    {C : FullRangeExactPhysicalSeparatorCertificate}
    (R : ExactRateCutoffRemoval C) : PosEv R.continuumRate :=
  ⟨C.uniformFloor.floor, C.uniformFloor.floor_pos,
    R.continuumRate_ge_floor⟩

end ExactRateCutoffRemoval

/-! ## 4. OS/GNS realization on the same continuum object -/

/-- The complete M4 realization contract for an exact physical separator
certificate and one projective continuum measure.

`exactGap` identifies the constructed exact-rate limit with the computed
`-log(reconstruction.gapBound)` value.  This is the same logarithmic currency
as the finite physical separator.  It does not follow merely from pointwise
finite-scale decay. -/
structure PhysicalSeparatorContinuumRealization
    (C : FullRangeExactPhysicalSeparatorCertificate)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  /-- The externally supplied interpretation of observables on stage measures. -/
  stageCorrelators : StageCorrelationSemantics C.separator M
  /-- Same physical correlators on the selected projective-measure thread. -/
  projectiveIdentification :
    ProjectiveCorrIdentification C.separator mu stageCorrelators
  /-- Quantitative spacing/cutoff removal for the exact rate family. -/
  cutoffRemoval : ExactRateCutoffRemoval C
  /-- Physical lattice separations used at fixed continuum time. -/
  physicalSampling :
    PhysicalSeparationSampling C.rateFamily.physicalSpacing
  /-- Physically rescaled limits of the same selected-stage correlators. -/
  continuumCorrelators : ContinuumCorrelationSemantics C.separator mu
    stageCorrelators C.rateFamily.physicalSpacing physicalSampling
  /-- Genuine 4D continuum Yang--Mills existence on this same measure. -/
  existence : ContinuumYMExistence mu
  /-- The OS functional is the selected-thread limit, and its reconstruction
  uses definitionally the same OS4 spectral model and gap separator. -/
  osGNS : MeasureLinkedOSGNSData existence
  /-- The reconstruction's nonzero spectral channel is the continuum limit of
  the same physically sampled separator-controlled correlator. -/
  reconstructionCorrelators : ReconstructionCorrIdentification C.separator
    osGNS.reconstruction continuumCorrelators
  /-- Fixed connected-two-point insertion semantics in the OS algebra. -/
  osConnectedTwoPoint : OSConnectedTwoPointSemantics existence
  /-- The OS functional, continuum correlation, and reconstructed spectral
  channel all describe the same gap observable. -/
  osGapCorrelation : OSGapCorrelationIdentification C.separator existence
    osConnectedTwoPoint continuumCorrelators reconstructionCorrelators
  /-- Exact identification of the limiting physical rate with the
  reconstruction's logarithmic Hamiltonian gap. -/
  exactGap : ExactLogGapAt osGNS.reconstruction cutoffRemoval.continuumRate

/-- The exact-log continuum endpoint.  Unlike `ContinuumYMWithGap`, its gap
statement is in Hamiltonian-rate currency `-log(mu)`, not the dimensionless
transfer margin `1-mu`. -/
structure ContinuumYMWithExactLogGap
    (C : FullRangeExactPhysicalSeparatorCertificate)
    {M : Nat -> Type} (mu : ContinuumMeasure M) : Type 2 where
  existence : ContinuumYMExistence mu
  osGNS : MeasureLinkedOSGNSData existence
  cutoffRemoval : ExactRateCutoffRemoval C
  exactGap : ExactLogGapAt osGNS.reconstruction cutoffRemoval.continuumRate

/-- Type-level witness of a strictly positive exact logarithmic Hamiltonian
gap for one reconstruction. -/
structure PositiveExactLogGapWitness
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (reconstruction : OSReconstruction mu) : Type 1 where
  rate : CReal
  rate_posEv : PosEv rate
  exactGap : ExactLogGapAt reconstruction rate

namespace PhysicalSeparatorContinuumRealization

/-- The OS reconstruction fixed by the same measure-linked existence bundle. -/
def reconstruction
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (R : PhysicalSeparatorContinuumRealization C mu) : OSReconstruction mu :=
  R.osGNS.reconstruction

/-- The OS two-point insertion used for the gap is itself obtained as the
limit of expectations on the selected projective-measure thread. -/
theorem osStageGapExpectationConverges
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (R : PhysicalSeparatorContinuumRealization C mu) (t : Nat) :
    CReal.ConvergesTo
      (fun j => R.osGNS.stageFunctional.expectationFromStage j (mu.pick j)
        (R.osConnectedTwoPoint.connectedInsertion
          R.osConnectedTwoPoint.gapInsertion t))
      (CReal.ofQ' (R.existence.os_axioms.E.E
        (R.osConnectedTwoPoint.connectedInsertion
          R.osConnectedTwoPoint.gapInsertion t))) :=
  R.osGNS.projectiveFunctional.stageExpectationConverges _

/-- The limiting OS two-point value is exactly the reconstruction's spectral
correlator for the same nonzero gauge-invariant local channel. -/
theorem osGapCorr_equiv_spectral
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (R : PhysicalSeparatorContinuumRealization C mu) (t : Nat) :
    CReal.Equiv
      (CReal.ofQ' (R.existence.os_axioms.E.E
        (R.osConnectedTwoPoint.connectedInsertion
          R.osConnectedTwoPoint.gapInsertion t)))
      (CReal.ofQ' (SpectralGap.corr R.reconstruction.spec t)) :=
  CReal.Equiv.trans (R.osGapCorrelation.gapCorr_eq t)
    (R.reconstructionCorrelators.spectralCorr_eq t)

/-- The exact certificate's rational floor is a strictly positive
constructive real. -/
def floorIsPositive
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (_R : PhysicalSeparatorContinuumRealization C mu) :
    CReal.IsPositive (CReal.ofQ' C.uniformFloor.floor) :=
  ⟨C.uniformFloor.floor, C.uniformFloor.floor_pos,
    CReal.le_refl (CReal.ofQ' C.uniformFloor.floor)⟩

/-- **M4 exact-rate assembly.**  A same-object realization turns the exact
finite-scale physical-rate certificate into a continuum Yang--Mills datum whose
mass is identified with the reconstructed exact logarithmic gap. -/
def toContinuumYMWithExactLogGap
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (R : PhysicalSeparatorContinuumRealization C mu) :
    ContinuumYMWithExactLogGap C mu where
  existence := R.existence
  osGNS := R.osGNS
  cutoffRemoval := R.cutoffRemoval
  exactGap := R.exactGap

/-- The exact endpoint's mass is the constructed cutoff limit. -/
def endpointMass
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMWithExactLogGap C mu) : CReal :=
  H.cutoffRemoval.continuumRate

/-- The exact endpoint's mass retains the certificate's positive rational
floor in the eventual order. -/
theorem endpointMass_posEv
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMWithExactLogGap C mu) : PosEv (endpointMass H) :=
  H.cutoffRemoval.continuumRate_posEv

@[simp] theorem toContinuumYMWithExactLogGap_mass
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (R : PhysicalSeparatorContinuumRealization C mu) :
    endpointMass R.toContinuumYMWithExactLogGap =
      R.cutoffRemoval.continuumRate := rfl

/-- The resulting continuum Hamiltonian has an exact logarithmic gap at a
strictly positive physical rate, in the equivalence-stable eventual order. -/
def continuumYangMillsExactLogGap
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (R : PhysicalSeparatorContinuumRealization C mu) :
    PositiveExactLogGapWitness R.reconstruction where
  rate := R.cutoffRemoval.continuumRate
  rate_posEv := R.cutoffRemoval.continuumRate_posEv
  exactGap := R.exactGap

/-- Currency-correct export to the historical margin-valued continuum
endpoint.  Its mass is the reconstruction's canonical transfer margin
`1 - gapBound`, not the generally larger exact logarithmic rate. -/
def toContinuumYMWithCanonicalMarginGap
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (R : PhysicalSeparatorContinuumRealization C mu) :
    ContinuumYMWithGap mu :=
  continuumYMWithCanonicalMarginGap R.existence R.reconstruction

/-- Compatibility export to the historical margin-valued endpoint.

This requires a separate hypothesis because `HasSpectralGapAt` compares its
argument with `1 - gapBound`; the exact physical rate is instead `-log(mu)`.
No conversion between those differently normalized quantities is claimed. -/
def toContinuumYMWithGapOfMarginCompatibility
    {C : FullRangeExactPhysicalSeparatorCertificate}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (R : PhysicalSeparatorContinuumRealization C mu)
    (floorMarginGap :
      HasSpectralGapAt R.reconstruction
        (CReal.ofQ' C.uniformFloor.floor)) :
    ContinuumYMWithGap mu where
  toContinuumYMExistence := R.existence
  reconstruction := R.reconstruction
  mass := CReal.ofQ' C.uniformFloor.floor
  mass_pos := R.floorIsPositive
  spectral_gap := floorMarginGap

end PhysicalSeparatorContinuumRealization

end YMGap.Continuum.PhysicalSeparatorContinuumRealization

#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ProjectiveCorrIdentification.pickedCorrControl
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ProjectiveCorrIdentification.rescaledPickedCorrControl
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.leEv_of_termwise_le_completeLimitCauchy
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.leEv_completeLimitCauchy_of_termwise_le
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ExactRateLimitData.ofRateCauchy
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ExactRateLimitData.ofSummableStepVariation
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ExactRateLimitData.ofSummableEventualStepVariation
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ExactRateLimitData.withSpacing
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ExactRateCutoffRemoval.continuumRate
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ExactRateCutoffRemoval.continuumRate_eventuallyPositive
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.ExactRateCutoffRemoval.continuumRate_posEv
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.floorIsPositive
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.osStageGapExpectationConverges
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.osGapCorr_equiv_spectral
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.toContinuumYMWithExactLogGap
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.endpointMass_posEv
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.continuumYangMillsExactLogGap
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.toContinuumYMWithCanonicalMarginGap
#print axioms YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.toContinuumYMWithGapOfMarginCompatibility
