/-
Stage-2 SYNTHESIS CAPSTONE / R2+R3+O(4) — **the single continuum certificate**:
ONE named structure bundling the three sharp, asymptotic-freedom-routed continuum
inputs, from which the entire a→0 continuum Yang–Mills package — a strictly
positive continuum mass gap, nontriviality, and O(4) rotation restoration — is
PROVED at once.

# What this module IS

This is the Stage-2 analogue of how a single thermodynamic-limit input collapses
the entire infinite-volume frontier into one named bound.  Here the a→0 continuum
frontier is collapsed into ONE `ContinuumCertificate` carrying exactly THREE
spacing-uniform single-step bounds — already the genuine open analytic core
(Bałaban-class spacing-uniform estimates) factored out by prior waves:

  * a `UniformRatioVariation` — the summable single-step variation of the
    dimensionless gap ratio `Δ/√σ̂` along the proved AF schedule (the GAP wall);
  * a `ScalingDimensionDecay` — the single-step geometric contraction of the
    leading rotation-breaking operator's coefficient (the O(4) wall);
  * a `LambdaPositiveLimit` — the positive-finite continuum limit of the
    RG-invariant scale `Λ` (the NONTRIVIALITY / dimensional-transmutation wall),

together with the `AFTrajectoryCertificate` trajectory data those inputs share
(whose schedule/rate half is already PROVED — the reciprocal AF rate, with
`af_BetaNonzero` discharged unconditionally upstream).

# What this module PROVES (all genuine compositions — no new analytic content)

The capstone theorems are GENUINE COMPOSITIONS of the three already-proved
reductions; no new analytic content is smuggled in.

  * `continuum_gap_positive` — the continuum gap (the constructed dimensionless
    ratio limit) is `CReal.IsPositive`, via `continuum_ratio_isPositive` applied
    to the certificate's `UniformRatioVariation` field.
  * `continuum_o4_restored` — the O(4) rotation-breaking coefficient converges
    (restoration), via `rotationRestored_of_decay` applied to the certificate's
    `ScalingDimensionDecay` field.
  * `continuum_nontrivial` — `IsNontrivial`, via
    `isNontrivial_of_lambdaPositiveLimit` applied to the certificate's
    `LambdaPositiveLimit` field.

  * `ContinuumYMGap` / `continuumYMGap_of_certificate` — THE PACKAGED CONCLUSION:
    a single `Type`-level structure carrying the strictly-positive continuum mass
    (the located gap `CReal` + its positivity), the nontriviality witness, and
    the O(4)-restoration witness TOGETHER, produced from the ONE certificate by
    composing the three reductions.

  * `osCarrier_of_certificate` — the capstone supersedes the older opaque oracle:
    GIVEN the abstract OS-reconstruction objects, the certificate's
    `LambdaPositiveLimit` field DISCHARGES the previously-opaque
    `ContinuumOSCarrier.nontrivial` oracle (a strictly-positive continuum
    correlation), routed through the proved AF running.

# THE LEDGER (proved-vs-named, in one place)

The ENTIRE a→0 continuum frontier is now reduced to the THREE spacing-uniform
single-step bounds carried by `ContinuumCertificate`:

  | continuum requirement        | reduced to (named open input)   | the reduction PROVED  |
  |------------------------------|---------------------------------|-----------------------|
  | R3 strictly-positive gap     | `UniformRatioVariation`         | `continuum_ratio_isPositive` |
  | R2 nontriviality             | `LambdaPositiveLimit`           | `isNontrivial_of_lambdaPositiveLimit` |
  | O(4) rotation restoration    | `ScalingDimensionDecay`         | `rotationRestored_of_decay`  |

The AF SCHEDULE / reciprocal rate half is already PROVED (the certificate's
trajectory supplies it), and the running-obstruction `af_BetaNonzero` is
discharged unconditionally upstream.  The capstone proves the three named inputs
JOINTLY deliver the Clay continuum requirements (R2 + R3 + O(4)).

This does NOT close the continuum limit.  The three fields of
`ContinuumCertificate` are the genuine open analytic core (Bałaban-class
spacing-uniform single-step estimates); they are NAMED, `Type`-level, and NOT
inhabited here.  What is proved is that they SUFFICE — together they collapse the
whole a→0 frontier to one certificate.

# Axiom-gate (AGENTS.md Rules 1, 6, 8)

Pure composition over already-proved reductions; no new analytic content, no new
`axiom`, no `sorry`/`admit`, no `Classical.*`/`native_decide`/`decide`-on-
nondecidable, no `Prop := True` stub.  The three certificate fields remain the
named open inputs, carried as `Type`-level data (Rule 8).  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.
-/

import YMGap.Continuum.ContinuumGapModulus
import YMGap.Continuum.O4RestorationAF
import YMGap.Continuum.Nontriviality

namespace YMGap.Continuum.ContinuumCertificate

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.ContinuumGapModulus
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.Nontriviality

/-! ## 1. The single continuum certificate

`ContinuumCertificate` bundles the THREE sharp, AF-routed named inputs — the gap
ratio variation, the O(4) scaling-dimension decay, and the positive-finite scale
limit — together with the shared AF trajectory data they consume.  These three
fields ARE the genuine open analytic core (Bałaban-class spacing-uniform
single-step estimates); the certificate is the one named object the whole a→0
frontier reduces to. -/

/-- **The single continuum certificate (the one a→0 frontier input).**

`Type`-level data bundling the three sharp, asymptotic-freedom-routed continuum
inputs and the shared AF trajectory:

  * `traj` — the AF trajectory certificate (the two-loop running with explicit
    remainder, whose reciprocal-rate SCHEDULE half is already PROVED);
  * `ratioVar` — the `UniformRatioVariation` for `traj`: the summable single-step
    variation of the dimensionless gap ratio along the AF schedule (the GAP wall);
  * `scalingDecay` — the `ScalingDimensionDecay`: the single-step geometric
    contraction of the leading rotation-breaking coefficient (the O(4) wall);
  * `lambdaLimit` — the `LambdaPositiveLimit` for `traj`: the positive-finite
    continuum limit of the RG-invariant scale `Λ` (the NONTRIVIALITY wall).

The three named fields are the genuine open analytic core; they are NOT inhabited
here.  The capstone proves they JOINTLY deliver the continuum requirements. -/
structure ContinuumCertificate : Type where
  /-- The shared AF trajectory certificate (two-loop running; the reciprocal-rate
  schedule half is already PROVED upstream). -/
  traj : AFTrajectoryCertificate
  /-- **The gap wall:** the summable single-step variation of the dimensionless
  gap ratio `Δ/√σ̂` along the AF schedule. -/
  ratioVar : UniformRatioVariation traj
  /-- **The O(4) wall:** the single-step geometric contraction of the leading
  rotation-breaking operator's coefficient. -/
  scalingDecay : ScalingDimensionDecay
  /-- **The nontriviality wall:** the positive-finite continuum limit of the
  RG-invariant scale `Λ` (dimensional transmutation). -/
  lambdaLimit : LambdaPositiveLimit traj

/-! ## 2. The three capstone theorems

Each is a GENUINE COMPOSITION of one already-proved reduction with the matching
certificate field — no new analytic content. -/

/-- **Capstone (R3 gap).**  The continuum gap — the constructed dimensionless
ratio limit along the AF schedule — is strictly positive, `CReal.IsPositive`.
This is `continuum_ratio_isPositive` applied to the certificate's
`UniformRatioVariation` field: the dimensionless gap survives the a→0 limit, given
the named single-step variation bound. -/
theorem continuum_gap_positive (cert : ContinuumCertificate) :
    CReal.IsPositive (continuumRatioLimit cert.traj cert.ratioVar) :=
  continuum_ratio_isPositive cert.traj cert.ratioVar

/-- **Capstone (O(4) restoration).**  The leading rotation-breaking operator's
coefficient converges along the AF schedule (with an explicit two-sided modulus):
continuous O(4) rotation symmetry is restored as a→0.  This is
`rotationRestored_of_decay` applied to the certificate's `ScalingDimensionDecay`
field. -/
theorem continuum_o4_restored (cert : ContinuumCertificate) :
    RotationRestored cert.scalingDecay :=
  rotationRestored_of_decay cert.scalingDecay

/-- **Capstone (R2 nontriviality).**  The continuum theory is nontrivial: the
RG-invariant scale `Λ` has a positive-finite continuum limit (dimensional
transmutation), so a genuine physical scale survives — the theory is interacting,
not free.  This is `isNontrivial_of_lambdaPositiveLimit` applied to the
certificate's `LambdaPositiveLimit` field. -/
def continuum_nontrivial (cert : ContinuumCertificate) :
    IsNontrivial cert.lambdaLimit.schedule :=
  isNontrivial_of_lambdaPositiveLimit cert.traj cert.lambdaLimit

/-! ## 3. The packaged conclusion

`ContinuumYMGap` carries the three continuum conclusions TOGETHER, and
`continuumYMGap_of_certificate` produces it from the ONE certificate by composing
the three capstone theorems above. -/

/-- **The full continuum Yang–Mills gap package.**

`Type`-level data carrying, TOGETHER, the three continuum requirements delivered
by a `ContinuumCertificate`:

  * `gap` — the continuum gap, as a `CReal` (the constructed dimensionless ratio
    limit along the AF schedule);
  * `gap_positive` — the gap is strictly positive (R3);
  * `nontrivial` — the dimensional-transmutation nontriviality witness for the
    certificate's scale schedule (R2);
  * `o4_restored` — the proved O(4) rotation-restoration convergence. -/
structure ContinuumYMGap (cert : ContinuumCertificate) : Type where
  /-- The continuum gap (the constructed dimensionless ratio limit). -/
  gap : CReal
  /-- **R3:** the continuum gap is strictly positive. -/
  gap_positive : CReal.IsPositive gap
  /-- **R2:** the continuum theory is nontrivial (dimensional transmutation). -/
  nontrivial : IsNontrivial cert.lambdaLimit.schedule
  /-- **O(4):** continuous rotation symmetry is restored (coefficient converges). -/
  o4_restored : RotationRestored cert.scalingDecay

/-- **THE CAPSTONE.**  From a single `ContinuumCertificate`, the full continuum
Yang–Mills gap package is delivered — a strictly-positive continuum mass gap (R3),
nontriviality (R2), and O(4) rotation restoration — by composing the three
already-proved reductions.  No new analytic content: each conclusion is the
matching capstone theorem read off the certificate's field. -/
def continuumYMGap_of_certificate (cert : ContinuumCertificate) :
    ContinuumYMGap cert where
  gap := continuumRatioLimit cert.traj cert.ratioVar
  gap_positive := continuum_gap_positive cert
  nontrivial := continuum_nontrivial cert
  o4_restored := continuum_o4_restored cert

/-- The packaged gap's strict positivity IS the constructed dimensionless ratio
limit's positivity — confirming the package carries the genuine (not stub) R3
content. -/
theorem continuumYMGap_gap_positive (cert : ContinuumCertificate) :
    CReal.IsPositive (continuumYMGap_of_certificate cert).gap :=
  (continuumYMGap_of_certificate cert).gap_positive

/-! ## 4. Superseding the old opaque OS oracle

The certificate's `LambdaPositiveLimit` field DISCHARGES the previously-opaque
`ContinuumYMStack.ContinuumOSCarrier.nontrivial` oracle: the surviving positive
continuum scale `Λ_∞` is itself a strictly-positive continuum correlation, so it
serves as the nontriviality witness.  GIVEN the remaining abstract
OS-reconstruction objects (the genuine reconstruction inputs this capstone does
not sharpen), the certificate BUILDS the carrier with its nontriviality oracle
replaced by the physical dimensional-transmutation statement, routed through the
proved AF running. -/

/-- **The OS carrier from the certificate.**  GIVEN the abstract
OS-reconstruction objects (Hilbert space, Hamiltonian, finite spectral model with
its genuine located gap), the certificate's `LambdaPositiveLimit` field discharges
the `ContinuumOSCarrier.nontrivial` oracle via the surviving positive continuum
scale.  The capstone thereby supersedes the old opaque nontriviality oracle. -/
def osCarrier_of_certificate (cert : ContinuumCertificate)
    (H : OSReconstruction.HilbertSpace)
    (Ham : OSReconstruction.SelfAdjointOp H)
    (spec : SpectralGap.SpectralModel)
    (locatedGap : LocatedSpectralGap spec) :
    ContinuumYMStack.ContinuumOSCarrier :=
  osCarrier_of_lambdaPositiveLimit cert.traj cert.lambdaLimit H Ham spec locatedGap

/-- The carrier built from the certificate really is nontrivial: the observable at
its nontriviality index is the surviving scale `Λ_∞`, which is strictly positive.
Confirms the discharge supplies genuine (not `True`) content. -/
theorem osCarrier_of_certificate_nontrivial (cert : ContinuumCertificate)
    (H : OSReconstruction.HilbertSpace)
    (Ham : OSReconstruction.SelfAdjointOp H)
    (spec : SpectralGap.SpectralModel)
    (locatedGap : LocatedSpectralGap spec) :
    CReal.IsPositive
      ((osCarrier_of_certificate cert H Ham spec locatedGap).observable
        (osCarrier_of_certificate cert H Ham spec locatedGap).nontrivial.1) :=
  osCarrier_nontrivial_of_lambdaPositiveLimit cert.traj cert.lambdaLimit
    H Ham spec locatedGap

/-! ## 5. The honest ledger, restated as a checkable summary

`certificate_ledger` records, as a `Type`-level conjunction (a `Σ'`/`PProd`
package), the status this module establishes from one certificate: all three
continuum conclusions hold simultaneously.  It is proved by exhibiting the three
capstone results — the open content is exactly the three named fields of
`ContinuumCertificate`. -/

/-- **The certificate ledger.**  From a single `ContinuumCertificate`, the three
continuum requirements hold together: the continuum gap is strictly positive (R3),
the theory is nontrivial (R2), and O(4) rotation symmetry is restored.  The proof
bundles the three capstone results; the open content lives ENTIRELY in the three
named fields of `ContinuumCertificate`. -/
def certificate_ledger (cert : ContinuumCertificate) :
    PProd (CReal.IsPositive (continuumRatioLimit cert.traj cert.ratioVar))
      (PProd (IsNontrivial cert.lambdaLimit.schedule)
        (RotationRestored cert.scalingDecay)) :=
  ⟨continuum_gap_positive cert,
   ⟨continuum_nontrivial cert, continuum_o4_restored cert⟩⟩

end YMGap.Continuum.ContinuumCertificate

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumCertificate.continuum_gap_positive
#print axioms YMGap.Continuum.ContinuumCertificate.continuum_o4_restored
#print axioms YMGap.Continuum.ContinuumCertificate.continuum_nontrivial
#print axioms YMGap.Continuum.ContinuumCertificate.continuumYMGap_of_certificate
#print axioms YMGap.Continuum.ContinuumCertificate.continuumYMGap_gap_positive
#print axioms YMGap.Continuum.ContinuumCertificate.osCarrier_of_certificate
#print axioms YMGap.Continuum.ContinuumCertificate.osCarrier_of_certificate_nontrivial
#print axioms YMGap.Continuum.ContinuumCertificate.certificate_ledger
