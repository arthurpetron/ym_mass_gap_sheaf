/-
Sharp O(4) output of the continuum certificate.

`ContinuumCertificate.continuum_o4_restored` predates the distinction between
mere Cauchy convergence of the scalar anisotropy coefficient and convergence
of that coefficient to zero.  Keep that declaration for compatibility, but do
not use it as the sharp restoration conclusion.  The geometric decay already
carried by a `ContinuumCertificate` proves the stronger statements:

* the rational rotation-breaking coefficient vanishes with an explicit
  rational cutoff;
* its constructive-real limit is equivalent to zero; and
* after supplying the typed finite-spacing observable response estimate, the
  selected continuum observable action is exactly invariant.

The final item is deliberately parameterized by one selected map and its actual
response estimate.  It is not advertised as full O(4) invariance; constructing
the physical approximating O(4) action and proving that estimate remain the
interacting analytic input.
-/

import YMGap.Continuum.ContinuumCertificate
import YMGap.Continuum.O4ObservableSymmetryBridge

namespace YMGap.Continuum.ContinuumCertificateSharpO4

open YMGap.Constructive
open YMGap.Constructive.RegularCReal
open YMGap.Continuum
open YMGap.Continuum.ContinuumCertificate
open YMGap.Continuum.O4RestorationAF
open YMGap.Continuum.O4RestorationZero
open YMGap.Continuum.O4ObservableSymmetryBridge
open YMGap.Continuum.RegularFunctional
open YMGap.Continuum.RegularLinearScalingLimit

/-! ## 1. The sharp scalar conclusion -/

/-- A continuum certificate forces the leading rotation-breaking coefficient
to vanish, not merely to be Cauchy. -/
theorem continuum_o4_breakCoeff_vanishes (cert : ContinuumCertificate) :
    RotationBreakingVanishes cert.scalingDecay :=
  breakCoeff_vanishes cert.scalingDecay

/-- The constructive-real anisotropy limit determined by the certificate is
exactly zero. -/
theorem continuum_o4_breakCoeffLimit_zero (cert : ContinuumCertificate) :
    CReal.Equiv (breakCoeffLimit cert.scalingDecay) CReal.czero :=
  breakCoeffLimit_equiv_czero cert.scalingDecay

/-- The sharpened conditional continuum package.  It retains the gap and
nontriviality fields of `ContinuumYMGap`, but replaces its legacy Cauchy-only
O(4) field by the genuine scalar zero statements.  This is still conditional
on the three analytic fields of `ContinuumCertificate`; it does not inhabit a
Clay-facing frontier bundle. -/
structure SharpContinuumCertificateResult (cert : ContinuumCertificate) : Type where
  /-- The legacy package supplies the constructed gap and nontriviality data. -/
  base : ContinuumYMGap cert
  /-- The rational anisotropy schedule tends to zero. -/
  anisotropy_vanishes : RotationBreakingVanishes cert.scalingDecay
  /-- The previously constructed anisotropy limit is the zero constructive real. -/
  anisotropy_limit_zero :
    CReal.Equiv (breakCoeffLimit cert.scalingDecay) CReal.czero

/-- Build the sharpened package from the same continuum certificate. -/
def sharpResult_of_certificate (cert : ContinuumCertificate) :
    SharpContinuumCertificateResult cert where
  base := continuumYMGap_of_certificate cert
  anisotropy_vanishes := continuum_o4_breakCoeff_vanishes cert
  anisotropy_limit_zero := continuum_o4_breakCoeffLimit_zero cert

/-! ## 2. Observable-level consequence under the physical response estimate -/

/-- A selected finite-spacing observable response estimate turns the
certificate's scalar zero decay into exact continuum invariance for that
selected action. -/
theorem continuum_selected_observable_invariant
    (cert : ContinuumCertificate)
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    (R : DecayControlledSymmetryResponse A L cert.scalingDecay)
    (o : A.carrier) :
    Equiv (limitE L (R.map o)) (limitE L o) :=
  limitE_invariant_of_decay_response R o

/-- The sharp certificate result together with exact invariance for every
observable under one explicitly supplied selected action.  The action is the
map carried by `R`; no quantification over, or construction of, the full O(4)
group is hidden in this structure. -/
structure SelectedObservableSymmetryResult
    (cert : ContinuumCertificate)
    (A : LinearObsAlg) (L : LinearScalingLimitModulus A)
    (R : DecayControlledSymmetryResponse A L cert.scalingDecay) : Type where
  sharp : SharpContinuumCertificateResult cert
  invariant : ∀ o : A.carrier, Equiv (limitE L (R.map o)) (limitE L o)

/-- Package the selected observable symmetry consequence without weakening or
renaming any pinned Clay-facing statement. -/
def selectedObservableResult_of_response
    (cert : ContinuumCertificate)
    {A : LinearObsAlg} {L : LinearScalingLimitModulus A}
    (R : DecayControlledSymmetryResponse A L cert.scalingDecay) :
    SelectedObservableSymmetryResult cert A L R where
  sharp := sharpResult_of_certificate cert
  invariant := continuum_selected_observable_invariant cert R

#print axioms continuum_o4_breakCoeff_vanishes
#print axioms continuum_o4_breakCoeffLimit_zero
#print axioms SharpContinuumCertificateResult
#print axioms sharpResult_of_certificate
#print axioms continuum_selected_observable_invariant
#print axioms SelectedObservableSymmetryResult
#print axioms selectedObservableResult_of_response

end YMGap.Continuum.ContinuumCertificateSharpO4
