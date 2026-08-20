/-
M4g -- a canonical export from the reconstruction's logarithmic currency to
the legacy margin-valued continuum endpoint.

`OSReconstruction` already carries both a located transfer separator
`gapBound < 1` and the spectral assertion that all excited eigenvalues lie
below it.  Therefore its own margin `1 - gapBound` is a positive constructive
real and satisfies `HasSpectralGapAt` reflexively.  This module records that
currency-correct fact.

It does not derive the reconstruction or its spectral bound; those are fields
of the input `OSReconstruction` and remain analytic obligations.
-/

import YMGap.Continuum.FourDExistence
import YMGap.Continuum.LocatedSpectralGap

namespace YMGap.Continuum.OSCanonicalMarginGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.OSReconstruction

/-- The reconstruction's own dimensionless transfer-margin gap. -/
def canonicalMarginGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) : CReal :=
  CReal.ofQ' (1 - rec.gapBound)

/-- The canonical transfer margin is strictly positive because the separator
is structurally below one. -/
def canonicalMarginGap_isPositive
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) :
    CReal.IsPositive (canonicalMarginGap rec) :=
  CReal.isPositive_of_approx_ge
    (YMGap.Continuum.one_sub_pos_of_lt_one rec.gapBound_lt_one)
    (fun _ => Q'.le_refl' (1 - rec.gapBound))

/-- The reconstruction has a spectral gap at its own margin.  The rate binding
is reflexive; no comparison with the larger logarithmic rate is asserted. -/
def canonicalMarginGapAt
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) :
    HasSpectralGapAt rec (canonicalMarginGap rec) :=
  ⟨rec.hasGap, CReal.le_refl (canonicalMarginGap rec)⟩

/-- Package any continuum YM existence datum and reconstruction into the
legacy margin-valued gap endpoint, using exactly that reconstruction's own
located spectral margin. -/
def continuumYMWithCanonicalMarginGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu) (rec : OSReconstruction mu) :
    ContinuumYMWithGap mu where
  toContinuumYMExistence := H
  reconstruction := rec
  mass := canonicalMarginGap rec
  mass_pos := canonicalMarginGap_isPositive rec
  spectral_gap := canonicalMarginGapAt rec

end YMGap.Continuum.OSCanonicalMarginGap

#print axioms YMGap.Continuum.OSCanonicalMarginGap.canonicalMarginGap_isPositive
#print axioms YMGap.Continuum.OSCanonicalMarginGap.canonicalMarginGapAt
#print axioms YMGap.Continuum.OSCanonicalMarginGap.continuumYMWithCanonicalMarginGap
