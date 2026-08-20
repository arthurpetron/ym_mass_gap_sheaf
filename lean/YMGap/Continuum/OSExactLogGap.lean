/-
M4c -- the exact logarithmic Hamiltonian-rate interface for an OS
reconstruction.

`OSReconstruction.HasSpectralGapAt rec m` uses the dimensionless transfer
margin `1 - rec.gapBound`.  The physical separator pipeline instead constructs
the logarithmic Hamiltonian rate `-log(q)/a`.  These quantities are related but
are not interchangeable.  In particular, `-log(q)` is generally larger than
`1-q`, so an exact logarithmic rate must not be inserted into a margin bound.

This file gives the reconstruction side its matching exact currency.  For a
strictly positive rational transfer separator `mu = rec.gapBound < 1`, the
existing computable binary reduction constructs the faithful value

    exactLogGap rec = -log(mu) > 0.

`ExactLogGapAt rec m` then says that a proposed continuum Hamiltonian rate `m`
is `CReal.Equiv` to that computed value.  The finite spectral bound itself is
already the structural field `rec.hasGap`; this record adds only the missing
strict positivity of `mu` (excluding the infinite-energy case `mu = 0`) and the
exact rate identification.

No continuum reconstruction or rate identification is constructed here.  The
module only supplies the dimensionally correct target and proves the exact-log
value positive.
-/

import YMGap.Continuum.HamiltonianAllSep
import YMGap.Continuum.OSReconstruction

namespace YMGap.Continuum.OSExactLogGap

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.OSReconstruction

/-! ## 1. Positive transfer separator and its computable binary reduction -/

/-- The finite transfer separator of a reconstruction is strictly positive.
`OSReconstruction` itself only supplies nonnegativity; strict positivity rules
out `mu = 0`, whose logarithmic Hamiltonian energy would be infinite. -/
structure PositiveTransferGapBound
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) : Type where
  num_pos : 0 < rec.gapBound.num

/-- Numerator/denominator form of the structural strict bound `mu < 1`. -/
theorem gapBound_num_lt_den
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) :
    rec.gapBound.num < (rec.gapBound.den : Int) := by
  have h := rec.gapBound_lt_one
  change rec.gapBound.num * (1 : Int) <
    (1 : Int) * (rec.gapBound.den : Int) at h
  simpa only [Int.mul_one, Int.one_mul] using h

/-- Computable binary exponent putting the reconstruction separator's mantissa
in `[1/2,1)`. -/
def gapBinExp
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) (P : PositiveTransferGapBound rec) :
    BinExpData rec.gapBound :=
  binExpOf rec.gapBound P.num_pos (gapBound_num_lt_den rec)

/-- Reduced mantissa of the reconstruction's rational transfer separator. -/
def gapMantissa
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) (P : PositiveTransferGapBound rec) : Q' :=
  mant rec.gapBound (gapBinExp rec P).k

/-- The reduced mantissa is strictly below one. -/
theorem gapMantissa_lt_one
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) (P : PositiveTransferGapBound rec) :
    gapMantissa rec P < (1 : Q') :=
  mant_lt_one rec.gapBound (gapBinExp rec P).k (gapBinExp rec P).hlt

/-- Positivity input for the mantissa's artanh coordinate. -/
theorem gapMantissaPlusOne_pos
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) (P : PositiveTransferGapBound rec) :
    (0 : Q') < gapMantissa rec P + 1 :=
  mant_pos rec.gapBound (gapBinExp rec P).k P.num_pos

/-- The reduced mantissa lies in the direct constructive logarithm window. -/
theorem gapMantissa_window
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) (P : PositiveTransferGapBound rec) :
    Q'.abs (yOf (gapMantissa rec P) (gapMantissaPlusOne_pos rec P)) <=
      recipOdd 1 :=
  mant_window rec.gapBound (gapBinExp rec P) P.num_pos

/-! ## 2. Exact logarithmic Hamiltonian gap -/

/-- The exact reconstructed Hamiltonian rate `-log(mu)`, with the binary
logarithm scale pinned by the computed exponent. -/
def exactLogGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) (P : PositiveTransferGapBound rec) : CReal :=
  hamiltonianGapRealAll (gapMantissa rec P) (gapBinExp rec P).k
    (gapMantissaPlusOne_pos rec P) (gapMantissa_window rec P)

/-- The computed exact logarithmic Hamiltonian gap is strictly positive. -/
theorem exactLogGap_isPositive
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) (P : PositiveTransferGapBound rec) :
    CReal.IsPositive (exactLogGap rec P) :=
  hamiltonianGapRealAll_pos
    (gapMantissa rec P) (gapBinExp rec P).k
    (gapMantissaPlusOne_pos rec P) (gapMantissa_lt_one rec P)
    (gapMantissa_window rec P)

/-- Exact physical-rate identification for one reconstruction.

The record does not own the rate or the reconstruction: both are external
parameters.  Its equality field therefore cannot manufacture a free rate; it
must identify the supplied `rate` with the separator already stored in `rec`. -/
structure ExactLogGapAt
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (rec : OSReconstruction mu) (rate : CReal) : Type 1 where
  positiveGapBound : PositiveTransferGapBound rec
  rate_equiv : CReal.Equiv rate (exactLogGap rec positiveGapBound)

namespace ExactLogGapAt

/-- The exact-rate binding is attached to a genuine located transfer spectral
bound, inherited from the reconstruction rather than postulated again. -/
theorem spectralGapBound
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {rec : OSReconstruction mu} {rate : CReal}
    (_E : ExactLogGapAt rec rate) :
    SpectralGap.SpectralGapBound rec.spec rec.gapBound :=
  rec.hasGap

/-- The reconstruction-side exact logarithmic value is strictly positive. -/
theorem reconstructedRate_isPositive
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {rec : OSReconstruction mu} {rate : CReal}
    (E : ExactLogGapAt rec rate) :
    CReal.IsPositive (exactLogGap rec E.positiveGapBound) :=
  exactLogGap_isPositive rec E.positiveGapBound

end ExactLogGapAt

end YMGap.Continuum.OSExactLogGap

#print axioms YMGap.Continuum.OSExactLogGap.gapBound_num_lt_den
#print axioms YMGap.Continuum.OSExactLogGap.gapBinExp
#print axioms YMGap.Continuum.OSExactLogGap.gapMantissa_window
#print axioms YMGap.Continuum.OSExactLogGap.exactLogGap_isPositive
#print axioms YMGap.Continuum.OSExactLogGap.ExactLogGapAt.spectralGapBound
#print axioms YMGap.Continuum.OSExactLogGap.ExactLogGapAt.reconstructedRate_isPositive
