/-
# Sharded exact rows for the lower-six E8/E9 identities

The generated E8/E9 grids are first stripped of syntactic zero terms and
bucketed by the mode exponent.  The structured Taylor contribution is formed
as a row-wise Cauchy product, and the Base contribution is scaled row by row.
No definition here canonicalizes a dense composite polynomial.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorRaw
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRawRows
import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
import YMGap.Continuum.QuadraticRawGridSemanticTransport
import YMGap.Continuum.RawGridRowConvolution

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows

set_option maxRecDepth 100000

open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorRaw
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.QuadraticRawGridSemanticTransport
open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.RawGridRowConvolution
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

private abbrev RP := RingNormaliser.RawPoly

/-- The exact left side `4608 * E8Cleared`, with zero terms erased before
row bucketing. -/
def tailEnvelopeE8ScaledRawPolynomial : RP :=
  removeZeroRaw
    (quadraticRawGrid 83 44 89
      (fun i j => 4608 * gridCoeff tailEnvelopeE8ClearedRows i j))

/-- The exact left side `512 * E9Cleared`, with zero terms erased before row
bucketing. -/
def tailEnvelopeE9ScaledRawPolynomial : RP :=
  removeZeroRaw
    (quadraticRawGrid 87 44 89
      (fun i j => 512 * gridCoeff tailEnvelopeE9ClearedRows i j))

def tailEnvelopeE8ScaledRawRows : List RP :=
  bucketRaw 28 tailEnvelopeE8ScaledRawPolynomial

def tailEnvelopeE9ScaledRawRows : List RP :=
  bucketRaw 28 tailEnvelopeE9ScaledRawPolynomial

/-! The Taylor factors have first-exponent support `< 19` and `< 10`.
Using the uniform count `19` for both E8 and E9 pads E8 by two exact empty
rows and makes both Cauchy products have exactly 28 rows. -/

def tailEnvelopeTaylor8PrefixRows : List RP :=
  bucketRaw 19 tailEnvelopeTaylor8PrefixSquareRaw

def tailEnvelopeTaylor9PrefixRows : List RP :=
  bucketRaw 19 tailEnvelopeTaylor9PrefixSquareRaw

def tailEnvelopeTaylorCommonStepRows : List RP :=
  bucketRaw 10 tailEnvelopeTaylorCommonStepRaw

def tailEnvelopeTaylor8ConvolutionRows : List RP :=
  rawRowsConvolution
    tailEnvelopeTaylor8PrefixRows tailEnvelopeTaylorCommonStepRows

def tailEnvelopeTaylor9ConvolutionRows : List RP :=
  rawRowsConvolution
    tailEnvelopeTaylor9PrefixRows tailEnvelopeTaylorCommonStepRows

/-- Exact multiplication of every public Base semantic row by `737280`. -/
def tailEnvelopeBaseScaledRows : List RP :=
  rawMulRows (scalarRawRow 737280) tailBaseSemanticTotalRows

def tailEnvelopeE8StructuredRawRows : List RP :=
  appendRawRows
    tailEnvelopeTaylor8ConvolutionRows tailEnvelopeBaseScaledRows

def tailEnvelopeE9StructuredRawRows : List RP :=
  appendRawRows
    tailEnvelopeTaylor9ConvolutionRows tailEnvelopeBaseScaledRows

/-! ## Structural row counts (no coefficient normalization) -/

theorem tailEnvelopeE8ScaledRawRows_length :
    tailEnvelopeE8ScaledRawRows.length = 28 := by
  exact bucketRaw_length 28 tailEnvelopeE8ScaledRawPolynomial

theorem tailEnvelopeE9ScaledRawRows_length :
    tailEnvelopeE9ScaledRawRows.length = 28 := by
  exact bucketRaw_length 28 tailEnvelopeE9ScaledRawPolynomial

private theorem tailEnvelopeTaylor8PrefixRows_length :
    tailEnvelopeTaylor8PrefixRows.length = 19 := by
  exact bucketRaw_length 19 tailEnvelopeTaylor8PrefixSquareRaw

private theorem tailEnvelopeTaylor9PrefixRows_length :
    tailEnvelopeTaylor9PrefixRows.length = 19 := by
  exact bucketRaw_length 19 tailEnvelopeTaylor9PrefixSquareRaw

private theorem tailEnvelopeTaylorCommonStepRows_length :
    tailEnvelopeTaylorCommonStepRows.length = 10 := by
  exact bucketRaw_length 10 tailEnvelopeTaylorCommonStepRaw

private theorem tailEnvelopeTaylor8PrefixRows_nonempty :
    tailEnvelopeTaylor8PrefixRows ≠ [] := by
  intro h
  have hlen := tailEnvelopeTaylor8PrefixRows_length
  rw [h] at hlen
  change 0 = 19 at hlen
  omega

private theorem tailEnvelopeTaylor9PrefixRows_nonempty :
    tailEnvelopeTaylor9PrefixRows ≠ [] := by
  intro h
  have hlen := tailEnvelopeTaylor9PrefixRows_length
  rw [h] at hlen
  change 0 = 19 at hlen
  omega

private theorem tailEnvelopeTaylorCommonStepRows_nonempty :
    tailEnvelopeTaylorCommonStepRows ≠ [] := by
  intro h
  have hlen := tailEnvelopeTaylorCommonStepRows_length
  rw [h] at hlen
  change 0 = 10 at hlen
  omega

theorem tailEnvelopeTaylor8ConvolutionRows_length :
    tailEnvelopeTaylor8ConvolutionRows.length = 28 := by
  have h := rawRowsConvolution_length_of_nonempty
    tailEnvelopeTaylor8PrefixRows tailEnvelopeTaylorCommonStepRows
    tailEnvelopeTaylor8PrefixRows_nonempty
    tailEnvelopeTaylorCommonStepRows_nonempty
  change (rawRowsConvolution tailEnvelopeTaylor8PrefixRows
    tailEnvelopeTaylorCommonStepRows).length = 28
  exact Eq.trans h (by
    rw [tailEnvelopeTaylor8PrefixRows_length,
      tailEnvelopeTaylorCommonStepRows_length])

theorem tailEnvelopeTaylor9ConvolutionRows_length :
    tailEnvelopeTaylor9ConvolutionRows.length = 28 := by
  have h := rawRowsConvolution_length_of_nonempty
    tailEnvelopeTaylor9PrefixRows tailEnvelopeTaylorCommonStepRows
    tailEnvelopeTaylor9PrefixRows_nonempty
    tailEnvelopeTaylorCommonStepRows_nonempty
  change (rawRowsConvolution tailEnvelopeTaylor9PrefixRows
    tailEnvelopeTaylorCommonStepRows).length = 28
  exact Eq.trans h (by
    rw [tailEnvelopeTaylor9PrefixRows_length,
      tailEnvelopeTaylorCommonStepRows_length])

theorem tailEnvelopeBaseScaledRows_length :
    tailEnvelopeBaseScaledRows.length = 23 := by
  rw [tailEnvelopeBaseScaledRows, rawMulRows_length]
  rfl

theorem tailEnvelopeE8StructuredRawRows_length :
    tailEnvelopeE8StructuredRawRows.length = 28 := by
  rw [tailEnvelopeE8StructuredRawRows, appendRawRows_length,
    tailEnvelopeTaylor8ConvolutionRows_length,
    tailEnvelopeBaseScaledRows_length]
  rfl

theorem tailEnvelopeE9StructuredRawRows_length :
    tailEnvelopeE9StructuredRawRows.length = 28 := by
  rw [tailEnvelopeE9StructuredRawRows, appendRawRows_length,
    tailEnvelopeTaylor9ConvolutionRows_length,
    tailEnvelopeBaseScaledRows_length]
  rfl

#print axioms tailEnvelopeE8ScaledRawPolynomial
#print axioms tailEnvelopeE9ScaledRawPolynomial
#print axioms tailEnvelopeE8StructuredRawRows
#print axioms tailEnvelopeE9StructuredRawRows
#print axioms tailEnvelopeE8ScaledRawRows_length
#print axioms tailEnvelopeE9ScaledRawRows_length
#print axioms tailEnvelopeE8StructuredRawRows_length
#print axioms tailEnvelopeE9StructuredRawRows_length

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows
