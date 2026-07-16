/-
# Semantics of the sharded lower-six E8/E9 identities

This module connects the row families to the existing physical cleared
evaluators, the staged Taylor raw polynomials, and the public Base semantic
rows.  It performs no large normalization.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawSupport
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawSemantics

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorRaw
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawSupport
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows
open YMGap.Continuum.QuadraticRawGridSemanticTransport
open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.RawGridRowConvolution
open YMGap.Continuum.TensorBernsteinSeparableReconstruction
open YMGap.Continuum.TensorBernsteinQuadraticProjectiveReconstruction

local infix:50 " ≈ " => Q'.eqv

theorem evalRawRows_tailEnvelopeE8ScaledRawRows (D n : Q') :
    evalRawRows (quadraticRawRho D n) tailEnvelopeE8ScaledRawRows ≈
      tailEnvelopeE8ClearedEval D n * Q'.ofInt 4608 := by
  have hbucket := evalRawRows_bucketRaw (quadraticRawRho D n) 28
    tailEnvelopeE8ScaledRawPolynomial tailEnvelopeE8ScaledRaw_bound
  have hremove := evalRaw_removeZeroRaw (quadraticRawRho D n)
    (quadraticRawGrid 83 44 89
      (fun i j => 4608 * gridCoeff tailEnvelopeE8ClearedRows i j))
  have hgrid := evalRaw_quadraticRawGrid 83 44 89
    (fun i j => 4608 * gridCoeff tailEnvelopeE8ClearedRows i j) D n
  have hscale := quadraticPowerEval_scale_left 83 44 89
    (gridCoeff tailEnvelopeE8ClearedRows) 4608 D n
  exact Q'.eqv_trans _ _ _ hbucket
    (Q'.eqv_trans _ _ _
      (by simpa [tailEnvelopeE8ScaledRawPolynomial] using hremove)
      (Q'.eqv_trans _ _ _ hgrid
        (by simpa [tailEnvelopeE8ClearedEval] using hscale)))

theorem evalRawRows_tailEnvelopeE9ScaledRawRows (D n : Q') :
    evalRawRows (quadraticRawRho D n) tailEnvelopeE9ScaledRawRows ≈
      tailEnvelopeE9ClearedEval D n * Q'.ofInt 512 := by
  have hbucket := evalRawRows_bucketRaw (quadraticRawRho D n) 28
    tailEnvelopeE9ScaledRawPolynomial tailEnvelopeE9ScaledRaw_bound
  have hremove := evalRaw_removeZeroRaw (quadraticRawRho D n)
    (quadraticRawGrid 87 44 89
      (fun i j => 512 * gridCoeff tailEnvelopeE9ClearedRows i j))
  have hgrid := evalRaw_quadraticRawGrid 87 44 89
    (fun i j => 512 * gridCoeff tailEnvelopeE9ClearedRows i j) D n
  have hscale := quadraticPowerEval_scale_left 87 44 89
    (gridCoeff tailEnvelopeE9ClearedRows) 512 D n
  exact Q'.eqv_trans _ _ _ hbucket
    (Q'.eqv_trans _ _ _
      (by simpa [tailEnvelopeE9ScaledRawPolynomial] using hremove)
      (Q'.eqv_trans _ _ _ hgrid
        (by simpa [tailEnvelopeE9ClearedEval] using hscale)))

private theorem evalRaw_tailEnvelopeTaylor8_product (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailEnvelopeTaylor8RawPolynomial ≈
      RingNormaliser.evalRaw rho tailEnvelopeTaylor8PrefixSquareRaw *
        RingNormaliser.evalRaw rho tailEnvelopeTaylorCommonStepRaw := by
  unfold tailEnvelopeTaylor8RawPolynomial
  exact Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho _)
    (RingNormaliser.evalRaw_rawMul rho _ _)

private theorem evalRaw_tailEnvelopeTaylor9_product (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailEnvelopeTaylor9RawPolynomial ≈
      RingNormaliser.evalRaw rho tailEnvelopeTaylor9PrefixSquareRaw *
        RingNormaliser.evalRaw rho tailEnvelopeTaylorCommonStepRaw := by
  unfold tailEnvelopeTaylor9RawPolynomial
  exact Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho _)
    (RingNormaliser.evalRaw_rawMul rho _ _)

theorem evalRawRows_tailEnvelopeTaylor8ConvolutionRows (rho : Nat → Q') :
    evalRawRows rho tailEnvelopeTaylor8ConvolutionRows ≈
      RingNormaliser.evalRaw rho tailEnvelopeTaylor8RawPolynomial := by
  have hconv := evalRawRows_bucketConvolution rho 19 10
    tailEnvelopeTaylor8PrefixSquareRaw tailEnvelopeTaylorCommonStepRaw
    tailEnvelopeTaylor8PrefixRaw_bound
    tailEnvelopeTaylorCommonStepRaw_bound
  exact Q'.eqv_trans _ _ _
    (by simpa [tailEnvelopeTaylor8ConvolutionRows,
      tailEnvelopeTaylor8PrefixRows,
      tailEnvelopeTaylorCommonStepRows] using hconv)
    (Q'.eqv_symm (evalRaw_tailEnvelopeTaylor8_product rho))

theorem evalRawRows_tailEnvelopeTaylor9ConvolutionRows (rho : Nat → Q') :
    evalRawRows rho tailEnvelopeTaylor9ConvolutionRows ≈
      RingNormaliser.evalRaw rho tailEnvelopeTaylor9RawPolynomial := by
  have hconv := evalRawRows_bucketConvolution rho 19 10
    tailEnvelopeTaylor9PrefixSquareRaw tailEnvelopeTaylorCommonStepRaw
    tailEnvelopeTaylor9PrefixRaw_bound
    tailEnvelopeTaylorCommonStepRaw_bound
  exact Q'.eqv_trans _ _ _
    (by simpa [tailEnvelopeTaylor9ConvolutionRows,
      tailEnvelopeTaylor9PrefixRows,
      tailEnvelopeTaylorCommonStepRows] using hconv)
    (Q'.eqv_symm (evalRaw_tailEnvelopeTaylor9_product rho))

theorem evalRawRows_tailEnvelopeBaseScaledRows (rho : Nat → Q') :
    evalRawRows rho tailEnvelopeBaseScaledRows ≈
      Q'.ofInt 737280 * evalRawRows rho tailBaseSemanticTotalRows := by
  have hrows := evalRawRows_rawMulRows rho
    (scalarRawRow 737280) tailBaseSemanticTotalRows
  exact Q'.eqv_trans _ _ _
    (by simpa [tailEnvelopeBaseScaledRows] using hrows)
    (Q'.mul_eqv_congr_right _ _ _
      (evalRaw_scalarRawRow rho 737280))

theorem evalRawRows_tailEnvelopeE8StructuredRawRows (rho : Nat → Q') :
    evalRawRows rho tailEnvelopeE8StructuredRawRows ≈
      RingNormaliser.evalRaw rho tailEnvelopeTaylor8RawPolynomial +
        Q'.ofInt 737280 * evalRawRows rho tailBaseSemanticTotalRows := by
  exact Q'.eqv_trans _ _ _
    (evalRawRows_appendRawRows rho
      tailEnvelopeTaylor8ConvolutionRows tailEnvelopeBaseScaledRows)
    (Q'.add_eqv_congr'
      (evalRawRows_tailEnvelopeTaylor8ConvolutionRows rho)
      (evalRawRows_tailEnvelopeBaseScaledRows rho))

theorem evalRawRows_tailEnvelopeE9StructuredRawRows (rho : Nat → Q') :
    evalRawRows rho tailEnvelopeE9StructuredRawRows ≈
      RingNormaliser.evalRaw rho tailEnvelopeTaylor9RawPolynomial +
        Q'.ofInt 737280 * evalRawRows rho tailBaseSemanticTotalRows := by
  exact Q'.eqv_trans _ _ _
    (evalRawRows_appendRawRows rho
      tailEnvelopeTaylor9ConvolutionRows tailEnvelopeBaseScaledRows)
    (Q'.add_eqv_congr'
      (evalRawRows_tailEnvelopeTaylor9ConvolutionRows rho)
      (evalRawRows_tailEnvelopeBaseScaledRows rho))

#print axioms evalRawRows_tailEnvelopeE8ScaledRawRows
#print axioms evalRawRows_tailEnvelopeE9ScaledRawRows
#print axioms evalRawRows_tailEnvelopeTaylor8ConvolutionRows
#print axioms evalRawRows_tailEnvelopeTaylor9ConvolutionRows
#print axioms evalRawRows_tailEnvelopeBaseScaledRows
#print axioms evalRawRows_tailEnvelopeE8StructuredRawRows
#print axioms evalRawRows_tailEnvelopeE9StructuredRawRows

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawSemantics
