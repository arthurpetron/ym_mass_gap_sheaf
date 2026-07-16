/-
# Staged raw polynomials for the lower-six E8/E9 Taylor contributions

The Taylor-square, common denominator, and step coefficient are normalized
separately and multiplied only after each factor is canonical.  This avoids
the large intermediate syntax tree produced by normalizing the composite
expression in one pass, while retaining exact `evalRaw` semantics.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic
import YMGap.Continuum.RawGridSemanticTransport

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorRaw

open YMGap.Constructive
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorSemantic

local infix:50 " ≈ " => Q'.eqv

private abbrev RP := RingNormaliser.RawPoly

def tailEnvelopeTaylor8PrefixSquareRaw : RP :=
  fastNormalize (.pow envelopeSemanticPrefix8 2)

def tailEnvelopeTaylor9PrefixSquareRaw : RP :=
  fastNormalize (.pow envelopeSemanticPrefix9 2)

def tailEnvelopeTaylorCommonRaw : RP :=
  fastNormalize envelopeSemanticCommon

def tailEnvelopeTaylorStepRaw : RP :=
  fastNormalize envelopeSemanticStep

def tailEnvelopeTaylorCommonStepRaw : RP :=
  RingNormaliser.canon
    (RingNormaliser.rawMul tailEnvelopeTaylorCommonRaw
      tailEnvelopeTaylorStepRaw)

def tailEnvelopeTaylor8RawPolynomial : RP :=
  RingNormaliser.canon
    (RingNormaliser.rawMul tailEnvelopeTaylor8PrefixSquareRaw
      tailEnvelopeTaylorCommonStepRaw)

def tailEnvelopeTaylor9RawPolynomial : RP :=
  RingNormaliser.canon
    (RingNormaliser.rawMul tailEnvelopeTaylor9PrefixSquareRaw
      tailEnvelopeTaylorCommonStepRaw)

private theorem evalRaw_commonStep (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailEnvelopeTaylorCommonStepRaw ≈
      RingNormaliser.eval rho envelopeSemanticCommon *
        RingNormaliser.eval rho envelopeSemanticStep := by
  refine Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho
      (RingNormaliser.rawMul tailEnvelopeTaylorCommonRaw
        tailEnvelopeTaylorStepRaw)) ?_
  refine Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_rawMul rho
      tailEnvelopeTaylorCommonRaw tailEnvelopeTaylorStepRaw) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (evalRaw_fastNormalize rho envelopeSemanticCommon))
    (Q'.mul_eqv_congr_left _ _ _
      (evalRaw_fastNormalize rho envelopeSemanticStep))

theorem evalRaw_tailEnvelopeTaylor8RawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailEnvelopeTaylor8RawPolynomial ≈
      RingNormaliser.eval rho envelopeSemanticTaylor8Scaled := by
  unfold tailEnvelopeTaylor8RawPolynomial
  refine Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho
      (RingNormaliser.rawMul tailEnvelopeTaylor8PrefixSquareRaw
        tailEnvelopeTaylorCommonStepRaw)) ?_
  refine Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_rawMul rho
      tailEnvelopeTaylor8PrefixSquareRaw
      tailEnvelopeTaylorCommonStepRaw) ?_
  unfold envelopeSemanticTaylor8Scaled
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (evalRaw_fastNormalize rho (.pow envelopeSemanticPrefix8 2)))
    (Q'.mul_eqv_congr_left _ _ _ (evalRaw_commonStep rho))

theorem evalRaw_tailEnvelopeTaylor9RawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailEnvelopeTaylor9RawPolynomial ≈
      RingNormaliser.eval rho envelopeSemanticTaylor9Scaled := by
  unfold tailEnvelopeTaylor9RawPolynomial
  refine Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho
      (RingNormaliser.rawMul tailEnvelopeTaylor9PrefixSquareRaw
        tailEnvelopeTaylorCommonStepRaw)) ?_
  refine Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_rawMul rho
      tailEnvelopeTaylor9PrefixSquareRaw
      tailEnvelopeTaylorCommonStepRaw) ?_
  unfold envelopeSemanticTaylor9Scaled
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (evalRaw_fastNormalize rho (.pow envelopeSemanticPrefix9 2)))
    (Q'.mul_eqv_congr_left _ _ _ (evalRaw_commonStep rho))

#print axioms tailEnvelopeTaylor8RawPolynomial
#print axioms tailEnvelopeTaylor9RawPolynomial
#print axioms evalRaw_tailEnvelopeTaylor8RawPolynomial
#print axioms evalRaw_tailEnvelopeTaylor9RawPolynomial

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorRaw
