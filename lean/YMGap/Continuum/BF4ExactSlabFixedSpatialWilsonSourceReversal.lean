/-
# Reversing the actual signed Wilson source polynomial

Offset reversal of a supported Wilson expression is the explicit reversal
of the complete chronological quaternion carrier. Every ordered loop word,
spin, signed coefficient, and multi-time product is unchanged internally.
The proof reverses each complete single-slice source character, then uses
the exact polynomial algebra of reindexing.

This pins the original source used by the odd-window kinetic quadratic.
It assumes no reflection positivity, stationarity, decay, or spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow
import YMGap.Continuum.SU2QuaternionHeadWindowReversal

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSourceReversal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOddWindow
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionSliceReversal
open YMGap.Continuum.SU2QuaternionHeadWindowReversal (prefix_lift)

local notation:max "N" width:arg => List.length (baseLinks width)

private theorem reindex_one {blocks : Nat} (s : QuaternionBlockInvolution blocks) :
    QuaternionPrefixPolynomialEqv blocks (reindexQuaternionPolynomial s polyOne) polyOne := by
  apply QuaternionPrefixPolynomialEqv.cons
  · constructor
    · exact Q'.eqv_refl 1
    · intro i hi
      exact exponentAt_reindexQuaternionExponents s [] hi
  · exact .nil

private theorem reverse_single_slice (blocks R offset : Nat) (hoffset : offset ≤ R)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    PaddedPolynomialCoeffEqv ((R+1)*blocks)
      (reversePolynomial blocks R (liftBoundary (offset*blocks) p))
      (liftBoundary ((R-offset)*blocks) p) := by
  have hplace := reversePolynomial_lift blocks R offset 0 (by omega) p
    (by simpa only [Nat.zero_add, Nat.one_mul] using hp)
  have hzero := reversePolynomial_zero blocks p hp
  have hsupport : SupportedQuaternionBlocks blocks (reversePolynomial blocks 0 p) := by
    simpa only [Nat.zero_add, Nat.one_mul] using reversePolynomial_supported blocks 0 p
  have hlift : PaddedPolynomialCoeffEqv ((R+1)*blocks)
      (liftBoundary ((R-offset)*blocks) (reversePolynomial blocks 0 p))
      (liftBoundary ((R-offset)*blocks) p) :=
    prefix_lift ((R-offset)*blocks) hsupport hp hzero
  exact (PaddedPolynomialCoeffEqv.of_prefix
    (by simpa only [Nat.sub_zero] using hplace)).trans hlift

/-- Exact source pin on the SAME chronological carrier. The support guard
rules out offsets whose information truncated subtraction would erase;
arbitrary loop order and signed multi-time products are retained. -/
theorem source_reverse {width : Nat} (R : Nat) :
    ∀ e : WindowExpression width, Within R e →
      PaddedPolynomialCoeffEqv ((R+1)*(N width))
        (sourcePolynomial (reverse R e))
        (reversePolynomial (N width) R (sourcePolynomial e))
  | .one, _ => (PaddedPolynomialCoeffEqv.of_prefix (reindex_one (sliceReverse (N width) R))).symm
  | .loop offset value spin, he =>
      (reverse_single_slice (N width) R offset he (sourceCharacter width value.edges spin)
        (sourceCharacter_supported width value.edges spin)).symm
  | .add e f, he => by
      change PaddedPolynomialCoeffEqv ((R+1)*(N width))
        (polyAdd (sourcePolynomial (reverse R e)) (sourcePolynomial (reverse R f)))
        (reversePolynomial (N width) R (polyAdd (sourcePolynomial e) (sourcePolynomial f)))
      unfold reversePolynomial
      rw [reindexQuaternionPolynomial_add]
      exact (source_reverse R e he.1).add (source_reverse R f he.2)
  | .mul e f, he => by
      change PaddedPolynomialCoeffEqv ((R+1)*(N width))
        (polyMul (sourcePolynomial (reverse R e)) (sourcePolynomial (reverse R f)))
        (reversePolynomial (N width) R (polyMul (sourcePolynomial e) (sourcePolynomial f)))
      unfold reversePolynomial
      rw [reindexQuaternionPolynomial_mul]
      exact (source_reverse R e he.1).mul (source_reverse R f he.2)
  | .smul c e, he => by
      change PaddedPolynomialCoeffEqv ((R+1)*(N width))
        (polySmul c (sourcePolynomial (reverse R e)))
        (reversePolynomial (N width) R (polySmul c (sourcePolynomial e)))
      unfold reversePolynomial
      rw [reindexQuaternionPolynomial_smul]
      exact (source_reverse R e he).smul c

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSourceReversal

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSourceReversal.source_reverse
