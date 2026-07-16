/-
# Semantic bridge for the lower-six high-branch Base certificate

The frozen Bernstein certificate evaluates a dense integer polynomial.  This
module identifies that polynomial with `178605` times the common-denominator
clearing of the production expression `lowerSixTailEnvelopeBase`.

The identity is checked at raw-coefficient level.  In particular, it does not
ask the normalizer to expand the 691-term dense polynomial as a nested syntax
tree, the route which exceeds the default native stack.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseRaw
import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
import YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificateData
import YMGap.Continuum.RawGridSemanticTransport
import YMGap.Continuum.TensorBernsteinHomogeneousCertificate

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificate
open YMGap.Continuum.HarmonicLowerSixTailBaseCoefficientCertificate
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.HarmonicLowerSixTailSlopeFloorCertificateData
open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.TensorBernsteinHomogeneousCertificate
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr
private abbrev RP := RingNormaliser.RawPoly

/-! ## Integer factorization of `178605 * BASE_FULL_NUM` -/

private def pN : PE := .var 0
private def pD : PE := .var 1
private def pOne : PE := .const 1
private def pDp : PE := .add pD pOne
private def pR : PE := .add (.pow pD 2) (.const (-1))
private def pN2 : PE := .pow pN 2

private def pJ : PE :=
  .add
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add
                  (.add
                    (.mul (.const 192) (.mul pN (.pow pD 4)))
                    (.mul (.const 384) (.mul (.pow pN 3) (.pow pD 3))))
                  (.neg (.mul (.const 6) (.mul pN (.pow pD 3)))))
                (.neg (.mul (.const 384) (.mul (.pow pN 5) (.pow pD 2)))))
              (.mul (.const 576) (.mul (.pow pN 4) (.pow pD 2))))
            (.mul (.const 184) (.mul (.pow pN 3) (.pow pD 2))))
          (.mul (.const 224) (.mul (.pow pN 5) pD)))
        (.neg (.mul (.const 256) (.pow pN 7))))
      (.mul (.const 576) (.pow pN 6)))
    (.mul (.const 3) (.pow pD 3))

private def pP : PE :=
  .add
    (.add
      (.add
        (.add
          (.neg (.mul (.const 15750) (.mul pN (.pow pD 4))))
          (.neg (.mul (.const 45560) (.mul (.pow pN 3) (.pow pD 3)))))
        (.mul (.const 10976) (.mul (.pow pN 5) (.pow pD 2))))
      (.neg (.mul (.const 30848) (.mul (.pow pN 7) pD))))
    (.neg (.mul (.const 4608) (.pow pN 9)))

private def pBasePoly : PE :=
  .add
    (.add (.neg pP) (.mul (.const 15630) (.pow pD 4)))
    (.mul (.const 60)
      (.mul (.pow pD 2)
        (.add pJ (.neg (.mul (.const 6) (.pow pD 3))))))

private def pTwoF : PE :=
  let H : PE := .add (.mul (.const 2) pR) pOne
  .add
    (.add
      (.mul (.const 2) (.pow pR 4))
      (.mul (.const 2)
        (.mul pN2 (.mul H (.pow pR 2)))))
    (.mul (.mul pN2 (.add pN2 (.const (-1)))) (.pow H 2))

private def pL1ClearedTerms : List (Nat × Nat × Int) :=
  lowerSixTailNextSlopeFloorClearedTerms.map
    (fun (dExponent, nExponent, coefficient) =>
      (nExponent, dExponent, coefficient))

private def pL1Cleared : PE :=
  bivariatePowerExpr pL1ClearedTerms

/-- The minimal integer clearing `22680 * U0NUM`.  Triples use the local
variable order `(N exponent, D exponent, coefficient)`. -/
private def tailBaseU0MinimalTerms : List (Nat × Nat × Int) := [
  (10, 0, 32),
  (9, 1, -144), (9, 0, -400),
  (8, 2, 576), (8, 1, 1296), (8, 0, 1920),
  (7, 3, -2016), (7, 2, -3456), (7, 1, -4104), (7, 0, -4200),
  (6, 4, 6048), (6, 3, 7056), (6, 2, 6048), (6, 1, 4536),
    (6, 0, 3066),
  (5, 5, -15120), (5, 4, -9072), (5, 3, -3528), (5, 1, 2079),
    (5, 0, 3255),
  (4, 6, 30240), (4, 4, -7560), (4, 3, -8820), (4, 2, -8316),
    (4, 1, -7371), (4, 0, -6395),
  (3, 7, -45360), (3, 6, 30240), (3, 5, 18900), (3, 4, 11340),
    (3, 3, 7056), (3, 2, 4536), (3, 1, 2979), (3, 0, 1975),
  (2, 8, 45360), (2, 7, -68040), (2, 6, -7560), (2, 4, 1512),
    (2, 3, 1764), (2, 2, 1692), (2, 1, 1539), (2, 0, 1377),
  (1, 8, 68040), (1, 7, -22680), (1, 6, -7560), (1, 5, -3780),
    (1, 4, -2268), (1, 3, -1512), (1, 2, -1080), (1, 1, -810),
    (1, 0, -630),
  (0, 9, -22680), (0, 8, 22680)
]

private def pU0Cleared : PE :=
  bivariatePowerExpr tailBaseU0MinimalTerms

private def pDen : PE :=
  .mul (.pow pD 18) (.mul (.pow pR 4) (.pow pDp 15))

/-- Five integer pieces.  The coefficients `162`, `257191200`, `4`, and
`514382400` incorporate the exact minimal clearings
`2520 * L1NUM`, `22680 * U0NUM`, and `2 * FNUM`.  Keeping the pieces named
lets the closed coefficient audit reduce them independently. -/
private def tailBaseStructuredPiece0 : PE :=
  .mul (.const 178605) (.mul pBasePoly pDen)

private def tailBaseStructuredPiece1 : PE :=
  .mul (.const 162)
    (.mul (.pow pD 18)
      (.mul pTwoF (.mul (.pow pL1Cleared 2) (.pow pD 6))))

private def tailBaseStructuredPiece2 : PE :=
  .neg
    (.mul (.const 257191200)
      (.mul (.pow pD 18)
        (.mul pTwoF
          (.mul pN2
            (.mul
              (.add (.mul (.const 12) (.pow pDp 2)) pOne)
              (.mul (.pow pDp 13) (.pow pD 6)))))))

private def tailBaseStructuredPiece3 : PE :=
  .neg
    (.mul (.const 4)
      (.mul pD
        (.mul (.pow pR 4)
          (.mul (.pow pDp 15)
            (.mul (.pow pU0Cleared 2) (.pow pD 6))))))

private def tailBaseStructuredPiece4 : PE :=
  .mul (.const 514382400)
    (.mul pD
      (.mul (.pow pR 4)
        (.mul (.pow pDp 15)
          (.mul pN2
            (.mul
              (.add (.mul (.const 12) (.pow pD 2)) pOne)
              (.mul (.pow pD 15) (.pow pD 6)))))))

private def tailBaseStructuredExpr : PE :=
  .add tailBaseStructuredPiece0
    (.add tailBaseStructuredPiece1
      (.add tailBaseStructuredPiece2
        (.add tailBaseStructuredPiece3 tailBaseStructuredPiece4)))

/-! ## Staged raw factors

The two square pieces are deliberately assembled from already-canonical
atomic factors.  This keeps every canonicalization polynomial in the actual
sparse support size; normalizing either composite syntax tree directly makes
the normalizer revisit the same large square expansion. -/

private def tailBasePiece0Raw : RP :=
  fastNormalize tailBaseStructuredPiece0

private def tailBaseL1Raw : RP :=
  bivariateTermsRaw pL1ClearedTerms

private def tailBaseL1SquareRaw : RP :=
  RingNormaliser.canon
    (RingNormaliser.rawMul tailBaseL1Raw tailBaseL1Raw)

private def tailBaseTwoFRaw : RP :=
  fastNormalize pTwoF

private def tailBaseTwoFL1SquareRaw : RP :=
  RingNormaliser.canon
    (RingNormaliser.rawMul tailBaseTwoFRaw tailBaseL1SquareRaw)

private def tailBasePiece1Raw : RP :=
  RingNormaliser.scaleTerm [0, 24] 162 tailBaseTwoFL1SquareRaw

private def tailBasePiece2Raw : RP :=
  fastNormalize tailBaseStructuredPiece2

private def tailBaseU0Raw : RP :=
  bivariateTermsRaw tailBaseU0MinimalTerms

private def tailBaseU0SquareRaw : RP :=
  RingNormaliser.canon
    (RingNormaliser.rawMul tailBaseU0Raw tailBaseU0Raw)

private def tailBaseR4Raw : RP :=
  fastNormalize (.pow pR 4)

private def tailBaseU0SquareR4Raw : RP :=
  RingNormaliser.canon
    (RingNormaliser.rawMul tailBaseR4Raw tailBaseU0SquareRaw)

private def tailBaseDp15Raw : RP :=
  fastNormalize (.pow pDp 15)

private def tailBaseU0SquareCommonRaw : RP :=
  RingNormaliser.canon
    (RingNormaliser.rawMul tailBaseDp15Raw tailBaseU0SquareR4Raw)

private def tailBasePiece3Raw : RP :=
  RingNormaliser.scaleTerm [0, 7] (-4) tailBaseU0SquareCommonRaw

private def tailBasePiece4Raw : RP :=
  fastNormalize tailBaseStructuredPiece4

private def tailBaseMergedSemanticRows : List RP :=
  appendRawRows tailBaseSemanticPiece0Rows
    (appendRawRows tailBaseSemanticPiece1Rows
      (appendRawRows tailBaseSemanticPiece2Rows
        (appendRawRows tailBaseSemanticPiece3Rows
          tailBaseSemanticPiece4Rows)))

def tailBaseRawRows : List RP :=
  tailBaseSemanticTotalRows

private theorem tailBasePiece0Raw_first_bound :
    rawFirstExponentBound 23 tailBasePiece0Raw = true := by
  rfl

private theorem tailBasePiece0Raw_rows_relation :
    canonRowsRelationChunks 4 6 (bucketRaw 23 tailBasePiece0Raw)
      tailBaseSemanticPiece0Rows = true := by
  rfl

private theorem tailBasePiece1Raw_first_bound :
    rawFirstExponentBound 23 tailBasePiece1Raw = true := by
  rfl

private theorem tailBasePiece1Raw_rows_relation :
    canonRowsRelationChunks 4 6 (bucketRaw 23 tailBasePiece1Raw)
      tailBaseSemanticPiece1Rows = true := by
  rfl

/-! ## Public staged interface

The expensive piece-1 coefficient reconciliation above is intentionally
sealed in this module.  Downstream semantic composition can therefore reuse
its checked theorem without asking the kernel to recompute the 52-by-52
slope-square convolution. -/

def tailBaseL1ClearedTermData : List (Nat × Nat × Int) :=
  pL1ClearedTerms

def tailBaseNExpr : PE :=
  pN

def tailBaseDExpr : PE :=
  pD

def tailBaseDpExpr : PE :=
  pDp

def tailBaseRExpr : PE :=
  pR

def tailBaseN2Expr : PE :=
  pN2

def tailBaseCoreExpr : PE :=
  pBasePoly

def tailBaseL1ClearedExpr : PE :=
  pL1Cleared

def tailBaseTwoFExpr : PE :=
  pTwoF

def tailBaseU0MinimalTermData : List (Nat × Nat × Int) :=
  tailBaseU0MinimalTerms

def tailBaseU0ClearedExpr : PE :=
  pU0Cleared

def tailBaseDenExpr : PE :=
  pDen

def tailBaseStructuredPiece0Expr : PE :=
  tailBaseStructuredPiece0

def tailBaseStructuredPiece1Expr : PE :=
  tailBaseStructuredPiece1

def tailBaseStructuredPiece2Expr : PE :=
  tailBaseStructuredPiece2

def tailBaseStructuredPiece3Expr : PE :=
  tailBaseStructuredPiece3

def tailBaseStructuredPiece4Expr : PE :=
  tailBaseStructuredPiece4

def tailBaseStructuredExpression : PE :=
  tailBaseStructuredExpr

def tailBaseStructuredPiece0Raw : RP :=
  tailBasePiece0Raw

def tailBaseL1RawPolynomial : RP :=
  tailBaseL1Raw

def tailBaseL1SquareRawPolynomial : RP :=
  tailBaseL1SquareRaw

def tailBaseTwoFRawPolynomial : RP :=
  tailBaseTwoFRaw

def tailBaseTwoFL1SquareRawPolynomial : RP :=
  tailBaseTwoFL1SquareRaw

def tailBaseStructuredPiece1Raw : RP :=
  tailBasePiece1Raw

def tailBaseStructuredPiece2Raw : RP :=
  tailBasePiece2Raw

def tailBaseU0RawPolynomial : RP :=
  tailBaseU0Raw

def tailBaseU0SquareRawPolynomial : RP :=
  tailBaseU0SquareRaw

def tailBaseR4RawPolynomial : RP :=
  tailBaseR4Raw

def tailBaseU0SquareR4RawPolynomial : RP :=
  tailBaseU0SquareR4Raw

def tailBaseDp15RawPolynomial : RP :=
  tailBaseDp15Raw

def tailBaseU0SquareCommonRawPolynomial : RP :=
  tailBaseU0SquareCommonRaw

def tailBaseStructuredPiece3Raw : RP :=
  tailBasePiece3Raw

def tailBaseStructuredPiece4Raw : RP :=
  tailBasePiece4Raw

def tailBaseMergedRows : List RP :=
  tailBaseMergedSemanticRows

theorem tailBaseStructuredPiece0Raw_bound :
    rawFirstExponentBound 23 tailBaseStructuredPiece0Raw = true :=
  tailBasePiece0Raw_first_bound

theorem tailBaseStructuredPiece0Raw_rows :
    canonRowsRelationChunks 4 6
      (bucketRaw 23 tailBaseStructuredPiece0Raw)
      tailBaseSemanticPiece0Rows = true :=
  tailBasePiece0Raw_rows_relation

theorem tailBaseStructuredPiece1Raw_bound :
    rawFirstExponentBound 23 tailBaseStructuredPiece1Raw = true :=
  tailBasePiece1Raw_first_bound

theorem tailBaseStructuredPiece1Raw_rows :
    canonRowsRelationChunks 4 6
      (bucketRaw 23 tailBaseStructuredPiece1Raw)
      tailBaseSemanticPiece1Rows = true :=
  tailBasePiece1Raw_rows_relation

#print axioms tailBaseStructuredPiece0Raw_rows
#print axioms tailBaseStructuredPiece1Raw_rows

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
