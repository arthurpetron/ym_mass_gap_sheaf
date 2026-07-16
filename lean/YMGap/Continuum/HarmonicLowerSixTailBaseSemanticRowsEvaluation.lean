/-
# Semantic composition of the Base coefficient rows

The closed row certificates are converted here into one evaluation identity.
No coefficient normalization occurs in this module: all expensive equalities
arrive as opaque checked theorems from the certificate modules.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticTotalRows

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.RawGridSemanticTransport

local infix:50 " ≈ " => Q'.eqv

private theorem evalRows_eqv_evalRaw_of_certificate
    (rho : Nat → Q') (raw : RingNormaliser.RawPoly)
    (rows : List RingNormaliser.RawPoly)
    (hbound : rawFirstExponentBound 23 raw = true)
    (hrows : canonRowsRelationChunks 4 6 (bucketRaw 23 raw) rows = true) :
    evalRawRows rho rows ≈ RingNormaliser.evalRaw rho raw := by
  have hbucket := evalRawRows_bucketRaw rho 23 raw hbound
  have hrelation := evalRawRows_eqv_of_canonRowsRelationChunks_true
    rho 4 6 (bucketRaw 23 raw) rows hrows
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrelation) hbucket

private theorem evalRows_piece0 (rho : Nat → Q') :
    evalRawRows rho tailBaseSemanticPiece0Rows ≈
      RingNormaliser.evalRaw rho tailBaseStructuredPiece0Raw :=
  evalRows_eqv_evalRaw_of_certificate rho _ _
    tailBaseStructuredPiece0Raw_bound tailBaseStructuredPiece0Raw_rows

private theorem evalRows_piece1 (rho : Nat → Q') :
    evalRawRows rho tailBaseSemanticPiece1Rows ≈
      RingNormaliser.evalRaw rho tailBaseStructuredPiece1Raw :=
  evalRows_eqv_evalRaw_of_certificate rho _ _
    tailBaseStructuredPiece1Raw_bound tailBaseStructuredPiece1Raw_rows

private theorem evalRows_piece2 (rho : Nat → Q') :
    evalRawRows rho tailBaseSemanticPiece2Rows ≈
      RingNormaliser.evalRaw rho tailBaseStructuredPiece2Raw :=
  evalRows_eqv_evalRaw_of_certificate rho _ _
    tailBaseStructuredPiece2Raw_bound tailBaseStructuredPiece2Raw_rows

private theorem evalRows_piece3 (rho : Nat → Q') :
    evalRawRows rho tailBaseSemanticPiece3Rows ≈
      RingNormaliser.evalRaw rho tailBaseStructuredPiece3Raw :=
  evalRawRows_tailBaseSemanticPiece3Rows rho

private theorem evalRows_piece4 (rho : Nat → Q') :
    evalRawRows rho tailBaseSemanticPiece4Rows ≈
      RingNormaliser.evalRaw rho tailBaseStructuredPiece4Raw :=
  evalRows_eqv_evalRaw_of_certificate rho _ _
    tailBaseStructuredPiece4Raw_bound tailBaseStructuredPiece4Raw_rows

private theorem evalRows_merged_split (rho : Nat → Q') :
    evalRawRows rho tailBaseMergedRows ≈
      evalRawRows rho tailBaseSemanticPiece0Rows +
        (evalRawRows rho tailBaseSemanticPiece1Rows +
          (evalRawRows rho tailBaseSemanticPiece2Rows +
            (evalRawRows rho tailBaseSemanticPiece3Rows +
              evalRawRows rho tailBaseSemanticPiece4Rows))) := by
  have h0 := evalRawRows_appendRawRows rho tailBaseSemanticPiece0Rows
    (appendRawRows tailBaseSemanticPiece1Rows
      (appendRawRows tailBaseSemanticPiece2Rows
        (appendRawRows tailBaseSemanticPiece3Rows
          tailBaseSemanticPiece4Rows)))
  have h1 := evalRawRows_appendRawRows rho tailBaseSemanticPiece1Rows
    (appendRawRows tailBaseSemanticPiece2Rows
      (appendRawRows tailBaseSemanticPiece3Rows tailBaseSemanticPiece4Rows))
  have h2 := evalRawRows_appendRawRows rho tailBaseSemanticPiece2Rows
    (appendRawRows tailBaseSemanticPiece3Rows tailBaseSemanticPiece4Rows)
  have h3 := evalRawRows_appendRawRows rho tailBaseSemanticPiece3Rows
    tailBaseSemanticPiece4Rows
  change
    evalRawRows rho
        (appendRawRows tailBaseSemanticPiece0Rows
          (appendRawRows tailBaseSemanticPiece1Rows
            (appendRawRows tailBaseSemanticPiece2Rows
              (appendRawRows tailBaseSemanticPiece3Rows
                tailBaseSemanticPiece4Rows)))) ≈ _
  exact Q'.eqv_trans _ _ _ h0
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _ h1
        (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ h2
            (Q'.add_eqv_congr_left _ _ _ h3)))))

/-- The frozen sparse Base polynomial evaluates to the right-associated sum
of the five staged structured raw pieces. -/
theorem evalRaw_tailBaseRawPolynomial_structuredRawSum (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseRawPolynomial ≈
      RingNormaliser.evalRaw rho tailBaseStructuredPiece0Raw +
        (RingNormaliser.evalRaw rho tailBaseStructuredPiece1Raw +
          (RingNormaliser.evalRaw rho tailBaseStructuredPiece2Raw +
            (RingNormaliser.evalRaw rho tailBaseStructuredPiece3Raw +
              RingNormaliser.evalRaw rho tailBaseStructuredPiece4Raw))) := by
  have hraw := evalRaw_tailBaseRawPolynomial_rows rho
  have hmerge := Q'.eqv_symm (evalRawRows_tailBaseMerged_total rho)
  have hsplit := evalRows_merged_split rho
  have hpieces := Q'.add_eqv_congr' (evalRows_piece0 rho)
    (Q'.add_eqv_congr' (evalRows_piece1 rho)
      (Q'.add_eqv_congr' (evalRows_piece2 rho)
        (Q'.add_eqv_congr' (evalRows_piece3 rho) (evalRows_piece4 rho))))
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.eqv_trans _ _ _ hmerge
      (Q'.eqv_trans _ _ _ hsplit hpieces))

#print axioms evalRaw_tailBaseRawPolynomial_structuredRawSum

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
