/-
# Total-row reconciliation for the frozen Base polynomial

This module performs the two final coefficient-level checks:

* the public sparse polynomial from the frozen Bernstein certificate has the
  generated 23 N-exponent rows; and
* those total rows are the rowwise sum of the five structured pieces.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticDirectRows
import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticU0Rows

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.RawGridSemanticTransport

local infix:50 " ≈ " => Q'.eqv

theorem tailBaseRawPolynomial_bound :
    rawFirstExponentBound 23 tailBaseRawPolynomial = true := by
  rfl

theorem tailBaseRawPolynomial_rows :
    canonRowsRelationChunks 4 6
      (bucketRaw 23 tailBaseRawPolynomial) tailBaseRawRows = true := by
  rfl

theorem tailBaseMergedRows_total_rows :
    canonRowsRelationChunks 4 6 tailBaseMergedRows tailBaseRawRows = true := by
  rfl

theorem evalRaw_tailBaseRawPolynomial_rows (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseRawPolynomial ≈
      evalRawRows rho tailBaseRawRows := by
  have hbucket := evalRawRows_bucketRaw rho 23 tailBaseRawPolynomial
    tailBaseRawPolynomial_bound
  have hrows := evalRawRows_eqv_of_canonRowsRelationChunks_true rho 4 6
    (bucketRaw 23 tailBaseRawPolynomial) tailBaseRawRows
    tailBaseRawPolynomial_rows
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hbucket) hrows

theorem evalRawRows_tailBaseMerged_total (rho : Nat → Q') :
    evalRawRows rho tailBaseMergedRows ≈ evalRawRows rho tailBaseRawRows :=
  evalRawRows_eqv_of_canonRowsRelationChunks_true rho 4 6
    tailBaseMergedRows tailBaseRawRows tailBaseMergedRows_total_rows

#print axioms tailBaseRawPolynomial_rows
#print axioms tailBaseMergedRows_total_rows
#print axioms evalRaw_tailBaseRawPolynomial_rows

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
