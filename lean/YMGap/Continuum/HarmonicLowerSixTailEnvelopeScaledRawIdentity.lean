/-
# Production scaled raw identities for the lower-six E8/E9 envelopes

Each of the 28 mode rows is checked in an independent module.  This file
assembles those closed Boolean checks through the axiom-clean pointwise row
transport theorem; it performs no coefficient normalization itself.
-/

import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawSemantics
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Slice0
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row1
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row2
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row3
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row4
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row5
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row6
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row7
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row8
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row9
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row10
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row11
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row12
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row13
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row14
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row15
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row16
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row17
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row18
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row19
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row20
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row21
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row22
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row23
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row24
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row25
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row26
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row27
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row0
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row1
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row2
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row3
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row4
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row5
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row6
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row7
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row8
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row9
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row10
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row11
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row12
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row13
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row14
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row15
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row16
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row17
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row18
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row19
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row20
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row21
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row22
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row23
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row24
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row25
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row26
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row27

namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentity

open YMGap.Constructive
open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.RawGridRowConvolution
open YMGap.Continuum.QuadraticRawGridSemanticTransport
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawSemantics
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeRawScaling
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeTaylorRaw
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Slice0
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row1
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row2
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row3
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row4
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row5
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row6
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row7
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row8
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row9
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row10
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row11
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row12
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row13
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row14
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row15
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row16
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row17
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row18
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row19
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row20
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row21
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row22
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row23
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row24
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row25
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row26
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE8Row27
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row0
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row1
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row2
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row3
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row4
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row5
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row6
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row7
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row8
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row9
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row10
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row11
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row12
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row13
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row14
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row15
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row16
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row17
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row18
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row19
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row20
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row21
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row22
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row23
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row24
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row25
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row26
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentityE9Row27

local infix:50 " ≈ " => Q'.eqv

theorem tailEnvelopeE8ScaledRaw_allRows :
    allRowOffsets 28 (fun index =>
      decide
        (RingNormaliser.canon
            (rawRowAt tailEnvelopeE8ScaledRawRows index) =
          RingNormaliser.canon
            (rawRowAt tailEnvelopeE8StructuredRawRows index))) = true := by
  simp only [allRowOffsets,
    tailEnvelopeE8ScaledRaw_row0, tailEnvelopeE8ScaledRaw_row1, tailEnvelopeE8ScaledRaw_row2, tailEnvelopeE8ScaledRaw_row3,
    tailEnvelopeE8ScaledRaw_row4, tailEnvelopeE8ScaledRaw_row5, tailEnvelopeE8ScaledRaw_row6, tailEnvelopeE8ScaledRaw_row7,
    tailEnvelopeE8ScaledRaw_row8, tailEnvelopeE8ScaledRaw_row9, tailEnvelopeE8ScaledRaw_row10, tailEnvelopeE8ScaledRaw_row11,
    tailEnvelopeE8ScaledRaw_row12, tailEnvelopeE8ScaledRaw_row13, tailEnvelopeE8ScaledRaw_row14, tailEnvelopeE8ScaledRaw_row15,
    tailEnvelopeE8ScaledRaw_row16, tailEnvelopeE8ScaledRaw_row17, tailEnvelopeE8ScaledRaw_row18, tailEnvelopeE8ScaledRaw_row19,
    tailEnvelopeE8ScaledRaw_row20, tailEnvelopeE8ScaledRaw_row21, tailEnvelopeE8ScaledRaw_row22, tailEnvelopeE8ScaledRaw_row23,
    tailEnvelopeE8ScaledRaw_row24, tailEnvelopeE8ScaledRaw_row25, tailEnvelopeE8ScaledRaw_row26, tailEnvelopeE8ScaledRaw_row27,
    Bool.and_self]

theorem evalRawRows_tailEnvelopeE8ScaledRaw_identity (rho : Nat → Q') :
    evalRawRows rho tailEnvelopeE8ScaledRawRows ≈
      evalRawRows rho tailEnvelopeE8StructuredRawRows := by
  exact evalRawRows_eqv_of_allRowOffsets rho 28
    tailEnvelopeE8ScaledRawRows tailEnvelopeE8StructuredRawRows
    tailEnvelopeE8ScaledRawRows_length
    tailEnvelopeE8StructuredRawRows_length
    tailEnvelopeE8ScaledRaw_allRows

theorem tailEnvelopeE9ScaledRaw_allRows :
    allRowOffsets 28 (fun index =>
      decide
        (RingNormaliser.canon
            (rawRowAt tailEnvelopeE9ScaledRawRows index) =
          RingNormaliser.canon
            (rawRowAt tailEnvelopeE9StructuredRawRows index))) = true := by
  simp only [allRowOffsets,
    tailEnvelopeE9ScaledRaw_row0, tailEnvelopeE9ScaledRaw_row1, tailEnvelopeE9ScaledRaw_row2, tailEnvelopeE9ScaledRaw_row3,
    tailEnvelopeE9ScaledRaw_row4, tailEnvelopeE9ScaledRaw_row5, tailEnvelopeE9ScaledRaw_row6, tailEnvelopeE9ScaledRaw_row7,
    tailEnvelopeE9ScaledRaw_row8, tailEnvelopeE9ScaledRaw_row9, tailEnvelopeE9ScaledRaw_row10, tailEnvelopeE9ScaledRaw_row11,
    tailEnvelopeE9ScaledRaw_row12, tailEnvelopeE9ScaledRaw_row13, tailEnvelopeE9ScaledRaw_row14, tailEnvelopeE9ScaledRaw_row15,
    tailEnvelopeE9ScaledRaw_row16, tailEnvelopeE9ScaledRaw_row17, tailEnvelopeE9ScaledRaw_row18, tailEnvelopeE9ScaledRaw_row19,
    tailEnvelopeE9ScaledRaw_row20, tailEnvelopeE9ScaledRaw_row21, tailEnvelopeE9ScaledRaw_row22, tailEnvelopeE9ScaledRaw_row23,
    tailEnvelopeE9ScaledRaw_row24, tailEnvelopeE9ScaledRaw_row25, tailEnvelopeE9ScaledRaw_row26, tailEnvelopeE9ScaledRaw_row27,
    Bool.and_self]

theorem evalRawRows_tailEnvelopeE9ScaledRaw_identity (rho : Nat → Q') :
    evalRawRows rho tailEnvelopeE9ScaledRawRows ≈
      evalRawRows rho tailEnvelopeE9StructuredRawRows := by
  exact evalRawRows_eqv_of_allRowOffsets rho 28
    tailEnvelopeE9ScaledRawRows tailEnvelopeE9StructuredRawRows
    tailEnvelopeE9ScaledRawRows_length
    tailEnvelopeE9StructuredRawRows_length
    tailEnvelopeE9ScaledRaw_allRows

theorem tailEnvelopeE8ScaledRaw_production_identity (D n : Q') :
    tailEnvelopeE8ClearedEval D n * Q'.ofInt 4608 ≈
      RingNormaliser.evalRaw (quadraticRawRho D n)
          tailEnvelopeTaylor8RawPolynomial +
        Q'.ofInt 737280 *
          evalRawRows (quadraticRawRho D n) tailBaseSemanticTotalRows := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (evalRawRows_tailEnvelopeE8ScaledRawRows D n))
    (Q'.eqv_trans _ _ _
      (evalRawRows_tailEnvelopeE8ScaledRaw_identity
        (quadraticRawRho D n))
      (evalRawRows_tailEnvelopeE8StructuredRawRows
        (quadraticRawRho D n)))

theorem tailEnvelopeE9ScaledRaw_production_identity (D n : Q') :
    tailEnvelopeE9ClearedEval D n * Q'.ofInt 512 ≈
      RingNormaliser.evalRaw (quadraticRawRho D n)
          tailEnvelopeTaylor9RawPolynomial +
        Q'.ofInt 737280 *
          evalRawRows (quadraticRawRho D n) tailBaseSemanticTotalRows := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (evalRawRows_tailEnvelopeE9ScaledRawRows D n))
    (Q'.eqv_trans _ _ _
      (evalRawRows_tailEnvelopeE9ScaledRaw_identity
        (quadraticRawRho D n))
      (evalRawRows_tailEnvelopeE9StructuredRawRows
        (quadraticRawRho D n)))

#print axioms tailEnvelopeE8ScaledRaw_allRows
#print axioms tailEnvelopeE9ScaledRaw_allRows
#print axioms evalRawRows_tailEnvelopeE8ScaledRaw_identity
#print axioms evalRawRows_tailEnvelopeE9ScaledRaw_identity
#print axioms tailEnvelopeE8ScaledRaw_production_identity
#print axioms tailEnvelopeE9ScaledRaw_production_identity

end YMGap.Continuum.HarmonicLowerSixTailEnvelopeScaledRawIdentity
