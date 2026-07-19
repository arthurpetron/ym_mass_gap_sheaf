/-
# Arbitrary-polynomial positivity for finite quaternion products

This leaf composes the two dimension-uniform constructive reductions:

* radius homogenization proves square positivity for every polynomial in one
  fixed lazy coordinate-parity sector;
* parity-sector/complement recursion removes the fixed-parity hypothesis
  without enumerating parity assignments.

The result is the headline finite-dimensional algebraic theorem: for every
finite number of quaternion blocks, the exact rational product-sphere moment
functional is nonnegative on the raw square of every polynomial whose
exponent lists are structurally supported in those blocks.

Scope is intentionally precise.  `finiteProductHaar` is the exact rational
product of normalized `S^3` moment formulas.  This theorem does not by itself
identify that functional with abstract group Haar, prove reflection
positivity for the full lazy Wilson density, take a continuum limit, or prove
a Yang--Mills mass gap.  It supplies the finite polynomial positivity input
for those later bridges.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialParityClosure
import YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization

namespace YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarMultihomogeneousPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductHaarParityHomogenization
open YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialParityClosure

/-- The arbitrary-block parity-homogenization theorem discharges exactly the
fixed-parity premise required by the lazy sector/complement closure. -/
theorem finiteProductHaar_fixedParitySquarePositive
    (blockCount : Nat) : FixedParitySquarePositive blockCount := by
  intro parity polynomial hsupport hparity
  exact finiteProductHaar_square_nonneg_of_parity
    blockCount parity polynomial hsupport hparity

/-- **Arbitrary supported-block polynomial-square positivity.**  For every
finite product of exact quaternion sphere moments and every raw rational
polynomial supported on its scalar coordinates, the moment of the literal
raw square is nonnegative. -/
theorem finiteProductHaar_square_nonneg
    (blockCount : Nat) (polynomial : RatPoly)
    (hsupport : SupportedQuaternionBlocks blockCount polynomial) :
    (0 : Q') ≤
      finiteProductHaar blockCount
        (polyMul polynomial polynomial) := by
  exact finiteProductHaar_square_nonneg_of_fixedParity
    blockCount
    (finiteProductHaar_fixedParitySquarePositive blockCount)
    polynomial hsupport

#print axioms finiteProductHaar_fixedParitySquarePositive
#print axioms finiteProductHaar_square_nonneg

end YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
