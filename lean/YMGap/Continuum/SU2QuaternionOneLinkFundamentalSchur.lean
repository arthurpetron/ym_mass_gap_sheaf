/-
# One-link oriented fundamental Schur contraction in the quaternion carrier

The rational polynomial carrier is real, whereas the four fundamental
`SU(2)` matrix coefficients are complex.  The scalar-type fence in
`SU2QuaternionPolynomialHaarCarrier` therefore rules out encoding them as
four falsely rational entries.  This leaf uses the honest complexification

    ComplexRatPoly = RatPoly x RatPoly

whose two components are the real and imaginary parts.

For a scalar-first quaternion `q = r + i I + j J + k K`, the convention is

    D(q) = [[r + i sqrt(-1),  j + k sqrt(-1)],
            [-j + k sqrt(-1), r - i sqrt(-1)]].

The reverse-oriented coefficient is defined by conjugate transpose.  Under
the standard quaternion-to-complex-matrix homomorphism it is the matrix
coefficient of `D(q)⁻¹` on the unit-quaternion locus, with the row and column
reversal kept explicit in the definition.  That homomorphism is not claimed
in this leaf.  Direct evaluation by the exact normalized `S^3` moment proves
the fundamental Schur contraction

    integral D_ab(q) conjugate(D_dc(q)) dq
      = (1/2) delta_(a,d) delta_(b,c).

This is the smallest local normalization theorem needed by the elementary
cube comparison.  Twelve such link contractions and eight independent
two-valued vertex-index sums have scalar factor

    2^8 * (1/2)^12 = 1/16.

The final arithmetic identity is recorded here only as normalization
bookkeeping.  It does not claim that the production cube has already been
expanded into exactly those twelve oriented contractions and eight index
sums; that finite trace/wiring comparison remains a separate theorem.

No large face polynomial, density product, or slab enumeration is unfolded
or materialized in this leaf.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.RationalQuaternionRatPoly
import YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier

namespace YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Honest complexification of the real polynomial carrier -/

/-- A complex rational polynomial, stored as its real and imaginary raw
`RatPoly` components. -/
abbrev ComplexRatPoly := RatPoly × RatPoly

/-- A rational complex value, stored as real and imaginary components. -/
abbrev RationalComplex := Q' × Q'

/-- Componentwise rational equivalence of rational complex values. -/
def RationalComplexEqv
    (left right : RationalComplex) : Prop :=
  left.1 ≈ right.1 ∧ left.2 ≈ right.2

/-- Complex conjugation on the honest two-polynomial complexification. -/
def complexRatPolyConj (value : ComplexRatPoly) : ComplexRatPoly :=
  (value.1, polyNeg value.2)

/-- Complex multiplication on pairs of real raw polynomials. -/
def complexRatPolyMul
    (left right : ComplexRatPoly) : ComplexRatPoly :=
  (polyAdd (polyMul left.1 right.1)
      (polyNeg (polyMul left.2 right.2)),
    polyAdd (polyMul left.1 right.2)
      (polyMul left.2 right.1))

/-- Apply the exact finite-product quaternion moment to both scalar
components of one complex polynomial. -/
def finiteProductHaarComplex
    (blockCount : Nat) (value : ComplexRatPoly) : RationalComplex :=
  (finiteProductHaar blockCount value.1,
    finiteProductHaar blockCount value.2)

/-! ## 2. Fundamental matrix coefficients and link orientation -/

/-- The standard fundamental `SU(2)` matrix coefficient of a polynomial
quaternion.  `false` and `true` index the two rows and columns. -/
def fundamentalMatrixCoefficient
    (quaternion : RatPolyQuaternion) : Bool → Bool → ComplexRatPoly
  | false, false => (quaternion.r, quaternion.i)
  | false, true => (quaternion.j, quaternion.k)
  | true, false => (polyNeg quaternion.j, quaternion.k)
  | true, true => (quaternion.r, polyNeg quaternion.i)

/-- The coordinate quaternion carried by one base-four link block. -/
def fundamentalLinkQuaternion (block : Nat) : RatPolyQuaternion :=
  variablesAt (4 * block)

/-- A forward-oriented fundamental matrix coefficient on one link block. -/
def forwardFundamentalCoefficient
    (block : Nat) (row column : Bool) : ComplexRatPoly :=
  fundamentalMatrixCoefficient (fundamentalLinkQuaternion block) row column

/-- A reverse-oriented coefficient.  The transpose of the indices and
complex conjugation are both explicit.  The later matrix/quaternion semantic
bridge must identify it with the `(row,column)` entry of the inverse
fundamental matrix on the unit-quaternion locus. -/
def reverseFundamentalCoefficient
    (block : Nat) (row column : Bool) : ComplexRatPoly :=
  complexRatPolyConj
    (forwardFundamentalCoefficient block column row)

/-- The exact oriented Schur delta: row/column indices cross at an oppositely
oriented link and the surviving coefficient is `1 / dim(fund) = 1/2`. -/
def orientedFundamentalSchurDelta
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    RationalComplex :=
  if forwardRow = reverseColumn ∧ forwardColumn = reverseRow then
    (Q'.invSucc 1, 0)
  else
    (0, 0)

/-! ## 3. Exact one-link Schur contraction -/

/-- **Constructive one-link fundamental Schur orthogonality.**  In the exact
one-block quaternion sphere-moment carrier, a forward matrix coefficient
contracted with a reverse-oriented one is `1/2` precisely when the two index
strands cross, and is zero otherwise. -/
theorem oneLink_oriented_fundamental_schur
    (forwardRow forwardColumn reverseRow reverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (complexRatPolyMul
          (forwardFundamentalCoefficient 0 forwardRow forwardColumn)
          (reverseFundamentalCoefficient 0 reverseRow reverseColumn)))
      (orientedFundamentalSchurDelta
        forwardRow forwardColumn reverseRow reverseColumn) := by
  cases forwardRow <;> cases forwardColumn <;>
    cases reverseRow <;> cases reverseColumn <;>
      constructor <;> decide

/-! ## 4. Elementary-cube normalization bookkeeping -/

/-- The scalar supplied by eight independent fundamental vertex-index sums
and twelve one-link Schur contractions.  This is not yet the theorem that the
production cube expansion has exactly that wiring. -/
def elementaryCubeEulerSchurFactor : Q' :=
  qpow (Q'.ofNat 2) 8 * qpow (Q'.invSucc 1) 12

/-- Exact arithmetic target for the closed elementary cube. -/
theorem elementaryCubeEulerSchurFactor_exact :
    elementaryCubeEulerSchurFactor ≈ Q'.mkPos 1 16 (by decide) := by
  decide

#print axioms oneLink_oriented_fundamental_schur
#print axioms elementaryCubeEulerSchurFactor_exact

end YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
