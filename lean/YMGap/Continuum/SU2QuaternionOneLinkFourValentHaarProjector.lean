/-
# One-link signed four-valent Haar projector in the fundamental representation

At a link carrying two forward and two reverse fundamental coefficients, the
normalized quaternion Haar integral is not the scalar cardinality two. It is
the rank-two invariant projector. In the direct/crossed pairing basis the
pairing Gram matrix and its inverse are

    G      = [[4, 2], [2, 4]],
    G^{-1} = [[1/3, -1/6], [-1/6, 1/3]].

This leaf derives that signed kernel entrywise from the exact normalized `S^3`
moment carrier. It also traces the four diagonal matrix indices and recovers
the scalar value two. Thus the old link multiplicity is the closed trace of
the projector, not an entrywise replacement for it.

Only eight individual Boolean indices and one safe four-binder diagonal trace
occur. No double-cube face network, global assignment space, bounded labelling
family, or trajectory is unfolded or materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexFourBoolFubini

namespace YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionComplexBoolSumAlgebra
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two invariant pairings and their Gram matrix -/

/-- Exact Boolean Kronecker delta in the rational carrier. -/
def boolKronecker (left right : Bool) : Q' :=
  if left = right then 1 else 0

/-- The direct invariant pairing of two forward and two conjugate indices. -/
def directOrientedPairing
    (first second firstConjugate secondConjugate : Bool) : Q' :=
  boolKronecker first firstConjugate *
    boolKronecker second secondConjugate

/-- The crossed invariant pairing of the same four indices. -/
def crossedOrientedPairing
    (first second firstConjugate secondConjugate : Bool) : Q' :=
  boolKronecker first secondConjugate *
    boolKronecker second firstConjugate

/-- A bounded scalar Boolean binder. -/
def rationalBoolSum (family : Bool → Q') : Q' :=
  family false + family true

/-- Four nested bounded scalar binders. -/
def rationalFourBoolSum
    (family : Bool → Bool → Bool → Bool → Q') : Q' :=
  rationalBoolSum (fun first =>
    rationalBoolSum (fun second =>
      rationalBoolSum (fun third =>
        rationalBoolSum (fun fourth =>
          family first second third fourth))))

/-- Exact finite inner product of two four-index pairing tensors. -/
def orientedPairingInner
    (left right : Bool → Bool → Bool → Bool → Q') : Q' :=
  rationalFourBoolSum (fun first second firstConjugate secondConjugate =>
    left first second firstConjugate secondConjugate *
      right first second firstConjugate secondConjugate)

/-- The direct/crossed pairing basis has Gram matrix `[[4,2],[2,4]]`. -/
theorem direct_crossed_oriented_pairing_gram_exact :
    orientedPairingInner directOrientedPairing directOrientedPairing ≈ 4 ∧
    orientedPairingInner directOrientedPairing crossedOrientedPairing ≈ 2 ∧
    orientedPairingInner crossedOrientedPairing directOrientedPairing ≈ 2 ∧
    orientedPairingInner crossedOrientedPairing crossedOrientedPairing ≈ 4 := by
  unfold orientedPairingInner rationalFourBoolSum rationalBoolSum
    directOrientedPairing crossedOrientedPairing boolKronecker
  decide

/-! ## 2. The signed inverse-Gram projector -/

/-- The two positive diagonal entries of the inverse pairing Gram matrix. -/
def oneThird : Q' := Q'.mkPos 1 3 (by decide)

/-- The absolute value of the two negative mixed inverse-Gram entries. -/
def oneSixth : Q' := Q'.mkPos 1 6 (by decide)

/-- Scalar entry of the normalized two-forward/two-reverse Haar projector.

The reverse coefficient `reverseFundamentalCoefficient e f` is
`conj(U_f e)`, so the forward row indices pair with the *external reverse
columns*, while the forward columns pair with the external reverse rows. -/
def orientedFourFundamentalHaarProjectorScalar
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) : Q' :=
  let rowDirect := directOrientedPairing
    firstForwardRow secondForwardRow
    firstReverseColumn secondReverseColumn
  let rowCrossed := crossedOrientedPairing
    firstForwardRow secondForwardRow
    firstReverseColumn secondReverseColumn
  let columnDirect := directOrientedPairing
    firstForwardColumn secondForwardColumn
    firstReverseRow secondReverseRow
  let columnCrossed := crossedOrientedPairing
    firstForwardColumn secondForwardColumn
    firstReverseRow secondReverseRow
  (oneThird * (rowDirect * columnDirect) +
      (-oneSixth) * (rowDirect * columnCrossed)) +
    ((-oneSixth) * (rowCrossed * columnDirect) +
      oneThird * (rowCrossed * columnCrossed))

/-- Rational-complex form of the signed projector entry. -/
def orientedFourFundamentalHaarProjector
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) : RationalComplex :=
  (orientedFourFundamentalHaarProjectorScalar
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn, 0)

/-- The literal left-associated four-coefficient word at one link block. -/
def twoForwardTwoReverseFundamentalTerm
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) : ComplexRatPoly :=
  complexRatPolyMulFourLeft
    (forwardFundamentalCoefficient block
      firstForwardRow firstForwardColumn)
    (forwardFundamentalCoefficient block
      secondForwardRow secondForwardColumn)
    (reverseFundamentalCoefficient block
      firstReverseRow firstReverseColumn)
    (reverseFundamentalCoefficient block
      secondReverseRow secondReverseColumn)

/-- **Exact balanced fundamental fourth moment.** The normalized one-block
quaternion Haar integral is the signed rank-two invariant projector with
inverse Gram entries `1/3,-1/6,-1/6,1/3`. -/
theorem oneLink_twoForward_twoReverse_fundamental_projector
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (twoForwardTwoReverseFundamentalTerm 0
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn))
      (orientedFourFundamentalHaarProjector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn) := by
  cases firstForwardRow <;> cases firstForwardColumn <;>
    cases secondForwardRow <;> cases secondForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    constructor <;> decide

/-- A concrete negative mixed projector entry. This sign is invisible after
replacing the projector by its scalar trace or by squared Racah weights. -/
theorem oneLink_twoForward_twoReverse_negative_mixed_entry :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (twoForwardTwoReverseFundamentalTerm 0
          false false true true
          true false false true))
      (-oneSixth, 0) := by
  refine rationalComplexEqv_trans
    (oneLink_twoForward_twoReverse_fundamental_projector
      false false true true true false false true) ?_
  constructor <;> decide

/-- A positive diagonal projector entry. Together with the negative mixed
entry this prevents the closed scalar trace from hiding an index transpose or
an accidental replacement by unsigned Racah probabilities. -/
theorem oneLink_twoForward_twoReverse_positive_diagonal_entry :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (twoForwardTwoReverseFundamentalTerm 0
          false false false false
          false false false false))
      (oneThird, 0) := by
  refine rationalComplexEqv_trans
    (oneLink_twoForward_twoReverse_fundamental_projector
      false false false false false false false false) ?_
  constructor <;> decide

/-! ## 3. Closed four-character trace recovers scalar multiplicity two -/

/-- Finite-product Haar commutes with exactly four leading Boolean binders. -/
theorem finiteProductHaarComplex_fourBoolSum
    (blockCount : Nat)
    (family : Bool → Bool → Bool → Bool → ComplexRatPoly) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyFourBoolSum family))
      (rationalComplexFourBoolSum (fun first second third fourth =>
        finiteProductHaarComplex blockCount
          (family first second third fourth))) := by
  unfold complexRatPolyFourBoolSum rationalComplexFourBoolSum
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_boolBind blockCount _) ?_
  exact rationalComplexBoolBind_congr (fun first => by
    refine rationalComplexEqv_trans
      (finiteProductHaarComplex_boolBind blockCount _) ?_
    exact rationalComplexBoolBind_congr (fun second => by
      refine rationalComplexEqv_trans
        (finiteProductHaarComplex_boolBind blockCount _) ?_
      exact rationalComplexBoolBind_congr (fun third =>
        finiteProductHaarComplex_boolBind blockCount
          (fun fourth => family first second third fourth))))

/-- The bounded four-diagonal-index trace of the balanced local word. -/
def oneLinkFourValentClosedTracePolynomial : ComplexRatPoly :=
  complexRatPolyFourBoolSum (fun first second third fourth =>
    twoForwardTwoReverseFundamentalTerm 0
      first first second second third third fourth fourth)

/-- The trace of the signed projector is exactly the invariant-space
cardinality two. -/
theorem orientedFourFundamentalHaarProjector_diagonal_trace_exact :
    RationalComplexEqv
      (rationalComplexFourBoolSum (fun first second third fourth =>
        orientedFourFundamentalHaarProjector
          first first second second third third fourth fourth))
      ((2 : Q'), 0) := by
  constructor <;> decide

/-- **Closed four-character Haar value.** Tracing the normalized signed
projector gives two, while its individual mixed entries remain negative. -/
theorem finiteProductHaarComplex_oneLinkFourValentClosedTrace_exact :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        oneLinkFourValentClosedTracePolynomial)
      ((2 : Q'), 0) := by
  unfold oneLinkFourValentClosedTracePolynomial
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_fourBoolSum 1 _) ?_
  refine rationalComplexEqv_trans
    (rationalComplexFourBoolSum_congr (fun first second third fourth =>
      oneLink_twoForward_twoReverse_fundamental_projector
        first first second second third third fourth fourth)) ?_
  exact orientedFourFundamentalHaarProjector_diagonal_trace_exact

#print axioms direct_crossed_oriented_pairing_gram_exact
#print axioms oneLink_twoForward_twoReverse_fundamental_projector
#print axioms oneLink_twoForward_twoReverse_negative_mixed_entry
#print axioms oneLink_twoForward_twoReverse_positive_diagonal_entry
#print axioms finiteProductHaarComplex_fourBoolSum
#print axioms orientedFourFundamentalHaarProjector_diagonal_trace_exact
#print axioms finiteProductHaarComplex_oneLinkFourValentClosedTrace_exact

end YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
