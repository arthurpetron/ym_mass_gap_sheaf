/-
# Orientation-correct bivalent operator Haar kernel

The fundamental coefficient carrier stores a reverse coefficient with the
row/column transpose already built into `reverseFundamentalCoefficient`.
Consequently an occurrence carrying the matrix element from `input` to
`output` must store reverse indices as `(input, output)`, rather than as
`(output, input)`.  This leaf freezes that convention and packages the exact
bivalent Haar moment as a four-by-four kernel on Boolean operator indices.

The resulting kernel is the Haar projector from the fundamental operator
space onto its scalar line.  We prove, directly in the exact rational-complex
carrier, that it is pure real, self-adjoint, idempotent, and has trace one.
The middle-index square and trace use only two nested Boolean binders; no
global face-index network or bounded labelling family is materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector

namespace YMGap.Continuum.SU2QuaternionBivalentOperatorKernel

open YMGap.Constructive
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionGenericBlockOrientedBivalentHaarProjector

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Operator-index occurrences and epsilon signs -/

/-- One Boolean operator-space coordinate, stored in the semantic order
`(output,input)`.  Keeping this pair packaged prevents the reverse-oriented
matrix-storage transpose from leaking into later tensor-network wiring. -/
structure BivalentOperatorIndex where
  output : Bool
  input : Bool
  deriving DecidableEq

/-- The occurrence representing a fundamental operator coefficient from
`input` to `output`.  A reverse coefficient stores the transposed pair
`(input, output)`, because conjugate transpose is already part of
`reverseFundamentalCoefficient`. -/
def operatorOccurrence
    (orientation : FundamentalLinkOrientation)
    (output input : Bool) : FundamentalOccurrence :=
  match orientation with
  | .forward => ⟨.forward, output, input⟩
  | .reverse => ⟨.reverse, input, output⟩

/-- Epsilon duality reverses the orientation and complements both abstract
operator indices.  The stored reverse pair is transposed automatically by
`operatorOccurrence`. -/
theorem operatorOccurrence_dual
    (orientation : FundamentalLinkOrientation) (output input : Bool) :
    (operatorOccurrence orientation output input).dual =
      operatorOccurrence orientation.opposite (!output) (!input) := by
  cases orientation <;> cases output <;> cases input <;> rfl

/-- One-index epsilon sign.  Its product on row and column is positive on the
diagonal and negative off the diagonal. -/
def operatorIndexEpsilonSign : Bool → Q'
  | false => 1
  | true => -1

/-- Exact factorization of the fundamental duality sign into its row and
column epsilon factors. -/
theorem fundamentalDualitySign_row_column_factorization
    (row column : Bool) :
    fundamentalDualitySign row column ≈
      operatorIndexEpsilonSign row * operatorIndexEpsilonSign column := by
  cases row <;> cases column <;> decide

/-- The same exact sign factorization in abstract operator indices.  It is
independent of orientation: the reverse storage only swaps the two factors. -/
theorem operatorOccurrence_dualitySign_factorization
    (orientation : FundamentalLinkOrientation) (output input : Bool) :
    fundamentalDualitySign
        (operatorOccurrence orientation output input).row
        (operatorOccurrence orientation output input).column ≈
      operatorIndexEpsilonSign output * operatorIndexEpsilonSign input := by
  cases orientation <;> cases output <;> cases input <;> decide

/-! ## 2. The exact operator kernel -/

/-- Componentwise addition in the exact rational-complex value carrier. -/
def bivalentRationalComplexAdd
    (left right : RationalComplex) : RationalComplex :=
  (left.1 + right.1, left.2 + right.2)

/-- Complex multiplication in the exact rational-complex value carrier. -/
def bivalentRationalComplexMul
    (left right : RationalComplex) : RationalComplex :=
  (left.1 * right.1 - left.2 * right.2,
    left.1 * right.2 + left.2 * right.1)

/-- One bounded Boolean sum in the rational-complex carrier. -/
def bivalentRationalComplexBoolSum
    (family : Bool → RationalComplex) : RationalComplex :=
  bivalentRationalComplexAdd (family false) (family true)

/-- Sum over the four Boolean operator coordinates `(output,input)`. -/
def bivalentOperatorIndexSum
    (family : Bool → Bool → RationalComplex) : RationalComplex :=
  bivalentRationalComplexBoolSum (fun output =>
    bivalentRationalComplexBoolSum (fun input => family output input))

/-- One bounded Boolean sum in the exact rational scalar carrier. -/
def bivalentRationalBoolSum (family : Bool → Q') : Q' :=
  family false + family true

/-- The bivalent Haar kernel on operator coordinates.  The first occurrence
carries the target/source output indices.  The oppositely oriented second
occurrence carries the target/source input indices; its reverse branch stores
them transposed. -/
def bivalentOperatorKernel
    (orientation : FundamentalLinkOrientation)
    (targetOutput targetInput sourceOutput sourceInput : Bool) :
    RationalComplex :=
  orientedBivalentHaarKernel
    (operatorOccurrence orientation targetOutput sourceOutput)
    (operatorOccurrence orientation.opposite targetInput sourceInput)

/-- The same kernel with its target and source operator coordinates packaged
in semantic `(output,input)` order. -/
def bivalentOperatorKernelAt
    (orientation : FundamentalLinkOrientation)
    (target source : BivalentOperatorIndex) : RationalComplex :=
  bivalentOperatorKernel orientation
    target.output target.input source.output source.input

/-- Scalar component of the packaged bivalent operator kernel. -/
def bivalentOperatorKernelScalar
    (orientation : FundamentalLinkOrientation)
    (target source : BivalentOperatorIndex) : Q' :=
  (bivalentOperatorKernelAt orientation target source).1

/-- Matrix transpose on the two operator-coordinate pairs. -/
def bivalentOperatorKernelTranspose
    (orientation : FundamentalLinkOrientation)
    (targetOutput targetInput sourceOutput sourceInput : Bool) :
    RationalComplex :=
  bivalentOperatorKernel orientation
    sourceOutput sourceInput targetOutput targetInput

/-- Boolean middle-index matrix square of the bivalent operator kernel. -/
def bivalentOperatorKernelSquare
    (orientation : FundamentalLinkOrientation)
    (targetOutput targetInput sourceOutput sourceInput : Bool) :
    RationalComplex :=
  bivalentOperatorIndexSum (fun middleOutput middleInput =>
    bivalentRationalComplexMul
      (bivalentOperatorKernel orientation
        targetOutput targetInput middleOutput middleInput)
      (bivalentOperatorKernel orientation
        middleOutput middleInput sourceOutput sourceInput))

/-- Diagonal trace over the four Boolean operator coordinates. -/
def bivalentOperatorKernelTrace
    (orientation : FundamentalLinkOrientation) : RationalComplex :=
  bivalentOperatorIndexSum (fun output input =>
    bivalentOperatorKernel orientation output input output input)

/-! ## 3. Projector laws -/

/-- Every entry of the bivalent operator kernel is pure real. -/
theorem bivalentOperatorKernel_pureReal
    (orientation : FundamentalLinkOrientation)
    (targetOutput targetInput sourceOutput sourceInput : Bool) :
    (bivalentOperatorKernel orientation
      targetOutput targetInput sourceOutput sourceInput).2 ≈ 0 := by
  cases orientation <;>
    cases targetOutput <;> cases targetInput <;>
    cases sourceOutput <;> cases sourceInput <;> decide

/-- The operator kernel is self-adjoint (here, real symmetry). -/
theorem bivalentOperatorKernel_selfAdjoint
    (orientation : FundamentalLinkOrientation)
    (targetOutput targetInput sourceOutput sourceInput : Bool) :
    RationalComplexEqv
      (bivalentOperatorKernel orientation
        targetOutput targetInput sourceOutput sourceInput)
      (bivalentOperatorKernelTranspose orientation
        targetOutput targetInput sourceOutput sourceInput) := by
  cases orientation <;>
    cases targetOutput <;> cases targetInput <;>
    cases sourceOutput <;> cases sourceInput <;>
      constructor <;> decide

/-- Reversing the chosen link orientation does not change the scalar-line
operator projector. -/
theorem bivalentOperatorKernel_opposite_orientation
    (orientation : FundamentalLinkOrientation)
    (targetOutput targetInput sourceOutput sourceInput : Bool) :
    RationalComplexEqv
      (bivalentOperatorKernel orientation
        targetOutput targetInput sourceOutput sourceInput)
      (bivalentOperatorKernel orientation.opposite
        targetOutput targetInput sourceOutput sourceInput) := by
  cases orientation <;>
    cases targetOutput <;> cases targetInput <;>
    cases sourceOutput <;> cases sourceInput <;>
      constructor <;> decide

/-- The exact Boolean middle-index square is the original kernel. -/
theorem bivalentOperatorKernel_idempotent
    (orientation : FundamentalLinkOrientation)
    (targetOutput targetInput sourceOutput sourceInput : Bool) :
    RationalComplexEqv
      (bivalentOperatorKernelSquare orientation
        targetOutput targetInput sourceOutput sourceInput)
      (bivalentOperatorKernel orientation
        targetOutput targetInput sourceOutput sourceInput) := by
  cases orientation <;>
    cases targetOutput <;> cases targetInput <;>
    cases sourceOutput <;> cases sourceInput <;>
      constructor <;> decide

/-- The scalar-line Haar projector has exact operator trace one. -/
theorem bivalentOperatorKernel_trace_exact
    (orientation : FundamentalLinkOrientation) :
    RationalComplexEqv
      (bivalentOperatorKernelTrace orientation) (1, 0) := by
  cases orientation <;> constructor <;> decide

/-! ## 4. Positive scalar-channel resolution -/

/-- The invariant scalar vector in the fundamental operator space:
`delta(output,input)`.  It has one unit entry on each of the two diagonal
operator coordinates and vanishes off the diagonal. -/
def bivalentInvariantDelta (index : BivalentOperatorIndex) : Q' :=
  if index.output = index.input then 1 else 0

/-- The inverse Gram weight of the scalar invariant vector, namely `1/2`. -/
def bivalentInvariantChannelWeight : Q' :=
  Q'.invSucc 1

/-- The manifest positive rank-one scalar kernel
`(1/2) |delta><delta|`. -/
def bivalentOperatorPositiveChannelScalar
    (target source : BivalentOperatorIndex) : Q' :=
  bivalentInvariantChannelWeight *
    (bivalentInvariantDelta target * bivalentInvariantDelta source)

/-- Rational-complex lift of the positive scalar-channel kernel. -/
def bivalentOperatorPositiveChannelKernel
    (target source : BivalentOperatorIndex) : RationalComplex :=
  (bivalentOperatorPositiveChannelScalar target source, 0)

/-- For either link orientation, the scalar component of the exact Schur
kernel is `(1/2) delta(target) delta(source)`.  This is a fixed local
`2 * 4 * 4` operator-matrix check, independent of the size of any later
plaquette network. -/
theorem bivalentOperatorKernelScalar_eqv_positiveChannel
    (orientation : FundamentalLinkOrientation)
    (target source : BivalentOperatorIndex) :
    bivalentOperatorKernelScalar orientation target source ≈
      bivalentOperatorPositiveChannelScalar target source := by
  rcases target with ⟨targetOutput, targetInput⟩
  rcases source with ⟨sourceOutput, sourceInput⟩
  cases orientation <;>
    cases targetOutput <;> cases targetInput <;>
    cases sourceOutput <;> cases sourceInput <;>
    decide

/-- Rational-complex form of the positive rank-one resolution, uniformly in
the chosen orientation. -/
theorem bivalentOperatorKernelAt_eqv_positiveChannel
    (orientation : FundamentalLinkOrientation)
    (target source : BivalentOperatorIndex) :
    RationalComplexEqv
      (bivalentOperatorKernelAt orientation target source)
      (bivalentOperatorPositiveChannelKernel target source) := by
  constructor
  · exact bivalentOperatorKernelScalar_eqv_positiveChannel
      orientation target source
  · simpa [bivalentOperatorKernelAt,
      bivalentOperatorPositiveChannelKernel] using
      bivalentOperatorKernel_pureReal orientation
        target.output target.input source.output source.input

/-- Explicit forward-oriented form of the positive scalar-channel
resolution. -/
theorem bivalentOperatorKernelAt_forward_eqv_positiveChannel
    (target source : BivalentOperatorIndex) :
    RationalComplexEqv
      (bivalentOperatorKernelAt .forward target source)
      (bivalentOperatorPositiveChannelKernel target source) :=
  bivalentOperatorKernelAt_eqv_positiveChannel .forward target source

/-- Explicit reverse-oriented form of the same positive scalar-channel
resolution. -/
theorem bivalentOperatorKernelAt_reverse_eqv_positiveChannel
    (target source : BivalentOperatorIndex) :
    RationalComplexEqv
      (bivalentOperatorKernelAt .reverse target source)
      (bivalentOperatorPositiveChannelKernel target source) :=
  bivalentOperatorKernelAt_eqv_positiveChannel .reverse target source

/-- Exact squared norm of the scalar invariant vector, summed over its two
Boolean operator indices. -/
def bivalentInvariantDeltaSquaredNorm : Q' :=
  bivalentRationalBoolSum (fun output =>
    bivalentRationalBoolSum (fun input =>
      let index : BivalentOperatorIndex := ⟨output, input⟩
      bivalentInvariantDelta index * bivalentInvariantDelta index))

/-- The invariant vector has squared norm `2`: precisely its two diagonal
coordinates survive. -/
theorem bivalentInvariantDeltaSquaredNorm_exact :
    bivalentInvariantDeltaSquaredNorm ≈ 2 := by
  unfold bivalentInvariantDeltaSquaredNorm bivalentRationalBoolSum
    bivalentInvariantDelta
  decide

/-- Trace mass of the positive scalar channel before normalization is
`(1/2) * ||delta||^2`. -/
def bivalentOperatorWeightedTraceMass : Q' :=
  bivalentInvariantChannelWeight * bivalentInvariantDeltaSquaredNorm

/-- The rank-one scalar channel contributes exactly one unit of trace mass:
`(1/2) * 2 = 1`. -/
theorem bivalentOperatorWeightedTraceMass_exact :
    bivalentOperatorWeightedTraceMass ≈ 1 := by
  refine Q'.eqv_trans _
    (bivalentInvariantChannelWeight * 2) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left bivalentInvariantChannelWeight
      bivalentInvariantDeltaSquaredNorm 2
      bivalentInvariantDeltaSquaredNorm_exact
  · unfold bivalentInvariantChannelWeight
    decide

/-! ## 5. Sign and transpose regressions -/

/-- Reverse operator storage is exactly `(input,output)`. -/
theorem operatorOccurrence_reverse_storage_pin :
    operatorOccurrence .reverse false true =
      (⟨.reverse, true, false⟩ : FundamentalOccurrence) := by
  rfl

/-- A forward off-diagonal occurrence dualizes to the correctly transposed
reverse occurrence. -/
theorem operatorOccurrence_forward_dual_transpose_pin :
    (operatorOccurrence .forward false true).dual =
      operatorOccurrence .reverse true false := by
  rfl

/-- The off-diagonal operator coefficient carries the negative epsilon sign,
including on the reverse-storage branch. -/
theorem operatorOccurrence_reverse_offDiagonal_sign_pin :
    fundamentalDualitySign
        (operatorOccurrence .reverse false true).row
        (operatorOccurrence .reverse false true).column ≈ -1 := by
  decide

/-- Transpose-sensitive surviving entry.  Correct reverse storage gives
`integral U[0,1] U⁻¹[1,0] = 1/2`; an untransposed reverse occurrence would
make this entry vanish. -/
theorem bivalentOperatorKernel_transpose_sensitive_pin :
    RationalComplexEqv
      (bivalentOperatorKernel .forward false false true true)
      (Q'.invSucc 1, 0) := by
  constructor <;> decide

/-- Off-diagonal operator coordinates are killed by the scalar-line Haar
projector. -/
theorem bivalentOperatorKernel_offDiagonal_zero_pin :
    RationalComplexEqv
      (bivalentOperatorKernel .forward false true false true)
      (0, 0) := by
  constructor <;> decide

/-- Packaged diagonal coordinates used by the transpose-sensitive pin. -/
def bivalentZeroDiagonalOperatorIndex : BivalentOperatorIndex :=
  ⟨false, false⟩

def bivalentOneDiagonalOperatorIndex : BivalentOperatorIndex :=
  ⟨true, true⟩

/-- Packaged off-diagonal coordinate used by the zero pin. -/
def bivalentOffDiagonalOperatorIndex : BivalentOperatorIndex :=
  ⟨false, true⟩

/-- Packaged form of the existing transpose-sensitive surviving entry. -/
theorem bivalentOperatorKernelAt_transpose_sensitive_pin :
    RationalComplexEqv
      (bivalentOperatorKernelAt .forward
        bivalentZeroDiagonalOperatorIndex
        bivalentOneDiagonalOperatorIndex)
      (Q'.invSucc 1, 0) := by
  simpa [bivalentOperatorKernelAt,
    bivalentZeroDiagonalOperatorIndex,
    bivalentOneDiagonalOperatorIndex] using
    bivalentOperatorKernel_transpose_sensitive_pin

/-- Packaged form of the existing off-diagonal zero entry. -/
theorem bivalentOperatorKernelAt_offDiagonal_zero_pin :
    RationalComplexEqv
      (bivalentOperatorKernelAt .forward
        bivalentOffDiagonalOperatorIndex
        bivalentOffDiagonalOperatorIndex)
      (0, 0) := by
  simpa [bivalentOperatorKernelAt,
    bivalentOffDiagonalOperatorIndex] using
    bivalentOperatorKernel_offDiagonal_zero_pin

#print axioms operatorOccurrence_dual
#print axioms fundamentalDualitySign_row_column_factorization
#print axioms operatorOccurrence_dualitySign_factorization
#print axioms bivalentOperatorKernel_pureReal
#print axioms bivalentOperatorKernel_selfAdjoint
#print axioms bivalentOperatorKernel_opposite_orientation
#print axioms bivalentOperatorKernel_idempotent
#print axioms bivalentOperatorKernel_trace_exact
#print axioms bivalentOperatorKernelScalar_eqv_positiveChannel
#print axioms bivalentOperatorKernelAt_eqv_positiveChannel
#print axioms bivalentOperatorKernelAt_forward_eqv_positiveChannel
#print axioms bivalentOperatorKernelAt_reverse_eqv_positiveChannel
#print axioms bivalentInvariantDeltaSquaredNorm_exact
#print axioms bivalentOperatorWeightedTraceMass_exact
#print axioms operatorOccurrence_reverse_storage_pin
#print axioms operatorOccurrence_forward_dual_transpose_pin
#print axioms operatorOccurrence_reverse_offDiagonal_sign_pin
#print axioms bivalentOperatorKernel_transpose_sensitive_pin
#print axioms bivalentOperatorKernel_offDiagonal_zero_pin
#print axioms bivalentOperatorKernelAt_transpose_sensitive_pin
#print axioms bivalentOperatorKernelAt_offDiagonal_zero_pin

end YMGap.Continuum.SU2QuaternionBivalentOperatorKernel
