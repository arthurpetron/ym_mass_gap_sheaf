/-
# BF4 Peter--Weyl endpoint bridge on the exact positive physical carrier

The five-dimensional Gaussian calculation and the finite physical Choi
operator currently live on different carriers:

* `BF4FiveHolonomyGaussian` supplies the exact five-coordinate precision
  matrices and their `4 x 3`, `6 x 2` generalized spectrum;
* `centralPositiveHalfStates` is a finite list of literal BF4 face
  labellings `EdgeLabelling = Nat -> Nat`.

A bridge between them cannot be a bare map from five class coordinates to
face labels.  Peter--Weyl boundary states depend on matrix coefficients
(including magnetic and intertwiner contractions), and the endpoint matrix
is obtained by a genuine double Haar coefficient transform of the Mehler
kernel.

This module does two things.

1. It constructs the exact rational-complex spin-one-half matrix
   coefficients on the repository's rational unit-quaternion SU(2) carrier
   and proves their Schur table from the already-constructed product-Haar
   moment functional.  Thus the interface below is anchored in an actual
   matrix-coefficient calculation, not a class-character surrogate.

2. It states the smallest witness-bearing all-label endpoint transform
   needed to connect the five-holonomy kernel to
   `centralPositiveHalfStates`.  The structure carries boundary
   wavefunctions indexed by the literal `EdgeLabelling`, a double-Haar
   coefficient functional, and the exact projected rational joint matrix.
   It is deliberately not inhabited here: the repository has no
   five-holonomy Mehler kernel and no all-spin BF4 boundary spin-network
   wavefunction on this carrier yet.

The endpoint transform is kept separate from marginal matching and the
row-relative Yang--Mills estimate.  Consequently it cannot be confused with
a refresh kernel or used to manufacture a `CentralPhysicalMehlerComparison`
without the missing analysis.

## Axiom gate

Finite exact `Q'` algebra and explicit Type-level witnesses only.  No
`Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4FiveHolonomyGaussian
import YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

namespace YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4FiveHolonomyGaussian
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact rational-complex coefficient algebra -/

/-- A rational complex scalar.  Keeping the real and imaginary parts as data
avoids the false scalar-`Q'` complexification ruled out by
`no_rational_imaginary_unit`. -/
structure RationalComplex : Type where
  re : Q'
  im : Q'

namespace RationalComplex

def zero : RationalComplex := ⟨0, 0⟩
def one : RationalComplex := ⟨1, 0⟩
def conj (z : RationalComplex) : RationalComplex := ⟨z.re, -z.im⟩

def mul (z w : RationalComplex) : RationalComplex :=
  ⟨z.re * w.re + -(z.im * w.im),
   z.re * w.im + z.im * w.re⟩

def normSq (z : RationalComplex) : Q' :=
  z.re * z.re + z.im * z.im

def Eqv (z w : RationalComplex) : Prop :=
  z.re ≈ w.re ∧ z.im ≈ w.im

private def normMulL : PolyExpr :=
  let realPart :=
    .add (.mul (.var 0) (.var 2))
      (.neg (.mul (.var 1) (.var 3)))
  let imagPart :=
    .add (.mul (.var 0) (.var 3))
      (.mul (.var 1) (.var 2))
  .add (.mul realPart realPart) (.mul imagPart imagPart)

private def normMulR : PolyExpr :=
  .mul
    (.add (.mul (.var 0) (.var 0))
      (.mul (.var 1) (.var 1)))
    (.add (.mul (.var 2) (.var 2))
      (.mul (.var 3) (.var 3)))

private theorem normMul_normal :
    normalize normMulL = normalize normMulR := by
  decide

theorem mul_normSq (z w : RationalComplex) :
    normSq (mul z w) ≈ normSq z * normSq w := by
  let rho : Nat → Q' := fun
    | 0 => z.re
    | 1 => z.im
    | 2 => w.re
    | _ => w.im
  simpa [normMulL, normMulR, RingNormaliser.eval, rho,
    normSq, mul] using
    (poly_identity_of_normal_eq
      normMulL normMulR normMul_normal rho)

theorem conj_normSq (z : RationalComplex) :
    normSq (conj z) ≈ normSq z := by
  unfold normSq conj
  exact Q'.add_eqv_congr_left (z.re * z.re) _ _
    (Q'.eqv_trans _
      (-(z.im * (-z.im))) _
      (Q'.neg_mul_eqv z.im (-z.im))
      (Q'.eqv_trans _
        (-(-(z.im * z.im))) _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_neg_eqv z.im z.im))
        (Q'.neg_neg_eqv (z.im * z.im))))

end RationalComplex

/-- Complex polynomials in the explicit quaternion coordinate carrier. -/
abbrev RationalComplexPolynomial := RatPoly × RatPoly

/-- Real part of the product `conj(left) * right`. -/
def complexPolynomialRealInner
    (left right : RationalComplexPolynomial) : RatPoly :=
  polyAdd
    (polyMul left.1 right.1)
    (polyMul left.2 right.2)

/-- Exact product-Haar Hermitian pairing of two complex polynomials. -/
def complexPolynomialHaarInner
    (left right : RationalComplexPolynomial) : Q' :=
  productHaar (complexPolynomialRealInner left right)

private def fin2zero : Fin 2 := ⟨0, by decide⟩
private def fin2one : Fin 2 := ⟨1, by decide⟩

private theorem fin2_zero_or_one (index : Fin 2) :
    index = fin2zero ∨ index = fin2one := by
  rcases index with ⟨value, hvalue⟩
  have hcases : value = 0 ∨ value = 1 := by omega
  rcases hcases with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The four fundamental SU(2) matrix coefficients in quaternion
coordinates, with convention

`[[a + i b, c + i d], [-c + i d, a - i b]]`.
-/
def fundamentalMatrixCoefficientPolynomial
    (row column : Fin 2) : RationalComplexPolynomial :=
  if row = fin2zero then
    if column = fin2zero then
      (gCoordinate 0, gCoordinate 1)
    else
      (gCoordinate 2, gCoordinate 3)
  else
    if column = fin2zero then
      (polyNeg (gCoordinate 2), gCoordinate 3)
    else
      (gCoordinate 0, polyNeg (gCoordinate 1))

/-- Exact Schur weight for the fundamental representation. -/
def fundamentalSchurEntry
    (row column row' column' : Fin 2) : Q' :=
  if row = row' ∧ column = column'
  then Q'.mkPos 1 2 (by decide)
  else 0

/-- **Actual spin-one-half Schur table.**  The explicit quaternion
matrix-coefficient polynomials are orthogonal under the constructed
normalized product-Haar moment functional, with norm square `1/2`. -/
theorem fundamentalMatrixCoefficient_haar_schur
    (row column row' column' : Fin 2) :
    complexPolynomialHaarInner
        (fundamentalMatrixCoefficientPolynomial row column)
        (fundamentalMatrixCoefficientPolynomial row' column') ≈
      fundamentalSchurEntry row column row' column' := by
  rcases fin2_zero_or_one row with rfl | rfl <;>
  rcases fin2_zero_or_one column with rfl | rfl <;>
  rcases fin2_zero_or_one row' with rfl | rfl <;>
  rcases fin2_zero_or_one column' with rfl | rfl <;>
  decide

/-- The exact rational quaternion `-1` in SU(2). -/
def rationalUnitQuaternionNegOne : RationalUnitQuaternion where
  quaternion :=
    { coordinate := fun index =>
        if index.val = 0 then (-1 : Q') else 0 }
  unit_norm := by
    decide

/-! ## 2. Point evaluation and fivefold tensor coefficients -/

/-- Coordinate access on the canonical rational unit-quaternion carrier. -/
def quaternionCoordinate
    (q : RationalUnitQuaternion) (index : Fin 4) : Q' :=
  q.quaternion.coordinate index

/-- Literal point value of the fundamental matrix coefficient. -/
def fundamentalMatrixCoefficient
    (row column : Fin 2)
    (q : RationalUnitQuaternion) : RationalComplex :=
  let a := quaternionCoordinate q ⟨0, by decide⟩
  let b := quaternionCoordinate q ⟨1, by decide⟩
  let c := quaternionCoordinate q ⟨2, by decide⟩
  let d := quaternionCoordinate q ⟨3, by decide⟩
  if row = fin2zero then
    if column = fin2zero then ⟨a, b⟩ else ⟨c, d⟩
  else
    if column = fin2zero then ⟨-c, d⟩ else ⟨a, -b⟩

/-- **Signed-coefficient test.**  A genuine Peter--Weyl coefficient is not a
nonnegative probability weight: the real part of `D00(-1)` is exactly `-1`.
Therefore positivity of a projected endpoint joint law cannot be inferred
from matrix-coefficient synthesis alone. -/
theorem fundamentalMatrixCoefficient_has_negative_value :
    (fundamentalMatrixCoefficient
        fin2zero fin2zero rationalUnitQuaternionNegOne).re < (0 : Q') := by
  decide

/-- A fivefold fundamental matrix-coefficient index. -/
structure FundamentalFiveMode : Type where
  row : Fin 5 → Fin 2
  column : Fin 5 → Fin 2

/-- Product of rational-complex factors along an explicit coordinate list. -/
def complexProductOn
    (factor : Fin 5 → RationalComplex) :
    List (Fin 5) → RationalComplex
  | [] => RationalComplex.one
  | coordinate :: rest =>
      RationalComplex.mul
        (factor coordinate)
        (complexProductOn factor rest)

/-- Literal five-holonomy tensor matrix coefficient. -/
def fundamentalFiveCoefficient
    (mode : FundamentalFiveMode)
    (configuration : BF4FiveHolonomyConfiguration) :
    RationalComplex :=
  complexProductOn
    (fun coordinate =>
      fundamentalMatrixCoefficient
        (mode.row coordinate)
        (mode.column coordinate)
        (configuration coordinate))
    indices

/-- Norm square of a finite complex product is the product of the factor
norm squares. -/
theorem complexProductOn_normSq
    (factor : Fin 5 → RationalComplex) :
    ∀ coordinates : List (Fin 5),
      RationalComplex.normSq
          (complexProductOn factor coordinates) ≈
        coordinates.foldr
          (fun coordinate total =>
            RationalComplex.normSq (factor coordinate) * total)
          1
  | [] => by
      exact Q'.eqv_refl 1
  | coordinate :: rest => by
      exact Q'.eqv_trans _ _ _
        (RationalComplex.mul_normSq
          (factor coordinate)
          (complexProductOn factor rest))
        (Q'.mul_eqv_congr_left
          (RationalComplex.normSq (factor coordinate)) _ _
          (complexProductOn_normSq factor rest))

/-- Fivefold specialization of the exact tensor norm factorization. -/
theorem fundamentalFiveCoefficient_normSq
    (mode : FundamentalFiveMode)
    (configuration : BF4FiveHolonomyConfiguration) :
    RationalComplex.normSq
        (fundamentalFiveCoefficient mode configuration) ≈
      indices.foldr
        (fun coordinate total =>
          RationalComplex.normSq
              (fundamentalMatrixCoefficient
                (mode.row coordinate)
                (mode.column coordinate)
                (configuration coordinate)) *
            total)
        1 :=
  complexProductOn_normSq _ indices

/-! ## 3. The exact all-label endpoint-transform interface -/

/-- An arbitrary-spin SU(2) Peter--Weyl mode.  Twice-spin and both magnetic
indices are retained as literal natural-number data with constructive range
certificates. -/
structure SU2MatrixMode : Type where
  twiceSpin : Nat
  row : Nat
  column : Nat
  row_lt_dim : row < twiceSpin + 1
  column_lt_dim : column < twiceSpin + 1

/-- One five-holonomy Peter--Weyl tensor mode. -/
abbrev FiveHolonomyPWMode := Fin 5 → SU2MatrixMode

/-- A finite Peter--Weyl expansion term for one physical boundary state. -/
structure BoundaryPWTerm : Type where
  mode : FiveHolonomyPWMode
  coefficient : RationalComplex

/-- Exact equality of rational-complex point values in the `Q'` setoid. -/
def RationalComplexPointwiseEqv
    (left right :
      BF4FiveHolonomyConfiguration → RationalComplex) : Prop :=
  ∀ configuration, RationalComplex.Eqv
    (left configuration) (right configuration)

theorem rationalComplexPointwiseEqv_refl
    (value :
      BF4FiveHolonomyConfiguration → RationalComplex) :
    RationalComplexPointwiseEqv value value := by
  intro configuration
  exact ⟨Q'.eqv_refl _, Q'.eqv_refl _⟩

/-- **The genuine carrier-changing datum.**  This is the missing
Peter--Weyl/spin-network transform from the literal positive BF4 face-label
carrier to five-holonomy boundary wavefunctions.

The expansion is finite at fixed `K`, but it is not merely a map from a face
label to five representation labels: every term retains five magnetic
matrix indices and an exact complex coefficient.  `evaluateMode` is the
all-spin matrix-coefficient evaluator; `boundaryWavefunction` is pinned
definitionally to `EdgeLabelling`.
-/
structure CentralPositiveBoundaryPeterWeylTransform
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat) : Type where
  /-- Arbitrary-spin fivefold matrix-coefficient evaluator. -/
  evaluateMode :
    FiveHolonomyPWMode →
      BF4FiveHolonomyConfiguration → RationalComplex
  /-- Finite spin-network/Peter--Weyl expansion of each literal physical
  boundary labelling. -/
  expansion : EdgeLabelling → List BoundaryPWTerm
  /-- The resulting physical boundary wavefunction. -/
  boundaryWavefunction :
    EdgeLabelling →
      BF4FiveHolonomyConfiguration → RationalComplex
  /-- Normalized fivefold Haar inner product on boundary wavefunctions.
  This is a genuine analytic input, not the finite physical-state dot
  product. -/
  haarInner :
    (BF4FiveHolonomyConfiguration → RationalComplex) →
    (BF4FiveHolonomyConfiguration → RationalComplex) →
      Q'
  /-- Haar pairing respects pointwise rational-complex equivalence. -/
  haarInner_congr :
    ∀ left left' right right',
      RationalComplexPointwiseEqv left left' →
      RationalComplexPointwiseEqv right right' →
        haarInner left right ≈ haarInner left' right'
  /-- The zero boundary wavefunction has zero Haar pairing.  Together with
  normalization below this excludes the vacuous all-zero transform. -/
  haarInner_zero_left :
    ∀ right,
      haarInner
          (fun _ => RationalComplex.zero)
          right ≈
        0
  /-- Every retained physical state is Haar-normalized. -/
  boundary_normalized :
    ∀ state,
      state ∈ centralPositiveHalfStates w hw K halfExtent →
        haarInner
            (boundaryWavefunction state)
            (boundaryWavefunction state) ≈
          1
  /-- Distinct retained physical labels have orthogonal Peter--Weyl
  boundary wavefunctions.  Together with normalization, this is the finite
  physical-carrier isometry law. -/
  boundary_orthogonal :
    ∀ left,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      ∀ right,
        right ∈ centralPositiveHalfStates w hw K halfExtent →
        left ≠ right →
          haarInner
              (boundaryWavefunction left)
              (boundaryWavefunction right) ≈
            0
  /-- Exact synthesis of every retained physical state from its displayed
  finite matrix-coefficient expansion.  This is the nontrivial all-label
  carrier-identification law. -/
  synthesis :
    ∀ state,
      state ∈ centralPositiveHalfStates w hw K halfExtent →
        RationalComplexPointwiseEqv
          (boundaryWavefunction state)
          (fun configuration =>
            (expansion state).foldr
              (fun term total =>
                let value := evaluateMode term.mode configuration
                { re :=
                    term.coefficient.re * value.re +
                      -(term.coefficient.im * value.im) + total.re
                  im :=
                    term.coefficient.re * value.im +
                      term.coefficient.im * value.re + total.im })
              RationalComplex.zero)

namespace CentralPositiveBoundaryPeterWeylTransform

/-- Every retained physical boundary state has at least one displayed
Peter--Weyl term.  This is derived from genuine Haar normalization, so the
carrier-changing interface cannot be inhabited by the empty/zero expansion.
-/
theorem expansion_ne_nil
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    (pw :
      CentralPositiveBoundaryPeterWeylTransform
        w hw K halfExtent)
    {state : EdgeLabelling}
    (hstate :
      state ∈ centralPositiveHalfStates w hw K halfExtent) :
    pw.expansion state ≠ [] := by
  intro hempty
  have hsynth := pw.synthesis state hstate
  rw [hempty] at hsynth
  have hinnerZero :
      pw.haarInner
          (pw.boundaryWavefunction state)
          (pw.boundaryWavefunction state) ≈
        0 := by
    exact Q'.eqv_trans _
      (pw.haarInner
        (fun _ => RationalComplex.zero)
        (pw.boundaryWavefunction state)) _
      (pw.haarInner_congr
        (pw.boundaryWavefunction state)
        (fun _ => RationalComplex.zero)
        (pw.boundaryWavefunction state)
        (pw.boundaryWavefunction state)
        hsynth
        (rationalComplexPointwiseEqv_refl
          (pw.boundaryWavefunction state)))
      (pw.haarInner_zero_left
        (pw.boundaryWavefunction state))
  have hbad : (1 : Q') ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (pw.boundary_normalized state hstate))
      hinnerZero
  exact (by decide : ¬ ((1 : Q') ≈ 0)) hbad

end CentralPositiveBoundaryPeterWeylTransform

/-- Pointwise rational-complex equivalence of two endpoint kernels. -/
def RationalComplexKernelEqv
    (left right :
      BF4FiveHolonomyConfiguration →
        BF4FiveHolonomyConfiguration → RationalComplex) : Prop :=
  ∀ source target,
    RationalComplex.Eqv
      (left source target)
      (right source target)

/-- The identically-zero five-holonomy endpoint kernel. -/
def zeroFiveHolonomyKernel :
    BF4FiveHolonomyConfiguration →
      BF4FiveHolonomyConfiguration → RationalComplex :=
  fun _ _ => RationalComplex.zero

/-- A constructive double-Haar coefficient transform of a five-holonomy
endpoint kernel against the physical Peter--Weyl boundary wavefunctions.

`endpointKernel` is deliberately part of the data: the exact matrices
`spatialS`, `kineticK24`, and `generalizedA` do not by themselves define a
normalized endpoint kernel on `SU(2)^5`.
-/
structure CentralPositiveGaussianEndpointProjection
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (pw :
      CentralPositiveBoundaryPeterWeylTransform
        w hw K halfExtent) : Type where
  /-- The distinct five-holonomy endpoint kernel before coefficient
  projection.  Rational-complex values permit exact quadrature
  approximants; a continuum construction may package its CReal limit
  separately. -/
  endpointKernel :
    BF4FiveHolonomyConfiguration →
      BF4FiveHolonomyConfiguration → RationalComplex
  /-- Exact rational double-Haar coefficient extractor.  Its implementation
  must arise from the normalized SU(2)^5 Haar functional, not an arbitrary
  finite refresh matrix. -/
  doubleHaarCoefficient :
    (BF4FiveHolonomyConfiguration → RationalComplex) →
    (BF4FiveHolonomyConfiguration →
      BF4FiveHolonomyConfiguration → RationalComplex) →
    (BF4FiveHolonomyConfiguration → RationalComplex) →
      Q'
  /-- The projected endpoint joint matrix on the literal physical carrier. -/
  projectedJoint : EdgeLabelling → EdgeLabelling → Q'
  /-- Definitional carrier bridge: every projected entry is the genuine
  double-Haar coefficient of the endpoint kernel between the physical
  Peter--Weyl boundary wavefunctions. -/
  projectedJoint_eq_transform :
    ∀ left,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      ∀ right,
        right ∈ centralPositiveHalfStates w hw K halfExtent →
          projectedJoint left right ≈
            doubleHaarCoefficient
              (pw.boundaryWavefunction left)
              endpointKernel
              (pw.boundaryWavefunction right)
  /-- Constructive chart/difference extractor sending an endpoint kernel to
  its five-coordinate tangent precision. -/
  tangentPrecisionOf :
    (BF4FiveHolonomyConfiguration →
      BF4FiveHolonomyConfiguration → RationalComplex) →
      Matrix5
  /-- Tangent precision depends only on the pointwise kernel. -/
  tangentPrecision_congr :
    ∀ left right,
      RationalComplexKernelEqv left right →
        MatrixEqv
          (tangentPrecisionOf left)
          (tangentPrecisionOf right)
  /-- The zero endpoint kernel has zero tangent precision.  This prevents a
  vacuous extractor that simply returns the desired BF4 matrix for every
  input. -/
  tangentPrecision_zero :
    MatrixEqv
      (tangentPrecisionOf zeroFiveHolonomyKernel)
      (scalarMatrix 0)
  /-- The actual endpoint kernel, not merely a separately carried theorem,
  has the exact BF4 generalized tangent precision. -/
  endpoint_tangent_precision :
    MatrixEqv
      (tangentPrecisionOf endpointKernel)
      generalizedA
  /-- The endpoint projection is symmetric on the retained physical
  carrier. -/
  projectedJoint_symmetric :
    ∀ left right,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      right ∈ centralPositiveHalfStates w hw K halfExtent →
        projectedJoint left right ≈ projectedJoint right left

namespace CentralPositiveGaussianEndpointProjection

private def tangentIndexZero : Fin 5 := ⟨0, by decide⟩

/-- The tangent-precision pin makes the proposed endpoint kernel genuinely
nonzero: it cannot be pointwise equivalent to the zero kernel. -/
theorem endpointKernel_ne_zero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {pw :
      CentralPositiveBoundaryPeterWeylTransform
        w hw K halfExtent}
    (projection :
      CentralPositiveGaussianEndpointProjection
        w hw K halfExtent pw) :
    ¬ RationalComplexKernelEqv
        projection.endpointKernel
        zeroFiveHolonomyKernel := by
  intro hzero
  have hextract :=
    projection.tangentPrecision_congr
      projection.endpointKernel
      zeroFiveHolonomyKernel hzero
  have hbad :
      generalizedA tangentIndexZero tangentIndexZero ≈
        (scalarMatrix 0) tangentIndexZero tangentIndexZero :=
    Q'.eqv_trans _
      (projection.tangentPrecisionOf
        zeroFiveHolonomyKernel
        tangentIndexZero tangentIndexZero) _
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (projection.endpoint_tangent_precision
            tangentIndexZero tangentIndexZero))
        (hextract tangentIndexZero tangentIndexZero))
      (projection.tangentPrecision_zero
        tangentIndexZero tangentIndexZero)
  exact
    (by decide :
      ¬ (generalizedA tangentIndexZero tangentIndexZero ≈
        (scalarMatrix 0) tangentIndexZero tangentIndexZero))
      hbad

end CentralPositiveGaussianEndpointProjection

/-! ## 4. The extra positive-carrier datum required for Markov comparison -/

/-- **Positive refined-channel lumping of the signed Peter--Weyl endpoint
projection.**

An operator coefficient transform is not automatically an entrywise-positive
Markov joint law: the concrete theorem
`fundamentalMatrixCoefficient_has_negative_value` already shows why signs
cannot be discarded.  To feed `CentralPhysicalMehlerComparison`, one must
construct a refined positive endpoint carrier (for example endpoint paths,
magnetic strands, or another positivity-preserving Feynman--Kac carrier),
then prove that conditional summation over each source/target fiber recovers
the Peter--Weyl projected matrix.

This structure states exactly that missing datum.  It also requires the
lumped endpoint row marginal to equal the physical Choi marginal.  It is
strictly stronger than operator positivity and is deliberately uninhabited.
-/
structure CentralPositiveEndpointLumping
    (w : Q') (hw : (0 : Q') ≤ w)
    (K halfExtent : Nat)
    (pw :
      CentralPositiveBoundaryPeterWeylTransform
        w hw K halfExtent)
    (projection :
      CentralPositiveGaussianEndpointProjection
        w hw K halfExtent pw) : Type 1 where
  /-- Refined positive endpoint channel type. -/
  Channel : Type
  /-- Complete finite refined fiber over each physical source/target pair. -/
  fiber : EdgeLabelling → EdgeLabelling → List Channel
  /-- Nonnegative refined endpoint weight. -/
  weight : Channel → Q'
  weight_nonnegative :
    ∀ left,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      ∀ right,
        right ∈ centralPositiveHalfStates w hw K halfExtent →
        ∀ channel,
          channel ∈ fiber left right →
            (0 : Q') ≤ weight channel
  /-- Conditional integration/lumping recovers the actual double-Haar
  Peter--Weyl endpoint coefficient, not a substitute refresh matrix. -/
  projectedJoint_eq_fiber :
    ∀ left,
      left ∈ centralPositiveHalfStates w hw K halfExtent →
      ∀ right,
        right ∈ centralPositiveHalfStates w hw K halfExtent →
          projection.projectedJoint left right ≈
            listQSum weight (fiber left right)
  /-- Exact marginal matching after positive lumping. -/
  rowMarginal :
    ∀ source,
      source ∈ centralPositiveHalfStates w hw K halfExtent →
        listQSum
            (projection.projectedJoint source)
            (centralPositiveHalfStates w hw K halfExtent) ≈
          centralPhysicalRowMarginal
            w hw K halfExtent source

namespace CentralPositiveEndpointLumping

/-- A successful positive refined-carrier lumping makes the projected
endpoint entrywise nonnegative on the exact physical carrier. -/
theorem projectedJoint_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K halfExtent : Nat}
    {pw :
      CentralPositiveBoundaryPeterWeylTransform
        w hw K halfExtent}
    {projection :
      CentralPositiveGaussianEndpointProjection
        w hw K halfExtent pw}
    (lumping :
      CentralPositiveEndpointLumping
        w hw K halfExtent pw projection)
    {left right : EdgeLabelling}
    (hleft :
      left ∈ centralPositiveHalfStates w hw K halfExtent)
    (hright :
      right ∈ centralPositiveHalfStates w hw K halfExtent) :
    (0 : Q') ≤ projection.projectedJoint left right := by
  have hsum :
      (0 : Q') ≤
        listQSum lumping.weight
          (lumping.fiber left right) :=
    listQSum_nonnegative_on
      lumping.weight
      (lumping.fiber left right)
      (fun channel hchannel =>
        lumping.weight_nonnegative
          left hleft right hright channel hchannel)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (lumping.projectedJoint_eq_fiber
          left hleft right hright)))

end CentralPositiveEndpointLumping

/-- Every genuine endpoint projection carries the exact already-proved
division-free BF4 precision identity. -/
def canonicalTangentPrecision :
    MatrixEqv
      (matMul kineticK24 generalizedA)
      spatialS24 :=
  kinetic_mul_generalized

end YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.RationalComplex.mul_normSq
#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.fundamentalMatrixCoefficient_haar_schur
#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.fundamentalMatrixCoefficient_has_negative_value
#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.complexProductOn_normSq
#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.fundamentalFiveCoefficient_normSq
#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.CentralPositiveBoundaryPeterWeylTransform.expansion_ne_nil
#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.CentralPositiveGaussianEndpointProjection.endpointKernel_ne_zero
#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.CentralPositiveEndpointLumping.projectedJoint_nonnegative
#print axioms YMGap.Continuum.BF4CentralPositivePeterWeylEndpoint.canonicalTangentPrecision
