/-
# Constructive Gaussian square positivity in any finite coordinate dimension

The first product-Gaussian square theorem in the quaternion development was
written out for the eight coordinates of two quaternion blocks.  A lattice
gauge field has one four-coordinate block for every active link, so the
load-bearing statement is the dimension-uniform one proved here.

For `coordinateCount = N`, `finiteGaussianMono N m` is the product of the
first `N` one-dimensional Gaussian moments of the exponent vector `m`.
Every coordinate moment kernel already has an explicit finite Hermite Gram
witness.  Recursively taking constructive Schur products therefore gives an
explicit Gram witness in every finite dimension.  The raw `RatPoly` square is
then identified with its Gram quadratic form by the same finite bilinear
expansion as in the historical eight-coordinate proof.

The definitions remain lazy in the coordinate count: no list of monomials,
matrix, or expanded polynomial is materialized.  In particular, the theorem
specializes directly to `4 * blockCount` coordinates without constructing the
exponentially large Khatri--Rao feature family unless its data are explicitly
evaluated.

The final section proves exact compatibility, up to the rational setoid, with
the established eight-coordinate product-Gaussian functional.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram

namespace YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionProductGaussianTensor
open YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram
open YMGap.Continuum.SchurHadamardTransfer

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-! ## 1. Dimension-uniform monomial moments and kernels -/

/-- Product of the first `coordinateCount` independent standard-Gaussian
moments of a monomial.  The recursion is kept symbolic; it does not enumerate
monomials or feature vectors. -/
def finiteGaussianMono : Nat → List Nat → Q'
  | 0, _ => 1
  | coordinateCount + 1, monomial =>
      gaussianMoment1 (exponentAt monomial coordinateCount) *
        finiteGaussianMono coordinateCount monomial

/-- Entrywise product of the first `coordinateCount` coordinate Gaussian
kernels on the finite term list of `polynomial`. -/
def finiteGaussianKernel (polynomial : RatPoly) : Nat → Nat → Nat → Q'
  | 0, _, _ => 1
  | coordinateCount + 1, i, j =>
      coordinateGaussianKernel polynomial coordinateCount i j *
        finiteGaussianKernel polynomial coordinateCount i j

/-- Explicit finite Hermite/Khatri--Rao Gram witness for the Gaussian kernel
in every finite coordinate dimension. -/
def finiteGaussianGramRep (polynomial : RatPoly) :
    ∀ coordinateCount,
      GramRep (finiteGaussianKernel polynomial coordinateCount)
  | 0 => onesGramRep
  | coordinateCount + 1 =>
      schur_product
        (coordinateGaussianGramRep polynomial coordinateCount)
        (finiteGaussianGramRep polynomial coordinateCount)

@[simp] private theorem exponentAt_nil (coordinate : Nat) :
    exponentAt [] coordinate = 0 := by
  unfold exponentAt
  exact List.getD_nil

@[simp] private theorem exponentAt_cons_zero
    (head : Nat) (tail : List Nat) :
    exponentAt (head :: tail) 0 = head := by
  unfold exponentAt
  exact List.getD_cons_zero

@[simp] private theorem exponentAt_cons_succ
    (head : Nat) (tail : List Nat) (coordinate : Nat) :
    exponentAt (head :: tail) (coordinate + 1) =
      exponentAt tail coordinate := by
  unfold exponentAt
  exact List.getD_cons_succ

/-- Exponents add coordinatewise under raw monomial multiplication.  The
proof uses only the public `List.getD` equations, avoiding any choice-bearing
bounded-index machinery. -/
private theorem exponentAt_monoMul
    (left right : List Nat) (coordinate : Nat) :
    exponentAt (monoMul left right) coordinate =
      exponentAt left coordinate + exponentAt right coordinate := by
  induction left generalizing right coordinate with
  | nil =>
      simp only [monoMul, exponentAt_nil, Nat.zero_add]
  | cons head tail ih =>
      cases right with
      | nil =>
          simp only [monoMul, exponentAt_nil, Nat.add_zero]
      | cons other rest =>
          cases coordinate with
          | zero =>
              simp only [monoMul, exponentAt_cons_zero]
          | succ coordinate =>
              simp only [monoMul, exponentAt_cons_succ]
              exact ih rest coordinate

/-- The finite product kernel is exactly the finite product Gaussian moment
of the product of the two indexed monomials. -/
theorem finiteGaussianKernel_eq_monoMul
    (polynomial : RatPoly) (i j : Nat) : ∀ coordinateCount,
    finiteGaussianKernel polynomial coordinateCount i j ≈
      finiteGaussianMono coordinateCount
        (monoMul (termAt polynomial i).1 (termAt polynomial j).1)
  | 0 => Q'.eqv_refl 1
  | coordinateCount + 1 => by
      change
        gaussianMoment1
              (exponentAt (termAt polynomial i).1 coordinateCount +
                exponentAt (termAt polynomial j).1 coordinateCount) *
            finiteGaussianKernel polynomial coordinateCount i j ≈
          gaussianMoment1
              (exponentAt
                (monoMul (termAt polynomial i).1
                  (termAt polynomial j).1) coordinateCount) *
            finiteGaussianMono coordinateCount
              (monoMul (termAt polynomial i).1
                (termAt polynomial j).1)
      rw [exponentAt_monoMul]
      exact Q'.mul_eqv_congr_left _ _ _
        (finiteGaussianKernel_eq_monoMul polynomial i j coordinateCount)

/-! ## 2. The raw finite-dimensional Gaussian functional -/

/-- Ordinary coefficient-times-moment fold for the first `coordinateCount`
Gaussian coordinates.  Duplicate monomials are intentionally retained. -/
def finiteProductGaussian (coordinateCount : Nat) : RatPoly → Q'
  | [] => 0
  | term :: polynomial =>
      term.2 * finiteGaussianMono coordinateCount term.1 +
        finiteProductGaussian coordinateCount polynomial

/-- One row of the finite monomial-pair expansion. -/
def finiteGaussianRow (coordinateCount : Nat) (left : RatTerm) :
    RatPoly → Q'
  | [] => 0
  | right :: polynomial =>
      (left.2 * right.2) *
          finiteGaussianMono coordinateCount
            (monoMul left.1 right.1) +
        finiteGaussianRow coordinateCount left polynomial

/-- Raw finite bilinear product-Gaussian form in arbitrary dimension. -/
def finiteGaussianBilinear (coordinateCount : Nat) :
    RatPoly → RatPoly → Q'
  | [], _ => 0
  | left :: polynomial, right =>
      finiteGaussianRow coordinateCount left right +
        finiteGaussianBilinear coordinateCount polynomial right

theorem finiteProductGaussian_append (coordinateCount : Nat) :
    ∀ left right : RatPoly,
      finiteProductGaussian coordinateCount (left ++ right) ≈
        finiteProductGaussian coordinateCount left +
          finiteProductGaussian coordinateCount right
  | [], right => Q'.eqv_symm
      (QPoly.q_zero_add_eqv (finiteProductGaussian coordinateCount right))
  | term :: polynomial, right => by
      change
        term.2 * finiteGaussianMono coordinateCount term.1 +
            finiteProductGaussian coordinateCount (polynomial ++ right) ≈
          (term.2 * finiteGaussianMono coordinateCount term.1 +
              finiteProductGaussian coordinateCount polynomial) +
            finiteProductGaussian coordinateCount right
      refine Q'.eqv_trans _
        (term.2 * finiteGaussianMono coordinateCount term.1 +
          (finiteProductGaussian coordinateCount polynomial +
            finiteProductGaussian coordinateCount right)) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (finiteProductGaussian_append coordinateCount polynomial right)
      · exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem finiteProductGaussian_map_row
    (coordinateCount : Nat) (left : RatTerm) : ∀ right : RatPoly,
    finiteProductGaussian coordinateCount
        (right.map fun term =>
          (monoMul left.1 term.1, left.2 * term.2)) ≈
      finiteGaussianRow coordinateCount left right
  | [] => Q'.eqv_refl 0
  | term :: polynomial => by
      change
        (left.2 * term.2) *
              finiteGaussianMono coordinateCount
                (monoMul left.1 term.1) +
            finiteProductGaussian coordinateCount
              (polynomial.map fun other =>
                (monoMul left.1 other.1, left.2 * other.2)) ≈
          (left.2 * term.2) *
              finiteGaussianMono coordinateCount
                (monoMul left.1 term.1) +
            finiteGaussianRow coordinateCount left polynomial
      exact Q'.add_eqv_congr_left _ _ _
        (finiteProductGaussian_map_row coordinateCount left polynomial)

/-- Evaluating a raw polynomial product is exactly the finite bilinear form.
This statement is dimension-parametric and does not expand either polynomial. -/
theorem finiteProductGaussian_polyMul (coordinateCount : Nat) :
    ∀ left right : RatPoly,
      finiteProductGaussian coordinateCount (polyMul left right) ≈
        finiteGaussianBilinear coordinateCount left right
  | [], _ => Q'.eqv_refl 0
  | term :: polynomial, right => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (finiteProductGaussian coordinateCount
            (right.map fun other =>
              (monoMul term.1 other.1, term.2 * other.2)) +
          finiteProductGaussian coordinateCount
            (polyMul polynomial right)) _
        (finiteProductGaussian_append coordinateCount _ _) ?_
      exact QPoly.q_add_congr
        (finiteProductGaussian_map_row coordinateCount term right)
        (finiteProductGaussian_polyMul coordinateCount polynomial right)

private theorem finSum_finiteGaussianRow
    (coordinateCount : Nat) (left : RatTerm) : ∀ right : RatPoly,
    finSum (fun j =>
      (left.2 * (termAt right j).2) *
        finiteGaussianMono coordinateCount
          (monoMul left.1 (termAt right j).1)) right.length ≈
      finiteGaussianRow coordinateCount left right
  | [] => Q'.eqv_refl 0
  | term :: polynomial => by
      let f : Nat → Q' := fun j =>
        (left.2 * (termAt (term :: polynomial) j).2) *
          finiteGaussianMono coordinateCount
            (monoMul left.1 (termAt (term :: polynomial) j).1)
      refine Q'.eqv_trans _
        (f 0 + finSum (fun j => f (j + 1)) polynomial.length) _
        (finSum_head f polynomial.length) ?_
      refine QPoly.q_add_congr (Q'.eqv_refl _) ?_
      simpa [f, termAt] using
        finSum_finiteGaussianRow coordinateCount left polynomial

private theorem finSum_finiteGaussianBilinear
    (coordinateCount : Nat) : ∀ left right : RatPoly,
    finSum (fun i => finSum (fun j =>
      ((termAt left i).2 * (termAt right j).2) *
        finiteGaussianMono coordinateCount
          (monoMul (termAt left i).1 (termAt right j).1))
      right.length) left.length ≈
      finiteGaussianBilinear coordinateCount left right
  | [], _ => Q'.eqv_refl 0
  | term :: polynomial, right => by
      let f : Nat → Q' := fun i => finSum (fun j =>
        ((termAt (term :: polynomial) i).2 * (termAt right j).2) *
          finiteGaussianMono coordinateCount
            (monoMul (termAt (term :: polynomial) i).1
              (termAt right j).1)) right.length
      refine Q'.eqv_trans _
        (f 0 + finSum (fun i => f (i + 1)) polynomial.length) _
        (finSum_head f polynomial.length) ?_
      refine QPoly.q_add_congr ?_ ?_
      · simpa [f, termAt] using
          finSum_finiteGaussianRow coordinateCount term right
      · simpa [f, termAt] using
          finSum_finiteGaussianBilinear coordinateCount polynomial right

/-! ## 3. Arbitrary finite-dimensional square positivity -/

/-- **Dimension-uniform constructive Gaussian square theorem.**  For every
finite coordinate count and every raw rational polynomial, the corresponding
finite product-Gaussian functional is nonnegative on the raw square.

The witness is the recursive Hermite/Khatri--Rao Gram representation above;
no matrix factorization, spectral theorem, or fixed dimension is used. -/
theorem finiteProductGaussian_square_nonneg
    (coordinateCount : Nat) (polynomial : RatPoly) :
    (0 : Q') ≤
      finiteProductGaussian coordinateCount
        (polyMul polynomial polynomial) := by
  have hpositive := gramPSD_quadForm_nonneg
    (finiteGaussianGramRep polynomial coordinateCount)
    (fun i => (termAt polynomial i).2) polynomial.length
  have hkernel :
      gramQuadForm (finiteGaussianKernel polynomial coordinateCount)
          (fun i => (termAt polynomial i).2) polynomial.length ≈
        finiteGaussianBilinear coordinateCount polynomial polynomial := by
    unfold gramQuadForm
    refine Q'.eqv_trans _
      (finSum (fun i => finSum (fun j =>
        ((termAt polynomial i).2 * (termAt polynomial j).2) *
          finiteGaussianMono coordinateCount
            (monoMul (termAt polynomial i).1
              (termAt polynomial j).1))
        polynomial.length) polynomial.length) _ ?_ ?_
    · exact finSum_eqv_congr _ _ (fun i =>
        finSum_eqv_congr _ _ (fun j =>
          Q'.mul_eqv_congr_left _ _ _
            (finiteGaussianKernel_eq_monoMul
              polynomial i j coordinateCount))
          polynomial.length) polynomial.length
    · exact finSum_finiteGaussianBilinear
        coordinateCount polynomial polynomial
  have hevaluation :
      finiteProductGaussian coordinateCount
          (polyMul polynomial polynomial) ≈
        finiteGaussianBilinear coordinateCount polynomial polynomial :=
    finiteProductGaussian_polyMul coordinateCount polynomial polynomial
  have heq :
      finiteProductGaussian coordinateCount
          (polyMul polynomial polynomial) ≈
        gramQuadForm (finiteGaussianKernel polynomial coordinateCount)
          (fun i => (termAt polynomial i).2) polynomial.length :=
    Q'.eqv_trans _ _ _ hevaluation (Q'.eqv_symm hkernel)
  exact Q'.le_trans' _ _ _ hpositive
    (Q'.le_of_eqv (Q'.eqv_symm heq))

/-! ## 4. Quaternion-block specialization -/

/-- Product-Gaussian monomial moment for `blockCount` independent quaternion
blocks, laid out in four consecutive real coordinates per block. -/
def quaternionProductGaussianMono
    (blockCount : Nat) (monomial : List Nat) : Q' :=
  finiteGaussianMono (4 * blockCount) monomial

/-- Product-Gaussian polynomial functional for `blockCount` quaternion blocks. -/
def quaternionProductGaussian
    (blockCount : Nat) (polynomial : RatPoly) : Q' :=
  finiteProductGaussian (4 * blockCount) polynomial

/-- Lazy explicit Gram witness for the `4 * blockCount` coordinate kernel. -/
def quaternionProductGaussianGramRep
    (polynomial : RatPoly) (blockCount : Nat) :
    GramRep (finiteGaussianKernel polynomial (4 * blockCount)) :=
  finiteGaussianGramRep polynomial (4 * blockCount)

/-- Gaussian square positivity for every finite family of quaternion blocks. -/
theorem quaternionProductGaussian_square_nonneg
    (blockCount : Nat) (polynomial : RatPoly) :
    (0 : Q') ≤
      quaternionProductGaussian blockCount
        (polyMul polynomial polynomial) := by
  exact finiteProductGaussian_square_nonneg (4 * blockCount) polynomial

/-! ## 5. Regression to the established two-block/eight-coordinate carrier -/

private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero];
             try ac_rfl))

/-- The generic eight-coordinate monomial moment agrees with the historical
two-quaternion product-Gaussian monomial moment. -/
theorem finiteGaussianMono_eight_eqv_productGaussianMono
    (monomial : List Nat) :
    finiteGaussianMono 8 monomial ≈ productGaussianMono monomial := by
  refine Q'.eqv_trans _ (gaussianMoment8 monomial) _ ?_ ?_
  · simp only [finiteGaussianMono]
    unfold gaussianMoment8
    ring_qeqv
  · exact Q'.eqv_symm (productGaussianMono_eq_tensor monomial)

/-- At eight coordinates the dimension-uniform polynomial functional is the
established two-quaternion product-Gaussian functional. -/
theorem finiteProductGaussian_eight_eqv_productGaussian :
    ∀ polynomial : RatPoly,
      finiteProductGaussian 8 polynomial ≈ productGaussian polynomial
  | [] => Q'.eqv_refl 0
  | term :: polynomial => by
      change
        term.2 * finiteGaussianMono 8 term.1 +
            finiteProductGaussian 8 polynomial ≈
          term.2 * productGaussianMono term.1 +
            productGaussian polynomial
      exact QPoly.q_add_congr
        (Q'.mul_eqv_congr_left _ _ _
          (finiteGaussianMono_eight_eqv_productGaussianMono term.1))
        (finiteProductGaussian_eight_eqv_productGaussian polynomial)

/-- The historical eight-coordinate square theorem is recovered as the
`coordinateCount = 8` instance of the dimension-uniform result. -/
theorem productGaussian_square_nonneg_from_finite
    (polynomial : RatPoly) :
    (0 : Q') ≤ productGaussian (polyMul polynomial polynomial) := by
  have hpositive := finiteProductGaussian_square_nonneg 8 polynomial
  exact Q'.le_trans' _ _ _ hpositive
    (Q'.le_of_eqv
      (finiteProductGaussian_eight_eqv_productGaussian
        (polyMul polynomial polynomial)))

end YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity

#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity.finiteGaussianGramRep
#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity.finiteProductGaussian_polyMul
#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity.finiteProductGaussian_square_nonneg
#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity.quaternionProductGaussian_square_nonneg
#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity.productGaussian_square_nonneg_from_finite
