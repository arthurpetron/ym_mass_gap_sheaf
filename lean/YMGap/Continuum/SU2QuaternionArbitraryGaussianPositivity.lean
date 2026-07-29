/-
# Arbitrary-coordinate product-Gaussian positivity

The original quaternion-Haar positivity proof exposed an eight-coordinate
Gaussian tensor because it was written for two quaternion factors.  The BF4
endpoint has ten factors, hence forty coordinates.  This module removes the
fixed-eight restriction at the Gaussian layer.

For every finite number `coordinates`, the product moment

  `prod_{r < coordinates} E[X_r^(monomial_r)]`

is represented by an explicit iterated Schur product of the existing
one-coordinate Hermite Gram witnesses.  Consequently its value on the square
of every finite rational polynomial is nonnegative.  The number of
coordinates is data, not a theorem parameter hidden behind an existence
claim.

No classical spectral theorem, choice, or approximation is used.
-/

import YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram

namespace YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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

/-- Product of consecutive one-dimensional Gaussian monomial moments. -/
def gaussianMomentRange (start : Nat) : Nat → List Nat → Q'
  | 0, _ => 1
  | coordinates + 1, monomial =>
      gaussianMoment1 (exponentAt monomial start) *
        gaussianMomentRange (start + 1) coordinates monomial

/-- Product-Gaussian monomial moment in the first `coordinates` variables. -/
def arbitraryGaussianMono (coordinates : Nat) (monomial : List Nat) : Q' :=
  gaussianMomentRange 0 coordinates monomial

/-- Exact finite product-Gaussian functional. -/
def arbitraryGaussian (coordinates : Nat) : RatPoly → Q'
  | [] => 0
  | term :: rest =>
      term.2 * arbitraryGaussianMono coordinates term.1 +
        arbitraryGaussian coordinates rest

/-- Four consecutive one-dimensional Gaussian moments reproduce the
four-coordinate moment used by the sphere radial-factor theorem. -/
theorem gaussianMoment4_eq_tensor
    (e0 e1 e2 e3 : Nat) :
    gaussianMoment4 e0 e1 e2 e3 ≈
      gaussianMoment1 e0 *
        (gaussianMoment1 e1 *
          (gaussianMoment1 e2 *
            gaussianMoment1 e3)) := by
  have h := productGaussianMono_eq_tensor [e0, e1, e2, e3]
  have hleft :
      productGaussianMono [e0, e1, e2, e3] ≈
        gaussianMoment4 e0 e1 e2 e3 := by
    unfold productGaussianMono
    change
      gaussianMoment4 e0 e1 e2 e3 *
          gaussianMoment4 0 0 0 0 ≈
        gaussianMoment4 e0 e1 e2 e3
    have hzero :
        gaussianMoment4 0 0 0 0 = (1 : Q') := by
      decide
    rw [hzero]
    exact Q'.mul_one_eqv _
  have hright :
      gaussianMoment8 [e0, e1, e2, e3] ≈
        gaussianMoment1 e0 *
          (gaussianMoment1 e1 *
            (gaussianMoment1 e2 *
              gaussianMoment1 e3)) := by
    unfold gaussianMoment8
    change
      gaussianMoment1 e0 *
          (gaussianMoment1 e1 *
            (gaussianMoment1 e2 *
              (gaussianMoment1 e3 *
                (gaussianMoment1 0 *
                  (gaussianMoment1 0 *
                    (gaussianMoment1 0 *
                      gaussianMoment1 0)))))) ≈
        gaussianMoment1 e0 *
          (gaussianMoment1 e1 *
            (gaussianMoment1 e2 *
              gaussianMoment1 e3))
    have hzero :
        gaussianMoment1 0 = (1 : Q') := by
      decide
    rw [hzero]
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_one_eqv 1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_one_eqv 1)) ?_
    exact Q'.mul_one_eqv _
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ h hright)

private theorem exponentAt_monoMul
    (left right : List Nat) (index : Nat) :
    exponentAt (monoMul left right) index =
      exponentAt left index + exponentAt right index := by
  induction left generalizing right index with
  | nil => simp [monoMul, exponentAt]
  | cons x xs ih =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons y ys =>
          cases index with
          | zero => simp [monoMul, exponentAt]
          | succ index =>
              change exponentAt (monoMul xs ys) index =
                exponentAt xs index + exponentAt ys index
              exact ih ys index

/-- The product kernel over a consecutive coordinate window. -/
def gaussianRangeKernel
    (polynomial : RatPoly) (start : Nat) :
    Nat → Nat → Nat → Q'
  | 0, _, _ => 1
  | coordinates + 1, i, j =>
      coordinateGaussianKernel polynomial start i j *
        gaussianRangeKernel polynomial (start + 1) coordinates i j

/-- Constructive Gram witness for every finite coordinate window. -/
def gaussianRangeGramRep
    (polynomial : RatPoly) (start : Nat) :
    ∀ coordinates,
      GramRep
        (gaussianRangeKernel polynomial start coordinates)
  | 0 => onesGramRep
  | coordinates + 1 =>
      schur_product
        (coordinateGaussianGramRep polynomial start)
        (gaussianRangeGramRep polynomial (start + 1) coordinates)

theorem gaussianRangeKernel_eq_moment
    (polynomial : RatPoly) (start : Nat) :
    ∀ (coordinates i j : Nat),
      gaussianRangeKernel polynomial start coordinates i j ≈
        gaussianMomentRange start coordinates
          (monoMul
            (termAt polynomial i).1
            (termAt polynomial j).1)
  | 0, i, j => Q'.eqv_refl 1
  | coordinates + 1, i, j => by
      unfold gaussianRangeKernel gaussianMomentRange
      unfold coordinateGaussianKernel
      rw [exponentAt_monoMul]
      exact Q'.mul_eqv_congr_left _ _ _
        (gaussianRangeKernel_eq_moment
          polynomial (start + 1) coordinates i j)

private def transportGramRep
    {matrix transported : Nat → Nat → Q'}
    (representation : GramRep matrix)
    (entrywise :
      ∀ i j, transported i j ≈ matrix i j) :
    GramRep transported where
  r := representation.r
  d := representation.d
  hd := representation.hd
  v := representation.v
  hM := fun i j =>
    Q'.eqv_trans _ _ _
      (entrywise i j)
      (representation.hM i j)

/-- The arbitrary-coordinate moment kernel is a genuine finite Gram matrix. -/
def arbitraryGaussianGramRep
    (polynomial : RatPoly) (coordinates : Nat) :
    GramRep
      (fun i j =>
        arbitraryGaussianMono coordinates
          (monoMul
            (termAt polynomial i).1
            (termAt polynomial j).1)) :=
  transportGramRep
    (gaussianRangeGramRep polynomial 0 coordinates)
    (fun i j =>
      Q'.eqv_symm
        (gaussianRangeKernel_eq_moment
          polynomial 0 coordinates i j))

/-- One row of the raw monomial-pair expansion. -/
def arbitraryGaussianRow
    (coordinates : Nat) (source : RatTerm) :
    RatPoly → Q'
  | [] => 0
  | target :: rest =>
      (source.2 * target.2) *
          arbitraryGaussianMono coordinates
            (monoMul source.1 target.1) +
        arbitraryGaussianRow coordinates source rest

/-- Raw bilinear product-Gaussian fold. -/
def arbitraryGaussianBilinear
    (coordinates : Nat) :
    RatPoly → RatPoly → Q'
  | [], _ => 0
  | source :: rest, target =>
      arbitraryGaussianRow coordinates source target +
        arbitraryGaussianBilinear coordinates rest target

private theorem arbitraryGaussian_append
    (coordinates : Nat) :
    ∀ left right : RatPoly,
      arbitraryGaussian coordinates (left ++ right) ≈
        arbitraryGaussian coordinates left +
          arbitraryGaussian coordinates right
  | [], right =>
      Q'.eqv_symm
        (QPoly.q_zero_add_eqv
          (arbitraryGaussian coordinates right))
  | term :: rest, right => by
      change
        term.2 * arbitraryGaussianMono coordinates term.1 +
            arbitraryGaussian coordinates (rest ++ right) ≈
          (term.2 * arbitraryGaussianMono coordinates term.1 +
              arbitraryGaussian coordinates rest) +
            arbitraryGaussian coordinates right
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (arbitraryGaussian_append coordinates rest right)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem arbitraryGaussian_map_row
    (coordinates : Nat) (source : RatTerm) :
    ∀ target : RatPoly,
      arbitraryGaussian coordinates
          (target.map fun term =>
            (monoMul source.1 term.1,
              source.2 * term.2)) ≈
        arbitraryGaussianRow coordinates source target
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (source.2 * term.2) *
              arbitraryGaussianMono coordinates
                (monoMul source.1 term.1) +
            arbitraryGaussian coordinates
              (rest.map fun target =>
                (monoMul source.1 target.1,
                  source.2 * target.2)) ≈
          (source.2 * term.2) *
              arbitraryGaussianMono coordinates
                (monoMul source.1 term.1) +
            arbitraryGaussianRow coordinates source rest
      exact Q'.add_eqv_congr_left _ _ _
        (arbitraryGaussian_map_row coordinates source rest)

/-- Multiplying polynomials realizes the raw Gaussian bilinear form. -/
theorem arbitraryGaussian_polyMul
    (coordinates : Nat) :
    ∀ left right : RatPoly,
      arbitraryGaussian coordinates (polyMul left right) ≈
        arbitraryGaussianBilinear coordinates left right
  | [], _ => Q'.eqv_refl 0
  | source :: rest, right => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (arbitraryGaussian coordinates
            (right.map fun target =>
              (monoMul source.1 target.1,
                source.2 * target.2)) +
          arbitraryGaussian coordinates (polyMul rest right)) _
        (arbitraryGaussian_append coordinates _ _) ?_
      exact QPoly.q_add_congr
        (arbitraryGaussian_map_row coordinates source right)
        (arbitraryGaussian_polyMul coordinates rest right)

private theorem finSum_row
    (coordinates : Nat) (source : RatTerm) :
    ∀ target : RatPoly,
      finSum
          (fun j =>
            (source.2 * (termAt target j).2) *
              arbitraryGaussianMono coordinates
                (monoMul source.1 (termAt target j).1))
          target.length ≈
        arbitraryGaussianRow coordinates source target
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      let f : Nat → Q' := fun j =>
        (source.2 * (termAt (term :: rest) j).2) *
          arbitraryGaussianMono coordinates
            (monoMul source.1
              (termAt (term :: rest) j).1)
      refine Q'.eqv_trans _
        (f 0 + finSum (fun j => f (j + 1)) rest.length) _
        (finSum_head f rest.length) ?_
      exact QPoly.q_add_congr
        (Q'.eqv_refl _)
        (by
          simpa [f, termAt] using
            finSum_row coordinates source rest)

private theorem finSum_bilinear
    (coordinates : Nat) :
    ∀ left right : RatPoly,
      finSum
          (fun i =>
            finSum
              (fun j =>
                ((termAt left i).2 *
                    (termAt right j).2) *
                  arbitraryGaussianMono coordinates
                    (monoMul
                      (termAt left i).1
                      (termAt right j).1))
              right.length)
          left.length ≈
        arbitraryGaussianBilinear coordinates left right
  | [], _ => Q'.eqv_refl 0
  | source :: rest, right => by
      let f : Nat → Q' := fun i =>
        finSum
          (fun j =>
            ((termAt (source :: rest) i).2 *
                (termAt right j).2) *
              arbitraryGaussianMono coordinates
                (monoMul
                  (termAt (source :: rest) i).1
                  (termAt right j).1))
          right.length
      refine Q'.eqv_trans _
        (f 0 + finSum (fun i => f (i + 1)) rest.length) _
        (finSum_head f rest.length) ?_
      exact QPoly.q_add_congr
        (by
          simpa [f, termAt] using
            finSum_row coordinates source right)
        (by
          simpa [f, termAt] using
            finSum_bilinear coordinates rest right)

/-- The product-Gaussian functional in any finite number of coordinates is
nonnegative on every rational polynomial square. -/
theorem arbitraryGaussian_square_nonnegative
    (coordinates : Nat) (polynomial : RatPoly) :
    (0 : Q') ≤
      arbitraryGaussian coordinates
        (polyMul polynomial polynomial) := by
  let kernel : Nat → Nat → Q' := fun i j =>
    arbitraryGaussianMono coordinates
      (monoMul
        (termAt polynomial i).1
        (termAt polynomial j).1)
  have hpositive :
      (0 : Q') ≤
        gramQuadForm kernel
          (fun i => (termAt polynomial i).2)
          polynomial.length :=
    gramPSD_quadForm_nonneg
      (arbitraryGaussianGramRep polynomial coordinates)
      (fun i => (termAt polynomial i).2)
      polynomial.length
  have hkernel :
      gramQuadForm kernel
          (fun i => (termAt polynomial i).2)
          polynomial.length ≈
        arbitraryGaussianBilinear
          coordinates polynomial polynomial := by
    unfold gramQuadForm kernel
    exact finSum_bilinear
      coordinates polynomial polynomial
  have hevaluation :
      arbitraryGaussian coordinates
          (polyMul polynomial polynomial) ≈
        arbitraryGaussianBilinear
          coordinates polynomial polynomial :=
    arbitraryGaussian_polyMul
      coordinates polynomial polynomial
  exact Q'.le_trans' _ _ _ hpositive
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        hkernel
        (Q'.eqv_symm hevaluation)))

end YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity

#print axioms YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity.gaussianRangeKernel_eq_moment
#print axioms YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity.arbitraryGaussianGramRep
#print axioms YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity.arbitraryGaussian_polyMul
#print axioms YMGap.Continuum.SU2QuaternionArbitraryGaussianPositivity.arbitraryGaussian_square_nonnegative
