/-
# Arbitrary eight-variable product-Gaussian square positivity

The eight coordinate Hermite Gram witnesses are combined by seven explicit
constructive Schur products.  The resulting Gram quadratic form is identified
term-for-term with the raw `RatPoly` product-Gaussian evaluation of `p * p`.
-/

import YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram

namespace YMGap.Continuum.SU2QuaternionProductGaussianPositivity

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarGaussianRadialFactor
open YMGap.Continuum.SU2QuaternionProductGaussianTensor
open YMGap.Continuum.SU2QuaternionProductGaussianHermiteGram
open YMGap.Continuum.SchurHadamardTransfer

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- The right-associated product of the eight coordinate moment kernels. -/
def eightGaussianKernel (p : RatPoly) (i j : Nat) : Q' :=
  coordinateGaussianKernel p 0 i j *
    (coordinateGaussianKernel p 1 i j *
      (coordinateGaussianKernel p 2 i j *
        (coordinateGaussianKernel p 3 i j *
          (coordinateGaussianKernel p 4 i j *
            (coordinateGaussianKernel p 5 i j *
              (coordinateGaussianKernel p 6 i j *
                coordinateGaussianKernel p 7 i j))))))

/-- Explicit eight-fold Khatri--Rao/Hermite Gram witness. -/
def eightGaussianGramRep (p : RatPoly) : GramRep (eightGaussianKernel p) :=
  schur_product (coordinateGaussianGramRep p 0)
    (schur_product (coordinateGaussianGramRep p 1)
      (schur_product (coordinateGaussianGramRep p 2)
        (schur_product (coordinateGaussianGramRep p 3)
          (schur_product (coordinateGaussianGramRep p 4)
            (schur_product (coordinateGaussianGramRep p 5)
              (schur_product (coordinateGaussianGramRep p 6)
                (coordinateGaussianGramRep p 7)))))))

theorem eightGaussianKernel_eq_productMono (p : RatPoly) (i j : Nat) :
    eightGaussianKernel p i j ≈
      productGaussianMono (monoMul (termAt p i).1 (termAt p j).1) := by
  exact Q'.eqv_symm (productGaussianMono_mul_tensor
    (termAt p i).1 (termAt p j).1)

/-- One row of the raw monomial-pair expansion. -/
def gaussianRow (s : RatTerm) : RatPoly → Q'
  | [] => 0
  | t :: q =>
      (s.2 * t.2) * productGaussianMono (monoMul s.1 t.1) + gaussianRow s q

/-- The raw finite bilinear product-Gaussian form. -/
def gaussianBilinear : RatPoly → RatPoly → Q'
  | [], _ => 0
  | s :: p, q => gaussianRow s q + gaussianBilinear p q

theorem productGaussian_append : ∀ p q : RatPoly,
    productGaussian (p ++ q) ≈ productGaussian p + productGaussian q
  | [], q => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | t :: p, q => by
      change t.2 * productGaussianMono t.1 + productGaussian (p ++ q) ≈
        (t.2 * productGaussianMono t.1 + productGaussian p) + productGaussian q
      refine Q'.eqv_trans _
        (t.2 * productGaussianMono t.1 +
          (productGaussian p + productGaussian q)) _
        (Q'.add_eqv_congr_left _ _ _ (productGaussian_append p q)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)

private theorem productGaussian_map_row (s : RatTerm) : ∀ q : RatPoly,
    productGaussian
      (q.map fun t => (monoMul s.1 t.1, s.2 * t.2)) ≈ gaussianRow s q
  | [] => Q'.eqv_refl 0
  | t :: q => by
      change (s.2 * t.2) * productGaussianMono (monoMul s.1 t.1) +
          productGaussian
            (q.map fun u => (monoMul s.1 u.1, s.2 * u.2)) ≈
        (s.2 * t.2) * productGaussianMono (monoMul s.1 t.1) + gaussianRow s q
      exact Q'.add_eqv_congr_left _ _ _ (productGaussian_map_row s q)

theorem productGaussian_polyMul : ∀ p q : RatPoly,
    productGaussian (polyMul p q) ≈ gaussianBilinear p q
  | [], _ => Q'.eqv_refl 0
  | s :: p, q => by
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (productGaussian
            (q.map fun t => (monoMul s.1 t.1, s.2 * t.2)) +
          productGaussian (polyMul p q)) _
        (productGaussian_append _ _) ?_
      exact QPoly.q_add_congr
        (productGaussian_map_row s q) (productGaussian_polyMul p q)

private theorem finSum_row (s : RatTerm) : ∀ q : RatPoly,
    finSum (fun j =>
      (s.2 * (termAt q j).2) *
        productGaussianMono (monoMul s.1 (termAt q j).1)) q.length ≈
      gaussianRow s q
  | [] => Q'.eqv_refl 0
  | t :: q => by
      let f : Nat → Q' := fun j =>
        (s.2 * (termAt (t :: q) j).2) *
          productGaussianMono (monoMul s.1 (termAt (t :: q) j).1)
      refine Q'.eqv_trans _ (f 0 + finSum (fun j => f (j + 1)) q.length) _
        (finSum_head f q.length) ?_
      refine QPoly.q_add_congr (Q'.eqv_refl _) ?_
      simpa [f, termAt] using finSum_row s q

private theorem finSum_bilinear : ∀ p q : RatPoly,
    finSum (fun i => finSum (fun j =>
      ((termAt p i).2 * (termAt q j).2) *
        productGaussianMono (monoMul (termAt p i).1 (termAt q j).1))
      q.length) p.length ≈ gaussianBilinear p q
  | [], _ => Q'.eqv_refl 0
  | s :: p, q => by
      let f : Nat → Q' := fun i => finSum (fun j =>
        ((termAt (s :: p) i).2 * (termAt q j).2) *
          productGaussianMono
            (monoMul (termAt (s :: p) i).1 (termAt q j).1)) q.length
      refine Q'.eqv_trans _ (f 0 + finSum (fun i => f (i + 1)) p.length) _
        (finSum_head f p.length) ?_
      refine QPoly.q_add_congr ?_ ?_
      · simpa [f, termAt] using finSum_row s q
      · simpa [f, termAt] using finSum_bilinear p q

/-- **Direct arbitrary eight-variable square theorem.**  The raw finite
`RatPoly` product-Gaussian functional is nonnegative on every square. -/
theorem productGaussian_square_nonneg (p : RatPoly) :
    (0 : Q') ≤ productGaussian (polyMul p p) := by
  have hpos := gramPSD_quadForm_nonneg (eightGaussianGramRep p)
    (fun i => (termAt p i).2) p.length
  have hkernel : gramQuadForm (eightGaussianKernel p)
      (fun i => (termAt p i).2) p.length ≈ gaussianBilinear p p := by
    unfold gramQuadForm
    refine Q'.eqv_trans _
      (finSum (fun i => finSum (fun j =>
        ((termAt p i).2 * (termAt p j).2) *
          productGaussianMono (monoMul (termAt p i).1 (termAt p j).1))
        p.length) p.length) _ ?_ ?_
    · exact finSum_eqv_congr _ _ (fun i =>
        finSum_eqv_congr _ _ (fun j =>
          Q'.mul_eqv_congr_left _ _ _
            (eightGaussianKernel_eq_productMono p i j)) p.length) p.length
    · exact finSum_bilinear p p
  have heval : productGaussian (polyMul p p) ≈ gaussianBilinear p p :=
    productGaussian_polyMul p p
  have heq : productGaussian (polyMul p p) ≈
      gramQuadForm (eightGaussianKernel p)
        (fun i => (termAt p i).2) p.length :=
    Q'.eqv_trans _ _ _ heval (Q'.eqv_symm hkernel)
  exact Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv (Q'.eqv_symm heq))

end YMGap.Continuum.SU2QuaternionProductGaussianPositivity

#print axioms YMGap.Continuum.SU2QuaternionProductGaussianPositivity.eightGaussianGramRep
#print axioms YMGap.Continuum.SU2QuaternionProductGaussianPositivity.productGaussian_polyMul
#print axioms YMGap.Continuum.SU2QuaternionProductGaussianPositivity.productGaussian_square_nonneg
