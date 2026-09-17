/-
# Exact ordinary-Haar square budget for the constructed telescope

Successive conditional Haar projections split the input square into the
squares of the existing explicit telescope terms and the final projection
square. Dropping only that nonnegative final square gives a coefficient-one
bound, with no factor counting the coordinates.

This is an ordinary-Haar identity. It does not assert orthogonality after
inverse-density conjugation or supply a uniform interacting-energy bound.
-/

import YMGap.Continuum.SU2QuaternionHaarBlockTelescope

namespace YMGap.Continuum.SU2QuaternionHaarBlockTelescopeNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (square_decomposition)
open YMGap.Continuum.SU2QuaternionHaarBlockTelescope
  (partialProjection partialProjection_succ partialProjection_supported term)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem sum_append : ∀ xs ys : List Q',
    qListSum (xs ++ ys) ≈ qListSum xs + qListSum ys
  | [], ys => Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (qListSum ys)))
  | x :: xs, ys =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl x) (sum_append xs ys))
        (Q'.eqv_symm (Q'.add_assoc_eqv x (qListSum xs) (qListSum ys)))

private theorem sum_range_succ (f : Nat → Q') (count : Nat) :
    qListSum ((List.range (count + 1)).map f) ≈
      qListSum ((List.range count).map f) + f count := by
  rw [List.range_succ, List.map_append]
  exact Q'.eqv_trans _ _ _ (sum_append _ _)
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_of_eq (Q'.add_zero' (f count))))

/-- Exact Pythagoras through any in-range initial coordinate segment.
The endpoint square is retained, including when count or blocks is zero. -/
theorem telescope_pythagoras (blocks count : Nat) (hc : count ≤ blocks)
    (p : RatPoly) :
    quaternionHaar blocks (polyMul p p) ≈
      qListSum ((List.range count).map (fun i =>
        quaternionHaar blocks (polyMul (term i p) (term i p)))) +
      quaternionHaar blocks
        (polyMul (partialProjection count p) (partialProjection count p)) := by
  induction count with
  | zero =>
      exact Q'.eqv_symm
        (Q'.eqv_of_eq (Q'.zero_add' (quaternionHaar blocks (polyMul p p))))
  | succ count ih =>
      let s := qListSum ((List.range count).map (fun i =>
        quaternionHaar blocks (polyMul (term i p) (term i p))))
      let a := quaternionHaar blocks (polyMul (term count p) (term count p))
      let r := quaternionHaar blocks
        (polyMul (partialProjection (count + 1) p) (partialProjection (count + 1) p))
      have hstep : quaternionHaar blocks
          (polyMul (partialProjection count p) (partialProjection count p)) ≈ r + a := by
        simpa only [r, a, term, partialProjection_succ] using
          (square_decomposition blocks count (by omega) (partialProjection count p))
      have hfull : quaternionHaar blocks (polyMul p p) ≈ s + (r + a) :=
        Q'.eqv_trans _ _ _ (ih (by omega))
          (Q'.add_eqv_congr' (Q'.eqv_refl s) hstep)
      have horder : s + (r + a) ≈ (s + a) + r :=
        Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl s) (Q'.add_comm_eqv r a))
          (Q'.eqv_symm (Q'.add_assoc_eqv s a r))
      exact Q'.eqv_trans _ _ _ hfull
        (Q'.eqv_trans _ _ _ horder
          (Q'.add_eqv_congr'
            (Q'.eqv_symm (sum_range_succ (fun i =>
              quaternionHaar blocks (polyMul (term i p) (term i p))) count))
            (Q'.eqv_refl r)))

/-- The actual sum of term squares is bounded without a coordinate-count loss. -/
theorem term_square_sum_le (blocks count : Nat) (hc : count ≤ blocks)
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    qListSum ((List.range count).map (fun i =>
      quaternionHaar blocks (polyMul (term i p) (term i p)))) ≤
      quaternionHaar blocks (polyMul p p) := by
  have hr : (0 : Q') ≤ quaternionHaar blocks
      (polyMul (partialProjection count p) (partialProjection count p)) :=
    (Certificate.square (partialProjection count p)
      (partialProjection_supported count hp)).haar_nonnegative
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hr)
    (Q'.ge_of_eqv (telescope_pythagoras blocks count hc p))

/-- Full original-coordinate specialization for the finite seed-family consumer. -/
theorem full_term_square_sum_le (blocks : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) :
    qListSum ((List.range blocks).map (fun i =>
      quaternionHaar blocks (polyMul (term i p) (term i p)))) ≤
      quaternionHaar blocks (polyMul p p) :=
  term_square_sum_le blocks blocks (Nat.le_refl blocks) p hp

end YMGap.Continuum.SU2QuaternionHaarBlockTelescopeNorm

#print axioms YMGap.Continuum.SU2QuaternionHaarBlockTelescopeNorm.telescope_pythagoras
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockTelescopeNorm.term_square_sum_le
#print axioms YMGap.Continuum.SU2QuaternionHaarBlockTelescopeNorm.full_term_square_sum_le
