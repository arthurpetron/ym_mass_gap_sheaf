/-
Normalized monotonicity of the actual cubic theta carrier.

The predecessor gives the positive-reserve polynomial crossing identity and
proves that multiplication by `(k+2)^3` converts the actual harmonic cubic
carrier into that polynomial exactly.  This successor transports the order
back through the positive denominator cube.  The result is division-free:

  `(n+1) R_k(n) <= n R_k(n+1)`.

This is the one-crossing invariant needed by the cumulative prefix proof.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCrossing

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierMonotone

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCrossing
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Polynomial evaluation respects equivalence of its mode argument. -/
theorem thetaCubicSlopePolynomial_eqv_congr_mode (D N M : Q')
    (hNM : N ≈ M) :
    thetaCubicSlopePolynomial D N ≈ thetaCubicSlopePolynomial D M := by
  have hNp1 : N + 1 ≈ M + 1 :=
    Q'.add_eqv_congr_right N M 1 hNM
  have hneg : -N ≈ -M := Q'.neg_eqv_congr N M hNM
  have hDm : D + -N ≈ D + -M :=
    Q'.add_eqv_congr_left D _ _ hneg
  have hsq : (D + -N) * (D + -N) ≈
      (D + -M) * (D + -M) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (D + -N) hDm) ?_
    exact Q'.mul_eqv_congr_left (D + -M) _ _ hDm
  have htail :
      (D + -1) * ((D + -N) * (D + -N)) ≈
        (D + -1) * ((D + -M) * (D + -M)) :=
    Q'.mul_eqv_congr_left (D + -1) _ _ hsq
  have hweighted :
      (N + 1) * ((D + -1) * ((D + -N) * (D + -N))) ≈
        (M + 1) * ((D + -1) * ((D + -M) * (D + -M))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _
        ((D + -1) * ((D + -N) * (D + -N))) hNp1) ?_
    exact Q'.mul_eqv_congr_left (M + 1) _ _ htail
  have hfirst : N * qcube D ≈ M * qcube D :=
    Q'.mul_eqv_congr_right N M (qcube D) hNM
  unfold thetaCubicSlopePolynomial
  exact Q'.add_eqv_congr' hfirst
    (Q'.neg_eqv_congr _ _ hweighted)

/-- Nat-indexed form of the polynomial normalized-slope inequality.  The
`ofNat (n+1)` representation is retained on both sides so it can be combined
directly with the actual harmonic carrier. -/
theorem thetaCubicSlopePolynomial_normalized_mono_nat {k n : Nat}
    (hn : n + 1 ≤ k + 2) :
    Q'.ofNat (n + 1) *
        thetaCubicSlopePolynomial (Q'.ofNat (k + 2)) (Q'.ofNat n) ≤
      Q'.ofNat n *
        thetaCubicSlopePolynomial (Q'.ofNat (k + 2)) (Q'.ofNat (n + 1)) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  have hNp1 : Q'.ofNat (n + 1) ≈ N + 1 := by
    dsimp only [N]
    exact Q'.ofNat_add_eqv n 1
  have hD : (1 : Q') ≤ D := by
    dsimp only [D]
    show (1 : Int) * (((Q'.ofNat (k + 2)).den : Nat) : Int) ≤
      (Q'.ofNat (k + 2)).num * (((1 : Q').den : Nat) : Int)
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      show ((1 : Q').den : Int) = 1 from rfl,
      Int.mul_one]
    exact_mod_cast (show 1 ≤ k + 2 by omega)
  have hN : (0 : Q') ≤ N := by
    dsimp only [N]
    exact zero_le_ofNat n
  have hNat : Q'.ofNat (n + 1) ≤ D := by
    dsimp only [D]
    exact CReal.ofNat_le_ofNat hn
  have hND : N + 1 ≤ D :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hNp1)) hNat
  have hmono := thetaCubicSlopePolynomial_normalized_mono hD hN hND
  have hnext := thetaCubicSlopePolynomial_eqv_congr_mode
    D (Q'.ofNat (n + 1)) (N + 1) hNp1
  have hleft :
      Q'.ofNat (n + 1) * thetaCubicSlopePolynomial D N ≤
        (N + 1) * thetaCubicSlopePolynomial D N :=
    Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ (thetaCubicSlopePolynomial D N) hNp1)
  have hright :
      N * thetaCubicSlopePolynomial D (N + 1) ≤
        N * thetaCubicSlopePolynomial D (Q'.ofNat (n + 1)) :=
    Q'.le_of_eqv
      (Q'.mul_eqv_congr_left N _ _ (Q'.eqv_symm hnext))
  dsimp only [D, N] at hleft hmono hright ⊢
  exact Q'.le_trans' _ _ _ hleft
    (Q'.le_trans' _ _ _ hmono hright)

/-- **Actual all-scale normalized monotonicity.**  The cubic carrier divided
by its positive mode is monotone on every harmonic scale, stated without any
division.  This theorem is uniform in `k`; the only range condition is the
natural one that the next mode not exceed the harmonic denominator. -/
theorem thetaCubicRightCarrier_normalized_mono {k n : Nat}
    (hn : n + 1 ≤ k + 2) :
    Q'.ofNat (n + 1) * thetaCubicRightCarrier k n ≤
      Q'.ofNat n * thetaCubicRightCarrier k (n + 1) := by
  let D := Q'.ofNat (k + 2)
  let C := qcube D
  have hpoly := thetaCubicSlopePolynomial_normalized_mono_nat hn
  have hnscale := thetaCubicRightCarrier_mul_denCube k n
  have hnextscale := thetaCubicRightCarrier_mul_denCube k (n + 1)
  have hleft :
      (Q'.ofNat (n + 1) * thetaCubicRightCarrier k n) * C ≈
        Q'.ofNat (n + 1) *
          thetaCubicSlopePolynomial D (Q'.ofNat n) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (n + 1))
        (thetaCubicRightCarrier k n) C) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat (n + 1)) _ _ hnscale
  have hright :
      (Q'.ofNat n * thetaCubicRightCarrier k (n + 1)) * C ≈
        Q'.ofNat n *
          thetaCubicSlopePolynomial D (Q'.ofNat (n + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat n)
        (thetaCubicRightCarrier k (n + 1)) C) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat n) _ _ hnextscale
  have hmul :
      (Q'.ofNat (n + 1) * thetaCubicRightCarrier k n) * C ≤
        (Q'.ofNat n * thetaCubicRightCarrier k (n + 1)) * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hpoly
        (Q'.le_of_eqv (Q'.eqv_symm hright)))
  have hDpos : (0 : Q') < D := by
    dsimp only [D]
    exact Q'.ofNat_succ_pos (k + 1)
  have hCpos : (0 : Q') < C := by
    dsimp only [C]
    unfold qcube
    exact Q'.mul_pos (Q'.mul_pos hDpos hDpos) hDpos
  exact BakryEmery.le_of_mul_le_mul_right_pos hCpos hmul

#print axioms thetaCubicSlopePolynomial_eqv_congr_mode
#print axioms thetaCubicSlopePolynomial_normalized_mono_nat
#print axioms thetaCubicRightCarrier_normalized_mono

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierMonotone
