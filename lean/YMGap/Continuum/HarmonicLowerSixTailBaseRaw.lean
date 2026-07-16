/-
# Public N,D raw polynomial for the frozen lower-six Base certificate

This module identifies the diagonal projective evaluator used by the positive
Bernstein certificate with its sparse N,D power polynomial.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseCertificate
import YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms
import YMGap.Continuum.RawGridSemanticTransport
import YMGap.Continuum.TensorBernsteinHomogeneousCertificate

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificate
open YMGap.Continuum.HarmonicLowerSixTailBaseCoefficientCertificate
open YMGap.Continuum.HarmonicLowerSixTailBaseCertificateTerms
open YMGap.Continuum.RawGridSemanticTransport
open YMGap.Continuum.TensorBernsteinSeparableReconstruction

local infix:50 " ≈ " => Q'.eqv

private abbrev RP := RingNormaliser.RawPoly

/-! ## Raw form of the frozen diagonal evaluator -/

private def diagonalRawRow
    (totalDegree a : Nat) (raw : Nat → Nat → Int) : Nat → RP
  | 0 => []
  | j + 1 =>
      diagonalRawRow totalDegree a raw j ++
        [([j, totalDegree - a - j], raw a j)]

private def diagonalRawGrid
    (degreeY totalDegree : Nat) (raw : Nat → Nat → Int) : Nat → RP
  | 0 => []
  | a + 1 =>
      diagonalRawGrid degreeY totalDegree raw a ++
        diagonalRawRow totalDegree a raw (degreeY + 1)

private def tailBaseDiagonalRaw : RP :=
  diagonalRawGrid 22 50 tailBaseClearedDiagCoeff 42

def tailBaseRawPolynomial : RP :=
  tailBaseClearedTerms.map (fun (d, n, coefficient) =>
    ([n, d], coefficient))

private theorem tailBaseDiagonalRaw_canon_eq_sparse :
    RingNormaliser.canon tailBaseDiagonalRaw =
      RingNormaliser.canon tailBaseRawPolynomial := by
  rfl

def tailBaseRawEnvironment (D N : Q') : Nat → Q'
  | 0 => N
  | 1 => D
  | _ => 0

private theorem rnqpow_eqv_pow (x : Q') : ∀ exponent,
    RingNormaliser.qpow x exponent ≈ x ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      have ih := rnqpow_eqv_pow x exponent
      change RingNormaliser.qpow x exponent * x ≈ x * x ^ exponent
      exact Q'.eqv_trans _ (x ^ exponent * x) _
        (Q'.mul_eqv_congr_right _ _ x ih)
        (Q'.mul_comm_eqv (x ^ exponent) x)

private theorem mul_eqv_congr_both
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem diagonalRawSingleton_eval
    (D N : Q') (totalDegree a j : Nat) (raw : Nat → Nat → Int) :
    RingNormaliser.evalRaw (tailBaseRawEnvironment D N)
        [([j, totalDegree - a - j], raw a j)] ≈
      Q'.ofInt (raw a j) *
        (N ^ j * D ^ (totalDegree - a - j)) := by
  let e := totalDegree - a - j
  have hN := rnqpow_eqv_pow N j
  have hD := rnqpow_eqv_pow D e
  have hmono :
      RingNormaliser.evalMono (tailBaseRawEnvironment D N) [j, e] ≈
        N ^ j * D ^ e := by
    change RingNormaliser.qpow N j *
        (RingNormaliser.qpow D e * (1 : Q')) ≈ N ^ j * D ^ e
    refine Q'.eqv_trans _
      (N ^ j * (D ^ e * (1 : Q'))) _ ?_ ?_
    · exact mul_eqv_congr_both hN
        (Q'.mul_eqv_congr_right _ _ (1 : Q') hD)
    · exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)
  change Q'.ofInt (raw a j) *
      RingNormaliser.evalMono (tailBaseRawEnvironment D N) [j, e] + 0 ≈
    Q'.ofInt (raw a j) * (N ^ j * D ^ e)
  exact Q'.eqv_trans _
    (Q'.ofInt (raw a j) *
      RingNormaliser.evalMono (tailBaseRawEnvironment D N) [j, e]) _
    (QPoly.q_add_zero_eqv _)
    (Q'.mul_eqv_congr_left _ _ _ hmono)

private theorem diagonalRawRow_eval
    (D N : Q') (totalDegree a : Nat) (raw : Nat → Nat → Int) :
    ∀ count,
    RingNormaliser.evalRaw (tailBaseRawEnvironment D N)
          (diagonalRawRow totalDegree a raw count) ≈
        RationalTail.finSum (fun j => Q'.ofInt (raw a j) *
          (N ^ j * D ^ (totalDegree - a - j))) count
  | 0 => Q'.eqv_refl 0
  | j + 1 => by
      have happ := RingNormaliser.evalRaw_append (tailBaseRawEnvironment D N)
        (diagonalRawRow totalDegree a raw j)
        [([j, totalDegree - a - j], raw a j)]
      have ih := diagonalRawRow_eval D N totalDegree a raw j
      have hterm := diagonalRawSingleton_eval D N totalDegree a j raw
      have hsum := Q'.add_eqv_congr' ih hterm
      change
        RingNormaliser.evalRaw (tailBaseRawEnvironment D N)
          (diagonalRawRow totalDegree a raw j ++
            [([j, totalDegree - a - j], raw a j)]) ≈
        RationalTail.finSum (fun j => Q'.ofInt (raw a j) *
          (N ^ j * D ^ (totalDegree - a - j))) j +
          Q'.ofInt (raw a j) *
            (N ^ j * D ^ (totalDegree - a - j))
      exact Q'.eqv_trans _ _ _ happ hsum

private theorem diagonalRawGrid_eval
    (D N : Q') (degreeY totalDegree : Nat)
    (raw : Nat → Nat → Int) : ∀ count,
      RingNormaliser.evalRaw (tailBaseRawEnvironment D N)
          (diagonalRawGrid degreeY totalDegree raw count) ≈
        RationalTail.finSum (fun a =>
          RationalTail.finSum (fun j => Q'.ofInt (raw a j) *
            (N ^ j * D ^ (totalDegree - a - j))) (degreeY + 1)) count
  | 0 => Q'.eqv_refl 0
  | a + 1 => by
      have happ := RingNormaliser.evalRaw_append (tailBaseRawEnvironment D N)
        (diagonalRawGrid degreeY totalDegree raw a)
        (diagonalRawRow totalDegree a raw (degreeY + 1))
      have ih := diagonalRawGrid_eval D N degreeY totalDegree raw a
      have hrow := diagonalRawRow_eval D N totalDegree a raw (degreeY + 1)
      have hsum := Q'.add_eqv_congr' ih hrow
      change
        RingNormaliser.evalRaw (tailBaseRawEnvironment D N)
          (diagonalRawGrid degreeY totalDegree raw a ++
            diagonalRawRow totalDegree a raw (degreeY + 1)) ≈
        RationalTail.finSum (fun a =>
          RationalTail.finSum (fun j => Q'.ofInt (raw a j) *
            (N ^ j * D ^ (totalDegree - a - j))) (degreeY + 1)) a +
          RationalTail.finSum (fun j => Q'.ofInt (raw a j) *
            (N ^ j * D ^ (totalDegree - a - j))) (degreeY + 1)
      exact Q'.eqv_trans _ _ _ happ hsum

private theorem tailBaseCleared_eqv_diagonalRaw (D N : Q') :
    tailBaseCleared D N ≈
      RingNormaliser.evalRaw (tailBaseRawEnvironment D N) tailBaseDiagonalRaw := by
  have h := diagonalRawGrid_eval D N 22 50 tailBaseClearedDiagCoeff 42
  exact Q'.eqv_symm h

/-- Public N,D-ordered sparse raw form of the frozen Base polynomial. -/
theorem tailBaseCleared_eqv_raw (D N : Q') :
    tailBaseCleared D N ≈
      RingNormaliser.evalRaw (tailBaseRawEnvironment D N)
        tailBaseRawPolynomial := by
  exact Q'.eqv_trans _ _ _ (tailBaseCleared_eqv_diagonalRaw D N)
    (evalRaw_eqv_of_canon_eq (tailBaseRawEnvironment D N)
      tailBaseDiagonalRaw_canon_eq_sparse)

#print axioms tailBaseCleared_eqv_raw

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
