/-
# Exact row certificate for the old-slope square Base piece

The old-slope term is assembled as
`D^7 * (D^2 - 1)^4 * (D + 1)^15 * U0Cleared^2`.  The staged raw product is
checked against its 23 generated mode-exponent rows here, behind a dedicated
module boundary so the square is reduced only once.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticU0FactorRows

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.RawGridSemanticTransport

local infix:50 " ≈ " => Q'.eqv

/-! ## Semantic transport of the row map -/

private theorem mul_eqv_congr₂ {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem mul_zero_eqv (a : Q') : a * 0 ≈ 0 :=
  Q'.eqv_trans _ (0 * a) _
    (Q'.mul_comm_eqv a 0)
    (RingNormaliser.q_zero_mul a)

private theorem nested_three_mul_add
    (K A B x y : Q') :
    K * (A * (B * (x + y))) ≈
      K * (A * (B * x)) + K * (A * (B * y)) := by
  refine Q'.eqv_trans _ (K * (A * (B * x + B * y))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left K _ _
      (Q'.mul_eqv_congr_left A _ _ (Q'.mul_add_eqv B x y))
  refine Q'.eqv_trans _
    (K * (A * (B * x) + A * (B * y))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left K _ _
      (Q'.mul_add_eqv A (B * x) (B * y))
  · exact Q'.mul_add_eqv K (A * (B * x)) (A * (B * y))

private theorem evalRaw_tailBasePiece3RowTransform
    (rho : Nat → Q') (row : RingNormaliser.RawPoly) :
    RingNormaliser.evalRaw rho (tailBasePiece3RowTransform row) ≈
      (Q'.ofInt (-4) * RingNormaliser.evalMono rho [0, 7]) *
        (RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
          (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial *
            RingNormaliser.evalRaw rho row)) := by
  have hscale := RingNormaliser.evalRaw_scaleTerm rho [0, 7] (-4)
    (RingNormaliser.canon
      (RingNormaliser.rawMul tailBaseDp15RawPolynomial
        (RingNormaliser.canon
          (RingNormaliser.rawMul tailBaseR4RawPolynomial row))))
  have hdpCanon := RingNormaliser.evalRaw_canon rho
    (RingNormaliser.rawMul tailBaseDp15RawPolynomial
      (RingNormaliser.canon
        (RingNormaliser.rawMul tailBaseR4RawPolynomial row)))
  have hdpMul := RingNormaliser.evalRaw_rawMul rho
    tailBaseDp15RawPolynomial
    (RingNormaliser.canon
      (RingNormaliser.rawMul tailBaseR4RawPolynomial row))
  have hrCanon := RingNormaliser.evalRaw_canon rho
    (RingNormaliser.rawMul tailBaseR4RawPolynomial row)
  have hrMul := RingNormaliser.evalRaw_rawMul rho
    tailBaseR4RawPolynomial row
  have hcommon :
      RingNormaliser.evalRaw rho
          (RingNormaliser.canon
            (RingNormaliser.rawMul tailBaseDp15RawPolynomial
              (RingNormaliser.canon
                (RingNormaliser.rawMul tailBaseR4RawPolynomial row)))) ≈
        RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
          (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial *
            RingNormaliser.evalRaw rho row) := by
    exact Q'.eqv_trans _ _ _ hdpCanon
      (Q'.eqv_trans _ _ _ hdpMul
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ hrCanon hrMul)))
  exact Q'.eqv_trans _ _ _ hscale
    (Q'.mul_eqv_congr_left _ _ _ hcommon)

private theorem evalRawRows_map_tailBasePiece3RowTransform
    (rho : Nat → Q') : ∀ rows,
    evalRawRows rho (rows.map tailBasePiece3RowTransform) ≈
      (Q'.ofInt (-4) * RingNormaliser.evalMono rho [0, 7]) *
        (RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
          (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial *
            evalRawRows rho rows))
  | [] => by
      change (0 : Q') ≈
        (Q'.ofInt (-4) * RingNormaliser.evalMono rho [0, 7]) *
          (RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
            (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial * 0))
      have hr :
          RingNormaliser.evalRaw rho tailBaseR4RawPolynomial * 0 ≈ 0 :=
        mul_zero_eqv _
      have hdp :
          RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
              (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial * 0) ≈
            0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hr)
          (mul_zero_eqv _)
      have houter :
          (Q'.ofInt (-4) * RingNormaliser.evalMono rho [0, 7]) *
              (RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
                (RingNormaliser.evalRaw rho
                  tailBaseR4RawPolynomial * 0)) ≈
            0 :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hdp)
          (mul_zero_eqv _)
      exact Q'.eqv_symm houter
  | row :: rows => by
      change
        RingNormaliser.evalRaw rho (tailBasePiece3RowTransform row) +
            evalRawRows rho (rows.map tailBasePiece3RowTransform) ≈
          (Q'.ofInt (-4) * RingNormaliser.evalMono rho [0, 7]) *
            (RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
              (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial *
                (RingNormaliser.evalRaw rho row + evalRawRows rho rows)))
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (evalRaw_tailBasePiece3RowTransform rho row)
          (evalRawRows_map_tailBasePiece3RowTransform rho rows))
        (Q'.eqv_symm
          (nested_three_mul_add
            (Q'.ofInt (-4) * RingNormaliser.evalMono rho [0, 7])
            (RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial)
            (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial)
            (RingNormaliser.evalRaw rho row)
            (evalRawRows rho rows)))

private theorem tailBasePiece3RowTransform_whole :
    tailBasePiece3RowTransform tailBaseU0SquareRawPolynomial =
      tailBaseStructuredPiece3Raw := by
  rfl

private theorem evalRawRows_tailBasePiece3FactorRows_whole
    (rho : Nat → Q') :
    evalRawRows rho tailBasePiece3FactorRows ≈
      RingNormaliser.evalRaw rho tailBaseStructuredPiece3Raw := by
  have hmap := evalRawRows_map_tailBasePiece3RowTransform rho
    tailBaseU0SquareRows
  have hbucket := evalRawRows_bucketRaw rho 23
    tailBaseU0SquareRawPolynomial tailBaseU0SquareRaw_bound
  have hfactor :
      (Q'.ofInt (-4) * RingNormaliser.evalMono rho [0, 7]) *
          (RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
            (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial *
              evalRawRows rho tailBaseU0SquareRows)) ≈
        (Q'.ofInt (-4) * RingNormaliser.evalMono rho [0, 7]) *
          (RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial *
            (RingNormaliser.evalRaw rho tailBaseR4RawPolynomial *
              RingNormaliser.evalRaw rho tailBaseU0SquareRawPolynomial)) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hbucket))
  have hwhole := evalRaw_tailBasePiece3RowTransform rho
    tailBaseU0SquareRawPolynomial
  rw [tailBasePiece3RowTransform_whole] at hwhole
  exact Q'.eqv_trans _ _ _ hmap
    (Q'.eqv_trans _ _ _ hfactor (Q'.eqv_symm hwhole))

/-- Semantic row certificate for the large old-slope square.  This is the
interface consumed downstream; the flat 682-term normal form is never
unfolded by a closed equality check. -/
theorem evalRawRows_tailBaseSemanticPiece3Rows (rho : Nat → Q') :
    evalRawRows rho tailBaseSemanticPiece3Rows ≈
      RingNormaliser.evalRaw rho tailBaseStructuredPiece3Raw := by
  have hrelation := evalRawRows_eqv_of_canonRowsRelationChunks_true
    rho 4 6 tailBasePiece3FactorRows
      tailBaseSemanticPiece3Rows tailBasePiece3FactorRows_rows
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hrelation)
    (evalRawRows_tailBasePiece3FactorRows_whole rho)

#print axioms tailBasePiece3FactorRows_rows
#print axioms evalRawRows_tailBaseSemanticPiece3Rows

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
