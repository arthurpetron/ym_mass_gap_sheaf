/-
# Evaluation semantics of the staged Base factors

This module proves that the five staged raw factors evaluate to the five
pieces of `tailBaseStructuredExpression`.  The two square terms are handled
factor-by-factor, so no dense composite expression is normalized here.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRowsEvaluation

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CoreBResidualSimplex
open YMGap.Continuum.RawGridSemanticTransport

local infix:50 " ≈ " => Q'.eqv

/- Small kernel-checked normalizer for purely associative/commutative Q'
rearrangements.  It unfolds `eqv` to an integer cross-product identity; no
decision procedure or classical principle enters the proof term. -/
private theorem semantic_neg_num (a : Q') : (-a).num = -a.num := rfl
private theorem semantic_ofInt_num (z : Int) : (Q'.ofInt z).num = z := rfl
private theorem semantic_ofInt_den (z : Int) :
    ((Q'.ofInt z).den : Int) = 1 := rfl

local macro "semantic_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp_all only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               semantic_neg_num, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               semantic_ofInt_num, semantic_ofInt_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

private theorem mul_eqv_congr₂ {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem qpow_two_eqv_mul (x : Q') :
    RingNormaliser.qpow x 2 ≈ x * x := by
  change ((1 : Q') * x) * x ≈ x * x
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

private theorem evalMono_secondPower (rho : Nat → Q') (exponent : Nat)
    (hpos : 0 < exponent) :
    RingNormaliser.evalMono rho [0, exponent] ≈
      RingNormaliser.qpow (rho 1) exponent := by
  have h := evalMono_bivariateMonomial rho 0 exponent
  simp only [bivariateMonomial, if_neg (Nat.ne_of_gt hpos)] at h
  exact Q'.eqv_trans _ _ _ h
    (Q'.one_mul_eqv (RingNormaliser.qpow (rho 1) exponent))

theorem evalRaw_tailBaseL1RawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseL1RawPolynomial ≈
      RingNormaliser.eval rho tailBaseL1ClearedExpr := by
  change
    RingNormaliser.evalRaw rho
        (bivariateTermsRaw tailBaseL1ClearedTermData) ≈
      RingNormaliser.eval rho
        (TensorBernsteinHomogeneousCertificate.bivariatePowerExpr
          tailBaseL1ClearedTermData)
  exact evalRaw_bivariateTermsRaw rho tailBaseL1ClearedTermData

theorem evalRaw_tailBaseU0RawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseU0RawPolynomial ≈
      RingNormaliser.eval rho tailBaseU0ClearedExpr := by
  change
    RingNormaliser.evalRaw rho
        (bivariateTermsRaw tailBaseU0MinimalTermData) ≈
      RingNormaliser.eval rho
        (TensorBernsteinHomogeneousCertificate.bivariatePowerExpr
          tailBaseU0MinimalTermData)
  exact evalRaw_bivariateTermsRaw rho tailBaseU0MinimalTermData

private theorem evalRaw_tailBaseL1SquareRawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseL1SquareRawPolynomial ≈
      RingNormaliser.qpow
        (RingNormaliser.eval rho tailBaseL1ClearedExpr) 2 := by
  change
    RingNormaliser.evalRaw rho
        (RingNormaliser.canon
          (RingNormaliser.rawMul tailBaseL1RawPolynomial
            tailBaseL1RawPolynomial)) ≈ _
  exact Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho
      (RingNormaliser.rawMul tailBaseL1RawPolynomial
        tailBaseL1RawPolynomial))
    (Q'.eqv_trans _ _ _
      (RingNormaliser.evalRaw_rawMul rho tailBaseL1RawPolynomial
        tailBaseL1RawPolynomial)
      (Q'.eqv_trans _ _ _
        (mul_eqv_congr₂ (evalRaw_tailBaseL1RawPolynomial rho)
          (evalRaw_tailBaseL1RawPolynomial rho))
        (Q'.eqv_symm
          (qpow_two_eqv_mul
            (RingNormaliser.eval rho tailBaseL1ClearedExpr)))))

private theorem evalRaw_tailBaseTwoFRawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseTwoFRawPolynomial ≈
      RingNormaliser.eval rho tailBaseTwoFExpr := by
  change
    RingNormaliser.evalRaw rho (fastNormalize tailBaseTwoFExpr) ≈
      RingNormaliser.eval rho tailBaseTwoFExpr
  exact evalRaw_fastNormalize rho tailBaseTwoFExpr

private theorem evalRaw_tailBaseTwoFL1SquareRawPolynomial
    (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseTwoFL1SquareRawPolynomial ≈
      RingNormaliser.eval rho tailBaseTwoFExpr *
        RingNormaliser.qpow
          (RingNormaliser.eval rho tailBaseL1ClearedExpr) 2 := by
  change
    RingNormaliser.evalRaw rho
        (RingNormaliser.canon
          (RingNormaliser.rawMul tailBaseTwoFRawPolynomial
            tailBaseL1SquareRawPolynomial)) ≈ _
  exact Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho
      (RingNormaliser.rawMul tailBaseTwoFRawPolynomial
        tailBaseL1SquareRawPolynomial))
    (Q'.eqv_trans _ _ _
      (RingNormaliser.evalRaw_rawMul rho tailBaseTwoFRawPolynomial
        tailBaseL1SquareRawPolynomial)
      (mul_eqv_congr₂ (evalRaw_tailBaseTwoFRawPolynomial rho)
        (evalRaw_tailBaseL1SquareRawPolynomial rho)))

private theorem evalRaw_piece0 (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseStructuredPiece0Raw ≈
      RingNormaliser.eval rho tailBaseStructuredPiece0Expr := by
  change RingNormaliser.evalRaw rho
      (fastNormalize tailBaseStructuredPiece0Expr) ≈ _
  exact evalRaw_fastNormalize rho tailBaseStructuredPiece0Expr

private theorem evalRaw_piece1 (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseStructuredPiece1Raw ≈
      RingNormaliser.eval rho tailBaseStructuredPiece1Expr := by
  let D := rho 1
  let F := RingNormaliser.eval rho tailBaseTwoFExpr
  let L2 := RingNormaliser.qpow
    (RingNormaliser.eval rho tailBaseL1ClearedExpr) 2
  have hscale := RingNormaliser.evalRaw_scaleTerm rho [0, 24] 162
    tailBaseTwoFL1SquareRawPolynomial
  have hmono : RingNormaliser.evalMono rho [0, 24] ≈
      RingNormaliser.qpow D 24 := by
    dsimp only [D]
    exact evalMono_secondPower rho 24 (by omega)
  have hcore := evalRaw_tailBaseTwoFL1SquareRawPolynomial rho
  have hstaged :
      RingNormaliser.evalRaw rho tailBaseStructuredPiece1Raw ≈
        (Q'.ofInt 162 * RingNormaliser.qpow D 24) * (F * L2) := by
    exact Q'.eqv_trans _ _ _ hscale
      (mul_eqv_congr₂
        (Q'.mul_eqv_congr_left (Q'.ofInt 162) _ _ hmono) hcore)
  have hsplit : RingNormaliser.qpow D 24 ≈
      RingNormaliser.qpow D 18 * RingNormaliser.qpow D 6 := by
    simpa only using RingNormaliser.qpow_add D 18 6
  have hrearrange :
      (Q'.ofInt 162 * RingNormaliser.qpow D 24) * (F * L2) ≈
        Q'.ofInt 162 *
          (RingNormaliser.qpow D 18 *
            (F * (L2 * RingNormaliser.qpow D 6))) := by
    refine Q'.eqv_trans _
      ((Q'.ofInt 162 *
          (RingNormaliser.qpow D 18 * RingNormaliser.qpow D 6)) *
        (F * L2)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ (F * L2)
        (Q'.mul_eqv_congr_left (Q'.ofInt 162) _ _ hsplit)
    · semantic_ring
  exact Q'.eqv_trans _ _ _ hstaged (by
    dsimp only [D, F, L2] at hrearrange ⊢
    exact hrearrange)

private theorem evalRaw_piece2 (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseStructuredPiece2Raw ≈
      RingNormaliser.eval rho tailBaseStructuredPiece2Expr := by
  change RingNormaliser.evalRaw rho
      (fastNormalize tailBaseStructuredPiece2Expr) ≈ _
  exact evalRaw_fastNormalize rho tailBaseStructuredPiece2Expr

private theorem evalRaw_tailBaseU0SquareRawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseU0SquareRawPolynomial ≈
      RingNormaliser.qpow
        (RingNormaliser.eval rho tailBaseU0ClearedExpr) 2 := by
  change
    RingNormaliser.evalRaw rho
        (RingNormaliser.canon
          (RingNormaliser.rawMul tailBaseU0RawPolynomial
            tailBaseU0RawPolynomial)) ≈ _
  exact Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho
      (RingNormaliser.rawMul tailBaseU0RawPolynomial
        tailBaseU0RawPolynomial))
    (Q'.eqv_trans _ _ _
      (RingNormaliser.evalRaw_rawMul rho tailBaseU0RawPolynomial
        tailBaseU0RawPolynomial)
      (Q'.eqv_trans _ _ _
        (mul_eqv_congr₂ (evalRaw_tailBaseU0RawPolynomial rho)
          (evalRaw_tailBaseU0RawPolynomial rho))
        (Q'.eqv_symm
          (qpow_two_eqv_mul
            (RingNormaliser.eval rho tailBaseU0ClearedExpr)))))

private theorem evalRaw_tailBaseR4RawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseR4RawPolynomial ≈
      RingNormaliser.eval rho
        (.pow (.add (.pow (.var 1) 2) (.const (-1))) 4) := by
  exact evalRaw_fastNormalize rho _

private theorem evalRaw_tailBaseDp15RawPolynomial (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseDp15RawPolynomial ≈
      RingNormaliser.eval rho
        (.pow (.add (.var 1) (.const 1)) 15) := by
  exact evalRaw_fastNormalize rho _

private theorem evalRaw_tailBaseU0SquareR4RawPolynomial
    (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseU0SquareR4RawPolynomial ≈
      RingNormaliser.eval rho
          (.pow (.add (.pow (.var 1) 2) (.const (-1))) 4) *
        RingNormaliser.qpow
          (RingNormaliser.eval rho tailBaseU0ClearedExpr) 2 := by
  change RingNormaliser.evalRaw rho
    (RingNormaliser.canon
      (RingNormaliser.rawMul tailBaseR4RawPolynomial
        tailBaseU0SquareRawPolynomial)) ≈ _
  exact Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho
      (RingNormaliser.rawMul tailBaseR4RawPolynomial
        tailBaseU0SquareRawPolynomial))
    (Q'.eqv_trans _ _ _
      (RingNormaliser.evalRaw_rawMul rho tailBaseR4RawPolynomial
        tailBaseU0SquareRawPolynomial)
      (mul_eqv_congr₂ (evalRaw_tailBaseR4RawPolynomial rho)
        (evalRaw_tailBaseU0SquareRawPolynomial rho)))

private theorem evalRaw_tailBaseU0SquareCommonRawPolynomial
    (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseU0SquareCommonRawPolynomial ≈
      RingNormaliser.eval rho (.pow (.add (.var 1) (.const 1)) 15) *
        (RingNormaliser.eval rho
            (.pow (.add (.pow (.var 1) 2) (.const (-1))) 4) *
          RingNormaliser.qpow
            (RingNormaliser.eval rho tailBaseU0ClearedExpr) 2) := by
  change RingNormaliser.evalRaw rho
    (RingNormaliser.canon
      (RingNormaliser.rawMul tailBaseDp15RawPolynomial
        tailBaseU0SquareR4RawPolynomial)) ≈ _
  exact Q'.eqv_trans _ _ _
    (RingNormaliser.evalRaw_canon rho
      (RingNormaliser.rawMul tailBaseDp15RawPolynomial
        tailBaseU0SquareR4RawPolynomial))
    (Q'.eqv_trans _ _ _
      (RingNormaliser.evalRaw_rawMul rho tailBaseDp15RawPolynomial
        tailBaseU0SquareR4RawPolynomial)
      (mul_eqv_congr₂ (evalRaw_tailBaseDp15RawPolynomial rho)
        (evalRaw_tailBaseU0SquareR4RawPolynomial rho)))

private theorem evalRaw_piece3 (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseStructuredPiece3Raw ≈
      RingNormaliser.eval rho tailBaseStructuredPiece3Expr := by
  let D := rho 1
  let R4 := RingNormaliser.eval rho
    (.pow (.add (.pow (.var 1) 2) (.const (-1))) 4)
  let Dp15 := RingNormaliser.eval rho
    (.pow (.add (.var 1) (.const 1)) 15)
  let U2 := RingNormaliser.qpow
    (RingNormaliser.eval rho tailBaseU0ClearedExpr) 2
  have hscale := RingNormaliser.evalRaw_scaleTerm rho [0, 7] (-4)
    tailBaseU0SquareCommonRawPolynomial
  have hmono : RingNormaliser.evalMono rho [0, 7] ≈
      RingNormaliser.qpow D 7 := by
    dsimp only [D]
    exact evalMono_secondPower rho 7 (by omega)
  have hcommon := evalRaw_tailBaseU0SquareCommonRawPolynomial rho
  have hstaged :
      RingNormaliser.evalRaw rho tailBaseStructuredPiece3Raw ≈
        (Q'.ofInt (-4) * RingNormaliser.qpow D 7) *
          (Dp15 * (R4 * U2)) := by
    exact Q'.eqv_trans _ _ _ hscale
      (mul_eqv_congr₂
        (Q'.mul_eqv_congr_left (Q'.ofInt (-4)) _ _ hmono) hcommon)
  have hsplit : RingNormaliser.qpow D 7 ≈
      D * RingNormaliser.qpow D 6 := by
    have hadd := RingNormaliser.qpow_add D 1 6
    have hone : RingNormaliser.qpow D 1 ≈ D := by
      change (1 : Q') * D ≈ D
      exact Q'.one_mul_eqv D
    exact Q'.eqv_trans _ _ _ hadd
      (Q'.mul_eqv_congr_right _ _ (RingNormaliser.qpow D 6) hone)
  have hrearrange :
      (Q'.ofInt (-4) * RingNormaliser.qpow D 7) *
          (Dp15 * (R4 * U2)) ≈
        -(Q'.ofInt 4 *
          (D * (R4 * (Dp15 * (U2 * RingNormaliser.qpow D 6))))) := by
    refine Q'.eqv_trans _
      ((Q'.ofInt (-4) * (D * RingNormaliser.qpow D 6)) *
        (Dp15 * (R4 * U2))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ (Dp15 * (R4 * U2))
        (Q'.mul_eqv_congr_left (Q'.ofInt (-4)) _ _ hsplit)
    · semantic_ring
  exact Q'.eqv_trans _ _ _ hstaged (by
    dsimp only [D, R4, Dp15, U2] at hrearrange ⊢
    exact hrearrange)

private theorem evalRaw_piece4 (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseStructuredPiece4Raw ≈
      RingNormaliser.eval rho tailBaseStructuredPiece4Expr := by
  change RingNormaliser.evalRaw rho
      (fastNormalize tailBaseStructuredPiece4Expr) ≈ _
  exact evalRaw_fastNormalize rho tailBaseStructuredPiece4Expr

/-- Exact semantic identification of the frozen N,D raw polynomial with the
five-piece structured integer expression. -/
theorem evalRaw_tailBaseRawPolynomial_structuredExpression
    (rho : Nat → Q') :
    RingNormaliser.evalRaw rho tailBaseRawPolynomial ≈
      RingNormaliser.eval rho tailBaseStructuredExpression := by
  have hsum := evalRaw_tailBaseRawPolynomial_structuredRawSum rho
  have hpieces := Q'.add_eqv_congr' (evalRaw_piece0 rho)
    (Q'.add_eqv_congr' (evalRaw_piece1 rho)
      (Q'.add_eqv_congr' (evalRaw_piece2 rho)
        (Q'.add_eqv_congr' (evalRaw_piece3 rho) (evalRaw_piece4 rho))))
  exact Q'.eqv_trans _ _ _ hsum (by
    change
      RingNormaliser.evalRaw rho tailBaseStructuredPiece0Raw +
          (RingNormaliser.evalRaw rho tailBaseStructuredPiece1Raw +
            (RingNormaliser.evalRaw rho tailBaseStructuredPiece2Raw +
              (RingNormaliser.evalRaw rho tailBaseStructuredPiece3Raw +
                RingNormaliser.evalRaw rho tailBaseStructuredPiece4Raw))) ≈
        RingNormaliser.eval rho tailBaseStructuredPiece0Expr +
          (RingNormaliser.eval rho tailBaseStructuredPiece1Expr +
            (RingNormaliser.eval rho tailBaseStructuredPiece2Expr +
              (RingNormaliser.eval rho tailBaseStructuredPiece3Expr +
                RingNormaliser.eval rho tailBaseStructuredPiece4Expr)))
    exact hpieces)

theorem tailBaseCleared_eqv_structuredExpression (D N : Q') :
    HarmonicLowerSixTailBaseCertificate.tailBaseCleared D N ≈
      RingNormaliser.eval (tailBaseRawEnvironment D N)
        tailBaseStructuredExpression := by
  exact Q'.eqv_trans _ _ _ (tailBaseCleared_eqv_raw D N)
    (evalRaw_tailBaseRawPolynomial_structuredExpression
      (tailBaseRawEnvironment D N))

#print axioms evalRaw_tailBaseL1RawPolynomial
#print axioms evalRaw_tailBaseU0RawPolynomial
#print axioms evalRaw_tailBaseRawPolynomial_structuredExpression
#print axioms tailBaseCleared_eqv_structuredExpression

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
