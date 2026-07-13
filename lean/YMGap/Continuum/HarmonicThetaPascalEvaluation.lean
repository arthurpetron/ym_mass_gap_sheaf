/-
# Semantic evaluation of the harmonic theta Pascal row

This module connects the public signed coefficient row from
`HarmonicThetaPascalBridge` to an actual `Q'` polynomial.  It first proves
that the two independently introduced Pascal recursions agree, then lifts
addition, negation, and integer scaling through signed Bernstein evaluation.
-/

import YMGap.Continuum.BernsteinMonomialReconstruction
import YMGap.Continuum.HarmonicThetaPascalBridge
import YMGap.Continuum.HarmonicThetaLinearCarrier

namespace YMGap.Continuum.HarmonicThetaPascalEvaluation

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaPascalBridge
open YMGap.Continuum.HarmonicThetaRepresentation

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one]; ac_rfl))

private theorem pow_add_eqv (w : Q') (a : Nat) : ∀ b,
    w ^ (a + b) ≈ w ^ a * w ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (w ^ a))
  | b + 1 => by
      have ih := pow_add_eqv w a b
      show w * w ^ (a + b) ≈ w ^ a * (w * w ^ b)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ ih) ?_
      ring_qeqv

private theorem mul_pow_eqv (a b : Q') : ∀ (n : Nat),
    (a * b) ^ n ≈ a ^ n * b ^ n
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | n + 1 => by
      have ih := mul_pow_eqv a b n
      show (a * b) * (a * b) ^ n ≈ (a * a ^ n) * (b * b ^ n)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (a * b) _ _ ih) ?_
      ring_qeqv

private theorem qpow_eqv_pow (w : Q') : ∀ n,
    RingNormaliser.qpow w n ≈ w ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := qpow_eqv_pow w n
      show RingNormaliser.qpow w n * w ≈ w * w ^ n
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w ih) ?_
      exact Q'.mul_comm_eqv (w ^ n) w

private theorem qpow_square_eqv_double_pow (w : Q') (n : Nat) :
    RingNormaliser.qpow (w * w) n ≈ w ^ (n + n) := by
  refine Q'.eqv_trans _ _ _ (qpow_eqv_pow (w * w) n) ?_
  refine Q'.eqv_trans _ _ _ (mul_pow_eqv w w n) ?_
  exact Q'.eqv_symm (pow_add_eqv w n n)

private theorem rgQpow_eqv_pow (w : Q') : ∀ n,
    RGTransport.qpow w n ≈ w ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := rgQpow_eqv_pow w n
      show RGTransport.qpow w n * w ≈ w * w ^ n
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w ih) ?_
      exact Q'.mul_comm_eqv (w ^ n) w

private theorem rgQpow_square_eqv_double_pow (w : Q') (n : Nat) :
    RGTransport.qpow (w * w) n ≈ w ^ (n + n) := by
  refine Q'.eqv_trans _ _ _ (rgQpow_eqv_pow (w * w) n) ?_
  refine Q'.eqv_trans _ _ _ (mul_pow_eqv w w n) ?_
  exact Q'.eqv_symm (pow_add_eqv w n n)

/-- The Pascal coefficient used by `PNPaths` is exactly the independently
defined RG binomial coefficient. -/
theorem pnChoose_eq_binom : ∀ n k,
    PNPaths.choose n k = binom n k
  | n, 0 => by cases n <;> rfl
  | 0, _ + 1 => rfl
  | n + 1, k + 1 => by
      rw [PNPaths.choose, binom_succ_succ,
        pnChoose_eq_binom n k, pnChoose_eq_binom n (k + 1)]

private def rowAdd (a b : Nat → Int) : Nat → Int :=
  fun j => a j + b j

private def rowNeg (a : Nat → Int) : Nat → Int :=
  fun j => -(a j)

private def rowScale (z : Int) (a : Nat → Int) : Nat → Int :=
  fun j => z * a j

private theorem signedEval_add (D : Nat) (a b : Nat → Int) (w : Q') :
    signedBernsteinEval D (rowAdd a b) w ≈
      signedBernsteinEval D a w + signedBernsteinEval D b w := by
  unfold signedBernsteinEval rowAdd
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun j => Q'.ofInt (a j + b j) * bernsteinBasis D w j)
      (fun j => Q'.ofInt (a j) * bernsteinBasis D w j +
        Q'.ofInt (b j) * bernsteinBasis D w j) (fun j => ?_) (D + 1)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (RingNormaliser.ofInt_add (a j) (b j))) ?_
    exact Q'.add_mul_eqv (Q'.ofInt (a j)) (Q'.ofInt (b j))
      (bernsteinBasis D w j)
  · exact RationalTail.finSum_add
      (fun j => Q'.ofInt (a j) * bernsteinBasis D w j)
      (fun j => Q'.ofInt (b j) * bernsteinBasis D w j) (D + 1)

private theorem ofInt_neg_eqv (z : Int) :
    Q'.ofInt (-z) ≈ -(Q'.ofInt z) := by
  rfl

private theorem signedEval_neg (D : Nat) (a : Nat → Int) (w : Q') :
    signedBernsteinEval D (rowNeg a) w ≈
      -(signedBernsteinEval D a w) := by
  unfold signedBernsteinEval rowNeg
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun j => Q'.ofInt (-a j) * bernsteinBasis D w j)
      (fun j => -(Q'.ofInt (a j) * bernsteinBasis D w j))
      (fun j => ?_) (D + 1)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (ofInt_neg_eqv (a j))) ?_
    exact Q'.neg_mul_eqv (Q'.ofInt (a j)) (bernsteinBasis D w j)
  · exact Q'.eqv_symm
      (YMGap.Constructive.neg_finSum
        (fun j => Q'.ofInt (a j) * bernsteinBasis D w j) (D + 1))

private theorem signedEval_scale (D : Nat) (z : Int)
    (a : Nat → Int) (w : Q') :
    signedBernsteinEval D (rowScale z a) w ≈
      Q'.ofInt z * signedBernsteinEval D a w := by
  unfold signedBernsteinEval rowScale
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun j => Q'.ofInt (z * a j) * bernsteinBasis D w j)
      (fun j => Q'.ofInt z *
        (Q'.ofInt (a j) * bernsteinBasis D w j)) (fun j => ?_) (D + 1)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (RingNormaliser.ofInt_mul z (a j))) ?_
    exact Q'.mul_assoc_eqv (Q'.ofInt z) (Q'.ofInt (a j))
      (bernsteinBasis D w j)
  · exact Q'.eqv_symm
      (const_mul_finSum
        (fun j => Q'.ofInt (a j) * bernsteinBasis D w j)
        (Q'.ofInt z) (D + 1))

private theorem thetaMonoCoeff_eq_elevated (D e j : Nat) :
    thetaMonoBernCoeff D e j = Int.ofNat (elevatedMonoCoeff D e j) := by
  unfold thetaMonoBernCoeff elevatedMonoCoeff
  split <;> simp_all [pnChoose_eq_binom]

/-- A public theta monomial coefficient row reconstructs the claimed
monomial exactly. -/
theorem thetaMonoBernCoeff_eval (D e : Nat) (w : Q') (heD : e ≤ D) :
    signedBernsteinEval D (thetaMonoBernCoeff D e) w ≈ w ^ e := by
  have hrow : signedBernsteinEval D (thetaMonoBernCoeff D e) w =
      elevatedMonoEval D e w := by
    unfold signedBernsteinEval elevatedMonoEval
    congr 2
    funext j
    rw [thetaMonoCoeff_eq_elevated]
    rfl
  rw [hrow]
  exact elevatedMonoEval_eqv_pow D e w heD

private def diagComboRow (D n : Nat) : Nat → Int :=
  rowAdd (thetaMonoBernCoeff D (2 * n * n - 2))
    (rowAdd (rowScale 3 (thetaMonoBernCoeff D (2 * n * n - 1)))
      (rowAdd (rowScale 3 (thetaMonoBernCoeff D (2 * n * n)))
        (thetaMonoBernCoeff D (2 * n * n + 1))))

private def thetaDiagPolynomial (n : Nat) (w : Q') : Q' :=
  Q'.ofNat (n * n) *
    (w ^ (2 * n * n - 2) +
      (Q'.ofNat 3 * w ^ (2 * n * n - 1) +
        (Q'.ofNat 3 * w ^ (2 * n * n) +
          w ^ (2 * n * n + 1))))

private def thetaOffPolynomial (n : Nat) (w : Q') : Q' :=
  Q'.ofNat (8 * n * (n + 1)) *
    w ^ (2 * n * (n + 1) - 1)

private def thetaCellPolynomial (n : Nat) (w : Q') : Q' :=
  thetaDiagPolynomial n w + -(thetaOffPolynomial n w)

private def thetaCellPolynomialSum (n : Nat) (w : Q') : Nat → Q'
  | 0 => 0
  | c + 1 => thetaCellPolynomial n w + thetaCellPolynomialSum (n + 1) w c

private def thetaActualCellPow (n : Nat) (w : Q') : Q' :=
  RingNormaliser.qpow ((1 : Q') + w) 3 *
      (Q'.ofNat (n * n) * w ^ (2 * n * n)) +
    -(Q'.ofNat (8 * n * (n + 1)) *
      w ^ (2 * n * (n + 1) + 1))

private def diagRingL : RingNormaliser.PolyExpr :=
  .mul (.pow (.var 0) 2)
    (.mul (.var 1)
      (.add (.var 2)
        (.add (.mul (.const 3) (.mul (.var 2) (.var 0)))
          (.add
            (.mul (.const 3) (.mul (.var 2) (.pow (.var 0) 2)))
            (.mul (.var 2) (.pow (.var 0) 3))))))

private def diagRingR : RingNormaliser.PolyExpr :=
  .mul (.pow (.add (.const 1) (.var 0)) 3)
    (.mul (.var 1) (.mul (.var 2) (.pow (.var 0) 2)))

private theorem diagRing_normal :
    RingNormaliser.normalize diagRingL =
      RingNormaliser.normalize diagRingR := by
  decide

private theorem diag_ring_qpow (w A X : Q') :
    RingNormaliser.qpow w 2 *
        (A * (X +
          (Q'.ofNat 3 * (X * w) +
            (Q'.ofNat 3 * (X * RingNormaliser.qpow w 2) +
              X * RingNormaliser.qpow w 3)))) ≈
      RingNormaliser.qpow ((1 : Q') + w) 3 *
        (A * (X * RingNormaliser.qpow w 2)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    diagRingL diagRingR diagRing_normal
    (fun
      | 0 => w
      | 1 => A
      | _ => X)
  simpa [diagRingL, diagRingR, RingNormaliser.eval] using h

private theorem diag_ring (w A X : Q') :
    w ^ 2 *
        (A * (X +
          (Q'.ofNat 3 * (X * w) +
            (Q'.ofNat 3 * (X * w ^ 2) + X * w ^ 3)))) ≈
      RingNormaliser.qpow ((1 : Q') + w) 3 *
        (A * (X * w ^ 2)) := by
  have h2 := qpow_eqv_pow w 2
  have h3 := qpow_eqv_pow w 3
  have hinner :
      A * (X +
          (Q'.ofNat 3 * (X * w) +
            (Q'.ofNat 3 * (X * w ^ 2) + X * w ^ 3))) ≈
        A * (X +
          (Q'.ofNat 3 * (X * w) +
            (Q'.ofNat 3 * (X * RingNormaliser.qpow w 2) +
              X * RingNormaliser.qpow w 3))) := by
    refine Q'.mul_eqv_congr_left A _ _ ?_
    refine Q'.add_eqv_congr_left X _ _ ?_
    refine Q'.add_eqv_congr_left (Q'.ofNat 3 * (X * w)) _ _ ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _
        (Q'.mul_eqv_congr_left X _ _ (Q'.eqv_symm h2))
    · exact Q'.mul_eqv_congr_left X _ _ (Q'.eqv_symm h3)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm h2)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (RingNormaliser.qpow w 2) _ _ hinner) ?_
  refine Q'.eqv_trans _ _ _ (diag_ring_qpow w A X) ?_
  exact Q'.mul_eqv_congr_left (RingNormaliser.qpow (1 + w) 3) _ _
    (Q'.mul_eqv_congr_left A _ _
      (Q'.mul_eqv_congr_left X _ _ h2))

private theorem thetaDiagPolynomial_unshift (n : Nat) (w : Q') (hn : 1 ≤ n) :
    thetaDiagPolynomial n w ≈
      Q'.ofNat (n * n) *
        (w ^ (2 * n * n - 2) +
          (Q'.ofNat 3 * (w ^ (2 * n * n - 2) * w) +
            (Q'.ofNat 3 * (w ^ (2 * n * n - 2) * w ^ 2) +
              w ^ (2 * n * n - 2) * w ^ 3))) := by
  have hbase : 2 ≤ 2 * n * n := by
    have hsq : 1 ≤ n * n := Nat.mul_pos hn hn
    have h := Nat.mul_le_mul_left 2 hsq
    simpa only [Nat.mul_assoc, Nat.mul_one] using h
  have he1 : 2 * n * n - 1 = (2 * n * n - 2) + 1 := by omega
  have he2 : 2 * n * n = (2 * n * n - 2) + 2 := by omega
  have he3 : 2 * n * n + 1 = (2 * n * n - 2) + 3 := by omega
  have h1 : w ^ (2 * n * n - 1) ≈ w ^ (2 * n * n - 2) * w := by
    rw [he1]
    refine Q'.eqv_trans _ _ _ (pow_add_eqv w (2 * n * n - 2) 1) ?_
    exact Q'.mul_eqv_congr_left (w ^ (2 * n * n - 2)) _ _
      (Q'.mul_one_eqv w)
  have h2 : w ^ (2 * n * n) ≈ w ^ (2 * n * n - 2) * w ^ 2 := by
    rw [he2]
    exact pow_add_eqv w (2 * n * n - 2) 2
  have h3 : w ^ (2 * n * n + 1) ≈ w ^ (2 * n * n - 2) * w ^ 3 := by
    rw [he3]
    exact pow_add_eqv w (2 * n * n - 2) 3
  unfold thetaDiagPolynomial
  refine Q'.mul_eqv_congr_left (Q'.ofNat (n * n)) _ _ ?_
  refine Q'.add_eqv_congr_left (w ^ (2 * n * n - 2)) _ _ ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · exact Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _ h1
  · refine Q'.add_eqv_congr' ?_ h3
    exact Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _ h2

private theorem thetaDiagPolynomial_scaled (n : Nat) (w : Q') (hn : 1 ≤ n) :
    w ^ 2 * thetaDiagPolynomial n w ≈
      RingNormaliser.qpow ((1 : Q') + w) 3 *
        (Q'.ofNat (n * n) * w ^ (2 * n * n)) := by
  have hbase : 2 ≤ 2 * n * n := by
    have hsq : 1 ≤ n * n := Nat.mul_pos hn hn
    have h := Nat.mul_le_mul_left 2 hsq
    simpa only [Nat.mul_assoc, Nat.mul_one] using h
  have he2 : 2 * n * n = (2 * n * n - 2) + 2 := by omega
  have h2 : w ^ (2 * n * n) ≈ w ^ (2 * n * n - 2) * w ^ 2 := by
    rw [he2]
    exact pow_add_eqv w (2 * n * n - 2) 2
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (w ^ 2) _ _
      (thetaDiagPolynomial_unshift n w hn)) ?_
  refine Q'.eqv_trans _ _ _
    (diag_ring w (Q'.ofNat (n * n)) (w ^ (2 * n * n - 2))) ?_
  exact Q'.mul_eqv_congr_left (RingNormaliser.qpow (1 + w) 3) _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (n * n)) _ _ (Q'.eqv_symm h2))

private theorem thetaOffPolynomial_scaled (n : Nat) (w : Q') (hn : 1 ≤ n) :
    w ^ 2 * thetaOffPolynomial n w ≈
      Q'.ofNat (8 * n * (n + 1)) *
        w ^ (2 * n * (n + 1) + 1) := by
  have hbase : 1 ≤ 2 * n * (n + 1) := by
    exact Nat.le_trans (by omega : 1 ≤ 2 * n)
      (Nat.le_mul_of_pos_right _ (by omega))
  have he : 2 * n * (n + 1) + 1 =
      (2 * n * (n + 1) - 1) + 2 := by omega
  have hp : w ^ (2 * n * (n + 1) + 1) ≈
      w ^ (2 * n * (n + 1) - 1) * w ^ 2 := by
    rw [he]
    exact pow_add_eqv w (2 * n * (n + 1) - 1) 2
  unfold thetaOffPolynomial
  refine Q'.eqv_trans _
    (Q'.ofNat (8 * n * (n + 1)) *
      (w ^ (2 * n * (n + 1) - 1) * w ^ 2)) _ ?_ ?_
  · ring_qeqv
  exact Q'.mul_eqv_congr_left (Q'.ofNat (8 * n * (n + 1))) _ _
    (Q'.eqv_symm hp)

private theorem thetaCellPolynomial_scaled (n : Nat) (w : Q') (hn : 1 ≤ n) :
    w ^ 2 * thetaCellPolynomial n w ≈ thetaActualCellPow n w := by
  unfold thetaCellPolynomial thetaActualCellPow
  refine Q'.eqv_trans _
    (w ^ 2 * thetaDiagPolynomial n w +
      -(w ^ 2 * thetaOffPolynomial n w)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (w ^ 2) (thetaDiagPolynomial n w)
        (-(thetaOffPolynomial n w))) ?_
    exact Q'.add_eqv_congr_left (w ^ 2 * thetaDiagPolynomial n w) _ _
      (Q'.mul_neg_eqv (w ^ 2) (thetaOffPolynomial n w))
  exact Q'.add_eqv_congr'
    (thetaDiagPolynomial_scaled n w hn)
    (Q'.neg_eqv_congr _ _ (thetaOffPolynomial_scaled n w hn))

private theorem integerThetaTerm_eqv_pow (n : Nat) (w : Q') :
    integerThetaTerm w n ≈
      Q'.ofNat (n * n) * w ^ (2 * n * n) := by
  unfold integerThetaTerm
  refine Q'.mul_eqv_congr_left (Q'.ofNat (n * n)) _ _ ?_
  refine Q'.eqv_trans _ _ _ (rgQpow_square_eqv_double_pow w (n * n)) ?_
  have he : n * n + n * n = 2 * n * n := by
    rw [← Nat.add_mul]
    congr 1
    omega
  exact Q'.eqv_of_eq (congrArg (fun e : Nat => w ^ e) he)

private theorem halfThetaTerm_eqv_pow (n : Nat) (w : Q') :
    halfThetaTerm w n ≈
      Q'.ofNat (n * (n + 1)) * w ^ (2 * n * (n + 1)) := by
  unfold halfThetaTerm
  refine Q'.mul_eqv_congr_left (Q'.ofNat (n * (n + 1))) _ _ ?_
  refine Q'.eqv_trans _ _ _
    (rgQpow_square_eqv_double_pow w (n * (n + 1))) ?_
  have he : n * (n + 1) + n * (n + 1) = 2 * n * (n + 1) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  exact Q'.eqv_of_eq (congrArg (fun e : Nat => w ^ e) he)

private theorem off_actual_pow_eqv_theta (n : Nat) (w : Q') :
    Q'.ofNat (8 * n * (n + 1)) *
        w ^ (2 * n * (n + 1) + 1) ≈
      Q'.ofNat 8 * (w * halfThetaTerm w n) := by
  have hc : Q'.ofNat (8 * n * (n + 1)) ≈
      Q'.ofNat 8 * Q'.ofNat (n * (n + 1)) := by
    simpa only [Nat.mul_assoc] using
      HeatKernelRGStep.ofNat_mul_eqv 8 (n * (n + 1))
  have hp : w ^ (2 * n * (n + 1) + 1) =
      w * w ^ (2 * n * (n + 1)) := rfl
  rw [hp]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hc) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 8 *
      (w * (Q'.ofNat (n * (n + 1)) *
        w ^ (2 * n * (n + 1))))) _ ?_ ?_
  · ring_qeqv
  exact Q'.mul_eqv_congr_left (Q'.ofNat 8) _ _
    (Q'.mul_eqv_congr_left w _ _
      (Q'.eqv_symm (halfThetaTerm_eqv_pow n w)))

private theorem thetaActualCellPow_eqv_thetaTerms (n : Nat) (w : Q') :
    thetaActualCellPow n w ≈
      RingNormaliser.qpow ((1 : Q') + w) 3 * integerThetaTerm w n +
        -(Q'.ofNat 8 * (w * halfThetaTerm w n)) := by
  unfold thetaActualCellPow
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left (RingNormaliser.qpow (1 + w) 3) _ _
      (Q'.eqv_symm (integerThetaTerm_eqv_pow n w)))
    (Q'.neg_eqv_congr _ _ (off_actual_pow_eqv_theta n w))

private theorem diagComboRow_eq (D n : Nat) :
    thetaDiagBernCoeff D n = rowScale (Int.ofNat (n * n)) (diagComboRow D n) := by
  funext j
  unfold thetaDiagBernCoeff diagComboRow rowAdd rowScale
  congr 1
  ac_rfl

private theorem diagComboRow_eval (D n : Nat) (w : Q')
    (h0 : 2 * n * n - 2 ≤ D) (h1 : 2 * n * n - 1 ≤ D)
    (h2 : 2 * n * n ≤ D) (h3 : 2 * n * n + 1 ≤ D) :
    signedBernsteinEval D (diagComboRow D n) w ≈
      w ^ (2 * n * n - 2) +
        (Q'.ofNat 3 * w ^ (2 * n * n - 1) +
          (Q'.ofNat 3 * w ^ (2 * n * n) +
            w ^ (2 * n * n + 1))) := by
  unfold diagComboRow
  refine Q'.eqv_trans _ _ _ (signedEval_add D _ _ w) ?_
  refine Q'.add_eqv_congr'
    (thetaMonoBernCoeff_eval D (2 * n * n - 2) w h0) ?_
  refine Q'.eqv_trans _ _ _ (signedEval_add D _ _ w) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · refine Q'.eqv_trans _ _ _ (signedEval_scale D 3 _ w) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofInt 3) _ _
      (thetaMonoBernCoeff_eval D (2 * n * n - 1) w h1)
  · refine Q'.eqv_trans _ _ _ (signedEval_add D _ _ w) ?_
    refine Q'.add_eqv_congr' ?_
      (thetaMonoBernCoeff_eval D (2 * n * n + 1) w h3)
    refine Q'.eqv_trans _ _ _ (signedEval_scale D 3 _ w) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofInt 3) _ _
      (thetaMonoBernCoeff_eval D (2 * n * n) w h2)

private theorem thetaDiagBernCoeff_eval (D n : Nat) (w : Q')
    (h0 : 2 * n * n - 2 ≤ D) (h1 : 2 * n * n - 1 ≤ D)
    (h2 : 2 * n * n ≤ D) (h3 : 2 * n * n + 1 ≤ D) :
    signedBernsteinEval D (thetaDiagBernCoeff D n) w ≈
      thetaDiagPolynomial n w := by
  rw [diagComboRow_eq]
  refine Q'.eqv_trans _ _ _ (signedEval_scale D (Int.ofNat (n * n)) _ w) ?_
  unfold thetaDiagPolynomial
  exact Q'.mul_eqv_congr_left (Q'.ofNat (n * n)) _ _
    (diagComboRow_eval D n w h0 h1 h2 h3)

private theorem thetaOffBernCoeff_eval (D n : Nat) (w : Q')
    (h : 2 * n * (n + 1) - 1 ≤ D) :
    signedBernsteinEval D (thetaOffBernCoeff D n) w ≈
      thetaOffPolynomial n w := by
  have hrow : thetaOffBernCoeff D n =
      rowScale (Int.ofNat (8 * n * (n + 1)))
        (thetaMonoBernCoeff D (2 * n * (n + 1) - 1)) := by
    funext j
    rfl
  rw [hrow]
  refine Q'.eqv_trans _ _ _
    (signedEval_scale D (Int.ofNat (8 * n * (n + 1))) _ w) ?_
  unfold thetaOffPolynomial
  exact Q'.mul_eqv_congr_left (Q'.ofNat (8 * n * (n + 1))) _ _
    (thetaMonoBernCoeff_eval D (2 * n * (n + 1) - 1) w h)

private def thetaCellBernCoeff (D n : Nat) : Nat → Int :=
  rowAdd (thetaDiagBernCoeff D n) (rowNeg (thetaOffBernCoeff D n))

private def thetaCellBernSum (D n : Nat) : Nat → Nat → Int
  | 0 => fun _ => 0
  | c + 1 => rowAdd (thetaCellBernCoeff D n) (thetaCellBernSum D (n + 1) c)

private theorem cumulative_minus_terminal_eq_cellSum
    (D n j : Nat) : ∀ c,
    cumulativeThetaBernCoeff D n j c -
        thetaDiagBernCoeff D (n + c) j =
      thetaCellBernSum D n c j
  | 0 => by
      unfold cumulativeThetaBernCoeff thetaCellBernSum
      rw [Nat.add_zero]
      exact Int.sub_self _
  | c + 1 => by
      have ih := cumulative_minus_terminal_eq_cellSum D (n + 1) j c
      have hn : n + (c + 1) = n + 1 + c := by omega
      rw [hn]
      unfold cumulativeThetaBernCoeff thetaCellBernSum thetaCellBernCoeff
      unfold rowAdd rowNeg
      calc
        thetaDiagBernCoeff D n j - thetaOffBernCoeff D n j +
              cumulativeThetaBernCoeff D (n + 1) j c -
              thetaDiagBernCoeff D (n + 1 + c) j =
            thetaDiagBernCoeff D n j - thetaOffBernCoeff D n j +
              (cumulativeThetaBernCoeff D (n + 1) j c -
                thetaDiagBernCoeff D (n + 1 + c) j) := by omega
        _ = thetaDiagBernCoeff D n j - thetaOffBernCoeff D n j +
              thetaCellBernSum D (n + 1) c j := by rw [ih]
        _ = thetaDiagBernCoeff D n j + -thetaOffBernCoeff D n j +
              thetaCellBernSum D (n + 1) c j := by omega

private theorem growingHeadCoeff_eq_cellSum (D m : Nat) (hm : 1 ≤ m) :
    growingHeadThetaBernCoeff D m = thetaCellBernSum D 1 (m - 1) := by
  funext j
  unfold growingHeadThetaBernCoeff
  have h := cumulative_minus_terminal_eq_cellSum D 1 j (m - 1)
  have hend : 1 + (m - 1) = m := by omega
  rw [hend] at h
  exact h

private theorem signedEval_zero (D : Nat) (w : Q') :
    signedBernsteinEval D (fun _ => (0 : Int)) w ≈ 0 := by
  unfold signedBernsteinEval
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr _ (fun _ => (0 : Q')) (fun j => ?_) (D + 1)) ?_
  · change (0 : Q') * bernsteinBasis D w j ≈ 0
    exact Q'.zero_mul_eqv _
  · rw [finSum_zero_seq]
    exact Q'.eqv_refl 0

private theorem thetaCellBernCoeff_eval (D n : Nat) (w : Q')
    (hdiag : 2 * n * n + 1 ≤ D)
    (hoff : 2 * n * (n + 1) - 1 ≤ D) :
    signedBernsteinEval D (thetaCellBernCoeff D n) w ≈
      thetaCellPolynomial n w := by
  unfold thetaCellBernCoeff thetaCellPolynomial
  refine Q'.eqv_trans _ _ _ (signedEval_add D _ _ w) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · exact thetaDiagBernCoeff_eval D n w (by omega) (by omega) (by omega) hdiag
  · refine Q'.eqv_trans _ _ _ (signedEval_neg D _ w) ?_
    exact Q'.neg_eqv_congr _ _ (thetaOffBernCoeff_eval D n w hoff)

private theorem thetaCellBernSum_eval (D n c : Nat) (w : Q')
    (hdiag : ∀ i, i < c → 2 * (n + i) * (n + i) + 1 ≤ D)
    (hoff : ∀ i, i < c → 2 * (n + i) * (n + i + 1) - 1 ≤ D) :
    signedBernsteinEval D (thetaCellBernSum D n c) w ≈
      thetaCellPolynomialSum n w c := by
  induction c generalizing n with
  | zero =>
      unfold thetaCellBernSum thetaCellPolynomialSum
      exact signedEval_zero D w
  | succ c ih =>
      unfold thetaCellBernSum thetaCellPolynomialSum
      refine Q'.eqv_trans _ _ _ (signedEval_add D _ _ w) ?_
      refine Q'.add_eqv_congr' ?_ ?_
      · exact thetaCellBernCoeff_eval D n w
          (hdiag 0 (by omega)) (hoff 0 (by omega))
      · apply ih
        · intro i hi
          have h := hdiag (i + 1) (by omega)
          have hn : n + (i + 1) = n + 1 + i := by omega
          rw [hn] at h
          exact h
        · intro i hi
          have h := hoff (i + 1) (by omega)
          have hn : n + (i + 1) = n + 1 + i := by omega
          rw [hn] at h
          exact h

private theorem minimal_diag_bound (m s : Nat) (hs : s ≤ m) :
    2 * s * s + 1 ≤ 2 * m * m + 1 := by
  have hsq : s * s ≤ m * m := Nat.mul_le_mul hs hs
  have h2 := Nat.mul_le_mul_left 2 hsq
  simpa only [Nat.mul_assoc] using Nat.add_le_add_right h2 1

private theorem minimal_off_bound (m s : Nat) (hs : s + 1 ≤ m) :
    2 * s * (s + 1) - 1 ≤ 2 * m * m + 1 := by
  have hs0 : s ≤ m := by omega
  have hp : s * (s + 1) ≤ m * m := Nat.mul_le_mul hs0 hs
  have h2 : 2 * s * (s + 1) ≤ 2 * m * m := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hp
  have hsub : 2 * s * (s + 1) - 1 ≤ 2 * s * (s + 1) := Nat.sub_le _ _
  have hadd : 2 * m * m ≤ 2 * m * m + 1 := Nat.le_add_right _ _
  exact Nat.le_trans hsub (Nat.le_trans h2 hadd)

/-- The minimal-degree growing-head coefficient row evaluates to the finite
sum of its paired diagonal/off-diagonal cell polynomials. -/
theorem growingHeadThetaBernCoeff_eval (m : Nat) (w : Q') (hm : 2 ≤ m) :
    signedBernsteinEval (2 * m * m + 1)
        (growingHeadThetaBernCoeff (2 * m * m + 1) m) w ≈
      thetaCellPolynomialSum 1 w (m - 1) := by
  rw [growingHeadCoeff_eq_cellSum (2 * m * m + 1) m (by omega)]
  apply thetaCellBernSum_eval
  · intro i hi
    exact minimal_diag_bound m (1 + i) (by omega)
  · intro i hi
    exact minimal_off_bound m (1 + i) (by omega)

private def thetaActualCellPowSum (n : Nat) (w : Q') : Nat → Q'
  | 0 => 0
  | c + 1 => thetaActualCellPow n w + thetaActualCellPowSum (n + 1) w c

private theorem thetaCellPolynomialSum_scaled (n c : Nat) (w : Q')
    (hn : 1 ≤ n) :
    w ^ 2 * thetaCellPolynomialSum n w c ≈
      thetaActualCellPowSum n w c := by
  induction c generalizing n with
  | zero =>
      unfold thetaCellPolynomialSum thetaActualCellPowSum
      exact Q'.mul_zero_eqv (w ^ 2)
  | succ c ih =>
      unfold thetaCellPolynomialSum thetaActualCellPowSum
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv (w ^ 2) (thetaCellPolynomial n w)
          (thetaCellPolynomialSum (n + 1) w c)) ?_
      exact Q'.add_eqv_congr'
        (thetaCellPolynomial_scaled n w hn)
        (ih (n + 1) (by omega))

private theorem thetaActualCellPowSum_eqv_finSum
    (n c : Nat) (w : Q') :
    thetaActualCellPowSum n w c ≈
      finSum (fun j => thetaActualCellPow (n + j) w) c := by
  induction c generalizing n with
  | zero =>
      exact Q'.eqv_refl 0
  | succ c ih =>
      unfold thetaActualCellPowSum
      have hp := RationalTail.finSum_peel_left
        (fun j => thetaActualCellPow (n + j) w) c
      refine Q'.eqv_trans _
        (thetaActualCellPow n w +
          finSum (fun j => thetaActualCellPow (n + 1 + j) w) c) _ ?_ ?_
      · exact Q'.add_eqv_congr_left (thetaActualCellPow n w) _ _
          (ih (n + 1))
      refine Q'.eqv_trans _
        (thetaActualCellPow (n + 0) w +
          finSum (fun j => thetaActualCellPow (n + (j + 1)) w) c) _ ?_ ?_
      · refine Q'.add_eqv_congr' (Q'.eqv_refl _) ?_
        refine finSum_eqv_congr _ _ (fun j => ?_) c
        have he : n + 1 + j = n + (j + 1) := by omega
        rw [he]
        exact Q'.eqv_refl _
      exact Q'.eqv_symm hp

private theorem finSum_thetaTerms (w : Q') (c : Nat) :
    finSum
        (fun j =>
          RingNormaliser.qpow ((1 : Q') + w) 3 * integerThetaTerm w (j + 1) +
            -(Q'.ofNat 8 * (w * halfThetaTerm w (j + 1)))) c ≈
      RingNormaliser.qpow ((1 : Q') + w) 3 *
          finSum (fun j => integerThetaTerm w (j + 1)) c +
        -(Q'.ofNat 8 *
          (w * finSum (fun j => halfThetaTerm w (j + 1)) c)) := by
  let F := RingNormaliser.qpow ((1 : Q') + w) 3
  let I : QSeq := fun j => integerThetaTerm w (j + 1)
  let H : QSeq := fun j => halfThetaTerm w (j + 1)
  let B : QSeq := fun j => Q'.ofNat 8 * (w * H j)
  refine Q'.eqv_trans _
    (finSum (fun j => F * I j) c + finSum (fun j => -(B j)) c) _ ?_ ?_
  · exact RationalTail.finSum_add (fun j => F * I j)
      (fun j => -(B j)) c
  refine Q'.add_eqv_congr' ?_ ?_
  · exact Q'.eqv_symm (const_mul_finSum I F c)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (YMGap.Constructive.neg_finSum B c)) ?_
  refine Q'.neg_eqv_congr _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (const_mul_finSum (fun j => w * H j) (Q'.ofNat 8) c)) ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat 8) _ _
    (Q'.eqv_symm (const_mul_finSum H w c))

private theorem thetaActualCellPowSum_eqv_growingResidual
    (c : Nat) (w : Q') (hc : 1 ≤ c) :
    thetaActualCellPowSum 1 w c ≈
      growingHeadScaledThetaResidual w (c - 1) := by
  refine Q'.eqv_trans _ _ _ (thetaActualCellPowSum_eqv_finSum 1 c w) ?_
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun j => thetaActualCellPow (1 + j) w)
      (fun j =>
        RingNormaliser.qpow ((1 : Q') + w) 3 * integerThetaTerm w (j + 1) +
          -(Q'.ofNat 8 * (w * halfThetaTerm w (j + 1))))
      (fun j => by
        simpa only [Nat.one_add] using
          thetaActualCellPow_eqv_thetaTerms (j + 1) w) c) ?_
  refine Q'.eqv_trans _ _ _ (finSum_thetaTerms w c) ?_
  have hlen : c - 1 + 1 = c := by omega
  unfold growingHeadScaledThetaResidual integerThetaSum halfThetaSum
  rw [hlen]
  exact Q'.eqv_refl _

/-- **Actual semantic reconstruction of the growing-head Pascal row.**
After restoring the common `w²` factored from every cell, the signed
minimal-degree Bernstein evaluation is exactly the physical growing-head
theta residual. -/
theorem growingHeadThetaBernCoeff_scaled_eval_eqv_residual
    (m : Nat) (w : Q') (hm : 2 ≤ m) :
    w ^ 2 *
        signedBernsteinEval (2 * m * m + 1)
          (growingHeadThetaBernCoeff (2 * m * m + 1) m) w ≈
      growingHeadScaledThetaResidual w (m - 2) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (w ^ 2) _ _
      (growingHeadThetaBernCoeff_eval m w hm)) ?_
  refine Q'.eqv_trans _ _ _
    (thetaCellPolynomialSum_scaled 1 (m - 1) w (by omega)) ?_
  have hc : 1 ≤ m - 1 := by omega
  have h := thetaActualCellPowSum_eqv_growingResidual (m - 1) w hc
  have hidx : m - 1 - 1 = m - 2 := by omega
  rw [hidx] at h
  exact h

#print axioms pnChoose_eq_binom
#print axioms thetaMonoBernCoeff_eval
#print axioms growingHeadThetaBernCoeff_eval
#print axioms growingHeadThetaBernCoeff_scaled_eval_eqv_residual

end YMGap.Continuum.HarmonicThetaPascalEvaluation
