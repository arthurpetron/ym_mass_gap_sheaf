/-
Physical closure of the seven-Dirichlet Pascal certificate.

The projective theorem is parametrised by `m = 2t+4`.  On the harmonic
schedule, `t=k+1` and this is definitionally the endpoint
`growingAnchor k + 2`.  This file reconstructs the signed Bernstein row as
the actual endpoint-free Dirichlet core, cancels the positive projective
denominator, and transports the resulting sign to the frozen shell/spacing
consumer.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBulkInduction
import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFirstBandPayment

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPhysicalClosure

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMovingDeterminantAllTail
open YMGap.Continuum.HarmonicMovingDeterminantDirect
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaCross
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalBulkInduction
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCore
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCentral
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaLinearCarrier
open YMGap.Continuum.HarmonicThetaPascalBridge
open YMGap.Continuum.HarmonicThetaPascalEvaluation
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem physical_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "physical_ring" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, physical_neg_num_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private def physicalRowAdd (a b : Nat → Int) : Nat → Int :=
  fun j => a j + b j

private def physicalRowNeg (a : Nat → Int) : Nat → Int :=
  fun j => -(a j)

private def physicalRowScale (z : Int) (a : Nat → Int) : Nat → Int :=
  fun j => z * a j

private theorem signedEval_add (D : Nat) (a b : Nat → Int) (w : Q') :
    signedBernsteinEval D (physicalRowAdd a b) w ≈
      signedBernsteinEval D a w + signedBernsteinEval D b w := by
  unfold signedBernsteinEval physicalRowAdd
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

private theorem signedEval_neg (D : Nat) (a : Nat → Int) (w : Q') :
    signedBernsteinEval D (physicalRowNeg a) w ≈
      -(signedBernsteinEval D a w) := by
  unfold signedBernsteinEval physicalRowNeg
  refine Q'.eqv_trans _ _ _
    (finSum_eqv_congr
      (fun j => Q'.ofInt (-a j) * bernsteinBasis D w j)
      (fun j => -(Q'.ofInt (a j) * bernsteinBasis D w j))
      (fun j => ?_) (D + 1)) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (show Q'.ofInt (-a j) ≈
        -(Q'.ofInt (a j)) by rfl)) ?_
    exact Q'.neg_mul_eqv (Q'.ofInt (a j)) (bernsteinBasis D w j)
  · exact Q'.eqv_symm
      (YMGap.Constructive.neg_finSum
        (fun j => Q'.ofInt (a j) * bernsteinBasis D w j) (D + 1))

private theorem signedEval_scale (D : Nat) (z : Int)
    (a : Nat → Int) (w : Q') :
    signedBernsteinEval D (physicalRowScale z a) w ≈
      Q'.ofInt z * signedBernsteinEval D a w := by
  unfold signedBernsteinEval physicalRowScale
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

private theorem signedEval_congr (D : Nat) (a b : Nat → Int) (w : Q')
    (h : ∀ j, a j = b j) :
    signedBernsteinEval D a w ≈ signedBernsteinEval D b w := by
  unfold signedBernsteinEval
  exact finSum_eqv_congr _ _ (fun j => by rw [h j]; exact Q'.eqv_refl _) _

private theorem pow_add_eqv (w : Q') (a : Nat) : ∀ b,
    w ^ (a + b) ≈ w ^ a * w ^ b
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (w ^ a))
  | b + 1 => by
      have ih := pow_add_eqv w a b
      show w * w ^ (a + b) ≈ w ^ a * (w * w ^ b)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ ih) ?_
      physical_ring

private theorem rgQpow_eqv_pow (w : Q') : ∀ n,
    RGTransport.qpow w n ≈ w ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      have ih := rgQpow_eqv_pow w n
      show RGTransport.qpow w n * w ≈ w * w ^ n
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ w ih) ?_
      exact Q'.mul_comm_eqv (w ^ n) w

private theorem mul_pow_eqv (a b : Q') : ∀ (n : Nat),
    (a * b) ^ n ≈ a ^ n * b ^ n
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | n + 1 => by
      have ih := mul_pow_eqv a b n
      show (a * b) * (a * b) ^ n ≈ (a * a ^ n) * (b * b ^ n)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (a * b) _ _ ih) ?_
      physical_ring

private theorem rgQpow_square_eqv_double_pow (w : Q') (n : Nat) :
    RGTransport.qpow (w * w) n ≈ w ^ (n + n) := by
  refine Q'.eqv_trans _ _ _ (rgQpow_eqv_pow (w * w) n) ?_
  refine Q'.eqv_trans _ _ _ (mul_pow_eqv w w n) ?_
  exact Q'.eqv_symm (pow_add_eqv w n n)

private def sevenMassCellPolynomial (n : Nat) (w : Q') : Q' :=
  Q'.ofNat (7 * n * n) *
    (w ^ (2 * n * n - 2) +
      (-(Q'.ofNat 2 * w ^ (2 * n * n - 1)) + w ^ (2 * n * n)))

private def sevenMassHeadPolynomial (w : Q') : Nat → Q'
  | 0 => 0
  | c + 1 => sevenMassHeadPolynomial w c + sevenMassCellPolynomial (c + 1) w

private theorem sevenMassCellBernCoeff_eval (D n : Nat) (w : Q')
    (hD : 2 * n * n ≤ D) :
    signedBernsteinEval D (sevenMassCellBernCoeff D n) w ≈
      sevenMassCellPolynomial n w := by
  let a := thetaMonoBernCoeff D (2 * n * n - 2)
  let b := thetaMonoBernCoeff D (2 * n * n - 1)
  let c := thetaMonoBernCoeff D (2 * n * n)
  have hrow : ∀ j, sevenMassCellBernCoeff D n j =
      physicalRowScale (Int.ofNat (7 * n * n))
        (physicalRowAdd a
          (physicalRowAdd (physicalRowNeg (physicalRowScale 2 b)) c)) j := by
    intro j
    simp only [sevenMassCellBernCoeff, physicalRowScale, physicalRowAdd,
      physicalRowNeg, a, b, c]
    simp only [Int.sub_eq_add_neg]
    ac_rfl
  refine Q'.eqv_trans _ _ _ (signedEval_congr D _ _ w hrow) ?_
  refine Q'.eqv_trans _ _ _ (signedEval_scale D _ _ w) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ (signedEval_add D a _ w) ?_
  refine Q'.add_eqv_congr'
    (thetaMonoBernCoeff_eval D (2 * n * n - 2) w (by omega)) ?_
  refine Q'.eqv_trans _ _ _ (signedEval_add D _ c w) ?_
  refine Q'.add_eqv_congr' ?_
    (thetaMonoBernCoeff_eval D (2 * n * n) w hD)
  refine Q'.eqv_trans _ _ _ (signedEval_neg D _ w) ?_
  refine Q'.neg_eqv_congr _ _ ?_
  refine Q'.eqv_trans _ _ _ (signedEval_scale D 2 b w) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (thetaMonoBernCoeff_eval D (2 * n * n - 1) w (by omega))

private theorem sevenMassHeadBernCoeff_eval (D c : Nat) (w : Q')
    (hD : 2 * c * c ≤ D) :
    signedBernsteinEval D (sevenMassHeadBernCoeff D · c) w ≈
      sevenMassHeadPolynomial w c := by
  induction c with
  | zero =>
      unfold sevenMassHeadBernCoeff sevenMassHeadPolynomial signedBernsteinEval
      refine Q'.eqv_trans _ _ _
        (finSum_eqv_congr _ (fun _ => (0 : Q')) (fun j => ?_) (D + 1)) ?_
      · exact Q'.zero_mul_eqv _
      · rw [finSum_zero_seq]
        exact Q'.eqv_refl 0
  | succ c ih =>
      have hcD : 2 * c * c ≤ D := by
        have hle : c ≤ c + 1 := by omega
        have hs := Nat.mul_le_mul hle hle
        simp only [Nat.mul_assoc] at hD ⊢
        omega
      have hrow : ∀ j, sevenMassHeadBernCoeff D j (c + 1) =
          physicalRowAdd (sevenMassHeadBernCoeff D · c)
            (sevenMassCellBernCoeff D (c + 1)) j := by
        intro j
        rfl
      refine Q'.eqv_trans _ _ _ (signedEval_congr D _ _ w hrow) ?_
      refine Q'.eqv_trans _ _ _ (signedEval_add D _ _ w) ?_
      exact Q'.add_eqv_congr' (ih hcD)
        (sevenMassCellBernCoeff_eval D (c + 1) w hD)

private theorem pow_mul_eqv (w : Q') (a b : Nat) :
    w ^ a * w ^ b ≈ w ^ (a + b) :=
  Q'.eqv_symm (pow_add_eqv w a b)

private theorem pow_one_eqv (w : Q') : w ^ 1 ≈ w := by
  change w * 1 ≈ w
  exact Q'.mul_one_eqv w

private def massSquarePolyL : RingNormaliser.PolyExpr :=
  let s := RingNormaliser.PolyExpr.var 0
  let n := RingNormaliser.PolyExpr.var 1
  let w := RingNormaliser.PolyExpr.var 2
  let x := RingNormaliser.PolyExpr.var 3
  .mul (.mul s n)
    (.add x (.add (.neg (.mul (.const 2) (.mul w x))) (.mul w (.mul w x))))

private def massSquarePolyR : RingNormaliser.PolyExpr :=
  let s := RingNormaliser.PolyExpr.var 0
  let n := RingNormaliser.PolyExpr.var 1
  let w := RingNormaliser.PolyExpr.var 2
  let x := RingNormaliser.PolyExpr.var 3
  .mul (.mul s (.mul (.add (.const 1) (.neg w))
    (.add (.const 1) (.neg w)))) (.mul n x)

private theorem massSquarePoly_normal :
    RingNormaliser.normalize massSquarePolyL =
      RingNormaliser.normalize massSquarePolyR := by
  decide

private theorem mass_square_identity (s n w x : Q') :
    (s * n) * (x + (-(Q'.ofNat 2 * (w * x)) + w * (w * x))) ≈
      s * (((1 : Q') + -w) * ((1 : Q') + -w)) * (n * x) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    massSquarePolyL massSquarePolyR massSquarePoly_normal
    (fun
      | 0 => s
      | 1 => n
      | 2 => w
      | _ => x)
  simpa [massSquarePolyL, massSquarePolyR, RingNormaliser.eval] using h

private theorem sevenMassCellPolynomial_scaled (n : Nat) (w : Q')
    (hn : 1 ≤ n) :
    w ^ 2 * sevenMassCellPolynomial n w ≈
      Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
        integerThetaTerm w n := by
  let A := 2 * n * n
  have hA : 2 ≤ A := by
    dsimp only [A]
    have hs : 1 ≤ n * n := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul hn hn
    simpa only [Nat.mul_assoc, Nat.mul_one] using Nat.mul_le_mul_left 2 hs
  have h0 : w ^ 2 * w ^ (A - 2) ≈ w ^ A := by
    refine Q'.eqv_trans _ _ _ (pow_mul_eqv w 2 (A - 2)) ?_
    have he : 2 + (A - 2) = A := by omega
    rw [he]
    exact Q'.eqv_refl _
  have h1 : w ^ 2 * w ^ (A - 1) ≈ w * w ^ A := by
    refine Q'.eqv_trans _ _ _ (pow_mul_eqv w 2 (A - 1)) ?_
    change w ^ (2 + (A - 1)) ≈ w ^ (A + 1)
    have he : 2 + (A - 1) = A + 1 := by omega
    rw [he]
    exact Q'.eqv_refl _
  have h2 : w ^ 2 * w ^ A ≈ w * (w * w ^ A) := by
    refine Q'.eqv_trans _ _ _ (pow_mul_eqv w 2 A) ?_
    change w ^ (2 + A) ≈ w ^ (A + 2)
    have he : 2 + A = A + 2 := by omega
    rw [he]
    exact Q'.eqv_refl _
  have hI : integerThetaTerm w n ≈ Q'.ofNat (n * n) * w ^ A := by
    unfold integerThetaTerm
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _ (rgQpow_square_eqv_double_pow w (n * n)) ?_
    have he : n * n + n * n = A := by
      dsimp only [A]
      rw [Nat.two_mul, Nat.add_mul]
    rw [he]
    exact Q'.eqv_refl _
  have hcoef : Q'.ofNat (7 * n * n) ≈
      Q'.ofNat 7 * Q'.ofNat (n * n) := by
    simpa only [Nat.mul_assoc] using
      (HeatKernelRGStep.ofNat_mul_eqv 7 (n * n))
  unfold sevenMassCellPolynomial
  dsimp only [A] at h0 h1 h2 hI
  refine Q'.eqv_trans _
    (Q'.ofNat (7 * n * n) *
      ((w ^ 2 * w ^ (2 * n * n - 2)) +
        (-(Q'.ofNat 2 * (w ^ 2 * w ^ (2 * n * n - 1))) +
          w ^ 2 * w ^ (2 * n * n)))) _ (by physical_ring) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (7 * n * n) *
      (w ^ (2 * n * n) +
        (-(Q'.ofNat 2 * (w * w ^ (2 * n * n))) +
          w * (w * w ^ (2 * n * n))))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.add_eqv_congr' h0
        (Q'.add_eqv_congr'
          (Q'.neg_eqv_congr _ _
            (Q'.mul_eqv_congr_left _ _ _ h1)) h2))
  refine Q'.eqv_trans _
    ((Q'.ofNat 7 * Q'.ofNat (n * n)) *
      (w ^ (2 * n * n) +
        (-(Q'.ofNat 2 * (w * w ^ (2 * n * n))) +
          w * (w * w ^ (2 * n * n))))) _
    (Q'.mul_eqv_congr_right _ _ _ hcoef) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
      (Q'.ofNat (n * n) * w ^ (2 * n * n))) _
    (mass_square_identity (Q'.ofNat 7) (Q'.ofNat (n * n)) w
      (w ^ (2 * n * n))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hI)

private theorem sevenMassHeadPolynomial_scaled (c : Nat) (w : Q') :
    w ^ 2 * sevenMassHeadPolynomial w c ≈
      Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
        finSum (fun j => integerThetaTerm w (j + 1)) c := by
  induction c with
  | zero =>
      simp only [sevenMassHeadPolynomial, finSum_zero]
      exact Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv (w ^ 2))
        (Q'.eqv_symm
          (Q'.mul_zero_eqv
            (Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)))))
  | succ c ih =>
      simp only [sevenMassHeadPolynomial, finSum_succ]
      refine Q'.eqv_trans _
        (w ^ 2 * sevenMassHeadPolynomial w c +
          w ^ 2 * sevenMassCellPolynomial (c + 1) w) _
        (Q'.mul_add_eqv _ _ _) ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
            finSum (fun j => integerThetaTerm w (j + 1)) c) +
          Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
            integerThetaTerm w (c + 1)) _
        (Q'.add_eqv_congr' ih
          (sevenMassCellPolynomial_scaled (c + 1) w (by omega))) ?_
      physical_ring

/-- Semantic reconstruction of the seven-unit Bernstein row before the
terminal endpoint is removed. -/
theorem sevenGapBernCoeff_scaled_eval (m : Nat) (w : Q') (hm : 2 ≤ m) :
    let D := sevenGapDegree m
    w ^ 2 * signedBernsteinEval D (sevenGapBernCoeff D m) w ≈
      Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
          integerThetaSum w (m - 2) +
        -(growingHeadScaledThetaResidual w (m - 2)) := by
  let D := sevenGapDegree m
  let M : Nat → Int := fun j => sevenMassHeadBernCoeff D j (m - 1)
  let G := growingHeadThetaBernCoeff D m
  have hD : 2 * (m - 1) * (m - 1) ≤ D := by
    dsimp only [D, sevenGapDegree]
    have hle : m - 1 ≤ m := Nat.sub_le m 1
    have hs := Nat.mul_le_mul hle hle
    simp only [Nat.mul_assoc] at hs ⊢
    omega
  have hrow : ∀ j, sevenGapBernCoeff D m j =
      physicalRowAdd M (physicalRowNeg G) j := by
    intro j
    simp only [sevenGapBernCoeff, physicalRowAdd, physicalRowNeg, M, G]
    omega
  have heval : signedBernsteinEval D (sevenGapBernCoeff D m) w ≈
      signedBernsteinEval D M w + -(signedBernsteinEval D G w) := by
    refine Q'.eqv_trans _ _ _ (signedEval_congr D _ _ w hrow) ?_
    refine Q'.eqv_trans _ _ _ (signedEval_add D M (physicalRowNeg G) w) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _) (signedEval_neg D G w)
  refine Q'.eqv_trans _
    (w ^ 2 *
      (signedBernsteinEval D M w + -(signedBernsteinEval D G w))) _
    (Q'.mul_eqv_congr_left _ _ _ heval) ?_
  refine Q'.eqv_trans _
    (w ^ 2 * signedBernsteinEval D M w +
      -(w ^ 2 * signedBernsteinEval D G w)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_neg_eqv _ _)
  have hmass0 := sevenMassHeadBernCoeff_eval D (m - 1) w hD
  have hmass1 : w ^ 2 * signedBernsteinEval D M w ≈
      w ^ 2 * sevenMassHeadPolynomial w (m - 1) :=
    Q'.mul_eqv_congr_left _ _ _ hmass0
  have hmass2 := sevenMassHeadPolynomial_scaled (m - 1) w
  have hlen : m - 2 + 1 = m - 1 := by omega
  have hmass : w ^ 2 * signedBernsteinEval D M w ≈
      Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
        integerThetaSum w (m - 2) := by
    refine Q'.eqv_trans _ _ _ hmass1 ?_
    refine Q'.eqv_trans _ _ _ hmass2 ?_
    unfold integerThetaSum
    rw [hlen]
    exact Q'.eqv_refl _
  have hgrow : w ^ 2 * signedBernsteinEval D G w ≈
      growingHeadScaledThetaResidual w (m - 2) := by
    dsimp only [D, G, sevenGapDegree]
    exact growingHeadThetaBernCoeff_scaled_eval_eqv_residual m w hm
  exact Q'.add_eqv_congr' hmass (Q'.neg_eqv_congr _ _ hgrow)

private theorem coreEndpoint_scaled_eval (m : Nat) (w : Q') (hm : 1 ≤ m) :
    let D := sevenGapDegree m
    let E := physicalRowScale (Int.ofNat (4 * m * m))
      (thetaMonoBernCoeff D (2 * m * m - 2))
    w ^ 2 * signedBernsteinEval D E w ≈
      Q'.ofNat 4 * integerThetaTerm w m := by
  let D := sevenGapDegree m
  let A := 2 * m * m
  let E := physicalRowScale (Int.ofNat (4 * m * m))
    (thetaMonoBernCoeff D (A - 2))
  have hA : 2 ≤ A := by
    dsimp only [A]
    have hs : 1 ≤ m * m := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul hm hm
    simpa only [Nat.mul_assoc, Nat.mul_one] using Nat.mul_le_mul_left 2 hs
  have heD : A - 2 ≤ D := by
    dsimp only [A, D, sevenGapDegree]
    omega
  have hscale := signedEval_scale D (Int.ofNat (4 * m * m))
    (thetaMonoBernCoeff D (A - 2)) w
  have hmono := thetaMonoBernCoeff_eval D (A - 2) w heD
  have hp : w ^ 2 * w ^ (A - 2) ≈ w ^ A := by
    refine Q'.eqv_trans _ _ _ (pow_mul_eqv w 2 (A - 2)) ?_
    have he : 2 + (A - 2) = A := by omega
    rw [he]
    exact Q'.eqv_refl _
  have hI : integerThetaTerm w m ≈ Q'.ofNat (m * m) * w ^ A := by
    unfold integerThetaTerm
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _ (rgQpow_square_eqv_double_pow w (m * m)) ?_
    have he : m * m + m * m = A := by
      dsimp only [A]
      rw [Nat.two_mul, Nat.add_mul]
    rw [he]
    exact Q'.eqv_refl _
  have hcoef : Q'.ofNat (4 * m * m) ≈
      Q'.ofNat 4 * Q'.ofNat (m * m) := by
    simpa only [Nat.mul_assoc] using
      (HeatKernelRGStep.ofNat_mul_eqv 4 (m * m))
  have hnat : Q'.ofInt (Int.ofNat (4 * m * m)) ≈
      Q'.ofNat (4 * m * m) := by
    rfl
  dsimp only [E]
  refine Q'.eqv_trans _
    (w ^ 2 * (Q'.ofInt (Int.ofNat (4 * m * m)) *
      signedBernsteinEval D (thetaMonoBernCoeff D (A - 2)) w)) _
    (Q'.mul_eqv_congr_left _ _ _ hscale) ?_
  refine Q'.eqv_trans _
    (w ^ 2 * (Q'.ofNat (4 * m * m) *
      signedBernsteinEval D (thetaMonoBernCoeff D (A - 2)) w)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hnat)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (4 * m * m) *
      (w ^ 2 * signedBernsteinEval D
        (thetaMonoBernCoeff D (A - 2)) w)) _ (by physical_ring) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (4 * m * m) * (w ^ 2 * w ^ (A - 2))) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hmono)) ?_
  refine Q'.eqv_trans _ (Q'.ofNat (4 * m * m) * w ^ A) _
    (Q'.mul_eqv_congr_left _ _ _ hp) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 4 * Q'.ofNat (m * m)) * w ^ A) _
    (Q'.mul_eqv_congr_right _ _ _ hcoef) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * (Q'.ofNat (m * m) * w ^ A)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hI)

/-- The exact endpoint-free row evaluates to the seven-unit carrier with the
positive terminal integer mode removed. -/
theorem sevenCoreBernCoeff_scaled_eval (m : Nat) (w : Q') (hm : 2 ≤ m) :
    let D := sevenGapDegree m
    w ^ 2 * signedBernsteinEval D (sevenCoreBernCoeff D m) w ≈
      (Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
          integerThetaSum w (m - 2) +
        -(growingHeadScaledThetaResidual w (m - 2))) +
      -(Q'.ofNat 4 * integerThetaTerm w m) := by
  let D := sevenGapDegree m
  let G := sevenGapBernCoeff D m
  let E := physicalRowScale (Int.ofNat (4 * m * m))
    (thetaMonoBernCoeff D (2 * m * m - 2))
  have hrow : ∀ j, sevenCoreBernCoeff D m j =
      physicalRowAdd G (physicalRowNeg E) j := by
    intro j
    simp only [sevenCoreBernCoeff, physicalRowAdd, physicalRowNeg,
      physicalRowScale, G, E]
    omega
  have heval : signedBernsteinEval D (sevenCoreBernCoeff D m) w ≈
      signedBernsteinEval D G w + -(signedBernsteinEval D E w) := by
    refine Q'.eqv_trans _ _ _ (signedEval_congr D _ _ w hrow) ?_
    refine Q'.eqv_trans _ _ _ (signedEval_add D G (physicalRowNeg E) w) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _) (signedEval_neg D E w)
  refine Q'.eqv_trans _
    (w ^ 2 * (signedBernsteinEval D G w +
      -(signedBernsteinEval D E w))) _
    (Q'.mul_eqv_congr_left _ _ _ heval) ?_
  refine Q'.eqv_trans _
    (w ^ 2 * signedBernsteinEval D G w +
      -(w ^ 2 * signedBernsteinEval D E w)) _ ?_ ?_
  · refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
    exact Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_neg_eqv _ _)
  have hgap : w ^ 2 * signedBernsteinEval D G w ≈
      Q'.ofNat 7 * (((1 : Q') + -w) * ((1 : Q') + -w)) *
          integerThetaSum w (m - 2) +
        -(growingHeadScaledThetaResidual w (m - 2)) := by
    dsimp only [D, G]
    exact sevenGapBernCoeff_scaled_eval m w hm
  have hend : w ^ 2 * signedBernsteinEval D E w ≈
      Q'.ofNat 4 * integerThetaTerm w m := by
    dsimp only [D, E]
    exact coreEndpoint_scaled_eval m w (by omega)
  exact Q'.add_eqv_congr' hgap (Q'.neg_eqv_congr _ _ hend)

private theorem harmonic_complement_eqv_unit (k : Nat) :
    ((1 : Q') + -(harmW k)) ≈ harmU k := by
  simpa [harmW, ReciprocalBernoulliUpper.oneSub] using
    (YMGap.Continuum.AFRateCalibration.one_sub_one_sub_eqv (harmU k))

private theorem harmonic_complement_mul_den (k : Nat) :
    ((1 : Q') - harmW k) * Q'.ofNat (k + 2) ≈ 1 := by
  have hcomp : ((1 : Q') - harmW k) ≈ harmU k := by
    simpa [Q'.sub] using harmonic_complement_eqv_unit k
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.ofNat (k + 2)) hcomp)
    (harmonicUnit_mul_den k)

private theorem pow_pos (q : Q') (hq : (0 : Q') < q) : ∀ n : Nat,
    (0 : Q') < q ^ n
  | 0 => by
      change (0 : Q') < 1
      decide
  | n + 1 => by
      rw [Q'.pow_succ]
      exact Q'.mul_pos hq (pow_pos q hq n)

/-- The schedule identity is exact: `m=2(k+1)+4` is precisely the first
integer mode omitted by `growingAnchor k`. -/
theorem harmonic_sevenCore_scaled_eval_eqv_dirichletCore (k : Nat) :
    let m := growingAnchor k + 2
    let D := sevenGapDegree m
    (harmW k) ^ 2 *
        signedBernsteinEval D (sevenCoreBernCoeff D m) (harmW k) ≈
      sevenDirichletCoreGap k := by
  let m := growingAnchor k + 2
  let D := sevenGapDegree m
  let I := integerThetaSum (harmW k) (growingAnchor k)
  let R := growingHeadScaledThetaResidual (harmW k) (growingAnchor k)
  let E := Q'.ofNat 4 * integerThetaTerm (harmW k) m
  let C := sevenDirichletCoreGap k
  have hm : 2 ≤ m := by dsimp only [m]; omega
  have hmback : m - 2 = growingAnchor k := by dsimp only [m]; omega
  have heval := sevenCoreBernCoeff_scaled_eval m (harmW k) hm
  dsimp only [D]
  refine Q'.eqv_trans _
    ((Q'.ofNat 7 *
          (((1 : Q') + -(harmW k)) * ((1 : Q') + -(harmW k))) * I +
        -R) + -E) _ ?_ ?_
  · dsimp only [D] at heval
    rw [hmback] at heval
    simpa only [I, R, E] using heval
  have hc := harmonic_complement_eqv_unit k
  have hsq :
      (((1 : Q') + -(harmW k)) * ((1 : Q') + -(harmW k))) ≈
        harmU k * harmU k :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.mul_eqv_congr_left _ _ _ hc)
  have hmass :
      Q'.ofNat 7 *
          (((1 : Q') + -(harmW k)) * ((1 : Q') + -(harmW k))) * I ≈
        Q'.ofNat 7 * (harmU k * harmU k) * I :=
    Q'.mul_eqv_congr_right _ _ I
      (Q'.mul_eqv_congr_left _ _ _ hsq)
  have hunit :
      Q'.ofNat 7 *
          (((1 : Q') + -(harmW k)) * ((1 : Q') + -(harmW k))) * I +
          -R ≈ sevenUnitResidualGap k := by
    unfold sevenUnitResidualGap growingPascalResidual
    dsimp only [I, R]
    exact Q'.add_eqv_congr' hmass (Q'.eqv_refl _)
  refine Q'.eqv_trans _ (sevenUnitResidualGap k + -E) _
    (Q'.add_eqv_congr' hunit (Q'.eqv_refl _)) ?_
  have hcore := sevenUnitResidualGap_eqv_core_endpoint k
  have hmendpoint : growingAnchor k + 2 = m := by rfl
  rw [hmendpoint] at hcore
  refine Q'.eqv_trans _ ((C + E) + -E) _
    (Q'.add_eqv_congr_right _ _ _ hcore) ?_
  refine Q'.eqv_trans _ (C + (E + -E)) _ (Q'.add_assoc_eqv C E (-E)) ?_
  refine Q'.eqv_trans _ (C + 0) _
    (Q'.add_eqv_congr_left C _ _ (Q'.add_neg_self_eqv E)) ?_
  exact YMGap.Constructive.QPoly.q_add_zero_eqv C

/-- Projective positivity cancels back to the signed Bernstein evaluation at
the harmonic point. -/
theorem harmonic_sevenCore_signed_eval_nonnegative (k : Nat) :
    let m := growingAnchor k + 2
    let D := sevenGapDegree m
    (0 : Q') ≤
      signedBernsteinEval D (sevenCoreBernCoeff D m) (harmW k) := by
  let m := growingAnchor k + 2
  let D := sevenGapDegree m
  let den := Q'.ofNat (k + 2)
  have hprojective :
      (0 : Q') ≤ projectiveDeficitEval D
        (sevenCoreBernCoeff D m) (Q'.ofNat (k + 1)) := by
    dsimp only [m, D]
    simpa [growingAnchor, Nat.mul_add, Nat.add_mul, Nat.add_assoc] using
      (sevenCore_projectiveDeficit_nonnegative (k + 1))
  have hclear := signedBernsteinEval_mul_den_pow_eqv_projectiveDeficitEval
    D (sevenCoreBernCoeff D m) (harmW k) den (Q'.ofNat (k + 1))
      (by dsimp only [den]; exact harmonicWeight_mul_den k)
      (by dsimp only [den]; exact harmonic_complement_mul_den k)
  have hscaled :
      (0 : Q') ≤ signedBernsteinEval D
          (sevenCoreBernCoeff D m) (harmW k) * den ^ D :=
    Q'.le_trans' _ _ _ hprojective (Q'.ge_of_eqv hclear)
  have hcomm :
      den ^ D * signedBernsteinEval D
          (sevenCoreBernCoeff D m) (harmW k) ≈
        signedBernsteinEval D
          (sevenCoreBernCoeff D m) (harmW k) * den ^ D :=
    Q'.mul_comm_eqv _ _
  have hleft :
      (0 : Q') ≤ den ^ D * signedBernsteinEval D
        (sevenCoreBernCoeff D m) (harmW k) :=
    Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hcomm)
  have hmul :
      den ^ D * (0 : Q') ≤ den ^ D * signedBernsteinEval D
        (sevenCoreBernCoeff D m) (harmW k) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv (den ^ D))) hleft
  have hden : (0 : Q') < den ^ D := by
    apply pow_pos
    dsimp only [den]
    exact Q'.ofNat_succ_pos (k + 1)
  exact Q'.le_of_mul_le_mul_left hmul hden

/-- The projective certificate is now an exact sign theorem for the physical
endpoint-free Dirichlet core. -/
theorem sevenDirichletCoreGap_pascal_nonnegative (k : Nat) :
    (0 : Q') ≤ sevenDirichletCoreGap k := by
  let m := growingAnchor k + 2
  let D := sevenGapDegree m
  have hsigned : (0 : Q') ≤
      signedBernsteinEval D (sevenCoreBernCoeff D m) (harmW k) := by
    dsimp only [m, D]
    exact harmonic_sevenCore_signed_eval_nonnegative k
  have hscaled : (0 : Q') ≤
      (harmW k) ^ 2 *
        signedBernsteinEval D (sevenCoreBernCoeff D m) (harmW k) :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg (harmW k) (harmW_nonneg k) 2) hsigned
  have heval := harmonic_sevenCore_scaled_eval_eqv_dirichletCore k
  dsimp only [m, D] at heval
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv heval)

/-- The previously open combined central-window payment follows uniformly;
the threshold is needed only to justify the frozen window partition. -/
theorem thetaProof_window_payment_pascal {k : Nat} (hk : 38 ≤ k) :
    thetaLeftLoss k + thetaProofRightLoss k ≤
      thetaProofCentralReserve k := by
  have hcore := sevenDirichletCoreGap_pascal_nonnegative k
  have heq := sevenDirichletCoreGap_proof_window hk
  have hdiff : (0 : Q') ≤
      thetaProofCentralReserve k +
        -(thetaLeftLoss k + thetaProofRightLoss k) :=
    Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv heq)
  apply Q'.le_of_sub_nonneg
  change (0 : Q') ≤ thetaProofCentralReserve k +
    -(thetaLeftLoss k + thetaProofRightLoss k)
  exact hdiff

theorem sevenUnitResidualGap_pascal_nonnegative (k : Nat) :
    (0 : Q') ≤ sevenUnitResidualGap k :=
  sevenUnitResidualGap_nonnegative_of_core
    (sevenDirichletCoreGap_pascal_nonnegative k)

theorem old_pascal_eight_budget_pascal {k : Nat} (hk : 38 ≤ k) :
    normalizedDemandCoeff k * growingPascalResidual k ≤
      Q'.ofNat 8 * (harmU k * harmU k) *
        integerThetaSum (harmW k) (growingAnchor k) :=
  old_pascal_eight_budget_of_seven_gap hk
    (sevenUnitResidualGap_pascal_nonnegative k)

/-- Earliest frozen physical consumer: the shell/spacing inequality now holds
uniformly throughout the large-scale branch (and in fact from `k=38`). -/
theorem harmonicMass_shell_spacing_pascal {k : Nat} (hk : 38 ≤ k) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k :=
  harmonicMass_shell_spacing_of_old_pascal_eight_budget hk
    (old_pascal_eight_budget_pascal hk)

/-- Hypothesis-free all-scale shell/spacing law: the exact finite prefix
through `k=37` joins the uniform Pascal certificate from `k=38` onward. -/
theorem harmonicMass_shell_spacing_pascal_all (k : Nat) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k := by
  by_cases hk : 38 ≤ k
  · exact harmonicMass_shell_spacing_pascal hk
  · exact harmonicMass_shell_spacing_of_fullDeterminant k
      (fullDeterminant_initial_thirtyEight (by omega))

/-- Hypothesis-free successor of the conditional Schur/spacing theorem. -/
theorem harmonicSchur_spacing_pascal_all (k : Nat) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k :=
  harmonicSchur_spacing_of_stage k (harmonicMass_shell_spacing_pascal_all k)

/-- Narrow replacement of `harmonic_operator_spacing_all`: the sole
`UniformQuadraticNodeCap` hypothesis has disappeared because its only use in
that upper chain was the large-scale shell/spacing law now supplied by the
seven-core Pascal certificate. -/
theorem harmonic_operator_spacing_pascal_all (k : Nat) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) *
        harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_pascal_all k)

#print axioms sevenGapBernCoeff_scaled_eval
#print axioms sevenCoreBernCoeff_scaled_eval
#print axioms harmonic_sevenCore_scaled_eval_eqv_dirichletCore
#print axioms harmonic_sevenCore_signed_eval_nonnegative
#print axioms sevenDirichletCoreGap_pascal_nonnegative
#print axioms thetaProof_window_payment_pascal
#print axioms sevenUnitResidualGap_pascal_nonnegative
#print axioms old_pascal_eight_budget_pascal
#print axioms harmonicMass_shell_spacing_pascal
#print axioms harmonicMass_shell_spacing_pascal_all
#print axioms harmonicSchur_spacing_pascal_all
#print axioms harmonic_operator_spacing_pascal_all

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalPhysicalClosure
