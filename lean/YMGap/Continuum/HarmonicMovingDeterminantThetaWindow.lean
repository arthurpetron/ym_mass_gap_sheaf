/-
Moving central-window / two-tail payment for the endpoint-free theta
Dirichlet core.

Both predecessor checkpoints are frozen.  This successor chooses the natural
integer square-root window at harmonic denominator `2(k+2)+1`, splits the
core into left loss, central reserve, and right loss, and records the exact
finite payment criterion.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
import YMGap.Continuum.ChebOrthoMidpointEst

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem window_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "window_ring" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Q'.neg_den, window_neg_num_cast,
               Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

/-- The harmonic denominator, equal to the number of cells in the full
Dirichlet core. -/
def thetaWindowLength (k : Nat) : Nat := 2 * (k + 2) + 1

def thetaWindowCenter (k : Nat) : Nat :=
  ChebOrthoMidpointEst.isqrt (thetaWindowLength k)

def thetaWindowLeft (k : Nat) : Nat := thetaWindowCenter k / 2

def thetaWindowRight (k : Nat) : Nat :=
  thetaWindowCenter k + thetaWindowCenter k / 4

theorem thetaWindowLength_eq_anchor (k : Nat) :
    thetaWindowLength k = growingAnchor k + 1 := by
  unfold thetaWindowLength growingAnchor
  omega

theorem thetaWindowCenter_ge_nine {k : Nat} (hk : 38 ≤ k) :
    9 ≤ thetaWindowCenter k := by
  unfold thetaWindowCenter thetaWindowLength
  apply ChebOrthoMidpointEst.isqrt_ge
  omega

theorem thetaWindowLeft_pos {k : Nat} (hk : 38 ≤ k) :
    0 < thetaWindowLeft k := by
  have hc := thetaWindowCenter_ge_nine hk
  unfold thetaWindowLeft
  omega

theorem thetaWindowLeft_le_right (k : Nat) :
    thetaWindowLeft k ≤ thetaWindowRight k := by
  unfold thetaWindowLeft thetaWindowRight
  have h := Nat.div_le_self (thetaWindowCenter k) 2
  omega

theorem thetaWindowRight_le_length {k : Nat} (hk : 38 ≤ k) :
    thetaWindowRight k ≤ thetaWindowLength k := by
  let c := thetaWindowCenter k
  have hc9 : 9 ≤ c := thetaWindowCenter_ge_nine hk
  have hsq : c * c ≤ thetaWindowLength k := by
    dsimp only [c, thetaWindowCenter]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have h2c : 2 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 2 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  have hquarter := Nat.div_le_self c 4
  unfold thetaWindowRight
  dsimp only [c] at hc9 hsq h2c hquarter ⊢
  omega

/-- Signed Poincare increment at cell `n`. -/
def thetaCoreIncrement (k n : Nat) : Q' :=
  sevenDirichletProfile k * integerThetaTerm (harmW k) n +
    -(Q'.ofNat 4 * thetaDirichletCell (harmW k) n)

/-- The adjacent-root slope after the common factor `w^(n²)` is removed. -/
def thetaRootSlope (k n : Nat) : Q' :=
  Q'.ofNat n +
    -(Q'.ofNat (n + 1) * qpow (harmW k) (2 * n + 1))

private theorem thetaRootTerm_succ_factor (w : Q') (n : Nat) :
    thetaRootTerm w (n + 1) ≈
      qpow w (n * n) *
        (Q'.ofNat (n + 1) * qpow w (2 * n + 1)) := by
  have hexp : (n + 1) * (n + 1) = n * n + (2 * n + 1) := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
    omega
  have hp := HeatKernelRGStep.qpow_add w (n * n) (2 * n + 1)
  rw [← hexp] at hp
  unfold thetaRootTerm
  refine Q'.eqv_trans _
    (Q'.ofNat (n + 1) *
      (qpow w (n * n) * qpow w (2 * n + 1))) _
    (Q'.mul_eqv_congr_left (Q'.ofNat (n + 1)) _ _ hp) ?_
  window_ring

theorem thetaRootTerm_diff_factor (k n : Nat) :
    thetaRootTerm (harmW k) n + -thetaRootTerm (harmW k) (n + 1) ≈
      qpow (harmW k) (n * n) * thetaRootSlope k n := by
  refine Q'.eqv_trans _
    (thetaRootTerm (harmW k) n +
      -(qpow (harmW k) (n * n) *
        (Q'.ofNat (n + 1) * qpow (harmW k) (2 * n + 1)))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (thetaRootTerm_succ_factor (harmW k) n))
  · unfold thetaRootTerm thetaRootSlope
    window_ring

theorem thetaDirichletCell_slope_factor (k n : Nat) :
    thetaDirichletCell (harmW k) n ≈
      qpow (harmW k * harmW k) (n * n) *
        (thetaRootSlope k n * thetaRootSlope k n) := by
  have hd := thetaRootTerm_diff_factor k n
  unfold thetaDirichletCell
  refine Q'.eqv_trans _
    ((qpow (harmW k) (n * n) * thetaRootSlope k n) *
      (thetaRootTerm (harmW k) n +
        -thetaRootTerm (harmW k) (n + 1))) _
    (Q'.mul_eqv_congr_right _ _ _ hd) ?_
  refine Q'.eqv_trans _
    ((qpow (harmW k) (n * n) * thetaRootSlope k n) *
      (qpow (harmW k) (n * n) * thetaRootSlope k n)) _
    (Q'.mul_eqv_congr_left _ _ _ hd) ?_
  refine Q'.eqv_trans _
    ((qpow (harmW k) (n * n) * qpow (harmW k) (n * n)) *
      (thetaRootSlope k n * thetaRootSlope k n)) _
    (by window_ring) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (FusionQuotientCollapse.qpow_mul_self (harmW k) (n * n)))

theorem thetaCoreIncrement_slope_factor (k n : Nat) :
    thetaCoreIncrement k n ≈
      qpow (harmW k * harmW k) (n * n) *
        (sevenDirichletProfile k * Q'.ofNat (n * n) +
          -(Q'.ofNat 4 *
            (thetaRootSlope k n * thetaRootSlope k n))) := by
  have hd := thetaDirichletCell_slope_factor k n
  unfold thetaCoreIncrement integerThetaTerm
  refine Q'.eqv_trans _
    (sevenDirichletProfile k *
        (Q'.ofNat (n * n) *
          qpow (harmW k * harmW k) (n * n)) +
      -(Q'.ofNat 4 *
        (qpow (harmW k * harmW k) (n * n) *
          (thetaRootSlope k n * thetaRootSlope k n)))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hd))
  · window_ring

theorem thetaCoreIncrement_nonnegative_of_slope {k n : Nat}
    (hslope :
      Q'.ofNat 4 * (thetaRootSlope k n * thetaRootSlope k n) ≤
        sevenDirichletProfile k * Q'.ofNat (n * n)) :
    (0 : Q') ≤ thetaCoreIncrement k n := by
  have hp : (0 : Q') ≤
      qpow (harmW k * harmW k) (n * n) :=
    qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hb : (0 : Q') ≤
      sevenDirichletProfile k * Q'.ofNat (n * n) +
        -(Q'.ofNat 4 *
          (thetaRootSlope k n * thetaRootSlope k n)) :=
    Q'.sub_nonneg_of_le hslope
  exact Q'.le_trans' _ _ _
    (Q'.mul_nonneg _ _ hp hb)
    (Q'.ge_of_eqv (thetaCoreIncrement_slope_factor k n))

def thetaLeftTailSum (k : Nat) : Q' :=
  finSum (fun j => thetaCoreIncrement k (j + 1))
    (thetaWindowLeft k - 1)

def thetaCentralReserve (k : Nat) : Q' :=
  finSum (fun j => thetaCoreIncrement k (thetaWindowLeft k + j))
    (thetaWindowRight k - thetaWindowLeft k + 1)

def thetaRightTailSum (k : Nat) : Q' :=
  finSum (fun j => thetaCoreIncrement k (thetaWindowRight k + 1 + j))
    (thetaWindowLength k - thetaWindowRight k)

def thetaLeftLoss (k : Nat) : Q' :=
  Q'.ofNat 4 * integerThetaTerm (harmW k) 1 + -thetaLeftTailSum k

def thetaRightLoss (k : Nat) : Q' := -thetaRightTailSum k

private def incrementStepPolyL : RingNormaliser.PolyExpr :=
  let p := RingNormaliser.PolyExpr.var 0
  let S := RingNormaliser.PolyExpr.var 1
  let x := RingNormaliser.PolyExpr.var 2
  let E := RingNormaliser.PolyExpr.var 3
  let d := RingNormaliser.PolyExpr.var 4
  .add (.add (.mul p S) (.neg (.mul (.const 4) E)))
    (.add (.mul p x) (.neg (.mul (.const 4) d)))

private def incrementStepPolyR : RingNormaliser.PolyExpr :=
  let p := RingNormaliser.PolyExpr.var 0
  let S := RingNormaliser.PolyExpr.var 1
  let x := RingNormaliser.PolyExpr.var 2
  let E := RingNormaliser.PolyExpr.var 3
  let d := RingNormaliser.PolyExpr.var 4
  .add (.mul p (.add S x)) (.neg (.mul (.const 4) (.add E d)))

private theorem incrementStepPoly_normal :
    RingNormaliser.normalize incrementStepPolyL =
      RingNormaliser.normalize incrementStepPolyR := by
  decide

private theorem increment_step_identity (p S x E d : Q') :
    (p * S + -(Q'.ofNat 4 * E)) +
        (p * x + -(Q'.ofNat 4 * d)) ≈
      p * (S + x) + -(Q'.ofNat 4 * (E + d)) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    incrementStepPolyL incrementStepPolyR incrementStepPoly_normal
    (fun
      | 0 => p
      | 1 => S
      | 2 => x
      | 3 => E
      | _ => d)
  simpa [incrementStepPolyL, incrementStepPolyR,
    RingNormaliser.eval] using h

theorem finSum_thetaCoreIncrement_eqv (k : Nat) : ∀ M : Nat,
    finSum (fun j => thetaCoreIncrement k (j + 1)) M ≈
      sevenDirichletProfile k *
          finSum (fun j => integerThetaTerm (harmW k) (j + 1)) M +
        -(Q'.ofNat 4 *
          finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) M)
  | 0 => by
      simp only [finSum_zero]
      have hp : sevenDirichletProfile k * 0 ≈ (0 : Q') :=
        Q'.mul_zero_eqv _
      have hd : -(Q'.ofNat 4 * 0) ≈ -(0 : Q') :=
        Q'.neg_eqv_congr _ _ (Q'.mul_zero_eqv _)
      have h := Q'.add_eqv_congr' hp hd
      exact Q'.eqv_symm (Q'.eqv_trans _ _ _ h (by decide))
  | M + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((sevenDirichletProfile k *
              finSum (fun j => integerThetaTerm (harmW k) (j + 1)) M +
            -(Q'.ofNat 4 *
              finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) M)) +
          thetaCoreIncrement k (M + 1)) _
        (Q'.add_eqv_congr_right _ _ _
          (finSum_thetaCoreIncrement_eqv k M)) ?_
      unfold thetaCoreIncrement
      exact increment_step_identity
        (sevenDirichletProfile k)
        (finSum (fun j => integerThetaTerm (harmW k) (j + 1)) M)
        (integerThetaTerm (harmW k) (M + 1))
        (finSum (fun j => thetaDirichletCell (harmW k) (j + 1)) M)
        (thetaDirichletCell (harmW k) (M + 1))

private def coreSumPolyL : RingNormaliser.PolyExpr :=
  let T := RingNormaliser.PolyExpr.var 0
  let B := RingNormaliser.PolyExpr.var 1
  .add T (.neg (.mul (.const 4) B))

private def coreSumPolyR : RingNormaliser.PolyExpr :=
  let P := RingNormaliser.PolyExpr.var 2
  let S := RingNormaliser.PolyExpr.var 3
  let B := RingNormaliser.PolyExpr.var 1
  let D := RingNormaliser.PolyExpr.var 4
  .add (.add (.mul P S) (.neg (.mul (.const 4) B)))
    (.neg (.mul (.const 4) D))

private theorem core_sum_rearrange (P S B D T : Q')
    (hT : T ≈ P * S + -(Q'.ofNat 4 * D)) :
    T + -(Q'.ofNat 4 * B) ≈
      (P * S + -(Q'.ofNat 4 * B)) + -(Q'.ofNat 4 * D) := by
  refine Q'.eqv_trans _
    ((P * S + -(Q'.ofNat 4 * D)) + -(Q'.ofNat 4 * B)) _
    (Q'.add_eqv_congr_right _ _ _ hT) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (P * S) (-(Q'.ofNat 4 * D))
      (-(Q'.ofNat 4 * B))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (P * S) _ _
      (Q'.add_comm_eqv (-(Q'.ofNat 4 * D)) (-(Q'.ofNat 4 * B)))) ?_
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv (P * S) (-(Q'.ofNat 4 * B))
      (-(Q'.ofNat 4 * D)))

theorem sevenDirichletCoreGap_eqv_increment_sum (k : Nat) :
    sevenDirichletCoreGap k ≈
      finSum (fun j => thetaCoreIncrement k (j + 1)) (thetaWindowLength k) +
        -(Q'.ofNat 4 * integerThetaTerm (harmW k) 1) := by
  have hs := finSum_thetaCoreIncrement_eqv k (thetaWindowLength k)
  rw [thetaWindowLength_eq_anchor] at hs
  unfold sevenDirichletCoreGap integerThetaSum
  exact Q'.eqv_symm (core_sum_rearrange
    (sevenDirichletProfile k)
    (finSum (fun j => integerThetaTerm (harmW k) (j + 1))
      (growingAnchor k + 1))
    (integerThetaTerm (harmW k) 1)
    (finSum (fun j => thetaDirichletCell (harmW k) (j + 1))
      (growingAnchor k + 1))
    (finSum (fun j => thetaCoreIncrement k (j + 1))
      (growingAnchor k + 1)) hs)

private def windowPaymentPolyL : RingNormaliser.PolyExpr :=
  let l := RingNormaliser.PolyExpr.var 0
  let c := RingNormaliser.PolyExpr.var 1
  let r := RingNormaliser.PolyExpr.var 2
  let b := RingNormaliser.PolyExpr.var 3
  .add (.add l (.add c r)) (.neg (.mul (.const 4) b))

private def windowPaymentPolyR : RingNormaliser.PolyExpr :=
  let l := RingNormaliser.PolyExpr.var 0
  let c := RingNormaliser.PolyExpr.var 1
  let r := RingNormaliser.PolyExpr.var 2
  let b := RingNormaliser.PolyExpr.var 3
  .add c (.neg (.add (.add (.mul (.const 4) b) (.neg l)) (.neg r)))

private theorem windowPaymentPoly_normal :
    RingNormaliser.normalize windowPaymentPolyL =
      RingNormaliser.normalize windowPaymentPolyR := by
  decide

private theorem window_payment_identity (l c r b : Q') :
    (l + (c + r)) + -(Q'.ofNat 4 * b) ≈
      c + -((Q'.ofNat 4 * b + -l) + -r) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    windowPaymentPolyL windowPaymentPolyR windowPaymentPoly_normal
    (fun
      | 0 => l
      | 1 => c
      | 2 => r
      | _ => b)
  simpa [windowPaymentPolyL, windowPaymentPolyR,
    RingNormaliser.eval] using h

theorem sevenDirichletCoreGap_window {k : Nat} (hk : 38 ≤ k) :
    sevenDirichletCoreGap k ≈
      thetaCentralReserve k + -(thetaLeftLoss k + thetaRightLoss k) := by
  let f := fun j => thetaCoreIncrement k (j + 1)
  let a := thetaWindowLeft k - 1
  let b := thetaWindowRight k - thetaWindowLeft k + 1
  let c := thetaWindowLength k - thetaWindowRight k
  have hL : 1 ≤ thetaWindowLeft k := by
    have := thetaWindowLeft_pos hk
    omega
  have hLR := thetaWindowLeft_le_right k
  have hRN := thetaWindowRight_le_length hk
  have htotal : a + (b + c) = thetaWindowLength k := by
    dsimp only [a, b, c]
    omega
  have hcentralIndex : ∀ j,
      a + j + 1 = thetaWindowLeft k + j := by
    intro j
    dsimp only [a]
    omega
  have hrightIndex : ∀ j,
      a + (b + j) + 1 = thetaWindowRight k + 1 + j := by
    intro j
    dsimp only [a, b]
    omega
  have hsplit1 := YMGap.Constructive.finSum_split f a (b + c)
  rw [htotal] at hsplit1
  have hsplit2 := YMGap.Constructive.finSum_split (fun j => f (a + j)) b c
  have hrange :
      finSum f (thetaWindowLength k) ≈
        thetaLeftTailSum k +
          (thetaCentralReserve k + thetaRightTailSum k) := by
    refine Q'.eqv_trans _ _ _ hsplit1 ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _ hsplit2 ?_
    unfold thetaCentralReserve thetaRightTailSum
    dsimp only [f, a, b, c]
    exact Q'.add_eqv_congr'
      (RationalTail.finSum_eqv_congr _ _ (fun j => by
        exact Q'.eqv_of_eq (by rw [hcentralIndex j])) _)
      (RationalTail.finSum_eqv_congr _ _ (fun j => by
        exact Q'.eqv_of_eq (by rw [hrightIndex j])) _)
  refine Q'.eqv_trans _ _ _ (sevenDirichletCoreGap_eqv_increment_sum k) ?_
  refine Q'.eqv_trans _
    ((thetaLeftTailSum k +
        (thetaCentralReserve k + thetaRightTailSum k)) +
      -(Q'.ofNat 4 * integerThetaTerm (harmW k) 1)) _
    (Q'.add_eqv_congr_right _ _ _ hrange) ?_
  unfold thetaLeftLoss thetaRightLoss
  exact window_payment_identity _ _ _ _

theorem sevenDirichletCoreGap_nonnegative_of_window {k : Nat} (hk : 38 ≤ k)
    (hpay : thetaLeftLoss k + thetaRightLoss k ≤ thetaCentralReserve k) :
    (0 : Q') ≤ sevenDirichletCoreGap k := by
  have hsub := Q'.sub_nonneg_of_le hpay
  exact Q'.le_trans' _ _ _ hsub
    (Q'.ge_of_eqv (sevenDirichletCoreGap_window hk))

/-- Exact threshold audit of the moving square-root window payment. -/
theorem theta_window_payment_k38 :
    thetaLeftLoss 38 + thetaRightLoss 38 ≤ thetaCentralReserve 38 := by
  unfold thetaLeftLoss thetaRightLoss thetaLeftTailSum thetaCentralReserve
    thetaRightTailSum thetaCoreIncrement thetaWindowLeft thetaWindowRight
    thetaWindowCenter thetaWindowLength sevenDirichletProfile
    thetaDirichletCell thetaRootTerm integerThetaTerm harmW harmU
    ReciprocalBernoulliUpper.oneSub unit ChebOrthoMidpointEst.isqrt
    ChebOrthoMidpointEst.isqrtAux finSum qpow
  decide

#print axioms thetaWindowLength
#print axioms thetaWindowCenter
#print axioms thetaWindowLeft
#print axioms thetaWindowRight
#print axioms thetaWindowCenter_ge_nine
#print axioms thetaWindowRight_le_length
#print axioms thetaCoreIncrement
#print axioms thetaRootSlope
#print axioms thetaRootTerm_diff_factor
#print axioms thetaDirichletCell_slope_factor
#print axioms thetaCoreIncrement_slope_factor
#print axioms thetaCoreIncrement_nonnegative_of_slope
#print axioms finSum_thetaCoreIncrement_eqv
#print axioms sevenDirichletCoreGap_eqv_increment_sum
#print axioms sevenDirichletCoreGap_window
#print axioms sevenDirichletCoreGap_nonnegative_of_window
#print axioms theta_window_payment_k38

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
