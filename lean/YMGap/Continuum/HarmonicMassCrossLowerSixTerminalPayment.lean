/-
Uniform terminal payment for the lower-six Dirichlet residual.

The growing-anchor scalar estimate says that the last omitted theta root is
at most one eighth of the preceding root.  A two-variable square identity
then shows that the final Dirichlet cell pays the entire omitted endpoint.
Consequently the remaining all-scale argument has no moving boundary loss.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
import YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

namespace YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem terminal_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "terminal_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               terminal_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private def terminalPaymentPolyL : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let c := RingNormaliser.PolyExpr.var 1
  let p := RingNormaliser.PolyExpr.var 2
  .add (.mul (.const 4) (.mul a a))
    (.neg (.add (.mul (.const 8) (.mul a c)) (.mul p (.mul a a))))

private def terminalPaymentPolyR : RingNormaliser.PolyExpr :=
  let a := RingNormaliser.PolyExpr.var 0
  let c := RingNormaliser.PolyExpr.var 1
  let p := RingNormaliser.PolyExpr.var 2
  .add
    (.add (.mul (.const 4) (.mul (.add a (.neg c)) (.add a (.neg c))))
      (.neg (.mul p (.mul a a))))
    (.neg (.mul (.const 4) (.mul c c)))

private theorem terminalPaymentPoly_normal :
    RingNormaliser.normalize terminalPaymentPolyL =
      RingNormaliser.normalize terminalPaymentPolyR := by decide

private theorem terminal_payment_algebra (a c p : Q') :
    Q'.ofNat 4 * (a * a) +
        -(Q'.ofNat 8 * (a * c) + p * (a * a)) ≈
      (Q'.ofNat 4 * ((a + -c) * (a + -c)) + -(p * (a * a))) +
        -(Q'.ofNat 4 * (c * c)) := by
  simpa [terminalPaymentPolyL, terminalPaymentPolyR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      terminalPaymentPolyL terminalPaymentPolyR terminalPaymentPoly_normal
      (fun | 0 => a | 1 => c | _ => p))

private theorem root_nonnegative (k n : Nat) :
    (0 : Q') ≤ thetaRootTerm (harmW k) n := by
  unfold thetaRootTerm
  exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (qpow_nonneg _ (harmW_nonneg k) _)

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
    (Q'.mul_eqv_congr_left _ _ _ hp) ?_
  refine Q'.eqv_trans _
    (qpow w (n * n) *
      (Q'.ofNat (n + 1) * qpow w (2 * n + 1))) _ ?_ ?_
  · terminal_ring
  · exact Q'.eqv_refl _

/-- The last omitted theta root is at most one eighth of the preceding root.
This is the root-level form of the already-proved growing-anchor scalar
cross estimate. -/
theorem terminalRoot_le_eighth_previous (k : Nat) :
    thetaRootTerm (harmW k) (growingAnchor k + 2) ≤
      Q'.mkPos 1 8 (by decide) *
        thetaRootTerm (harmW k) (growingAnchor k + 1) := by
  let b := growingAnchor k
  let q := qpow (harmW k) ((b + 1) * (b + 1))
  let c := Q'.ofNat (b + 2) * qpow (harmW k) (2 * b + 3)
  let a := Q'.ofNat (b + 1)
  have hc : c ≤ Q'.mkPos 1 8 (by decide) * a := by
    dsimp only [c, a, b]
    exact growing_anchor_scalar_cross_eighth k
  have hq0 : (0 : Q') ≤ q := by
    dsimp only [q]
    exact qpow_nonneg _ (harmW_nonneg k) _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ q hc hq0
  have hleft : thetaRootTerm (harmW k) (b + 2) ≈ q * c := by
    have hs := thetaRootTerm_succ_factor (harmW k) (b + 1)
    dsimp only [q, c]
    simpa only [show b + 1 + 1 = b + 2 by omega,
      show 2 * (b + 1) + 1 = 2 * b + 3 by omega] using hs
  have hright : q * (Q'.mkPos 1 8 (by decide) * a) ≈
      Q'.mkPos 1 8 (by decide) * thetaRootTerm (harmW k) (b + 1) := by
    dsimp only [q, a]
    unfold thetaRootTerm
    terminal_ring
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright))

private theorem harmU_le_fifth {k : Nat} (hk : 3 ≤ k) :
    harmU k ≤ Q'.mkPos 1 5 (by decide) := by
  unfold harmU unit
  show (Q'.mkPos 1 (k + 2) (by omega)).num *
      ((Q'.mkPos 1 5 (by decide)).den : Int) ≤
    (Q'.mkPos 1 5 (by decide)).num *
      ((Q'.mkPos 1 (k + 2) (by omega)).den : Int)
  simp only [Q'.mkPos_num, Q'.mkPos_den, Int.one_mul]
  exact_mod_cast (show 5 ≤ k + 2 by omega)

theorem lowerSixDirichletProfile_le_three {k : Nat} (hk : 3 ≤ k) :
    lowerSixDirichletProfile k ≤ Q'.ofNat 3 := by
  let u := harmU k
  have hu0 : (0 : Q') ≤ u := harmU_nonneg k
  have hu1 : u ≤ (1 : Q') := harmU_le_one k
  have hu2 : u * u ≤ (1 : Q') := by
    have h := Q'.mul_le_mul_of_nonneg hu1 hu1 (by decide) hu0
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.one_mul_eqv 1))
  have hsum : Q'.ofNat 12 + u * u ≤ Q'.ofNat 13 := by
    have h := Q'.add_le_add_left (Q'.ofNat 12) _ _ hu2
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide))
  have hmul := Q'.mul_le_mul_of_nonneg (harmU_le_fifth hk) hsum
    (by decide) (Q'.zero_le_add _ _ (by decide)
      (Q'.mul_nonneg _ _ hu0 hu0))
  unfold lowerSixDirichletProfile
  dsimp only [u] at hmul ⊢
  exact Q'.le_trans' _ _ _ hmul (by decide)

private theorem terminal_square_pays {a c p : Q'}
    (ha0 : (0 : Q') ≤ a)
    (hc : c ≤ Q'.mkPos 1 8 (by decide) * a)
    (hp : p ≤ Q'.ofNat 3) :
    Q'.ofNat 4 * (c * c) ≤
      Q'.ofNat 4 * ((a + -c) * (a + -c)) + -(p * (a * a)) := by
  have hac := Q'.mul_le_mul_of_nonneg_left _ _ a hc ha0
  have h8ac := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 8) hac
    (by decide)
  have h8 : Q'.ofNat 8 * (a * c) ≤ a * a := by
    have hleft : Q'.ofNat 8 * (a * c) ≈
        Q'.ofNat 8 * (a * c) := Q'.eqv_refl _
    have hrearr :
        Q'.ofNat 8 *
            (a * (Q'.mkPos 1 8 (by decide) * a)) ≈
          (Q'.ofNat 8 * Q'.mkPos 1 8 (by decide)) * (a * a) := by
      terminal_ring
    have hcollapse :
        (Q'.ofNat 8 * Q'.mkPos 1 8 (by decide)) * (a * a) ≈
          a * a := by
      exact Q'.eqv_trans _ ((1 : Q') * (a * a)) _
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
        (Q'.one_mul_eqv _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ h8ac
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hrearr hcollapse)))
  have haa0 : (0 : Q') ≤ a * a := Q'.mul_nonneg _ _ ha0 ha0
  have hpaa := Q'.mul_le_mul_of_nonneg_right _ _ (a * a) hp haa0
  have hadd := Q'.add_le_add h8 hpaa
  have hfour : a * a + Q'.ofNat 3 * (a * a) ≈
      Q'.ofNat 4 * (a * a) := by
    refine Q'.eqv_trans _
      ((1 : Q') * (a * a) + Q'.ofNat 3 * (a * a)) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _))
    refine Q'.eqv_trans _
      (((1 : Q') + Q'.ofNat 3) * (a * a)) _ ?_ ?_
    · exact Q'.eqv_symm (Q'.add_mul_eqv _ _ _)
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  have hbudget : Q'.ofNat 8 * (a * c) + p * (a * a) ≤
      Q'.ofNat 4 * (a * a) :=
    Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hfour)
  have hnonneg : (0 : Q') ≤
      Q'.ofNat 4 * (a * a) +
        -(Q'.ofNat 8 * (a * c) + p * (a * a)) :=
    Q'.sub_nonneg_of_le hbudget
  have hid := terminal_payment_algebra a c p
  have hdiff : (0 : Q') ≤
      (Q'.ofNat 4 * ((a + -c) * (a + -c)) + -(p * (a * a))) +
        -(Q'.ofNat 4 * (c * c)) := by
    exact Q'.le_trans' _ _ _ hnonneg (Q'.le_of_eqv hid)
  exact Q'.le_of_sub_nonneg hdiff

/-- The final signed Dirichlet increment pays the complete moving endpoint,
uniformly on every symbolic scale. -/
theorem terminalIncrement_pays_endpoint {k : Nat} (hk : 48 ≤ k) :
    Q'.ofNat 4 *
        integerThetaTerm (harmW k) (growingAnchor k + 2) ≤
      lowerSixDirichletIncrement k (growingAnchor k + 1) := by
  let a := thetaRootTerm (harmW k) (growingAnchor k + 1)
  let c := thetaRootTerm (harmW k) (growingAnchor k + 2)
  let p := lowerSixDirichletProfile k
  have hpay := terminal_square_pays
    (a := a) (c := c) (p := p)
    (root_nonnegative k (growingAnchor k + 1))
    (terminalRoot_le_eighth_previous k)
    (lowerSixDirichletProfile_le_three (by omega))
  have ha := thetaRootTerm_sq (harmW k) (growingAnchor k + 1)
  have hc := thetaRootTerm_sq (harmW k) (growingAnchor k + 2)
  unfold lowerSixDirichletIncrement thetaDirichletCell
  dsimp only [a, c, p] at hpay
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _
      (Q'.eqv_symm hc)))
    (Q'.le_trans' _ _ _ hpay
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left (lowerSixDirichletProfile k) _ _ ha)))))

/-- The boundary-free interior block left after the uniform terminal payment.
It contains cells `1,...,growingAnchor k`; the final cell is no longer needed
to pay any central loss. -/
def lowerSixInteriorSum (k : Nat) : Q' :=
  finSum (fun j => lowerSixDirichletIncrement k (j + 1))
    (growingAnchor k)

/-- Once the interior block plus the left endpoint is nonnegative, the
uniform terminal payment closes the actual six-unit residual.  The moving
right endpoint has disappeared from the remaining hypothesis. -/
theorem growingResidualLowerSix_of_interior_nonnegative {k : Nat}
    (hk : 48 ≤ k)
    (hinterior : (0 : Q') ≤
      lowerSixInteriorSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1) :
    GrowingResidualLowerSix k := by
  let E := Q'.ofNat 4 *
    integerThetaTerm (harmW k) (growingAnchor k + 2)
  let T := lowerSixDirichletIncrement k (growingAnchor k + 1)
  let A := lowerSixInteriorSum k +
    Q'.ofNat 4 * integerThetaTerm (harmW k) 1
  have hterminal : E ≤ T := by
    dsimp only [E, T]
    exact terminalIncrement_pays_endpoint hk
  have hadd := Q'.add_le_add hterminal hinterior
  have hleft : E ≈ E + 0 := Q'.eqv_symm (QPoly.q_add_zero_eqv E)
  have hright : T + A ≈
      lowerSixDirichletSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 := by
    dsimp only [T, A]
    unfold lowerSixDirichletSum lowerSixInteriorSum
    simp only [finSum_succ]
    terminal_ring
  have hpay : E ≤
      lowerSixDirichletSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))
  exact growingResidualLowerSix_of_dirichletPayment hpay

#print axioms terminalRoot_le_eighth_previous
#print axioms lowerSixDirichletProfile_le_three
#print axioms terminalIncrement_pays_endpoint
#print axioms growingResidualLowerSix_of_interior_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
