/-
Pointwise central-window successor for the endpoint-free theta Dirichlet core.

The predecessor `HarmonicMovingDeterminantThetaWindow` is frozen.  This file
repartitions its exact core at the integer square-root center itself.  The
smaller central interval supports complementary Bernoulli estimates while all
discarded cells remain, exactly, in the right tail.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCentral

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMovingDeterminantThetaAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- The proof window stops at `floor(sqrt(thetaWindowLength k))`. -/
def thetaProofCentralReserve (k : Nat) : Q' :=
  finSum (fun j => thetaCoreIncrement k (thetaWindowLeft k + j))
    (thetaWindowCenter k - thetaWindowLeft k + 1)

def thetaProofRightTailSum (k : Nat) : Q' :=
  finSum (fun j => thetaCoreIncrement k (thetaWindowCenter k + 1 + j))
    (thetaWindowLength k - thetaWindowCenter k)

def thetaProofRightLoss (k : Nat) : Q' := -thetaProofRightTailSum k

private def proofPaymentPolyL : RingNormaliser.PolyExpr :=
  let l := RingNormaliser.PolyExpr.var 0
  let c := RingNormaliser.PolyExpr.var 1
  let r := RingNormaliser.PolyExpr.var 2
  let b := RingNormaliser.PolyExpr.var 3
  .add (.add l (.add c r)) (.neg (.mul (.const 4) b))

private def proofPaymentPolyR : RingNormaliser.PolyExpr :=
  let l := RingNormaliser.PolyExpr.var 0
  let c := RingNormaliser.PolyExpr.var 1
  let r := RingNormaliser.PolyExpr.var 2
  let b := RingNormaliser.PolyExpr.var 3
  .add c (.neg (.add (.add (.mul (.const 4) b) (.neg l)) (.neg r)))

private theorem proofPaymentPoly_normal :
    RingNormaliser.normalize proofPaymentPolyL =
      RingNormaliser.normalize proofPaymentPolyR := by
  decide

private theorem proof_payment_identity (l c r b : Q') :
    (l + (c + r)) + -(Q'.ofNat 4 * b) ≈
      c + -((Q'.ofNat 4 * b + -l) + -r) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    proofPaymentPolyL proofPaymentPolyR proofPaymentPoly_normal
    (fun
      | 0 => l
      | 1 => c
      | 2 => r
      | _ => b)
  simpa [proofPaymentPolyL, proofPaymentPolyR,
    RingNormaliser.eval] using h

theorem thetaWindowCenter_le_length {k : Nat} (hk : 38 ≤ k) :
    thetaWindowCenter k ≤ thetaWindowLength k := by
  have hc9 := thetaWindowCenter_ge_nine hk
  have hsq : thetaWindowCenter k * thetaWindowCenter k ≤
      thetaWindowLength k := by
    unfold thetaWindowCenter
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hc_sq : thetaWindowCenter k ≤
      thetaWindowCenter k * thetaWindowCenter k :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem sevenDirichletCoreGap_proof_window {k : Nat} (hk : 38 ≤ k) :
    sevenDirichletCoreGap k ≈
      thetaProofCentralReserve k +
        -(thetaLeftLoss k + thetaProofRightLoss k) := by
  let f := fun j => thetaCoreIncrement k (j + 1)
  let a := thetaWindowLeft k - 1
  let b := thetaWindowCenter k - thetaWindowLeft k + 1
  let c := thetaWindowLength k - thetaWindowCenter k
  have hL : 1 ≤ thetaWindowLeft k := by
    have := thetaWindowLeft_pos hk
    omega
  have hLC : thetaWindowLeft k ≤ thetaWindowCenter k := by
    unfold thetaWindowLeft
    exact Nat.div_le_self _ 2
  have hCN := thetaWindowCenter_le_length hk
  have htotal : a + (b + c) = thetaWindowLength k := by
    dsimp only [a, b, c]
    omega
  have hcentralIndex : ∀ j,
      a + j + 1 = thetaWindowLeft k + j := by
    intro j
    dsimp only [a]
    omega
  have hrightIndex : ∀ j,
      a + (b + j) + 1 = thetaWindowCenter k + 1 + j := by
    intro j
    dsimp only [a, b]
    omega
  have hsplit1 := YMGap.Constructive.finSum_split f a (b + c)
  rw [htotal] at hsplit1
  have hsplit2 := YMGap.Constructive.finSum_split (fun j => f (a + j)) b c
  have hrange :
      finSum f (thetaWindowLength k) ≈
        thetaLeftTailSum k +
          (thetaProofCentralReserve k + thetaProofRightTailSum k) := by
    refine Q'.eqv_trans _ _ _ hsplit1 ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _ hsplit2 ?_
    unfold thetaProofCentralReserve thetaProofRightTailSum
    dsimp only [f, a, b, c]
    exact Q'.add_eqv_congr'
      (RationalTail.finSum_eqv_congr _ _ (fun j => by
        exact Q'.eqv_of_eq (by rw [hcentralIndex j])) _)
      (RationalTail.finSum_eqv_congr _ _ (fun j => by
        exact Q'.eqv_of_eq (by rw [hrightIndex j])) _)
  refine Q'.eqv_trans _ _ _
    (sevenDirichletCoreGap_eqv_increment_sum k) ?_
  refine Q'.eqv_trans _
    ((thetaLeftTailSum k +
        (thetaProofCentralReserve k + thetaProofRightTailSum k)) +
      -(Q'.ofNat 4 * integerThetaTerm (harmW k) 1)) _
    (Q'.add_eqv_congr_right _ _ _ hrange) ?_
  unfold thetaLeftLoss thetaProofRightLoss
  exact proof_payment_identity _ _ _ _

theorem sevenDirichletCoreGap_nonnegative_of_proof_window {k : Nat}
    (hk : 38 ≤ k)
    (hpay : thetaLeftLoss k + thetaProofRightLoss k ≤
      thetaProofCentralReserve k) :
    (0 : Q') ≤ sevenDirichletCoreGap k := by
  have hsub := Q'.sub_nonneg_of_le hpay
  exact Q'.le_trans' _ _ _ hsub
    (Q'.ge_of_eqv (sevenDirichletCoreGap_proof_window hk))

#print axioms thetaProofCentralReserve
#print axioms thetaProofRightTailSum
#print axioms thetaProofRightLoss
#print axioms thetaWindowCenter_le_length
#print axioms sevenDirichletCoreGap_proof_window
#print axioms sevenDirichletCoreGap_nonnegative_of_proof_window

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCentral
