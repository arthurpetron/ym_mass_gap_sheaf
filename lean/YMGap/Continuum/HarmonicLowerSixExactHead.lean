/-
Finite-sum splice for the exact lower-six Hermite certificate.

The exact pointwise theorem controls every physical mode through the moving
left square-root window.  This module packages that range as a nonnegative
head, splits the complete remainder sum into head and tail without changing
the production definition, and shows that any payment of the tail pays the
full signed remainder.
-/

import YMGap.Continuum.HarmonicLowerSixExactCertificate
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope

namespace YMGap.Continuum.HarmonicLowerSixExactHead

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicLowerSixExactCertificate
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic

local infix:50 " ≈ " => Q'.eqv

/-- The certified portion of the complete Hermite remainder sum. -/
def lowerSixHermiteRemainderHeadSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDiscreteHermiteRemainder k (j + 1))
    (thetaWindowLeft k)

/-- The exact complementary suffix after the certified square-root head. -/
def lowerSixHermiteRemainderTailSum (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDiscreteHermiteRemainder k
      (thetaWindowLeft k + j + 1))
    (growingAnchor k - thetaWindowLeft k)

private theorem finSum_nonnegative (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, hf => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative f N (fun j hj => hf j (by omega)))
        (hf N (by omega))

private theorem finSum_add_block (f : Nat → Q') (a : Nat) : ∀ t,
    finSum f (a + t) ≈
      finSum f a + finSum (fun s => f (a + s)) t
  | 0 => Q'.eqv_symm (QPoly.q_add_zero_eqv _)
  | t + 1 => by
      rw [show a + (t + 1) = (a + t) + 1 by omega,
        finSum_succ, finSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (finSum_add_block f a t)) ?_
      exact Q'.add_assoc_eqv _ _ _

private theorem thetaWindowLeft_le_growingAnchor_large
    {k : Nat} (hk : 8189 ≤ k) :
    thetaWindowLeft k ≤ growingAnchor k := by
  have hc := thetaWindowCenter_le_harmonicDen
    (k := k) (show 38 ≤ k by omega)
  unfold thetaWindowLeft growingAnchor
  have hdiv := Nat.div_le_self (thetaWindowCenter k) 2
  omega

/-- Every term in the retained square-root head is nonnegative. -/
theorem lowerSixHermiteRemainderHeadSum_nonnegative
    {k : Nat} (hk : 8189 ≤ k) :
    (0 : Q') ≤ lowerSixHermiteRemainderHeadSum k := by
  unfold lowerSixHermiteRemainderHeadSum
  apply finSum_nonnegative
  intro j hj
  exact lowerSixDiscreteHermiteRemainder_nonnegative_exact_large
    hk (show j + 1 ≤ thetaWindowLeft k by omega)

/-- Exact unchanged-definition split of the production remainder sum. -/
theorem lowerSixHermiteRemainderSum_eqv_head_add_tail
    {k : Nat} (hk : 8189 ≤ k) :
    lowerSixHermiteRemainderSum k ≈
      lowerSixHermiteRemainderHeadSum k +
        lowerSixHermiteRemainderTailSum k := by
  let f := fun j => lowerSixDiscreteHermiteRemainder k (j + 1)
  let c := thetaWindowLeft k
  let N := growingAnchor k
  let M := N - c
  have hcN : c ≤ N := by
    dsimp only [c, N]
    exact thetaWindowLeft_le_growingAnchor_large hk
  have hNat : c + M = N := by
    dsimp only [M]
    omega
  have hsplit := finSum_add_block f c M
  have htail :
      finSum (fun s => f (c + s)) M ≈
        finSum
          (fun j => lowerSixDiscreteHermiteRemainder k
            (thetaWindowLeft k + j + 1)) M := by
    apply RationalTail.finSum_eqv_congr
    intro j
    dsimp only [f, c]
    rw [show thetaWindowLeft k + j + 1 =
      thetaWindowLeft k + j + 1 by rfl]
    exact Q'.eqv_refl _
  unfold lowerSixHermiteRemainderSum
    lowerSixHermiteRemainderHeadSum lowerSixHermiteRemainderTailSum
  change finSum f N ≈
    finSum f c +
      finSum
        (fun j => lowerSixDiscreteHermiteRemainder k
          (thetaWindowLeft k + j + 1)) M
  refine Q'.eqv_trans _ (finSum f (c + M)) _ ?_ ?_
  · exact Q'.eqv_of_eq (congrArg (finSum f) hNat.symm)
  · exact Q'.eqv_trans _ _ _ hsplit
      (Q'.add_eqv_congr_left _ _ _ htail)

/-- The nonnegative certified head means the full sum is bounded below by
its unresolved tail. -/
theorem lowerSixHermiteRemainderTailSum_le_full
    {k : Nat} (hk : 8189 ≤ k) :
    lowerSixHermiteRemainderTailSum k ≤
      lowerSixHermiteRemainderSum k := by
  let H := lowerSixHermiteRemainderHeadSum k
  let T := lowerSixHermiteRemainderTailSum k
  let R := lowerSixHermiteRemainderSum k
  have hH : (0 : Q') ≤ H := by
    dsimp only [H]
    exact lowerSixHermiteRemainderHeadSum_nonnegative hk
  have hsplit : R ≈ H + T := by
    dsimp only [R, H, T]
    exact lowerSixHermiteRemainderSum_eqv_head_add_tail hk
  have hTH : T ≤ T + H := Q'.add_le_self_of_nonneg T H hH
  have hHT : T ≤ H + T :=
    Q'.le_trans' _ _ _ hTH (Q'.le_of_eqv (Q'.add_comm_eqv T H))
  exact Q'.le_trans' _ _ _ hHT (Q'.ge_of_eqv hsplit)

/-- Any upper payment of the negative tail is already an upper payment of
the negative complete remainder sum. -/
theorem lowerSixFullRemainderPayment_of_tailPayment
    {k : Nat} (hk : 8189 ≤ k) {B : Q'}
    (htail :
      -(Q'.ofNat 4 * lowerSixHermiteRemainderTailSum k) ≤ B) :
    -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤ B := by
  have hscaled :
      Q'.ofNat 4 * lowerSixHermiteRemainderTailSum k ≤
        Q'.ofNat 4 * lowerSixHermiteRemainderSum k :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (lowerSixHermiteRemainderTailSum_le_full hk) (by decide)
  exact Q'.le_trans' _ _ _ (Q'.neg_le_neg hscaled) htail

#print axioms lowerSixHermiteRemainderHeadSum_nonnegative
#print axioms lowerSixHermiteRemainderSum_eqv_head_add_tail
#print axioms lowerSixHermiteRemainderTailSum_le_full
#print axioms lowerSixFullRemainderPayment_of_tailPayment

end YMGap.Continuum.HarmonicLowerSixExactHead
