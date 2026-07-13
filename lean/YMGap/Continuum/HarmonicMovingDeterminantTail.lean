/-
Large-scale fences for the exact coupled moving-determinant residual.

The direct criterion allows an asymptotic inverse-square weight-drift
coefficient `50/9`: this is the `25/9` shell factor times the leading spacing
drop coefficient two.  A first natural attack is to allocate that entire
budget pointwise to the symmetrized drift kernel.  The allocation is false
already at the first unbanked tail scale `k=38`, on the vacuum pair `(0,0)`.

The refutation is local and exact.  It does not evaluate a finite cutoff sum,
and it shows that even the more generous asymptotic coefficient cannot avoid
off-diagonal reserve transport.  Thus a valid tail proof must retain global
antisymmetric cancellation (or an equivalent recurrence), rather than prove
a termwise moving-kernel envelope.
-/

import YMGap.Continuum.HarmonicDriftAntisymmetry

namespace YMGap.Continuum.HarmonicMovingDeterminantTail

set_option maxHeartbeats 1200000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicDriftAntisymmetry
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul,
               Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_add,
               Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-- Scaling the coefficient-two oriented covariance budget by `25/9` gives
the full asymptotic allowance `50/9`. -/
def tailPairScale : Q' := Q'.mkPos 25 9 (by decide)

def tailAsymptoticCoeff : Q' := Q'.mkPos 50 9 (by decide)

/-- The first plausible pointwise allocation of the full asymptotic moving
determinant budget. -/
def tailPairBudgetKernel (k i j : Nat) : Q' :=
  tailPairScale * driftBudgetKernel k i j

/-- Its oriented double sum.  Symmetrizing this sum supplies the two copies
used against `driftPairKernel`. -/
def tailOrientedBudgetSum (k : Nat) : Q' :=
  fsum (fun i => fsum (fun j => tailPairBudgetKernel k i j) (Ncut k))
    (Ncut k)

/-- Exact coefficient arithmetic: `(25/9) * 2 = 50/9`. -/
theorem tailPairScale_mul_two_eqv_coeff :
    tailPairScale * Q'.ofNat 2 ≈ tailAsymptoticCoeff := by
  unfold tailPairScale tailAsymptoticCoeff
  decide

/-- The proposed oriented allocation really spends the complete
`(50/9)/(k+2)^2` product-of-normalizers budget. -/
theorem tailOrientedBudgetSum_eq_fullProduct (k : Nat) :
    tailOrientedBudgetSum k ≈
      (tailAsymptoticCoeff * invSqTerm 2 (by decide) k) *
        (oldDiagPrefix k * driftDiagPrefix k) := by
  have hpull : tailOrientedBudgetSum k ≈
      tailPairScale * driftBudgetSum k := by
    unfold tailOrientedBudgetSum tailPairBudgetKernel driftBudgetSum
    refine Q'.eqv_trans _
      (fsum (fun i =>
        tailPairScale * fsum (fun j => driftBudgetKernel k i j) (Ncut k))
        (Ncut k)) _ ?_ ?_
    · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun i =>
        Q'.eqv_symm
          (CubeRatioBounds.fsum_const_mul tailPairScale
            (fun j => driftBudgetKernel k i j) (Ncut k))) (Ncut k)
    exact Q'.eqv_symm
      (CubeRatioBounds.fsum_const_mul tailPairScale
        (fun i => fsum (fun j => driftBudgetKernel k i j) (Ncut k))
        (Ncut k))
  refine Q'.eqv_trans _ (tailPairScale * driftBudgetSum k) _ hpull ?_
  refine Q'.eqv_trans _
    (tailPairScale *
      (twoInvSq k * (oldDiagPrefix k * driftDiagPrefix k))) _
    (Q'.mul_eqv_congr_left tailPairScale _ _
      (driftBudgetSum_eq_prefixProduct k)) ?_
  unfold twoInvSq
  refine Q'.eqv_trans _
    ((tailPairScale * Q'.ofNat 2) *
      (invSqTerm 2 (by decide) k *
        (oldDiagPrefix k * driftDiagPrefix k))) _ (by ring_qeqv) ?_
  refine Q'.eqv_trans _
    (tailAsymptoticCoeff *
      (invSqTerm 2 (by decide) k *
        (oldDiagPrefix k * driftDiagPrefix k))) _
    (Q'.mul_eqv_congr_right _ _ _ tailPairScale_mul_two_eqv_coeff) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv
    tailAsymptoticCoeff (invSqTerm 2 (by decide) k)
    (oldDiagPrefix k * driftDiagPrefix k))

/-- **Tail-start refutation.**  At `k=38`, even allocating the entire
asymptotic coefficient `50/9` pointwise does not pay the symmetrized vacuum
cell.  Negative off-diagonal cells must be transported into this diagonal
excess; a pointwise proof of the large-scale coupled residual is impossible. -/
theorem asymptotic_pairwise_envelope_fails_k38_i0 :
    ¬ (driftPairKernel 38 0 0 ≤
      tailPairBudgetKernel 38 0 0 + tailPairBudgetKernel 38 0 0) := by
  unfold tailPairBudgetKernel tailPairScale driftPairKernel driftKernel
    driftBudgetKernel twoInvSq oldAdj oldDiag driftAdjFactor driftSqFactor
    driftRatio harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow
  decide

/-- The failure is strict, not an artifact of negating an undecidable open
comparison. -/
theorem asymptotic_pairwise_envelope_strictly_fails_k38_i0 :
    tailPairBudgetKernel 38 0 0 + tailPairBudgetKernel 38 0 0 <
      driftPairKernel 38 0 0 := by
  unfold tailPairBudgetKernel tailPairScale driftPairKernel driftKernel
    driftBudgetKernel twoInvSq oldAdj oldDiag driftAdjFactor driftSqFactor
    driftRatio harmW harmU oneSub unit invSqTerm coeffW dimQ c4
    Q'.divPos Q'.recipPos qpow
  decide

#print axioms tailPairScale
#print axioms tailAsymptoticCoeff
#print axioms tailPairBudgetKernel
#print axioms tailOrientedBudgetSum
#print axioms tailPairScale_mul_two_eqv_coeff
#print axioms tailOrientedBudgetSum_eq_fullProduct
#print axioms asymptotic_pairwise_envelope_fails_k38_i0
#print axioms asymptotic_pairwise_envelope_strictly_fails_k38_i0

end YMGap.Continuum.HarmonicMovingDeterminantTail
