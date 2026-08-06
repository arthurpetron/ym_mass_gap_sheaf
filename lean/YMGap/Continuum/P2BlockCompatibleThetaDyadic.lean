/-
Track 11.7-fusion / R3j -- exact dyadic cells for the block Pascal residual.

# Result

The physical cutoff recurrence is `N_(k+1) = 2*N_k+1`.  At such a cutoff,
the integer theta head has `2*N+2` nodes and therefore splits into `N+1`
even/odd pairs.  The half-integer head has `2*N+1` edges and splits into
`N` complete pairs plus one endpoint edge.  Consequently the fine Pascal
residual is exactly

    sum_{p<N} dyadicPascalCell(w,p) + dyadicPascalEndpoint(w,N).

This is the computation-theoretic reduction needed before proving transport:
the growing fine sum is replaced by structural finite-sum induction and local
cells.  No large closed theta expression is evaluated.

# Constructivity

Primitive recursion on `Nat`, exact `Q'` algebra, and kernel-checked reflected
normalization only.  No `Classical`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Constructive.FinSumAlg
import YMGap.Continuum.P2BlockCompatibleThetaPascal

namespace YMGap.Continuum.P2BlockCompatibleThetaDyadic

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicThetaCumulativeResidual
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaPascal
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem dyadic_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "dyadic_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, dyadic_neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.neg_zero,
               Int.zero_add, Int.add_zero];
             try ac_rfl))

/-- One paired integer-theta node at the doubled cutoff. -/
def integerThetaPair (w : Q') (p : Nat) : Q' :=
  integerThetaTerm w (2 * p + 1) + integerThetaTerm w (2 * p + 2)

/-- One paired half-integer-theta edge at the doubled cutoff. -/
def halfThetaPair (w : Q') (p : Nat) : Q' :=
  halfThetaTerm w (2 * p + 1) + halfThetaTerm w (2 * p + 2)

/-- Interior even/odd cell of the doubled-cutoff Pascal residual. -/
def dyadicPascalCell (w : Q') (p : Nat) : Q' :=
  qpow ((1 : Q') + w) 3 * integerThetaPair w p +
    -(Q'.ofNat 8 * (w * halfThetaPair w p))

/-- The unmatched endpoint cell: two integer nodes pay the last half edge. -/
def dyadicPascalEndpoint (w : Q') (N : Nat) : Q' :=
  qpow ((1 : Q') + w) 3 * integerThetaPair w N +
    -(Q'.ofNat 8 * (w * halfThetaTerm w (2 * N + 1)))

/-- Pairing a finite sum is exact.  This is a proof about the recursive
computation of `finSum`, independent of the summand. -/
theorem finSum_pair_eqv (f : QSeq) : forall N : Nat,
    finSum f (2 * N) ≈
      finSum (fun p => f (2 * p) + f (2 * p + 1)) N
  | 0 => Q'.eqv_refl 0
  | N + 1 => by
      show ((finSum f (2 * N) + f (2 * N)) + f (2 * N + 1)) ≈
        finSum (fun p => f (2 * p) + f (2 * p + 1)) N +
          (f (2 * N) + f (2 * N + 1))
      refine Q'.eqv_trans _
        (finSum f (2 * N) + (f (2 * N) + f (2 * N + 1))) _
        (Q'.add_assoc_eqv _ _ _) ?_
      exact Q'.add_eqv_congr_right _ _ _ (finSum_pair_eqv f N)

/-- The `2*N+2` integer nodes are exactly `N+1` even/odd pairs. -/
theorem integerThetaSum_doubleSucc_eqv (w : Q') (N : Nat) :
    integerThetaSum w (2 * N + 1) ≈
      finSum (integerThetaPair w) (N + 1) := by
  simpa [integerThetaSum, integerThetaPair] using
    (finSum_pair_eqv (fun j => integerThetaTerm w (j + 1)) (N + 1))

/-- The `2*N+1` half edges are `N` even/odd pairs plus their last edge. -/
theorem halfThetaSum_doubleSucc_eqv (w : Q') (N : Nat) :
    halfThetaSum w (2 * N + 1) ≈
      finSum (halfThetaPair w) N + halfThetaTerm w (2 * N + 1) := by
  unfold halfThetaSum
  show finSum (fun j => halfThetaTerm w (j + 1)) (2 * N) +
      halfThetaTerm w (2 * N + 1) ≈
    finSum (halfThetaPair w) N + halfThetaTerm w (2 * N + 1)
  exact Q'.add_eqv_congr_right _ _ _
    (by simpa [halfThetaPair] using
      (finSum_pair_eqv (fun j => halfThetaTerm w (j + 1)) N))

/-- Summing the local cells reconstructs the interior paired residual. -/
theorem finSum_dyadicPascalCell_eqv (w : Q') : forall N : Nat,
    finSum (dyadicPascalCell w) N ≈
      qpow ((1 : Q') + w) 3 * finSum (integerThetaPair w) N +
        -(Q'.ofNat 8 * (w * finSum (halfThetaPair w) N))
  | 0 => by
      simp only [finSum_zero]
      dyadic_ring
  | N + 1 => by
      simp only [finSum_succ]
      refine Q'.eqv_trans _
        ((qpow ((1 : Q') + w) 3 * finSum (integerThetaPair w) N +
            -(Q'.ofNat 8 * (w * finSum (halfThetaPair w) N))) +
          dyadicPascalCell w N) _
        (Q'.add_eqv_congr_right _ _ _
          (finSum_dyadicPascalCell_eqv w N)) ?_
      unfold dyadicPascalCell
      dyadic_ring

/-- **Exact dyadic Pascal decomposition.**  The residual at cutoff `2*N+1`
is a sum of `N` complete parity cells and one explicit endpoint cell. -/
theorem cumulativeScaledThetaResidual_doubleSucc_eqv (w : Q') (N : Nat) :
    cumulativeScaledThetaResidual w (2 * N + 1) ≈
      finSum (dyadicPascalCell w) N + dyadicPascalEndpoint w N := by
  let F := qpow ((1 : Q') + w) 3
  let IS := finSum (integerThetaPair w) N
  let HS := finSum (halfThetaPair w) N
  let IP := integerThetaPair w N
  let HE := halfThetaTerm w (2 * N + 1)
  have hI := integerThetaSum_doubleSucc_eqv w N
  have hH := halfThetaSum_doubleSucc_eqv w N
  have hcells := finSum_dyadicPascalCell_eqv w N
  have hI' : integerThetaSum w (2 * N + 1) ≈ IS + IP := by
    simpa only [IS, IP, finSum_succ] using hI
  have hH' : halfThetaSum w (2 * N + 1) ≈ HS + HE := by
    simpa only [HS, HE] using hH
  have hheads :
      cumulativeScaledThetaResidual w (2 * N + 1) ≈
        F * (IS + IP) + -(Q'.ofNat 8 * (w * (HS + HE))) := by
    unfold cumulativeScaledThetaResidual
    refine Q'.eqv_trans _
      (F * (IS + IP) +
        -(Q'.ofNat 8 * (w * halfThetaSum w (2 * N + 1)))) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left F _ _ hI')
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat 8) _ _
            (Q'.mul_eqv_congr_left w _ _ hH')))
  refine Q'.eqv_trans _
    (F * (IS + IP) + -(Q'.ofNat 8 * (w * (HS + HE)))) _ hheads ?_
  refine Q'.eqv_trans _
    ((F * IS + -(Q'.ofNat 8 * (w * HS))) +
      dyadicPascalEndpoint w N) _ ?_ ?_
  · unfold dyadicPascalEndpoint
    dsimp only [F, IS, HS, IP, HE]
    dyadic_ring
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm (by simpa only [F, IS, HS] using hcells))

/-- The physical fine-scale residual therefore has exactly `blockNcut k`
interior parity cells plus the pinned endpoint cell. -/
theorem blockPascalResidual_succ_eqv_dyadicCells (k : Nat) :
    blockPascalResidual (k + 1) ≈
      finSum (dyadicPascalCell (blockWeight (k + 1))) (blockNcut k) +
        dyadicPascalEndpoint (blockWeight (k + 1)) (blockNcut k) := by
  unfold blockPascalResidual
  rw [blockNcut_succ]
  exact cumulativeScaledThetaResidual_doubleSucc_eqv
    (blockWeight (k + 1)) (blockNcut k)

#print axioms finSum_pair_eqv
#print axioms integerThetaSum_doubleSucc_eqv
#print axioms halfThetaSum_doubleSucc_eqv
#print axioms cumulativeScaledThetaResidual_doubleSucc_eqv
#print axioms blockPascalResidual_succ_eqv_dyadicCells

end YMGap.Continuum.P2BlockCompatibleThetaDyadic
