/-
Exact moving-cutoff endpoint tail for the fundamental p=2 fused spectrum.

At w=1 the finite character cutoff, rather than the Edgeworth retune, is the
only source of error.  This module proves the symbolic finite-sum core for
every cutoff N:

  boxSum(1,N,1) = 2 A_N,
  3 A_N = N(N+1)(N+2),
  6 D_N = (N+1)(N+2)(2N+3).

Here `A_N` is the adjacent-coordinate correlation and `D_N` the diagonal
norm.  Positive rational cancellation of these identities gives
`vacNorm = 2N/(2N+3)` and defect `3/(2N+3)`; that quotient composition is kept
in the companion closure module.  The proof here is symbolic in `N`, using
exact Clebsch--Gordan selection and constructive power-sum induction.  Thus
the endpoint tail is a derived finite Haar/character quantity, not a measured
constant or finite-case enumeration.
-/

import YMGap.Continuum.CutoffEndpointDefect
import YMGap.Continuum.ArbitraryTruncationRetuneCorr
import YMGap.Continuum.FusionCoreInduction
import YMGap.Continuum.FusionBratteli
import YMGap.Continuum.RenormalizedContinuumZ1
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.EndpointCutoffTailFormula

set_option maxHeartbeats 800000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionBratteli
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.RenormalizedContinuumZ1
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private def q2 : Q' := (2 : Q')
private def q3 : Q' := (3 : Q')
private def q6 : Q' := (6 : Q')

private theorem mul_eqv_both {a b c d : Q'} (hac : a ≈ c) (hbd : b ≈ d) :
    a * b ≈ c * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

private theorem add4_swap (P Q : Q') :
    (P + Q) + (P + Q) ≈ (P + P) + (Q + Q) := by
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv P Q (P + Q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P (Q + (P + Q)) ((Q + P) + Q)
      (Q'.eqv_symm (Q'.add_assoc_eqv Q P Q))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P ((Q + P) + Q) ((P + Q) + Q)
      (Q'.add_eqv_congr_right (Q + P) (P + Q) Q (Q'.add_comm_eqv Q P))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left P ((P + Q) + Q) (P + (Q + Q))
      (Q'.add_assoc_eqv P Q Q)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv P P (Q + Q))

/-! ## 1. Exact channel-one cutoff increment -/

theorem fusionInd_prev_top_one (N : Nat) :
    fusionInd N (N + 1) 1 = (1 : Q') := by
  unfold fusionInd
  rw [if_pos ((fusionOK_iff_ladder N (N + 1) 1).2
    ⟨N, Nat.le_refl N, by omega, by omega⟩)]

theorem fusionInd_top_prev_one (N : Nat) :
    fusionInd (N + 1) N 1 = (1 : Q') := by
  unfold fusionInd
  rw [if_pos ((fusionOK_iff_ladder (N + 1) N 1).2
    ⟨N, by omega, Nat.le_refl N, by omega⟩)]

theorem fusionInd_left_top_one_zero {a N : Nat} (ha : a < N) :
    fusionInd a (N + 1) 1 = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro h
  have hc := (fusionOK_eq_true_iff a (N + 1) 1).1 h
  have hmax : Nat.max a (N + 1) = N + 1 := Nat.max_eq_right (by omega)
  have hmin : Nat.min a (N + 1) = a := Nat.min_eq_left (by omega)
  rw [hmax, hmin] at hc
  omega

theorem fusionInd_top_right_one_zero {b N : Nat} (hb : b < N) :
    fusionInd (N + 1) b 1 = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro h
  have hc := (fusionOK_eq_true_iff (N + 1) b 1).1 h
  have hmax : Nat.max (N + 1) b = N + 1 := Nat.max_eq_left (by omega)
  have hmin : Nat.min (N + 1) b = b := Nat.min_eq_right (by omega)
  rw [hmax, hmin] at hc
  omega

theorem fusionInd_top_diag_one_zero (N : Nat) :
    fusionInd (N + 1) (N + 1) 1 = (0 : Q') := by
  unfold fusionInd
  rw [if_neg]
  intro h
  have hc := (fusionOK_eq_true_iff (N + 1) (N + 1) 1).1 h
  omega

private theorem fsum_collapse_bounded {g : Nat → Q'} {k n : Nat}
    (hk : k < n) (hz : ∀ b, b < n → b ≠ k → (g b) ≈ (0 : Q')) :
    fsum g n ≈ g k := by
  induction n with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      show fsum g n + g n ≈ g k
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkn | hkn
      · have hlast : g n ≈ (0 : Q') :=
          hz n (Nat.lt_succ_self n) (fun h => by subst h; omega)
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (ih hkn ?_) hlast) ?_
        · intro b hb hne
          exact hz b (Nat.lt_succ_of_lt hb) hne
        · exact QPoly.q_add_zero_eqv _
      · subst hkn
        have hpre : fsum g k ≈ (0 : Q') :=
          fsum_zero_below k (fun b hb => hz b (Nat.lt_succ_of_lt hb) (Nat.ne_of_lt hb))
        refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hpre) ?_
        exact QPoly.q_zero_add_eqv _

/-- Adding the top representation contributes exactly the two adjacent
Clebsch pairs `(N,N+1)` and `(N+1,N)` to channel one. -/
theorem boxSumDelta_one (w : Q') (N : Nat) :
    boxSumDelta w N 1 ≈
      (coeffW w N * coeffW w (N + 1)) +
        (coeffW w N * coeffW w (N + 1)) := by
  unfold boxSumDelta
  have hleft :
      (fsum (fun a => fusionInd a (N + 1) 1 *
        (coeffW w a * coeffW w (N + 1))) (N + 1)) ≈
        (coeffW w N * coeffW w (N + 1)) := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N) (n := N + 1) (Nat.lt_succ_self N)
        (fun a haB haN => ?_)) ?_
    · have ha : a < N := by omega
      rw [fusionInd_left_top_one_zero ha]
      exact Q'.zero_mul_eqv _
    · rw [fusionInd_prev_top_one]
      exact Q'.one_mul_eqv _
  have hright :
      (fsum (fun b => fusionInd (N + 1) b 1 *
        (coeffW w (N + 1) * coeffW w b)) (N + 1)) ≈
        (coeffW w N * coeffW w (N + 1)) := by
    refine Q'.eqv_trans _ _ _
      (fsum_collapse_bounded (k := N) (n := N + 1) (Nat.lt_succ_self N)
        (fun b hbB hbN => ?_)) ?_
    · have hb : b < N := by omega
      rw [fusionInd_top_right_one_zero hb]
      exact Q'.zero_mul_eqv _
    · rw [fusionInd_top_prev_one]
      refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ?_
      exact Q'.mul_comm_eqv _ _
  have hdiag :
      (fusionInd (N + 1) (N + 1) 1 *
        (coeffW w (N + 1) * coeffW w (N + 1))) ≈ (0 : Q') := by
    rw [fusionInd_top_diag_one_zero]
    exact Q'.zero_mul_eqv _
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hleft (Q'.add_eqv_congr' hright hdiag)) ?_
  exact Q'.add_eqv_congr_left _ _ _ (QPoly.q_add_zero_eqv _)

/-- The full channel-one box sum is twice the adjacent correlation, for
every base and every cutoff. -/
theorem boxSum_one_eq_twice_adjCorr (w : Q') (N : Nat) :
    boxSum w N 1 ≈ q2 * adjCorr w N := by
  induction N with
  | zero =>
      unfold boxSum adjCorr
      exact Q'.eqv_refl 0
  | succ N ih =>
      refine Q'.eqv_trans _ _ _ (boxSum_succ_decomp w N 1) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' ih
          (boxSumDelta_one w N)) ?_
      show q2 * adjCorr w N +
          ((coeffW w N * coeffW w (N + 1)) +
            (coeffW w N * coeffW w (N + 1))) ≈
        q2 * (adjCorr w N + coeffW w N * coeffW w (N + 1))
      have htwo (x : Q') : q2 * x ≈ x + x := by
        have h2 : q2 ≈ (1 : Q') + 1 := by decide
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x h2) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 x) ?_
        exact Q'.add_eqv_congr' (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)
      let t := coeffW w N * coeffW w (N + 1)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (htwo (adjCorr w N)) (Q'.eqv_refl _)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (add4_swap (adjCorr w N) t)) ?_
      exact Q'.eqv_symm (htwo (adjCorr w N + t))

/-! ## 2. Symbolic endpoint power sums -/

private theorem ofNat_succ (N : Nat) :
    Q'.ofNat (N + 1) ≈ Q'.ofNat N + (1 : Q') :=
  BulkModeCrux.ofNat_succ_eqv N

private def cubicStepLHS : PolyExpr :=
  .add
    (.mul (.mul (.var 0) (.add (.var 0) (.const 1)))
      (.add (.var 0) (.const 2)))
    (.mul (.const 3)
      (.mul (.add (.var 0) (.const 1)) (.add (.var 0) (.const 2))))

private def cubicStepRHS : PolyExpr :=
  .mul
    (.mul (.add (.var 0) (.const 1))
      (.add (.add (.var 0) (.const 1)) (.const 1)))
    (.add (.add (.var 0) (.const 1)) (.const 2))

private theorem cubicStep_normal :
    normalize cubicStepLHS = normalize cubicStepRHS := by decide

private theorem endpoint_cubic_step (x : Q') :
    x * (x + 1) * (x + 2) + q3 * ((x + 1) * (x + 2)) ≈
      (x + 1) * ((x + 1) + 1) * ((x + 1) + 2) := by
  have h := poly_identity_of_normal_eq cubicStepLHS cubicStepRHS cubicStep_normal
    (fun _ => x)
  simpa [eval, cubicStepLHS, cubicStepRHS, RingNormaliser.qpow, q3] using h

private def squareStepLHS : PolyExpr :=
  .add
    (.mul
      (.mul (.add (.var 0) (.const 1)) (.add (.var 0) (.const 2)))
      (.add (.mul (.const 2) (.var 0)) (.const 3)))
    (.mul (.const 6)
      (.mul (.add (.var 0) (.const 2)) (.add (.var 0) (.const 2))))

private def squareStepRHS : PolyExpr :=
  .mul
    (.mul
      (.add (.add (.var 0) (.const 1)) (.const 1))
      (.add (.add (.var 0) (.const 1)) (.const 2)))
    (.add (.mul (.const 2) (.add (.var 0) (.const 1))) (.const 3))

private theorem squareStep_normal :
    normalize squareStepLHS = normalize squareStepRHS := by decide

private theorem endpoint_square_step (x : Q') :
    (x + 1) * (x + 2) * (q2 * x + 3) + q6 * ((x + 2) * (x + 2)) ≈
      ((x + 1) + 1) * ((x + 1) + 2) *
        (q2 * (x + 1) + 3) := by
  have h := poly_identity_of_normal_eq squareStepLHS squareStepRHS squareStep_normal
    (fun _ => x)
  simpa [eval, squareStepLHS, squareStepRHS, RingNormaliser.qpow, q2, q6] using h

/-- `3 A_N = N(N+1)(N+2)` for the endpoint adjacent correlation. -/
theorem adjCorr_endpoint_closed : ∀ N : Nat,
    q3 * adjCorr (1 : Q') N ≈
      Q'.ofNat N * (Q'.ofNat N + 1) * (Q'.ofNat N + 2)
  | 0 => by decide
  | N + 1 => by
      have ih := adjCorr_endpoint_closed N
      have hcN := coeffW_at_one_eqv N
      have hcN1 := coeffW_at_one_eqv (N + 1)
      have hdimN : dimQ N ≈ Q'.ofNat N + 1 := ofNat_succ N
      have hdimN1 : dimQ (N + 1) ≈ Q'.ofNat N + 2 :=
        Q'.ofNat_add_eqv N 2
      have hterm :
          coeffW (1 : Q') N * coeffW (1 : Q') (N + 1) ≈
            (Q'.ofNat N + 1) * (Q'.ofNat N + 2) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hcN) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (dimQ N) _ _ hcN1) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hdimN) ?_
        exact Q'.mul_eqv_congr_left _ _ _ hdimN1
      show q3 * (adjCorr (1 : Q') N +
          coeffW (1 : Q') N * coeffW (1 : Q') (N + 1)) ≈ _
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' ih (Q'.mul_eqv_congr_left q3 _ _ hterm)) ?_
      refine Q'.eqv_trans _ _ _ (endpoint_cubic_step (Q'.ofNat N)) ?_
      have hs := ofNat_succ N
      have h1 : Q'.ofNat (N + 1) + 1 ≈ (Q'.ofNat N + 1) + 1 :=
        Q'.add_eqv_congr_right _ _ _ hs
      have h2 : Q'.ofNat (N + 1) + 2 ≈ (Q'.ofNat N + 1) + 2 :=
        Q'.add_eqv_congr_right _ _ _ hs
      exact Q'.eqv_symm (mul_eqv_both (mul_eqv_both hs h1) h2)

/-- `6 D_N = (N+1)(N+2)(2N+3)` for the endpoint squared norm. -/
theorem coordNormSq_endpoint_closed : ∀ N : Nat,
    q6 * coordNormSq (1 : Q') N ≈
      (Q'.ofNat N + 1) * (Q'.ofNat N + 2) * (q2 * Q'.ofNat N + 3)
  | 0 => by decide
  | N + 1 => by
      have ih := coordNormSq_endpoint_closed N
      have hc := coeffW_at_one_eqv (N + 1)
      have hdim : dimQ (N + 1) ≈ Q'.ofNat N + 2 :=
        Q'.ofNat_add_eqv N 2
      have hterm :
          coeffW (1 : Q') (N + 1) * coeffW (1 : Q') (N + 1) ≈
            (Q'.ofNat N + 2) * (Q'.ofNat N + 2) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hc) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hc) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hdim) ?_
        exact Q'.mul_eqv_congr_left _ _ _ hdim
      show q6 * (coordNormSq (1 : Q') N +
          coeffW (1 : Q') (N + 1) * coeffW (1 : Q') (N + 1)) ≈ _
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' ih (Q'.mul_eqv_congr_left q6 _ _ hterm)) ?_
      refine Q'.eqv_trans _ _ _ (endpoint_square_step (Q'.ofNat N)) ?_
      have hs := ofNat_succ N
      have h1 : Q'.ofNat (N + 1) + 1 ≈ (Q'.ofNat N + 1) + 1 :=
        Q'.add_eqv_congr_right _ _ _ hs
      have h2 : Q'.ofNat (N + 1) + 2 ≈ (Q'.ofNat N + 1) + 2 :=
        Q'.add_eqv_congr_right _ _ _ hs
      have hlin : q2 * Q'.ofNat (N + 1) + 3 ≈ q2 * (Q'.ofNat N + 1) + 3 :=
        Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left q2 _ _ hs)
      exact Q'.eqv_symm (mul_eqv_both (mul_eqv_both h1 h2) hlin)


end YMGap.Continuum.EndpointCutoffTailFormula

#print axioms YMGap.Continuum.EndpointCutoffTailFormula.boxSumDelta_one
#print axioms YMGap.Continuum.EndpointCutoffTailFormula.fusionInd_prev_top_one
#print axioms YMGap.Continuum.EndpointCutoffTailFormula.fusionInd_top_prev_one
#print axioms YMGap.Continuum.EndpointCutoffTailFormula.fusionInd_left_top_one_zero
#print axioms YMGap.Continuum.EndpointCutoffTailFormula.fusionInd_top_right_one_zero
#print axioms YMGap.Continuum.EndpointCutoffTailFormula.fusionInd_top_diag_one_zero
#print axioms YMGap.Continuum.EndpointCutoffTailFormula.boxSum_one_eq_twice_adjCorr
#print axioms YMGap.Continuum.EndpointCutoffTailFormula.adjCorr_endpoint_closed
#print axioms YMGap.Continuum.EndpointCutoffTailFormula.coordNormSq_endpoint_closed
