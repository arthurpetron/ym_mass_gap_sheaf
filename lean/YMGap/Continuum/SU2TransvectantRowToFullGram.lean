/-
# Exact infrastructure for passing from one row to the full binary Gram

The row-to-full argument needs three uniform ingredients: exact adjointness
of the raising/lowering shifts for the binomial monomial metric, covariance
of every iterated Cayley contraction under total lowering, and the finite
Euler identity showing that diagonal restriction converts total lowering to
ordinary lowering.  This file proves those ingredients constructively.  The
successor module combines them with support control and raising covariance
to derive constancy of the normalized output rows and perform the final
`m+n-2k+1`-row sum.  All identities here remain in the exact `Q'` substrate.
-/

import YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.SU2TransvectantRowToFullGram

set_option maxHeartbeats 1600000
set_option maxRecDepth 18000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BinaryForms
open YMGap.Continuum.TransvectantCG
open YMGap.Continuum.SU2TransvectantLinearity
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantAllOrder
open YMGap.Continuum.SU2TransvectantAllLabelGramCompleted
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.RingNormaliser

local infix:50 " ≈ " => Q'.eqv

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int) =
    (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem mul_eqv_both {a b c d : Q'} (hac : a ≈ c) (hbd : b ≈ d) :
    a * b ≈ c * d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

/-! ## Exact binomial shift and the dual monomial adjoint -/

/-- The adjacent-binomial identity in the exact rational carrier. -/
theorem tvBinomQ_adjacent_cross (m i : Nat) (hi : i < m) :
    tvBinomQ m (i + 1) * Q'.ofNat (i + 1) ≈
      tvBinomQ m i * Q'.ofNat (m - i) := by
  have h0 := tvBinomQ_eqv_choose m (i + 1) (by omega)
  have h1 := tvBinomQ_eqv_choose m i (by omega)
  have hnat :=
    YMGap.Continuum.ThetaResidualPascalTelescope.choose_adjacent_cross m i hi
  refine Q'.eqv_trans _
    (Q'.ofNat (PNPaths.choose m (i + 1)) * Q'.ofNat (i + 1)) _
    (Q'.mul_eqv_congr_right _ _ _ h0) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (PNPaths.choose m (i + 1) * (i + 1))) _
    (ofNat_mul_eqv _ _) ?_
  rw [Nat.mul_comm (PNPaths.choose m (i + 1)) (i + 1), hnat,
    Nat.mul_comm (m - i) (PNPaths.choose m i)]
  refine Q'.eqv_trans _
    (Q'.ofNat (PNPaths.choose m i) * Q'.ofNat (m - i)) _
    (Q'.eqv_symm (ofNat_mul_eqv _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm h1)

/-- Pullback by lowering is adjoint to pullback by raising for the dual
binomial metric.  This one-dimensional identity is the finite exact core of
the row recurrence. -/
theorem dual_binomial_shift_adjoint (m : Nat) (f g : Nat → Q') :
    finSum (fun i => tvBinomQ m i *
      ((Q'.ofNat i * f (i - 1)) * g i)) (m + 1) ≈
    finSum (fun i => tvBinomQ m i *
      (f i * (Q'.ofNat (m - i) * g (i + 1)))) (m + 1) := by
  have hleft := finSum_peel_left
    (fun i => tvBinomQ m i * ((Q'.ofNat i * f (i - 1)) * g i)) m
  have hzero :
      tvBinomQ m 0 * ((Q'.ofNat 0 * f (0 - 1)) * g 0) ≈ 0 := by
    simp only [Nat.zero_sub]
    have hz : Q'.ofNat 0 * f 0 ≈ 0 :=
      Q'.eqv_trans _ ((0 : Q') * f 0) _
        (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
    have hz' : (Q'.ofNat 0 * f 0) * g 0 ≈ 0 :=
      Q'.eqv_trans _ (0 * g 0) _
        (Q'.mul_eqv_congr_right _ _ (g 0) hz) (Q'.zero_mul_eqv _)
    exact Q'.eqv_trans _ (tvBinomQ m 0 * 0) _
      (Q'.mul_eqv_congr_left _ _ _ hz') (Q'.mul_zero_eqv _)
  have hleft' :
      finSum (fun i => tvBinomQ m i *
        ((Q'.ofNat i * f (i - 1)) * g i)) (m + 1) ≈
      finSum (fun i => tvBinomQ m (i + 1) *
        ((Q'.ofNat (i + 1) * f i) * g (i + 1))) m := by
    refine Q'.eqv_trans _ _ _ hleft ?_
    refine Q'.eqv_trans _
      (0 + finSum (fun i => tvBinomQ m (i + 1) *
        ((Q'.ofNat (i + 1) * f i) * g (i + 1))) m) _
      (Q'.add_eqv_congr' hzero (Q'.eqv_refl _)) ?_
    exact Q'.eqv_of_eq (Q'.zero_add' _)
  have hterms :
      finSum (fun i => tvBinomQ m (i + 1) *
        ((Q'.ofNat (i + 1) * f i) * g (i + 1))) m ≈
      finSum (fun i => tvBinomQ m i *
        (f i * (Q'.ofNat (m - i) * g (i + 1)))) m := by
    refine finSum_eqv_congr_lt _ _ m (fun i hi => ?_)
    have hadj := tvBinomQ_adjacent_cross m i hi
    refine Q'.eqv_trans _
      ((tvBinomQ m (i + 1) * Q'.ofNat (i + 1)) *
        (f i * g (i + 1))) _ ?_ ?_
    · ring_qeqv
    · refine Q'.eqv_trans _
        ((tvBinomQ m i * Q'.ofNat (m - i)) *
          (f i * g (i + 1))) _
        (Q'.mul_eqv_congr_right _ _ _ hadj) ?_
      ring_qeqv
  have hrightTop :
      tvBinomQ m m *
        (f m * (Q'.ofNat (m - m) * g (m + 1))) ≈ 0 := by
    have hz : Q'.ofNat (m - m) * g (m + 1) ≈ 0 := by
      simp only [Nat.sub_self]
      exact Q'.eqv_trans _ ((0 : Q') * g (m + 1)) _
        (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
        (Q'.zero_mul_eqv _)
    have hz' : f m * (Q'.ofNat (m - m) * g (m + 1)) ≈ 0 :=
      Q'.eqv_trans _ (f m * 0) _
        (Q'.mul_eqv_congr_left (f m) _ _ hz) (Q'.mul_zero_eqv _)
    exact Q'.eqv_trans _ (tvBinomQ m m * 0) _
      (Q'.mul_eqv_congr_left _ _ _ hz') (Q'.mul_zero_eqv _)
  have hright :
      finSum (fun i => tvBinomQ m i *
        (f i * (Q'.ofNat (m - i) * g (i + 1)))) (m + 1) ≈
      finSum (fun i => tvBinomQ m i *
        (f i * (Q'.ofNat (m - i) * g (i + 1)))) m := by
    change (finSum (fun i => tvBinomQ m i *
        (f i * (Q'.ofNat (m - i) * g (i + 1)))) m +
      tvBinomQ m m * (f m * (Q'.ofNat (m - m) * g (m + 1)))) ≈ _
    refine Q'.eqv_trans _ (finSum (fun i => tvBinomQ m i *
      (f i * (Q'.ofNat (m - i) * g (i + 1)))) m + 0) _
      (Q'.add_eqv_congr_left _ _ _ hrightTop) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  exact Q'.eqv_trans _ _ _ hleft'
    (Q'.eqv_trans _ _ _ hterms (Q'.eqv_symm hright))

/-! ## All-label raising/lowering covariance -/

private def omegaExpandLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.mul (.var 1) (.var 6))
      (.mul (.var 2) (.var 7))))
    (.neg (.mul (.var 3) (.add (.mul (.var 4) (.var 7))
      (.mul (.var 5) (.var 8)))))

private def omegaExpandRHS : PolyExpr :=
  .add
    (.add
      (.mul (.mul (.var 0) (.var 1)) (.var 6))
      (.mul
        (.add (.mul (.var 0) (.var 2))
          (.neg (.mul (.var 3) (.var 4))))
        (.var 7)))
    (.neg (.mul (.mul (.var 3) (.var 5)) (.var 8)))

private theorem omegaExpand_normal :
    normalize omegaExpandLHS = normalize omegaExpandRHS := by decide

private def omegaExpandEnv
    (A I J B K L x y z : Q') : Nat → Q'
  | 0 => A | 1 => I | 2 => J | 3 => B | 4 => K | 5 => L
  | 6 => x | 7 => y | _ => z

private theorem omega_expand
    (A I J B K L x y z : Q') :
    A * (I * x + J * y) + -(B * (K * y + L * z)) ≈
      (A * I) * x + (A * J + -(B * K)) * y + -(B * L) * z := by
  have h := poly_identity_of_normal_eq omegaExpandLHS omegaExpandRHS
    omegaExpand_normal (omegaExpandEnv A I J B K L x y z)
  have h' : A * (I * x + J * y) + -(B * (K * y + L * z)) ≈
      (A * I) * x + (A * J + -(B * K)) * y + -(B * L * z) := by
    simpa only [omegaExpandLHS, omegaExpandRHS, omegaExpandEnv, eval] using h
  refine Q'.eqv_trans _ _ _ h' ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.eqv_symm (Q'.neg_mul_eqv (B * L) z))

private def omegaTargetExpandLHS : PolyExpr :=
  .add
    (.mul (.var 0) (.add (.mul (.var 1) (.var 6))
      (.neg (.mul (.var 2) (.var 7)))))
    (.mul (.var 3) (.add (.mul (.var 4) (.var 7))
      (.neg (.mul (.var 5) (.var 8)))))

private def omegaTargetExpandRHS : PolyExpr :=
  .add
    (.add
      (.mul (.mul (.var 0) (.var 1)) (.var 6))
      (.mul
        (.add (.neg (.mul (.var 0) (.var 2)))
          (.mul (.var 3) (.var 4)))
        (.var 7)))
    (.mul (.mul (.var 3) (.neg (.var 5))) (.var 8))

private theorem omegaTargetExpand_normal :
    normalize omegaTargetExpandLHS = normalize omegaTargetExpandRHS := by decide

private theorem omega_target_expand
    (A I J B K L x y z : Q') :
    A * (I * x + -(J * y)) + B * (K * y + -(L * z)) ≈
      (A * I) * x + (-(A * J) + B * K) * y +
        (B * (-L)) * z := by
  have h := poly_identity_of_normal_eq omegaTargetExpandLHS omegaTargetExpandRHS
    omegaTargetExpand_normal (omegaExpandEnv A I J B K L x y z)
  simpa only [omegaTargetExpandLHS, omegaTargetExpandRHS,
    omegaExpandEnv, eval] using h

private def omegaMiddleLHS : PolyExpr :=
  .add
    (.mul (.mul (.var 0) (.add (.var 3) (.const 1))) (.var 1))
    (.neg (.mul (.mul (.add (.var 2) (.const 1)) (.var 1)) (.var 0)))

private def omegaMiddleRHS : PolyExpr :=
  .add
    (.neg (.mul (.mul (.var 0) (.var 2)) (.var 1)))
    (.mul (.mul (.var 1) (.var 0)) (.var 3))

private theorem omegaMiddle_normal :
    normalize omegaMiddleLHS = normalize omegaMiddleRHS := by decide

private def omegaMiddleEnv (x y M N : Q') : Nat → Q'
  | 0 => x | 1 => y | 2 => M | _ => N

private theorem omega_middle_ring (x y M N : Q') :
    x * (N + 1) * y + -((M + 1) * y * x) ≈
      -(x * M * y) + y * x * N := by
  have h := poly_identity_of_normal_eq omegaMiddleLHS omegaMiddleRHS
    omegaMiddle_normal (omegaMiddleEnv x y M N)
  simpa only [omegaMiddleLHS, omegaMiddleRHS, omegaMiddleEnv, eval] using h

private theorem ofNat_add_one_shift (p q : Nat) (h : p = q + 1) :
    Q'.ofNat p ≈ Q'.ofNat q + 1 := by
  rw [h]
  exact Q'.ofNat_add_eqv q 1

private theorem ofNat_triple_ac (a b c : Nat) :
    Q'.ofNat (a * b) * Q'.ofNat c ≈
      Q'.ofNat a * Q'.ofNat (c * b) := by
  refine Q'.eqv_trans _ (Q'.ofNat (a * b * c)) _ (ofNat_mul_eqv _ _) ?_
  rw [show a * b * c = a * (c * b) by ac_rfl]
  exact Q'.eqv_symm (ofNat_mul_eqv _ _)

private theorem ofNat_triple_rotate (a b c : Nat) :
    Q'.ofNat (a * b) * Q'.ofNat c ≈
      Q'.ofNat b * Q'.ofNat (a * c) := by
  refine Q'.eqv_trans _ (Q'.ofNat (a * b * c)) _ (ofNat_mul_eqv _ _) ?_
  rw [show a * b * c = b * (a * c) by ac_rfl]
  exact Q'.eqv_symm (ofNat_mul_eqv _ _)

private theorem omega_middle_coeff (m n a b : Nat)
    (ha : a < m) (hb : b < n) :
    Q'.ofNat ((a + 1) * (n - b)) * Q'.ofNat (b + 1) +
        -(Q'.ofNat ((m - a) * (b + 1)) * Q'.ofNat (a + 1)) ≈
      -(Q'.ofNat (a + 1) *
          Q'.ofNat ((m - (a + 1)) * (b + 1))) +
        Q'.ofNat (b + 1) *
          Q'.ofNat ((a + 1) * (n - (b + 1))) := by
  let x := Q'.ofNat (a + 1)
  let y := Q'.ofNat (b + 1)
  let M := Q'.ofNat (m - (a + 1))
  let N := Q'.ofNat (n - (b + 1))
  have hm : Q'.ofNat (m - a) ≈ M + 1 :=
    ofNat_add_one_shift _ _ (by omega)
  have hn : Q'.ofNat (n - b) ≈ N + 1 :=
    ofNat_add_one_shift _ _ (by omega)
  have hA : Q'.ofNat ((a + 1) * (n - b)) ≈ x * (N + 1) := by
    refine Q'.eqv_trans _ (x * Q'.ofNat (n - b)) _
      (Q'.eqv_symm (ofNat_mul_eqv _ _)) ?_
    exact Q'.mul_eqv_congr_left x _ _ hn
  have hB : Q'.ofNat ((m - a) * (b + 1)) ≈ (M + 1) * y := by
    refine Q'.eqv_trans _ (Q'.ofNat (m - a) * y) _
      (Q'.eqv_symm (ofNat_mul_eqv _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ y hm
  have hC : Q'.ofNat ((m - (a + 1)) * (b + 1)) ≈ M * y :=
    Q'.eqv_symm (ofNat_mul_eqv _ _)
  have hD : Q'.ofNat ((a + 1) * (n - (b + 1))) ≈ x * N :=
    Q'.eqv_symm (ofNat_mul_eqv _ _)
  have hleft :
      Q'.ofNat ((a + 1) * (n - b)) * y +
          -(Q'.ofNat ((m - a) * (b + 1)) * x) ≈
        (x * (N + 1)) * y + -(((M + 1) * y) * x) :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ y hA)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ x hB))
  have hright :
      -(x * Q'.ofNat ((m - (a + 1)) * (b + 1))) +
          y * Q'.ofNat ((a + 1) * (n - (b + 1))) ≈
        -(x * (M * y)) + y * (x * N) :=
    Q'.add_eqv_congr'
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left x _ _ hC))
      (Q'.mul_eqv_congr_left y _ _ hD)
  refine Q'.eqv_trans _ _ _ hleft ?_
  refine Q'.eqv_trans _
    (-(x * M * y) + y * x * N) _ (omega_middle_ring x y M N) ?_
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hright (by ring_qeqv))

/-- One Cayley contraction commutes with total lowering on the physical
residual bidegree. -/
theorem omega_F2_comm (m n a b : Nat) (c : BForm2)
    (ha : a < m) (hb : b < n) :
    Omega m n (F2 m n c) a b ≈
      F2 (m - 1) (n - 1) (Omega m n c) a b := by
  let x := c (a + 2) b
  let y := c (a + 1) (b + 1)
  let z := c a (b + 2)
  have hL := omega_expand
    (Q'.ofNat ((a + 1) * (n - b))) (Q'.ofNat (a + 2)) (Q'.ofNat (b + 1))
    (Q'.ofNat ((m - a) * (b + 1))) (Q'.ofNat (a + 1)) (Q'.ofNat (b + 2))
    x y z
  have hR := omega_target_expand
    (Q'.ofNat (a + 1)) (Q'.ofNat ((a + 2) * (n - b)))
      (Q'.ofNat ((m - (a + 1)) * (b + 1)))
    (Q'.ofNat (b + 1)) (Q'.ofNat ((a + 1) * (n - (b + 1))))
      (Q'.ofNat ((m - a) * (b + 2))) x y z
  have hfirst := ofNat_triple_ac (a + 1) (n - b) (a + 2)
  have hmiddle := omega_middle_coeff m n a b ha hb
  have hlast :
      -(Q'.ofNat ((m - a) * (b + 1)) * Q'.ofNat (b + 2)) ≈
        Q'.ofNat (b + 1) *
          (-(Q'.ofNat ((m - a) * (b + 2)))) := by
    have hcore := ofNat_triple_rotate (m - a) (b + 1) (b + 2)
    refine Q'.eqv_trans _ (-(Q'.ofNat (b + 1) *
      Q'.ofNat ((m - a) * (b + 2)))) _
      (Q'.neg_eqv_congr _ _ hcore) ?_
    exact Q'.eqv_symm
      (Q'.mul_neg_eqv (Q'.ofNat (b + 1))
        (Q'.ofNat ((m - a) * (b + 2))))
  unfold Omega F2
  simp only [Nat.add_assoc]
  refine Q'.eqv_trans _
    ((Q'.ofNat ((a + 1) * (n - b)) * Q'.ofNat (a + 2)) * x +
      (Q'.ofNat ((a + 1) * (n - b)) * Q'.ofNat (b + 1) +
        -(Q'.ofNat ((m - a) * (b + 1)) * Q'.ofNat (a + 1))) * y +
      -(Q'.ofNat ((m - a) * (b + 1)) * Q'.ofNat (b + 2)) * z) _
    (by simpa only [x, y, z, Nat.add_assoc] using hL) ?_
  -- The three coefficients agree exactly; the right expansion merely groups
  -- the two signed middle derivatives.
  refine Q'.eqv_trans _
    ((Q'.ofNat (a + 1) * Q'.ofNat ((a + 2) * (n - b))) * x +
      (-(Q'.ofNat (a + 1) *
          Q'.ofNat ((m - (a + 1)) * (b + 1))) +
        Q'.ofNat (b + 1) *
          Q'.ofNat ((a + 1) * (n - (b + 1)))) * y +
      (Q'.ofNat (b + 1) *
        (-(Q'.ofNat ((m - a) * (b + 2))))) * z) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ x hfirst)
        (Q'.mul_eqv_congr_right _ _ y hmiddle))
      (Q'.mul_eqv_congr_right _ _ z hlast)
  · exact Q'.eqv_symm (by
      simpa only [x, y, z, Nat.add_assoc] using hR)

/-- `OmegaK` only reads the rectangular forward box of radius `k` from an
output coefficient. -/
theorem omegaK_congr_forward_box : ∀ k m n a b : Nat, ∀ c d : BForm2,
    (∀ i, i ≤ a + k → ∀ j, j ≤ b + k → c i j ≈ d i j) →
      OmegaK m n k c a b ≈ OmegaK m n k d a b
  | 0, m, n, a, b, c, d, h => by
      exact h a (by omega) b (by omega)
  | k + 1, m, n, a, b, c, d, h => by
      apply omegaK_congr_forward_box k (m - 1) (n - 1) a b
        (Omega m n c) (Omega m n d)
      intro i hi j hj
      unfold Omega
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left _ _ _
          (h (i + 1) (by omega) j (by omega)))
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _
            (h i (by omega) (j + 1) (by omega))))

/-- Every iterated Cayley contraction commutes with total lowering on its
physical residual box. -/
theorem omegaK_F2_comm : ∀ k m n a b : Nat, ∀ c : BForm2,
    a + k ≤ m → b + k ≤ n →
      OmegaK m n k (F2 m n c) a b ≈
        F2 (m - k) (n - k) (OmegaK m n k c) a b
  | 0, m, n, a, b, c, _, _ => Q'.eqv_refl _
  | k + 1, m, n, a, b, c, hm, hn => by
      have hbox : ∀ i, i ≤ a + k → ∀ j, j ≤ b + k →
          Omega m n (F2 m n c) i j ≈
            F2 (m - 1) (n - 1) (Omega m n c) i j := by
        intro i hi j hj
        exact omega_F2_comm m n i j c (by omega) (by omega)
      have h0 := omegaK_congr_forward_box k (m - 1) (n - 1) a b
        (Omega m n (F2 m n c))
        (F2 (m - 1) (n - 1) (Omega m n c)) hbox
      have h1 := omegaK_F2_comm k (m - 1) (n - 1) a b (Omega m n c)
        (by omega) (by omega)
      refine Q'.eqv_trans _ _ _ h0 ?_
      simpa only [OmegaK, show m - (k + 1) = (m - 1) - k by omega,
        show n - (k + 1) = (n - 1) - k by omega] using h1

/-! The diagonal restriction turns total lowering into ordinary lowering. -/

private theorem weighted_left_pad (s : Nat) (h : Nat → Q') :
    finSum (fun i => Q'.ofNat (i + 1) * h (i + 1)) (s + 1) ≈
      finSum (fun i => Q'.ofNat i * h i) (s + 2) := by
  have hp := finSum_peel_left (fun i => Q'.ofNat i * h i) (s + 1)
  have hz : Q'.ofNat 0 * h 0 ≈ 0 :=
    Q'.eqv_trans _ ((0 : Q') * h 0) _
      (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv _)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hp
    (Q'.eqv_trans _
      (0 + finSum (fun i => Q'.ofNat (i + 1) * h (i + 1)) (s + 1)) _
      (Q'.add_eqv_congr' hz (Q'.eqv_refl _))
      (Q'.eqv_of_eq (Q'.zero_add' _))))

private theorem weighted_right_pad (s : Nat) (h : Nat → Q') :
    finSum (fun i => Q'.ofNat (s - i + 1) * h i) (s + 1) ≈
      finSum (fun i => Q'.ofNat (s + 1 - i) * h i) (s + 2) := by
  have hprefix :
      finSum (fun i => Q'.ofNat (s - i + 1) * h i) (s + 1) ≈
        finSum (fun i => Q'.ofNat (s + 1 - i) * h i) (s + 1) := by
    refine finSum_eqv_congr_lt _ _ (s + 1) (fun i hi => ?_)
    rw [show s - i + 1 = s + 1 - i by omega]
    exact Q'.eqv_refl _
  have htop : Q'.ofNat (s + 1 - (s + 1)) * h (s + 1) ≈ 0 := by
    simp only [Nat.sub_self]
    exact Q'.eqv_trans _ ((0 : Q') * h (s + 1)) _
      (Q'.mul_eqv_congr_right _ _ _ Q'.ofNat_zero_eqv)
      (Q'.zero_mul_eqv _)
  refine Q'.eqv_trans _ _ _ hprefix ?_
  exact Q'.eqv_symm (by
    change (finSum (fun i => Q'.ofNat (s + 1 - i) * h i) (s + 1) +
      Q'.ofNat (s + 1 - (s + 1)) * h (s + 1)) ≈ _
    exact Q'.eqv_trans _
      (finSum (fun i => Q'.ofNat (s + 1 - i) * h i) (s + 1) + 0) _
      (Q'.add_eqv_congr_left _ _ _ htop)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

private theorem ofNat_split_coeff (s i : Nat) (hi : i < s + 2)
    (x : Q') :
    Q'.ofNat i * x + Q'.ofNat (s + 1 - i) * x ≈
      Q'.ofNat (s + 1) * x := by
  have hadd := Q'.ofNat_add_eqv i (s + 1 - i)
  have hsum : i + (s + 1 - i) = s + 1 := by omega
  rw [hsum] at hadd
  refine Q'.eqv_trans _ ((Q'.ofNat i + Q'.ofNat (s + 1 - i)) * x) _
    (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
  exact Q'.mul_eqv_congr_right _ _ x (Q'.eqv_symm hadd)

/-- Euler's homogeneous-degree identity on one finite antidiagonal. -/
theorem weighted_antidiagonal_sum (s : Nat) (h : Nat → Q') :
    finSum (fun i => Q'.ofNat (i + 1) * h (i + 1)) (s + 1) +
        finSum (fun i => Q'.ofNat (s - i + 1) * h i) (s + 1) ≈
      Q'.ofNat (s + 1) * finSum h (s + 2) := by
  have hL := weighted_left_pad s h
  have hR := weighted_right_pad s h
  refine Q'.eqv_trans _
    (finSum (fun i => Q'.ofNat i * h i) (s + 2) +
      finSum (fun i => Q'.ofNat (s + 1 - i) * h i) (s + 2)) _
    (Q'.add_eqv_congr' hL hR) ?_
  refine Q'.eqv_trans _
    (finSum (fun i => Q'.ofNat i * h i +
      Q'.ofNat (s + 1 - i) * h i) (s + 2)) _
    (Q'.eqv_symm (RationalTail.finSum_add _ _ (s + 2))) ?_
  refine Q'.eqv_trans _
    (finSum (fun i => Q'.ofNat (s + 1) * h i) (s + 2)) _
    (finSum_eqv_congr_lt _ _ (s + 2)
      (fun i hi => ofNat_split_coeff s i hi (h i))) ?_
  exact Q'.eqv_symm (const_mul_finSum h (Q'.ofNat (s + 1)) (s + 2))

/-- Diagonal restriction commutes with total lowering. -/
theorem diag_F2 (p q s : Nat) (c : BForm2) :
    diag (F2 p q c) s ≈ Fop (p + q) (diag c) s := by
  let h : Nat → Q' := fun i => c i (s + 1 - i)
  unfold diag F2 Fop
  have hsplit := RationalTail.finSum_add
    (fun i => Q'.ofNat (i + 1) * c (i + 1) (s - i))
    (fun i => Q'.ofNat (s - i + 1) * c i (s - i + 1)) (s + 1)
  have hterms :
      finSum (fun i => Q'.ofNat (i + 1) * c (i + 1) (s - i)) (s + 1) +
          finSum (fun i => Q'.ofNat (s - i + 1) * c i (s - i + 1)) (s + 1) ≈
        finSum (fun i => Q'.ofNat (i + 1) * h (i + 1)) (s + 1) +
          finSum (fun i => Q'.ofNat (s - i + 1) * h i) (s + 1) := by
    apply Q'.add_eqv_congr'
    · refine finSum_eqv_congr_lt _ _ (s + 1) (fun i hi => ?_)
      simp only [h]
      rw [show s + 1 - (i + 1) = s - i by omega]
      exact Q'.eqv_refl _
    · refine finSum_eqv_congr_lt _ _ (s + 1) (fun i hi => ?_)
      simp only [h]
      rw [show s - i + 1 = s + 1 - i by omega]
      exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.eqv_trans _ _ _ hterms ?_
  simpa only [h] using weighted_antidiagonal_sum s h

end YMGap.Continuum.SU2TransvectantRowToFullGram

#print axioms YMGap.Continuum.SU2TransvectantRowToFullGram.tvBinomQ_adjacent_cross
#print axioms YMGap.Continuum.SU2TransvectantRowToFullGram.dual_binomial_shift_adjoint
#print axioms YMGap.Continuum.SU2TransvectantRowToFullGram.omega_F2_comm
#print axioms YMGap.Continuum.SU2TransvectantRowToFullGram.omegaK_congr_forward_box
#print axioms YMGap.Continuum.SU2TransvectantRowToFullGram.omegaK_F2_comm
#print axioms YMGap.Continuum.SU2TransvectantRowToFullGram.weighted_antidiagonal_sum
#print axioms YMGap.Continuum.SU2TransvectantRowToFullGram.diag_F2
