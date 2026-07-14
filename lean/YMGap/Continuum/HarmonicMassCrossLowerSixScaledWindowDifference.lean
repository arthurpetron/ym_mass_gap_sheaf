/-
Exact one-step difference for the denominator-scaled lower-six payment.

The head at scale `k+1` contains exactly two more modes than the head at
scale `k`.  The scaled-window step therefore splits into a shared-mode
cross-scale sum and a two-mode appended tail.  The latter is uniformly
nonnegative by the already-proved right-suffix certificate.  This leaves a
single cancellation-preserving shared sum for the subsequent Abel attack.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowDifference

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowInduction
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

local infix:50 " ≈ " => Q'.eqv

private theorem scaled_difference_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "scaled_difference_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               scaled_difference_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem split_scaled_difference_algebra
    (a b X Y Z : Q') :
    a * (X + Y) + -(b * Z) ≈ (a * X + -(b * Z)) + a * Y := by
  scaled_difference_ring

/-- Shared physical Abel term at scale `k`. -/
def lowerSixWeightedAbelTerm (k j : Nat) : Q' :=
  lowerSixAbelCarrier k j * lowerSixAbelWeight k j

/-- Cross-scale difference over the modes common to both heads. -/
def lowerSixScaledCrossShared (k : Nat) : Q' :=
  finSum
    (fun j =>
      Q'.ofNat (k + 3) * lowerSixWeightedAbelTerm (k + 1) j +
        -(Q'.ofNat (k + 2) * lowerSixWeightedAbelTerm k j))
    (growingAnchor k)

/-- The two new modes appended when the growing anchor advances. -/
def lowerSixScaledCrossTail (k : Nat) : Q' :=
  Q'.ofNat (k + 3) *
    finSum
      (fun j => lowerSixWeightedAbelTerm (k + 1)
        (growingAnchor k + j)) 2

/-- Complete exact one-step difference. -/
def lowerSixScaledCrossDifference (k : Nat) : Q' :=
  lowerSixScaledCrossShared k + lowerSixScaledCrossTail k

private theorem finSum_scaled_difference
    (a b : Q') (f g : Nat → Q') (N : Nat) :
    finSum (fun j => a * f j + -(b * g j)) N ≈
      a * finSum f N + -(b * finSum g N) := by
  let F := fun j => a * f j
  let G := fun j => -(b * g j)
  refine Q'.eqv_trans _ (finSum F N + finSum G N) _ ?_ ?_
  · exact finSum_add F G N
  · refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.eqv_symm (const_mul_finSum f a N)
    · refine Q'.eqv_trans _ (-(finSum (fun j => b * g j) N)) _ ?_ ?_
      · exact Q'.eqv_symm (neg_finSum (fun j => b * g j) N)
      · exact Q'.neg_eqv_congr _ _
          (Q'.eqv_symm (const_mul_finSum g b N))

private theorem growingAnchor_succ_eq (k : Nat) :
    growingAnchor (k + 1) = growingAnchor k + 2 := by
  unfold growingAnchor
  omega

private theorem scaled_finSum_step_difference
    (a b : Q') (f g : Nat → Q') (A : Nat) :
    a * finSum f (A + 2) + -(b * finSum g A) ≈
      finSum (fun j => a * f j + -(b * g j)) A +
        a * finSum (fun j => f (A + j)) 2 := by
  have hsplit := finSum_split f A 2
  have hshared := finSum_scaled_difference a b f g A
  refine Q'.eqv_trans _
    (a * (finSum f A + finSum (fun j => f (A + j)) 2) +
      -(b * finSum g A)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hsplit)
  · refine Q'.eqv_trans _
      ((a * finSum f A + -(b * finSum g A)) +
        a * finSum (fun j => f (A + j)) 2) _
      (split_scaled_difference_algebra _ _ _ _ _) ?_
    exact Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm hshared)

/-- Exact decomposition of the scaled adjacent-scale difference. -/
theorem lowerSixScaledInteriorPayment_step_difference (k : Nat) :
    lowerSixScaledInteriorPayment (k + 1) +
        -lowerSixScaledInteriorPayment k ≈
      lowerSixScaledCrossDifference k := by
  let A := growingAnchor k
  let f := fun j => lowerSixWeightedAbelTerm (k + 1) j
  let g := fun j => lowerSixWeightedAbelTerm k j
  have hk0 : lowerSixInteriorPayment k ≈ finSum g A := by
    unfold lowerSixInteriorPayment
    dsimp only [g, A, lowerSixWeightedAbelTerm]
    exact lowerSixInterior_eqv_weightedAbel k
  have hk1 : lowerSixInteriorPayment (k + 1) ≈ finSum f (A + 2) := by
    unfold lowerSixInteriorPayment
    dsimp only [f, A, lowerSixWeightedAbelTerm]
    have h := lowerSixInterior_eqv_weightedAbel (k + 1)
    rw [growingAnchor_succ_eq k] at h
    exact h
  unfold lowerSixScaledInteriorPayment
  refine Q'.eqv_trans _
    (Q'.ofNat (k + 3) *
        finSum f (A + 2) +
      -(Q'.ofNat (k + 2) *
        finSum g A)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ hk1)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hk0))
  · have h := scaled_finSum_step_difference
      (Q'.ofNat (k + 3)) (Q'.ofNat (k + 2)) f g A
    simpa [lowerSixScaledCrossDifference, lowerSixScaledCrossShared,
      lowerSixScaledCrossTail, lowerSixWeightedAbelTerm, f, g, A] using h

private theorem thetaWindowRight_le_previousAnchor
    {k : Nat} (hk : 48 ≤ k) :
    thetaWindowRight (k + 1) ≤ growingAnchor k := by
  let c := thetaWindowCenter (k + 1)
  have hc : 9 ≤ c := by
    dsimp only [c]
    exact thetaWindowCenter_ge_nine (show 38 ≤ k + 1 by omega)
  have hsq : c * c ≤ thetaWindowLength (k + 1) := by
    dsimp only [c, thetaWindowCenter]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hright : thetaWindowRight (k + 1) ≤ 2 * c := by
    unfold thetaWindowRight
    dsimp only [c]
    have hdiv := Nat.div_le_self (thetaWindowCenter (k + 1)) 4
    omega
  have hroom : 2 * c + 3 ≤ c * c := by
    have hmul := Nat.mul_le_mul_right c (show 3 ≤ c by omega)
    have hlinear : 2 * c + 3 ≤ 3 * c := by omega
    exact Nat.le_trans hlinear (by simpa [Nat.mul_comm] using hmul)
  rw [thetaWindowLength_eq_anchor] at hsq
  rw [growingAnchor_succ_eq k] at hsq
  omega

private theorem appended_weighted_term_nonnegative
    {k r : Nat} (hk : 48 ≤ k) (hr : r < 2) :
    (0 : Q') ≤ lowerSixWeightedAbelTerm (k + 1)
      (growingAnchor k + r) := by
  let R := thetaWindowRight (k + 1)
  let A := growingAnchor k
  have hRA : R ≤ A := by
    dsimp only [R, A]
    exact thetaWindowRight_le_previousAnchor hk
  let s := A + r - R
  have hidx : R + 1 + s = A + r + 1 := by
    dsimp only [s]
    omega
  have hinc := lowerSixSuffixIncrement_nonnegative
    (k := k + 1) (show 48 ≤ k + 1 by omega) s
  rw [hidx] at hinc
  have hpositive : 0 < A + r := by
    dsimp only [A]
    unfold growingAnchor
    omega
  cases hAr : A + r with
  | zero => omega
  | succ q =>
      have hterm := lowerSixAbel_term_eqv (k + 1) (A + r)
      rw [hAr] at hterm hinc
      simp only [lowerSixAugmentedIncrement] at hterm
      unfold lowerSixWeightedAbelTerm
      exact Q'.le_trans' _ _ _ hinc
        (Q'.le_of_eqv (Q'.eqv_symm hterm))

private theorem finSum_nonnegative_of_terms (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_of_terms f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

/-- Both newly appended modes are already in the certified positive suffix. -/
theorem lowerSixScaledCrossTail_nonnegative {k : Nat} (hk : 48 ≤ k) :
    (0 : Q') ≤ lowerSixScaledCrossTail k := by
  unfold lowerSixScaledCrossTail
  exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (finSum_nonnegative_of_terms _ 2
      (fun j hj => appended_weighted_term_nonnegative hk hj))

/-- The shared-mode cross sum is therefore the sole signed residual in the
scaled-window step. -/
theorem lowerSixScaledWindowStep_of_shared_nonnegative
    {k : Nat} (hk : 48 ≤ k)
    (hshared : (0 : Q') ≤ lowerSixScaledCrossShared k) :
    LowerSixScaledWindowStep k := by
  have htail := lowerSixScaledCrossTail_nonnegative hk
  have hdiff : (0 : Q') ≤ lowerSixScaledCrossDifference k := by
    unfold lowerSixScaledCrossDifference
    exact Q'.zero_le_add _ _ hshared htail
  have heq := lowerSixScaledInteriorPayment_step_difference k
  have hsub : (0 : Q') ≤
      lowerSixScaledInteriorPayment (k + 1) +
        -lowerSixScaledInteriorPayment k :=
    Q'.le_trans' _ _ _ hdiff (Q'.le_of_eqv (Q'.eqv_symm heq))
  have hinterior : lowerSixScaledInteriorPayment k ≤
      lowerSixScaledInteriorPayment (k + 1) :=
    Q'.le_of_sub_nonneg hsub
  have h0 := lowerSixScaledInteriorPayment_eqv_window (k := k) hk
  have h1 := lowerSixScaledInteriorPayment_eqv_window
    (k := k + 1) (by omega)
  unfold LowerSixScaledWindowStep
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm h0))
    (Q'.le_trans' _ _ _ hinterior (Q'.le_of_eqv h1))

#print axioms lowerSixScaledInteriorPayment_step_difference
#print axioms lowerSixScaledCrossTail_nonnegative
#print axioms lowerSixScaledWindowStep_of_shared_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledWindowDifference
