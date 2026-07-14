/-
Moving-edge geometry for the next-scale lower-six carrier.

The square-root right edge advances by at most two.  Hence every next-scale
mode in the old right suffix except possibly its first two modes is already in
the certified new right suffix.  At an actual edge jump, the new length is
within one unit of the new center square; this supplies tighter boundary shape
certificates.  The finite pre-asymptotic boundary band is checked exactly.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixActual
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixEndpoint
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixShapeCertificate
open YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem drift_suffix_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "drift_suffix_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               drift_suffix_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem linear_square (a b q : Nat) :
    (a * q + b) * (a * q + b) =
      (a * a) * (q * q) + (a * b) * q + (a * b) * q + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  ac_rfl

private theorem div_four_decomp (c : Nat) :
    c = 4 * (c / 4) + c % 4 := by omega

private theorem mod_four_cases (c : Nat) :
    c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega

private theorem nine_mul_le_square {q : Nat} (hq : 9 ≤ q) :
    9 * q ≤ q * q := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hq

private theorem ten_mul_le_square {q : Nat} (hq : 10 ≤ q) :
    10 * q ≤ q * q := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hq

private theorem isqrt_lt_succ_sq (m : Nat) :
    m < (ChebOrthoMidpointEst.isqrt m + 1) *
      (ChebOrthoMidpointEst.isqrt m + 1) := by
  rcases Nat.lt_or_ge m
      ((ChebOrthoMidpointEst.isqrt m + 1) *
        (ChebOrthoMidpointEst.isqrt m + 1)) with h | h
  · exact h
  · have hbad := ChebOrthoMidpointEst.isqrt_ge
      (m := m) (K := ChebOrthoMidpointEst.isqrt m + 1) h
    omega

/-- The integer square-root center advances by at most one harmonic step. -/
theorem thetaWindowCenter_succ_le (k : Nat) :
    thetaWindowCenter (k + 1) ≤ thetaWindowCenter k + 1 := by
  let c := thetaWindowCenter k
  let c1 := thetaWindowCenter (k + 1)
  let L := thetaWindowLength k
  let L1 := thetaWindowLength (k + 1)
  have hL : L1 = L + 2 := by
    dsimp only [L1, L, thetaWindowLength]
    omega
  have hc1sq : c1 * c1 ≤ L1 := by
    dsimp only [c1, L1, thetaWindowCenter]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hLupper : L < (c + 1) * (c + 1) := by
    dsimp only [c, L, thetaWindowCenter]
    exact isqrt_lt_succ_sq _
  have hgap : (c + 1) * (c + 1) + 2 ≤ (c + 2) * (c + 2) := by
    have h1 : (c + 1) * (c + 1) = c * c + c + c + 1 := by
      simpa [Nat.add_assoc] using linear_square 1 1 c
    have h2 : (c + 2) * (c + 2) = c * c + 2 * c + 2 * c + 4 := by
      simpa [Nat.add_assoc] using linear_square 1 2 c
    rw [h1, h2]
    omega
  by_cases hcc : c + 2 ≤ c1
  · have hsq : (c + 2) * (c + 2) ≤ c1 * c1 :=
      Nat.mul_le_mul hcc hcc
    rw [hL] at hc1sq
    omega
  · omega

/-- Consequently the square-root right edge advances by at most two. -/
theorem thetaWindowRight_succ_le_two (k : Nat) :
    thetaWindowRight (k + 1) ≤ thetaWindowRight k + 2 := by
  have hc := thetaWindowCenter_succ_le k
  have hdiv : thetaWindowCenter (k + 1) / 4 ≤
      (thetaWindowCenter k + 1) / 4 := Nat.div_le_div_right hc
  have hdivStep : (thetaWindowCenter k + 1) / 4 ≤
      thetaWindowCenter k / 4 + 1 := by omega
  unfold thetaWindowRight
  omega

/-- The stronger one-cell edge-motion claim is false in the symbolic range. -/
theorem thetaWindowRight_succ_le_one_fails_k69 :
    ¬ (thetaWindowRight (69 + 1) ≤ thetaWindowRight 69 + 1) := by
  unfold thetaWindowRight thetaWindowCenter thetaWindowLength
  decide

theorem lowerSixModeWeight_pos (k n : Nat) :
    (0 : Q') < lowerSixModeWeight k n := by
  unfold lowerSixModeWeight
  exact qpow_pos (Q'.mul_pos (harmW_pos k) (harmW_pos k)) _

/-- A nonnegative physical mode increment has a nonnegative mode carrier,
because its exact heat-kernel weight is strictly positive. -/
theorem lowerSixModeCarrier_nonnegative_of_increment
    {k n : Nat} (hinc : (0 : Q') ≤ lowerSixDirichletIncrement k n) :
    (0 : Q') ≤ lowerSixModeCarrier k n := by
  have hfactor := lowerSixDirichletIncrement_mode_factor k n
  have hproduct : (0 : Q') ≤
      lowerSixModeWeight k n * lowerSixModeCarrier k n :=
    Q'.le_trans' _ _ _ hinc (Q'.le_of_eqv hfactor)
  have hzero : lowerSixModeWeight k n * (0 : Q') ≤
      lowerSixModeWeight k n * lowerSixModeCarrier k n :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (lowerSixModeWeight k n))) hproduct
  exact le_of_mul_le_mul_left_pos (lowerSixModeWeight_pos k n) hzero

/-- Every already-certified right-suffix increment has a nonnegative mode
carrier. -/
theorem lowerSixSuffixModeCarrier_nonnegative
    {k : Nat} (hk : 48 ≤ k) (j : Nat) :
    (0 : Q') ≤ lowerSixModeCarrier k
      (thetaWindowRight k + 1 + j) := by
  exact lowerSixModeCarrier_nonnegative_of_increment
    (lowerSixSuffixIncrement_nonnegative hk j)

/-- Except for the first two old-suffix cells, all next-scale mode carriers are
automatically in the established next-scale suffix. -/
theorem lowerSixNextModeCarrier_nonnegative_afterTwo
    {k : Nat} (hk : 48 ≤ k) (j : Nat) :
    (0 : Q') ≤ lowerSixModeCarrier (k + 1)
      (thetaWindowRight k + 3 + j) := by
  let R := thetaWindowRight k
  let R1 := thetaWindowRight (k + 1)
  have hR : R1 ≤ R + 2 := by
    dsimp only [R1, R]
    exact thetaWindowRight_succ_le_two k
  let t := R + 3 + j - (R1 + 1)
  have hidx : R1 + 1 + t = R + 3 + j := by
    dsimp only [t]
    omega
  rw [← hidx]
  exact lowerSixSuffixModeCarrier_nonnegative (show 48 ≤ k + 1 by omega) t

/-- When the right edge does not advance, the first old-suffix mode is also
already in the next-scale suffix. -/
theorem lowerSixNextBoundaryCarrier_nonnegative_of_stableEdge
    {k : Nat} (hk : 48 ≤ k)
    (hstable : thetaWindowRight (k + 1) ≤ thetaWindowRight k) :
    (0 : Q') ≤ lowerSixModeCarrier (k + 1)
      (thetaWindowRight k + 1) := by
  let t := thetaWindowRight k - thetaWindowRight (k + 1)
  have hidx : thetaWindowRight (k + 1) + 1 + t =
      thetaWindowRight k + 1 := by
    dsimp only [t]
    omega
  rw [← hidx]
  exact lowerSixSuffixModeCarrier_nonnegative (show 48 ≤ k + 1 by omega) t

private theorem ofNat_succ_eqv (n : Nat) :
    Q'.ofNat n + 1 ≈ Q'.ofNat (n + 1) := by
  refine Q'.eqv_trans _ (Q'.ofNat n + Q'.ofNat 1) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (by decide)
  · exact Q'.eqv_symm (Q'.ofNat_add_eqv n 1)

private theorem ofNat_two_mul_add_one_eqv (n : Nat) :
    Q'.ofNat 2 * Q'.ofNat n + 1 ≈ Q'.ofNat (2 * n + 1) := by
  refine Q'.eqv_trans _
    (Q'.ofNat (2 * n) + Q'.ofNat 1) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 n)) (by decide)
  · exact Q'.eqv_symm (Q'.ofNat_add_eqv (2 * n) 1)

private def rightNumPolyL : RingNormaliser.PolyExpr :=
  let N := RingNormaliser.PolyExpr.var 0
  let D := RingNormaliser.PolyExpr.var 1
  .add
    (.mul N (.add D (.add (.mul (.const 2) N) (.const 1))))
    (.neg (.mul (.add N (.const 1)) D))

private def rightNumPolyR : RingNormaliser.PolyExpr :=
  let N := RingNormaliser.PolyExpr.var 0
  let D := RingNormaliser.PolyExpr.var 1
  .add (.mul N (.add (.mul (.const 2) N) (.const 1))) (.neg D)

private theorem rightNumPoly_normal :
    RingNormaliser.normalize rightNumPolyL =
      RingNormaliser.normalize rightNumPolyR := by decide

private theorem right_num_algebra (D N : Q') :
    N * (D + (Q'.ofNat 2 * N + 1)) + -((N + 1) * D) ≈
      N * (Q'.ofNat 2 * N + 1) + -D := by
  simpa [rightNumPolyL, rightNumPolyR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      rightNumPolyL rightNumPolyR rightNumPoly_normal
      (fun | 0 => N | _ => D))

private theorem lowerSixRightNum_eqv_natDifference (k n : Nat) :
    lowerSixRightNum k n ≈
      Q'.ofNat (n * (2 * n + 1)) + -Q'.ofNat (k + 2) := by
  let D := Q'.ofNat (k + 2)
  let N := Q'.ofNat n
  have hsucc : Q'.ofNat (n + 1) ≈ N + 1 :=
    Q'.eqv_symm (ofNat_succ_eqv n)
  have hT : Q'.ofNat (2 * n + 1) ≈ Q'.ofNat 2 * N + 1 := by
    dsimp only [N]
    exact Q'.eqv_symm (ofNat_two_mul_add_one_eqv n)
  have hstart : lowerSixRightNum k n ≈
      N * (D + (Q'.ofNat 2 * N + 1)) + -((N + 1) * D) := by
    unfold lowerSixRightNum lowerSixRightDen
    dsimp only [D, N]
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left N _ _
        (Q'.add_eqv_congr_left D _ _ hT))
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ D hsucc))
  refine Q'.eqv_trans _ _ _ hstart ?_
  refine Q'.eqv_trans _
    (N * (Q'.ofNat 2 * N + 1) + -D) _
    (right_num_algebra D N) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.eqv_trans _
      (Q'.ofNat n * Q'.ofNat (2 * n + 1)) _
      (Q'.mul_eqv_congr_left _ _ _
        (ofNat_two_mul_add_one_eqv n))
      (Q'.eqv_symm
        (HeatKernelRGStep.ofNat_mul_eqv n (2 * n + 1))))

private theorem lowerSixRightNum_nonnegative_of_shape
    {k n : Nat} (hsq : 3 * (k + 2) ≤ n * n) :
    (0 : Q') ≤ lowerSixRightNum k n := by
  have hnat : k + 2 ≤ n * (2 * n + 1) := by
    have hD : k + 2 ≤ n * n := by omega
    have hright : n * n ≤ n * (2 * n + 1) :=
      Nat.mul_le_mul_left n (by omega)
    exact Nat.le_trans hD hright
  have hcast := CReal.ofNat_le_ofNat hnat
  have hsub : (0 : Q') ≤
      Q'.ofNat (n * (2 * n + 1)) + -Q'.ofNat (k + 2) :=
    Q'.sub_nonneg_of_le hcast
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixRightNum_eqv_natDifference k n)))

/-- The two elementary integer shape inequalities imply nonnegativity of the
actual mode carrier, not merely of its cleared raw surrogate. -/
theorem lowerSixModeCarrier_nonnegative_of_shape
    {k n : Nat}
    (hsq : 3 * (k + 2) ≤ n * n)
    (hlinear : 5 * (2 * n + 1) ≤ 3 * (k + 2)) :
    (0 : Q') ≤ lowerSixModeCarrier k n := by
  have hsqQ : Q'.ofNat 3 * Q'.ofNat (k + 2) ≤
      RingNormaliser.qpow (Q'.ofNat n) 2 := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ofNat_three_mul_eqv (k + 2)))
      (Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hsq)
        (Q'.le_of_eqv (Q'.eqv_symm (ofNat_square_eqv n))))
  have hlinearQ :
      Q'.ofNat 5 * (Q'.ofNat 2 * Q'.ofNat n + 1) ≤
        Q'.ofNat 3 * Q'.ofNat (k + 2) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ofNat_shape_left_eqv n))
      (Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hlinear)
        (Q'.le_of_eqv
          (Q'.eqv_symm (ofNat_three_mul_eqv (k + 2)))))
  have hraw := lowerSixRightRawSlack_nonnegative_of_shape
    (D := Q'.ofNat (k + 2)) (N := Q'.ofNat n)
    (CReal.ofNat_le_ofNat (by omega : 1 ≤ k + 2))
    (HeatKernelRGStep.zero_le_ofNat _) hsqQ hlinearQ
  have heq := lowerSixRightRawSlack_eqv_clearedDifference k n
  have hdiff : (0 : Q') ≤
      (Q'.ofNat 4 *
          (lowerSixRightNum k n * lowerSixRightNum k n)) *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) +
        -((Q'.ofNat 12 *
              (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) + 1) *
          Q'.ofNat (n * n) *
          (lowerSixRightDen k n * lowerSixRightDen k n)) :=
    Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv heq)
  have hcleared : LowerSixRightClearedCertificate k n := by
    refine ⟨lowerSixRightNum_nonnegative_of_shape hsq, ?_⟩
    exact Q'.le_of_sub_nonneg hdiff
  exact lowerSixModeCarrier_nonnegative_of_increment
    (lowerSixDirichletIncrement_nonnegative_of_rightCertificate
      (lowerSixRightCertificate_of_cleared hcleared))

/-! ## Tight shape at a moving edge -/

private theorem center_right_edge_shape_of_tight_square
    {D c : Nat}
    (hc36 : 36 ≤ c)
    (hsq : c * c ≤ 2 * D + 1)
    (hsqUpper : 2 * D + 1 ≤ c * c + 1) :
    let n := c + c / 4
    3 * D ≤ n * n ∧ 5 * (2 * n + 1) ≤ 3 * D := by
  let q := c / 4
  have hcdiv : c = 4 * q + c % 4 := by
    simpa [q] using div_four_decomp c
  have hcases := mod_four_cases c
  rcases hcases with h0 | h1 | h2 | h3
  · have hc : c = 4 * q := by omega
    have hq : 9 ≤ q := by omega
    have hqq : 9 * q ≤ q * q := nine_mul_le_square hq
    have hcsq : c * c = 16 * (q * q) := by
      rw [hc]
      simpa using linear_square 4 0 q
    have hn : c + c / 4 = 5 * q := by omega
    have hnsq : (c + c / 4) * (c + c / 4) = 25 * (q * q) := by
      rw [hn]
      simpa using linear_square 5 0 q
    dsimp only
    rw [hcsq] at hsq hsqUpper
    rw [hnsq, hn]
    constructor <;> omega
  · have hc : c = 4 * q + 1 := by omega
    have hq : 9 ≤ q := by omega
    have hqq : 9 * q ≤ q * q := nine_mul_le_square hq
    have hcsq : c * c =
        16 * (q * q) + 4 * q + 4 * q + 1 := by
      rw [hc]
      simpa using linear_square 4 1 q
    have hn : c + c / 4 = 5 * q + 1 := by omega
    have hnsq : (c + c / 4) * (c + c / 4) =
        25 * (q * q) + 5 * q + 5 * q + 1 := by
      rw [hn]
      simpa using linear_square 5 1 q
    dsimp only
    rw [hcsq] at hsq hsqUpper
    rw [hnsq, hn]
    constructor <;> omega
  · have hc : c = 4 * q + 2 := by omega
    have hq : 9 ≤ q := by omega
    have hqq : 9 * q ≤ q * q := nine_mul_le_square hq
    have hcsq : c * c =
        16 * (q * q) + 8 * q + 8 * q + 4 := by
      rw [hc]
      simpa using linear_square 4 2 q
    have hn : c + c / 4 = 5 * q + 2 := by omega
    have hnsq : (c + c / 4) * (c + c / 4) =
        25 * (q * q) + 10 * q + 10 * q + 4 := by
      rw [hn]
      simpa using linear_square 5 2 q
    dsimp only
    rw [hcsq] at hsq hsqUpper
    rw [hnsq, hn]
    constructor <;> omega
  · have hc : c = 4 * q + 3 := by omega
    have hq : 9 ≤ q := by omega
    have hqq : 9 * q ≤ q * q := nine_mul_le_square hq
    have hcsq : c * c =
        16 * (q * q) + 12 * q + 12 * q + 9 := by
      rw [hc]
      simpa using linear_square 4 3 q
    have hn : c + c / 4 = 5 * q + 3 := by omega
    have hnsq : (c + c / 4) * (c + c / 4) =
        25 * (q * q) + 15 * q + 15 * q + 9 := by
      rw [hn]
      simpa using linear_square 5 3 q
    dsimp only
    rw [hcsq] at hsq hsqUpper
    rw [hnsq, hn]
    constructor <;> omega

private theorem center_before_right_edge_shape_of_tight_square
    {D c : Nat}
    (hc40 : 40 ≤ c)
    (hcmod : c % 4 = 0)
    (hsq : c * c ≤ 2 * D + 1)
    (hsqUpper : 2 * D + 1 ≤ c * c + 1) :
    let n := c + c / 4 - 1
    3 * D ≤ n * n ∧ 5 * (2 * n + 1) ≤ 3 * D := by
  let q := c / 4
  let n := c + c / 4 - 1
  have hc : c = 4 * q := by
    have hcdiv : c = 4 * q + c % 4 := by
      simpa [q] using div_four_decomp c
    omega
  have hq : 10 ≤ q := by omega
  have hqq : 10 * q ≤ q * q := ten_mul_le_square hq
  have hcsq : c * c = 16 * (q * q) := by
    rw [hc]
    simpa using linear_square 4 0 q
  have hn : n + 1 = 5 * q := by
    dsimp only [n]
    omega
  have hnSq : (n + 1) * (n + 1) =
      n * n + n + n + 1 := by
    simpa [Nat.add_assoc] using linear_square 1 1 n
  have hfiveSq : (5 * q) * (5 * q) = 25 * (q * q) := by
    simpa using linear_square 5 0 q
  dsimp only
  rw [hcsq] at hsq hsqUpper
  rw [hn] at hnSq
  rw [hfiveSq] at hnSq
  dsimp only [n] at hnSq ⊢
  constructor <;> omega

theorem thetaWindowCenter_mono_step (k : Nat) :
    thetaWindowCenter k ≤ thetaWindowCenter (k + 1) := by
  unfold thetaWindowCenter
  apply ChebOrthoMidpointEst.isqrt_ge
  have h := ChebOrthoMidpointEst.isqrt_sq_le (thetaWindowLength k)
  unfold thetaWindowLength at h ⊢
  omega

private theorem thetaWindowCenter_eq_succ_of_right_move
    {k : Nat} (hmove : thetaWindowRight k < thetaWindowRight (k + 1)) :
    thetaWindowCenter (k + 1) = thetaWindowCenter k + 1 := by
  have hmono := thetaWindowCenter_mono_step k
  have hstep := thetaWindowCenter_succ_le k
  by_cases heq : thetaWindowCenter (k + 1) = thetaWindowCenter k
  · have hR : thetaWindowRight (k + 1) = thetaWindowRight k := by
      unfold thetaWindowRight
      rw [heq]
    omega
  · omega

private theorem moving_length_tight
    {k : Nat} (hmove : thetaWindowRight k < thetaWindowRight (k + 1)) :
    thetaWindowLength (k + 1) ≤
      thetaWindowCenter (k + 1) * thetaWindowCenter (k + 1) + 1 := by
  have hc := thetaWindowCenter_eq_succ_of_right_move hmove
  have hprev := isqrt_lt_succ_sq (thetaWindowLength k)
  have hlength : thetaWindowLength (k + 1) = thetaWindowLength k + 2 := by
    unfold thetaWindowLength
    omega
  unfold thetaWindowCenter at hc
  rw [← hc] at hprev
  rw [hlength]
  unfold thetaWindowCenter
  omega

/-- At a moving right edge, the exact new edge satisfies the raw suffix
shape inequalities once the center reaches the stable threshold. -/
theorem lowerSixMovingEdge_shape_nat_large
    {k : Nat} (hk : 646 ≤ k)
    (hmove : thetaWindowRight k < thetaWindowRight (k + 1)) :
    let D := k + 3
    let n := thetaWindowRight (k + 1)
    3 * D ≤ n * n ∧ 5 * (2 * n + 1) ≤ 3 * D := by
  let c := thetaWindowCenter (k + 1)
  have hc36 : 36 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hsq : c * c ≤ 2 * (k + 3) + 1 := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hsqUpper : 2 * (k + 3) + 1 ≤ c * c + 1 := by
    simpa [thetaWindowLength, c] using moving_length_tight hmove
  simpa [thetaWindowRight, c] using
    (center_right_edge_shape_of_tight_square hc36 hsq hsqUpper)

private theorem center_mod_four_zero_of_right_jump_two
    {k : Nat}
    (hjump : thetaWindowRight (k + 1) = thetaWindowRight k + 2) :
    thetaWindowCenter (k + 1) % 4 = 0 := by
  have hmove : thetaWindowRight k < thetaWindowRight (k + 1) := by omega
  have hc := thetaWindowCenter_eq_succ_of_right_move hmove
  unfold thetaWindowRight at hjump
  omega

/-- On a two-cell edge jump, the old first suffix mode is one mode before
the new edge and satisfies the same tight-square shape certificate. -/
theorem lowerSixMovingBeforeEdge_shape_nat_large
    {k : Nat} (hk : 646 ≤ k)
    (hjump : thetaWindowRight (k + 1) = thetaWindowRight k + 2) :
    let D := k + 3
    let n := thetaWindowRight k + 1
    3 * D ≤ n * n ∧ 5 * (2 * n + 1) ≤ 3 * D := by
  let c := thetaWindowCenter (k + 1)
  have hmove : thetaWindowRight k < thetaWindowRight (k + 1) := by omega
  have hc36 : 36 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hcmod : c % 4 = 0 := by
    dsimp only [c]
    exact center_mod_four_zero_of_right_jump_two hjump
  have hsq : c * c ≤ 2 * (k + 3) + 1 := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hsqUpper : 2 * (k + 3) + 1 ≤ c * c + 1 := by
    simpa [thetaWindowLength, c] using moving_length_tight hmove
  have hc40 : 40 ≤ c := by
    rcases Nat.lt_or_ge c 40 with hsmall | hlarge
    · have hcUpper : c ≤ 39 := by omega
      have hcEq : c = 36 := by omega
      rw [hcEq] at hsqUpper
      omega
    · exact hlarge
  have hidx : thetaWindowRight k + 1 = c + c / 4 - 1 := by
    dsimp only [c]
    unfold thetaWindowRight at hjump ⊢
    omega
  rw [hidx]
  exact center_before_right_edge_shape_of_tight_square
    hc40 hcmod hsq hsqUpper

/-- At every sufficiently large moving edge, the new edge mode has a
nonnegative next-scale carrier. -/
theorem lowerSixMovingEdgeCarrier_nonnegative_large
    {k : Nat} (hk : 646 ≤ k)
    (hmove : thetaWindowRight k < thetaWindowRight (k + 1)) :
    (0 : Q') ≤ lowerSixModeCarrier (k + 1)
      (thetaWindowRight (k + 1)) := by
  have hshape := lowerSixMovingEdge_shape_nat_large hk hmove
  exact lowerSixModeCarrier_nonnegative_of_shape hshape.1 hshape.2

/-- On every sufficiently large two-cell jump, the old first suffix mode is
the mode just before the new edge and has a nonnegative next-scale carrier. -/
theorem lowerSixMovingBeforeEdgeCarrier_nonnegative_large
    {k : Nat} (hk : 646 ≤ k)
    (hjump : thetaWindowRight (k + 1) = thetaWindowRight k + 2) :
    (0 : Q') ≤ lowerSixModeCarrier (k + 1)
      (thetaWindowRight k + 1) := by
  have hshape := lowerSixMovingBeforeEdge_shape_nat_large hk hjump
  exact lowerSixModeCarrier_nonnegative_of_shape hshape.1 hshape.2

/-- Exact kernel bootstrap for both potentially exposed boundary carriers
below the stable moving-edge threshold. -/
theorem lowerSixNextBoundaryCarriers_nonnegative_small : ∀ i : Fin 598,
    (0 : Q') ≤ lowerSixModeCarrier (i.val + 49)
        (thetaWindowRight (i.val + 48) + 1) ∧
      (0 : Q') ≤ lowerSixModeCarrier (i.val + 49)
        (thetaWindowRight (i.val + 48) + 2) := by
  decide

/-- The first old-suffix cell has a nonnegative carrier at the next scale. -/
theorem lowerSixNextFirstBoundaryCarrier_nonnegative
    {k : Nat} (hk : 48 ≤ k) :
    (0 : Q') ≤ lowerSixModeCarrier (k + 1)
      (thetaWindowRight k + 1) := by
  by_cases hlarge : 646 ≤ k
  · by_cases hstable : thetaWindowRight (k + 1) ≤ thetaWindowRight k
    · exact lowerSixNextBoundaryCarrier_nonnegative_of_stableEdge hk hstable
    · have hmove : thetaWindowRight k < thetaWindowRight (k + 1) := by
        omega
      have hstep := thetaWindowRight_succ_le_two k
      by_cases hone : thetaWindowRight (k + 1) ≤ thetaWindowRight k + 1
      · have heq : thetaWindowRight (k + 1) =
            thetaWindowRight k + 1 := by omega
        rw [← heq]
        exact lowerSixMovingEdgeCarrier_nonnegative_large hlarge hmove
      · have hjump : thetaWindowRight (k + 1) =
            thetaWindowRight k + 2 := by omega
        exact lowerSixMovingBeforeEdgeCarrier_nonnegative_large hlarge hjump
  · let i : Fin 598 := ⟨k - 48, by omega⟩
    have h := (lowerSixNextBoundaryCarriers_nonnegative_small i).1
    have hkidx : k - 48 + 48 = k := by omega
    have hkidx1 : k - 48 + 49 = k + 1 := by omega
    simpa [i, hkidx, hkidx1] using h

/-- The second old-suffix cell has a nonnegative carrier at the next scale. -/
theorem lowerSixNextSecondBoundaryCarrier_nonnegative
    {k : Nat} (hk : 48 ≤ k) :
    (0 : Q') ≤ lowerSixModeCarrier (k + 1)
      (thetaWindowRight k + 2) := by
  by_cases hlarge : 646 ≤ k
  · have hstep := thetaWindowRight_succ_le_two k
    by_cases hone : thetaWindowRight (k + 1) ≤ thetaWindowRight k + 1
    · let t := thetaWindowRight k + 1 - thetaWindowRight (k + 1)
      have hidx : thetaWindowRight (k + 1) + 1 + t =
          thetaWindowRight k + 2 := by
        dsimp only [t]
        omega
      rw [← hidx]
      exact lowerSixSuffixModeCarrier_nonnegative
        (show 48 ≤ k + 1 by omega) t
    · have hjump : thetaWindowRight (k + 1) =
          thetaWindowRight k + 2 := by omega
      rw [← hjump]
      exact lowerSixMovingEdgeCarrier_nonnegative_large hlarge (by omega)
  · let i : Fin 598 := ⟨k - 48, by omega⟩
    have h := (lowerSixNextBoundaryCarriers_nonnegative_small i).2
    have hkidx : k - 48 + 48 = k := by omega
    have hkidx1 : k - 48 + 49 = k + 1 := by omega
    simpa [i, hkidx, hkidx1] using h

/-- Every mode in the old right suffix has a nonnegative carrier at the next
scale.  The proof splits the two possible boundary cells from the uniform
tail forced by the two-cell edge-motion bound. -/
theorem lowerSixNextModeCarrier_nonnegative
    {k : Nat} (hk : 48 ≤ k) (j : Nat) :
    (0 : Q') ≤ lowerSixModeCarrier (k + 1)
      (thetaWindowRight k + 1 + j) := by
  rcases j with _ | j
  · simpa using lowerSixNextFirstBoundaryCarrier_nonnegative hk
  · rcases j with _ | j
    · simpa [Nat.add_assoc] using
        lowerSixNextSecondBoundaryCarrier_nonnegative hk
    · have h := lowerSixNextModeCarrier_nonnegative_afterTwo hk j
      have hidx : thetaWindowRight k + 3 + j =
          thetaWindowRight k + 1 + (j + 2) := by omega
      rw [← hidx]
      exact h

#print axioms thetaWindowCenter_succ_le
#print axioms thetaWindowRight_succ_le_two
#print axioms thetaWindowRight_succ_le_one_fails_k69
#print axioms lowerSixModeWeight_pos
#print axioms lowerSixModeCarrier_nonnegative_of_increment
#print axioms lowerSixSuffixModeCarrier_nonnegative
#print axioms lowerSixNextModeCarrier_nonnegative_afterTwo
#print axioms lowerSixNextBoundaryCarrier_nonnegative_of_stableEdge
#print axioms lowerSixModeCarrier_nonnegative_of_shape
#print axioms thetaWindowCenter_mono_step
#print axioms lowerSixMovingEdge_shape_nat_large
#print axioms lowerSixMovingBeforeEdge_shape_nat_large
#print axioms lowerSixMovingEdgeCarrier_nonnegative_large
#print axioms lowerSixMovingBeforeEdgeCarrier_nonnegative_large
#print axioms lowerSixNextBoundaryCarriers_nonnegative_small
#print axioms lowerSixNextFirstBoundaryCarrier_nonnegative
#print axioms lowerSixNextSecondBoundaryCarrier_nonnegative
#print axioms lowerSixNextModeCarrier_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix
