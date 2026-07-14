/-
Two-sided square-root-window coordinates for the lower-six interior payment.

The exact interior residual is split at the derived right edge of the existing
theta proof window.  Its prefix contains the complete adverse band; its suffix
is the compensating right reserve.  Reciprocal Bernoulli gives a cleared,
division-free certificate implying nonnegativity of each suffix cell.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
import YMGap.Constructive.CornerBound
import YMGap.Continuum.BakryEmery

namespace YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixTerminalPayment
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicThetaRepresentation
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem two_sided_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "two_sided_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               two_sided_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- The prefix through the derived right edge, including the left endpoint. -/
def lowerSixWindowPrefix (k : Nat) : Q' :=
  Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
    finSum (fun j => lowerSixDirichletIncrement k (j + 1))
      (thetaWindowRight k)

/-- The compensating suffix beyond the derived right edge. -/
def lowerSixWindowRightReserve (k : Nat) : Q' :=
  finSum
    (fun j => lowerSixDirichletIncrement k (thetaWindowRight k + 1 + j))
    (growingAnchor k - thetaWindowRight k)

private theorem thetaWindowRight_le_anchor {k : Nat} (hk : 48 ≤ k) :
    thetaWindowRight k ≤ growingAnchor k := by
  have hc := thetaWindowCenter_le_harmonicDen (show 38 ≤ k by omega)
  have hquarter : thetaWindowCenter k / 4 ≤ k + 2 :=
    Nat.le_trans (Nat.div_le_self _ _) hc
  unfold thetaWindowRight growingAnchor
  omega

/-- Exact two-sided decomposition.  The central adverse block is not bounded
or discarded: it is retained in the prefix and paid by the full suffix. -/
theorem lowerSixInterior_eqv_windowPrefix_add_rightReserve {k : Nat}
    (hk : 48 ≤ k) :
    lowerSixInteriorSum k +
        Q'.ofNat 4 * integerThetaTerm (harmW k) 1 ≈
      lowerSixWindowPrefix k + lowerSixWindowRightReserve k := by
  let f := fun j => lowerSixDirichletIncrement k (j + 1)
  have hle := thetaWindowRight_le_anchor hk
  have hcount : growingAnchor k =
      thetaWindowRight k + (growingAnchor k - thetaWindowRight k) := by
    omega
  have hsplit := finSum_split f (thetaWindowRight k)
    (growingAnchor k - thetaWindowRight k)
  rw [← hcount] at hsplit
  unfold lowerSixInteriorSum lowerSixWindowPrefix
    lowerSixWindowRightReserve
  dsimp only [f] at hsplit
  refine Q'.eqv_trans _
    (Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
      finSum (fun j => lowerSixDirichletIncrement k (j + 1))
        (growingAnchor k)) _ ?_ ?_
  · exact Q'.add_comm_eqv _ _
  · refine Q'.eqv_trans _
      (Q'.ofNat 4 * integerThetaTerm (harmW k) 1 +
        (finSum (fun j => lowerSixDirichletIncrement k (j + 1))
            (thetaWindowRight k) +
          finSum
            (fun j => lowerSixDirichletIncrement k
              (thetaWindowRight k + j + 1))
            (growingAnchor k - thetaWindowRight k))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _ hsplit
    · two_sided_ring

/-- Direct two-sided payment consumer. -/
theorem lowerSixInterior_nonnegative_of_window_payment {k : Nat}
    (hk : 48 ≤ k)
    (hpay : -lowerSixWindowPrefix k ≤ lowerSixWindowRightReserve k) :
    (0 : Q') ≤ lowerSixInteriorSum k +
      Q'.ofNat 4 * integerThetaTerm (harmW k) 1 := by
  have hwindow : (0 : Q') ≤
      lowerSixWindowPrefix k + lowerSixWindowRightReserve k := by
    have hadd := Q'.add_le_add_left (lowerSixWindowPrefix k) _ _ hpay
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm (Q'.add_neg_self_eqv (lowerSixWindowPrefix k)))) hadd
  exact Q'.le_trans' _ _ _ hwindow
    (Q'.le_of_eqv
      (Q'.eqv_symm (lowerSixInterior_eqv_windowPrefix_add_rightReserve hk)))

/-- Cleared reciprocal-Bernoulli denominator at mode `n`. -/
def lowerSixRightDen (k n : Nat) : Q' :=
  Q'.ofNat (k + 2) + Q'.ofNat (2 * n + 1)

/-- Cleared reciprocal lower numerator for the exact root slope. -/
def lowerSixRightNum (k n : Nat) : Q' :=
  Q'.ofNat n * lowerSixRightDen k n +
    -(Q'.ofNat (n + 1) * Q'.ofNat (k + 2))

/-- Polynomial, division-free certificate for a positive right-tail cell. -/
def LowerSixRightCellCertificate (k n : Nat) : Prop :=
  (0 : Q') ≤ lowerSixRightNum k n ∧
  lowerSixDirichletProfile k * Q'.ofNat (n * n) *
      (lowerSixRightDen k n * lowerSixRightDen k n) ≤
    Q'.ofNat 4 *
      (lowerSixRightNum k n * lowerSixRightNum k n)

private theorem harmonicDen_mul_harmU (k : Nat) :
    Q'.ofNat (k + 2) * harmU k ≈ (1 : Q') := by
  unfold harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.mul_one, Int.one_mul]

private theorem lowerSix_qpow_mul_rightDen_le (k n : Nat) :
    qpow (harmW k) (2 * n + 1) * lowerSixRightDen k n ≤
      Q'.ofNat (k + 2) := by
  let D := Q'.ofNat (k + 2)
  let r := qpow (harmW k) (2 * n + 1)
  have hbern := oneSub_pow_mul_bernDen_le
    (harmU_nonneg k) (harmU_le_one k) (2 * n + 1)
  change qpow (harmW k) (2 * n + 1) *
    bernDen (harmU k) (2 * n + 1) ≤ (1 : Q') at hbern
  have hD0 : (0 : Q') ≤ D :=
    HeatKernelRGStep.zero_le_ofNat _
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ D hbern hD0
  have hleft : D *
      (r * bernDen (harmU k) (2 * n + 1)) ≈
      r * lowerSixRightDen k n := by
    have hregroup : D *
        (r * bernDen (harmU k) (2 * n + 1)) ≈
        r * (D * bernDen (harmU k) (2 * n + 1)) := by
      two_sided_ring
    have hden : D * bernDen (harmU k) (2 * n + 1) ≈
        lowerSixRightDen k n := by
      have hDu : D * harmU k ≈ (1 : Q') := by
        dsimp only [D]
        exact harmonicDen_mul_harmU k
      unfold bernDen lowerSixRightDen
      refine Q'.eqv_trans _
        (D + Q'.ofNat (2 * n + 1) * (D * harmU k)) _ ?_ ?_
      · two_sided_ring
      exact Q'.add_eqv_congr_left D _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hDu)
          (Q'.mul_one_eqv _))
    exact Q'.eqv_trans _ _ _ hregroup
      (Q'.mul_eqv_congr_left r _ _ hden)
  have hright : D * (1 : Q') ≈ D := Q'.mul_one_eqv D
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hright))

/-- Reciprocal Bernoulli clears the exact root slope against the polynomial
right numerator. -/
theorem lowerSixRightNum_le_slope_mul_den (k n : Nat) :
    lowerSixRightNum k n ≤
      thetaRootSlope k n * lowerSixRightDen k n := by
  let r := qpow (harmW k) (2 * n + 1)
  let D := Q'.ofNat (k + 2)
  let B := lowerSixRightDen k n
  have hrB : r * B ≤ D := lowerSix_qpow_mul_rightDen_le k n
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (n + 1))
    hrB (HeatKernelRGStep.zero_le_ofNat _)
  have hneg := Q'.neg_le_neg hmul
  have hadd := Q'.add_le_add_left
    (Q'.ofNat n * B) _ _ hneg
  have hleft : Q'.ofNat n * B +
      -(Q'.ofNat (n + 1) * D) ≈ lowerSixRightNum k n := by
    dsimp only [B, D]
    unfold lowerSixRightDen lowerSixRightNum
    exact Q'.eqv_refl _
  have hright : Q'.ofNat n * B +
      -(Q'.ofNat (n + 1) * (r * B)) ≈
      thetaRootSlope k n * B := by
    dsimp only [B, r]
    unfold thetaRootSlope
    two_sided_ring
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

private theorem lowerSixRightDen_pos (k n : Nat) :
    (0 : Q') < lowerSixRightDen k n := by
  unfold lowerSixRightDen
  exact Q'.pos_add_nonneg
    (by simpa [Nat.add_assoc] using Q'.ofNat_succ_pos (k + 1))
    (HeatKernelRGStep.zero_le_ofNat _)

/-- The cleared polynomial certificate is sufficient for actual cell
nonnegativity.  No quotient or approximate amplitude enters the statement. -/
theorem lowerSixDirichletIncrement_nonnegative_of_rightCertificate
    {k n : Nat} (hcert : LowerSixRightCellCertificate k n) :
    (0 : Q') ≤ lowerSixDirichletIncrement k n := by
  let A := lowerSixRightNum k n
  let B := lowerSixRightDen k n
  let S := thetaRootSlope k n
  have hAB : A ≤ S * B := lowerSixRightNum_le_slope_mul_den k n
  have hBpos : (0 : Q') < B := lowerSixRightDen_pos k n
  have hB0 : (0 : Q') ≤ B := Q'.le_of_lt hBpos
  have hA0 : (0 : Q') ≤ A := hcert.1
  have hSB0 : (0 : Q') ≤ S * B := Q'.le_trans' _ _ _ hA0 hAB
  have hS0 : (0 : Q') ≤ S := by
    apply BakryEmery.le_of_mul_le_mul_right_pos hBpos
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv B)) hSB0
  have hsq : A * A ≤ (S * B) * (S * B) :=
    Q'.mul_le_mul_of_nonneg hAB hAB hSB0 hA0
  have h4sq := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hsq
    (by decide)
  have hclear := Q'.le_trans' _ _ _ hcert.2 h4sq
  have hrearr : Q'.ofNat 4 * ((S * B) * (S * B)) ≈
      (Q'.ofNat 4 * (S * S)) * (B * B) := by
    two_sided_ring
  have hmul :
      (lowerSixDirichletProfile k * Q'.ofNat (n * n)) * (B * B) ≤
        (Q'.ofNat 4 * (S * S)) * (B * B) :=
    Q'.le_trans' _ _ _ hclear (Q'.le_of_eqv hrearr)
  have hBBpos : (0 : Q') < B * B := Q'.mul_pos hBpos hBpos
  have hcarrier : lowerSixDirichletProfile k * Q'.ofNat (n * n) ≤
      Q'.ofNat 4 * (S * S) :=
    BakryEmery.le_of_mul_le_mul_right_pos hBBpos hmul
  have hmode : (0 : Q') ≤ lowerSixModeCarrier k n := by
    unfold lowerSixModeCarrier
    exact Q'.sub_nonneg_of_le hcarrier
  have hweight : (0 : Q') ≤ lowerSixModeWeight k n := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  exact Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hweight hmode)
    (Q'.ge_of_eqv (lowerSixDirichletIncrement_mode_factor k n))

private theorem finSum_nonnegative_of_terms (f : Nat → Q') : ∀ N,
    (∀ j, j < N → (0 : Q') ≤ f j) → (0 : Q') ≤ finSum f N
  | 0, _ => Q'.le_refl' 0
  | N + 1, h => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_of_terms f N
          (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self N))))
        (h N (Nat.lt_succ_self N))

/-- Uniform right-reserve positivity follows from the cleared certificates
on its derived square-root range. -/
theorem lowerSixWindowRightReserve_nonnegative_of_certificates {k : Nat}
    (hcert : ∀ j, j < growingAnchor k - thetaWindowRight k →
      LowerSixRightCellCertificate k (thetaWindowRight k + 1 + j)) :
    (0 : Q') ≤ lowerSixWindowRightReserve k := by
  unfold lowerSixWindowRightReserve
  apply finSum_nonnegative_of_terms
  intro j hj
  exact lowerSixDirichletIncrement_nonnegative_of_rightCertificate
    (hcert j hj)

/-- Integer-polynomial form of the suffix certificate after clearing the
harmonic denominator cube. -/
def LowerSixRightClearedCertificate (k n : Nat) : Prop :=
  let D := Q'.ofNat (k + 2)
  let B := lowerSixRightDen k n
  let A := lowerSixRightNum k n
  (0 : Q') ≤ A ∧
    (Q'.ofNat 12 * (D * D) + 1) * Q'.ofNat (n * n) * (B * B) ≤
      (Q'.ofNat 4 * (A * A)) * (D * D * D)

private theorem lowerSixProfile_mul_denCube (k : Nat) :
    lowerSixDirichletProfile k *
        (Q'.ofNat (k + 2) * Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) ≈
      Q'.ofNat 12 *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) + 1 := by
  let D := Q'.ofNat (k + 2)
  let u := harmU k
  have hDu : D * u ≈ (1 : Q') := by
    dsimp only [D, u]
    exact harmonicDen_mul_harmU k
  have hcube : (D * u) * ((D * u) * (D * u)) ≈
      (1 : Q') * ((1 : Q') * (1 : Q')) := by
    exact mul_eqv_both hDu (mul_eqv_both hDu hDu)
  unfold lowerSixDirichletProfile
  dsimp only [D, u] at hDu hcube ⊢
  refine Q'.eqv_trans _
    (Q'.ofNat 12 *
        (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) *
          (Q'.ofNat (k + 2) * harmU k) +
      (Q'.ofNat (k + 2) * harmU k) *
        ((Q'.ofNat (k + 2) * harmU k) *
          (Q'.ofNat (k + 2) * harmU k))) _ ?_ ?_
  · two_sided_ring
  have hmid :
      Q'.ofNat 12 *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) *
            (Q'.ofNat (k + 2) * harmU k) +
        (Q'.ofNat (k + 2) * harmU k) *
          ((Q'.ofNat (k + 2) * harmU k) *
            (Q'.ofNat (k + 2) * harmU k)) ≈
      Q'.ofNat 12 *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) * 1 +
        (1 : Q') * ((1 : Q') * (1 : Q')) :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ hDu)
      hcube
  have hcollapse :
      Q'.ofNat 12 *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) * 1 +
        (1 : Q') * ((1 : Q') * (1 : Q')) ≈
      Q'.ofNat 12 *
          (Q'.ofNat (k + 2) * Q'.ofNat (k + 2)) + 1 := by
    exact Q'.add_eqv_congr'
      (Q'.mul_one_eqv _)
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _)
        (Q'.one_mul_eqv _))
  exact Q'.eqv_trans _ _ _ hmid hcollapse

/-- Clearing the harmonic denominator cube is exact and sufficient. -/
theorem lowerSixRightCertificate_of_cleared {k n : Nat}
    (h : LowerSixRightClearedCertificate k n) :
    LowerSixRightCellCertificate k n := by
  let D := Q'.ofNat (k + 2)
  let B := lowerSixRightDen k n
  let A := lowerSixRightNum k n
  let C := D * D * D
  let L := lowerSixDirichletProfile k * Q'.ofNat (n * n) * (B * B)
  let R := Q'.ofNat 4 * (A * A)
  have hprofile : lowerSixDirichletProfile k * C ≈
      Q'.ofNat 12 * (D * D) + 1 := by
    dsimp only [C, D]
    exact lowerSixProfile_mul_denCube k
  have hleft : L * C ≈
      (Q'.ofNat 12 * (D * D) + 1) *
        Q'.ofNat (n * n) * (B * B) := by
    dsimp only [L]
    refine Q'.eqv_trans _
      ((lowerSixDirichletProfile k * C) *
        Q'.ofNat (n * n) * (B * B)) _ ?_ ?_
    · two_sided_ring
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hprofile)
  have hright : R * C ≈
      (Q'.ofNat 4 * (A * A)) * (D * D * D) := by
    exact Q'.eqv_refl _
  have hscaled : L * C ≤ R * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ h.2 (Q'.le_of_eqv (Q'.eqv_symm hright)))
  have hDpos : (0 : Q') < D := by
    dsimp only [D]
    simpa [Nat.add_assoc] using Q'.ofNat_succ_pos (k + 1)
  have hCpos : (0 : Q') < C := by
    dsimp only [C]
    exact Q'.mul_pos (Q'.mul_pos hDpos hDpos) hDpos
  refine ⟨h.1, ?_⟩
  exact BakryEmery.le_of_mul_le_mul_right_pos hCpos hscaled

#print axioms lowerSixInterior_eqv_windowPrefix_add_rightReserve
#print axioms lowerSixInterior_nonnegative_of_window_payment
#print axioms lowerSixRightNum_le_slope_mul_den
#print axioms lowerSixDirichletIncrement_nonnegative_of_rightCertificate
#print axioms lowerSixWindowRightReserve_nonnegative_of_certificates
#print axioms lowerSixRightCertificate_of_cleared

end YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
