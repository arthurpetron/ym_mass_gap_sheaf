/-
An explicit fixed-prefix floor for the tapered Hermite head.

At the large-scale threshold, the first 30 tapered cells are each at least
three quarters.  Consequently the reserved head mass is at least `132 D^3`.
This converts the remaining signed-remainder payment into the uniform cubic
scale estimate `-R <= 33 D^3`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentUpperFluxPayment

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderHeadFloor

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentUpperFluxPayment
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem head_floor_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "head_floor_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               head_floor_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             try ac_rfl))

private def threeQuarters : Q' := Q'.mkPos 3 4 (by decide)

private abbrev PE := RingNormaliser.PolyExpr

private def pOneSubSquareL : PE :=
  let u : PE := .var 0
  let w : PE := .add (.const 1) (.neg u)
  .add (.const 1) (.neg (.mul w w))

private def pOneSubSquareR : PE :=
  let u : PE := .var 0
  let w : PE := .add (.const 1) (.neg u)
  .mul u (.add (.const 1) w)

private theorem pOneSubSquare_normal :
    RingNormaliser.normalize pOneSubSquareL =
      RingNormaliser.normalize pOneSubSquareR := by decide

private theorem oneSubSquare_algebra (u : Q') :
    (1 : Q') + -(((1 : Q') + -u) * ((1 : Q') + -u)) ≈
      u * ((1 : Q') + ((1 : Q') + -u)) := by
  simpa [pOneSubSquareL, pOneSubSquareR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pOneSubSquareL pOneSubSquareR pOneSubSquare_normal (fun _ => u))

private theorem one_sub_harmW_square_eqv (k : Nat) :
    (1 : Q') - harmW k * harmW k ≈
      harmU k * ((1 : Q') + harmW k) := by
  change (1 : Q') + -(harmW k * harmW k) ≈
    harmU k * ((1 : Q') + harmW k)
  unfold harmW ReciprocalBernoulliUpper.oneSub
  exact oneSubSquare_algebra _

private theorem one_sub_harmW_square_le_two_harmU (k : Nat) :
    (1 : Q') - harmW k * harmW k ≤ Q'.ofNat 2 * harmU k := by
  have hsum : (1 : Q') + harmW k ≤ (1 : Q') + 1 :=
    Q'.add_le_add_left (1 : Q') _ _ (harmW_le_one k)
  have hmul : harmU k * ((1 : Q') + harmW k) ≤
      harmU k * ((1 : Q') + 1) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsum (harmU_nonneg k)
  have htwo : harmU k * ((1 : Q') + 1) ≈
      Q'.ofNat 2 * harmU k := by
    refine Q'.eqv_trans _ (((1 : Q') + 1) * harmU k) _
      (Q'.mul_comm_eqv _ _) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (one_sub_harmW_square_eqv k))
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv htwo))

private theorem ringQpow_nonnegative {a : Q'} (ha : (0 : Q') ≤ a) :
    ∀ m, (0 : Q') ≤ RingNormaliser.qpow a m
  | 0 => by
      unfold RingNormaliser.qpow
      decide
  | m + 1 => by
      unfold RingNormaliser.qpow
      exact Q'.mul_nonneg _ _ (ringQpow_nonnegative ha m) ha

private theorem thetaWindowLeft_ge_thirtyTwo_large
    {k : Nat} (hk : 8189 ≤ k) :
    32 ≤ thetaWindowLeft k := by
  have hc : 64 ≤ thetaWindowCenter k := by
    unfold thetaWindowCenter thetaWindowLength
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  unfold thetaWindowLeft
  omega

private theorem lowerSixHermiteLinearHeadCell_ge_threeQuarters_large
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ 30) :
    threeQuarters ≤ lowerSixHermiteLinearHeadCell k n := by
  let delta := (1 : Q') - harmW k * harmW k
  let q := Q'.mkPos 1 4 (by decide)
  have hdelta := one_sub_harmW_square_le_two_harmU k
  have hn0 : (0 : Q') ≤ Q'.ofNat (n * n) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hsq : n * n ≤ 30 * 30 := Nat.mul_le_mul hn hn
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat (n * n)) hdelta hn0
  have hunit :
      Q'.ofNat (n * n) * (Q'.ofNat 2 * harmU k) ≤ q := by
    unfold harmU SummableInverseSquare.unit
    dsimp only [q]
    show
      (Q'.ofNat (n * n) *
        (Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (by omega))).num *
          ((Q'.mkPos 1 4 (by decide)).den : Int) ≤
      (Q'.mkPos 1 4 (by decide)).num *
        (Q'.ofNat (n * n) *
          (Q'.ofNat 2 * Q'.mkPos 1 (k + 2) (by omega))).den
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
      Int.mul_one, Int.one_mul]
    push_cast
    omega
  have hproduct : Q'.ofNat (n * n) * delta ≤ q := by
    dsimp only [delta]
    exact Q'.le_trans' _ _ _ hmul hunit
  have hneg := Q'.neg_le_neg hproduct
  have hadd := Q'.add_le_add_left (1 : Q') (-q)
    (-(Q'.ofNat (n * n) * delta)) hneg
  have hleft : threeQuarters ≈ (1 : Q') + -q := by
    dsimp only [threeQuarters, q]
    decide
  unfold lowerSixHermiteLinearHeadCell
  dsimp only [delta] at hadd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hadd

private theorem finSum_mono_of_nonnegative_between
    (f : Nat → Q') {M N : Nat} (hMN : M ≤ N)
    (h : ∀ j, M ≤ j → j < N → (0 : Q') ≤ f j) :
    finSum f M ≤ finSum f N := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hMN
  induction t with
  | zero =>
      rw [Nat.add_zero]
      exact Q'.le_refl' _
  | succ t ih =>
      rw [Nat.add_succ, finSum_succ]
      have hstep : (0 : Q') ≤ f (M + t) := h (M + t) (by omega) (by omega)
      have iht := ih (show M ≤ M + t by omega)
        (fun j hjM hjt => h j hjM (by omega))
      exact Q'.le_trans' _ _ _ iht
        (Q'.add_le_self_of_nonneg _ _ hstep)

/-- A fixed 30-cell prefix already contributes at least 22 units to the
tapered Hermite head at every scale in the production range. -/
theorem twentyTwo_le_lowerSixHermiteLinearHeadSum_large
    {k : Nat} (hk : 8189 ≤ k) :
    Q'.ofNat 22 ≤ lowerSixHermiteLinearHeadSum k := by
  let f : Nat → Q' := fun j => lowerSixHermiteLinearHeadCell k (j + 1)
  let c : Nat → Q' := fun _ => threeQuarters
  have hterms : ∀ j, j < 30 → c j ≤ f j := by
    intro j hj
    dsimp only [c, f]
    exact lowerSixHermiteLinearHeadCell_ge_threeQuarters_large hk (by omega)
  have hprefix := YMGap.Constructive.finSum_le_lt c f 30 hterms
  have hconst : Q'.ofNat 22 ≤ finSum c 30 := by
    dsimp only [c, threeQuarters]
    unfold finSum
    decide
  have h30 : 30 ≤ thetaWindowLeft k :=
    Nat.le_trans (by decide) (thetaWindowLeft_ge_thirtyTwo_large hk)
  have hextend : finSum f 30 ≤ finSum f (thetaWindowLeft k) := by
    apply finSum_mono_of_nonnegative_between f h30
    intro j _ hj
    dsimp only [f]
    exact lowerSixHermiteLinearHeadCell_nonnegative (by omega)
  unfold lowerSixHermiteLinearHeadSum
  exact Q'.le_trans' _ _ _ hconst
    (Q'.le_trans' _ _ _ hprefix hextend)

/-- Exact large-scale reserve floor supplied by the tapered head. -/
theorem lowerSixHermiteHeadMassFloor_ge_132_cubic_large
    {k : Nat} (hk : 8189 ≤ k) :
    Q'.ofNat 132 * RingNormaliser.qpow (Q'.ofNat (k + 2)) 3 ≤
      lowerSixHermiteLinearHeadMassFloor k := by
  let D3 := RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  let C := Q'.ofNat 6 * D3
  have hD0 : (0 : Q') ≤ Q'.ofNat (k + 2) :=
    HeatKernelRGStep.zero_le_ofNat _
  have hC0 : (0 : Q') ≤ C :=
    Q'.mul_nonneg _ _ (by decide)
      (by
        dsimp only [D3]
        exact ringQpow_nonnegative hD0 3)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ C
    (twentyTwo_le_lowerSixHermiteLinearHeadSum_large hk) hC0
  have halgebra : C * Q'.ofNat 22 ≈ Q'.ofNat 132 * D3 := by
    dsimp only [C]
    head_floor_ring
  unfold lowerSixHermiteLinearHeadMassFloor
  dsimp only [C, D3] at hscaled halgebra ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm halgebra)) hscaled

/-- The signed-remainder payment follows from a uniform cubic-scale bound. -/
theorem lowerSixSignedRemainderPayment_large_of_cubic_bound
    {k : Nat} (hk : 8189 ≤ k)
    (hremainder :
      -lowerSixHermiteRemainderSum k ≤
        Q'.ofNat 33 *
          RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) :
    -(Q'.ofNat 4 * lowerSixHermiteRemainderSum k) ≤
      lowerSixHermiteLinearHeadMassFloor k := by
  let R := lowerSixHermiteRemainderSum k
  let D3 := RingNormaliser.qpow (Q'.ofNat (k + 2)) 3
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4)
    hremainder (by decide)
  have hleft : -(Q'.ofNat 4 * R) ≈ Q'.ofNat 4 * (-R) := by
    head_floor_ring
  have hright : Q'.ofNat 4 * (Q'.ofNat 33 * D3) ≈
      Q'.ofNat 132 * D3 := by
    head_floor_ring
  dsimp only [R, D3] at hleft hright hscaled ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hright)
        (lowerSixHermiteHeadMassFloor_ge_132_cubic_large hk)))

/-- Production composition whose sole remaining input is the cubic-scale
bound for the complete signed finite-`D` Hermite remainder. -/
theorem lowerSixQuadraticPayment_large_of_cubic_remainder_bound
    {k : Nat} (hk : 8189 ≤ k)
    (hremainder :
      -lowerSixHermiteRemainderSum k ≤
        Q'.ofNat 33 *
          RingNormaliser.qpow (Q'.ofNat (k + 2)) 3) :
    -YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftScaleStep.lowerSixScaledLinearCrossPaymentResidual k ≤
      YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment.lowerSixScaledQuadraticCrossWindowSuffix k := by
  exact lowerSixQuadraticPayment_large_of_remainder hk
    (lowerSixSignedRemainderPayment_large_of_cubic_bound hk hremainder)

#print axioms twentyTwo_le_lowerSixHermiteLinearHeadSum_large
#print axioms lowerSixHermiteHeadMassFloor_ge_132_cubic_large
#print axioms lowerSixSignedRemainderPayment_large_of_cubic_bound
#print axioms lowerSixQuadraticPayment_large_of_cubic_remainder_bound

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderHeadFloor
