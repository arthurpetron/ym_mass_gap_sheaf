/-
# Physical carrier start for the cleared linear Abel payment

The physical complement-increment peak is useful only after the next-scale
linear carrier has crossed zero.  This module proves that sign from a sharp
reciprocal-Bernoulli budget and reduces the remaining physical specialization
to a natural-number inequality in the same-center coordinates.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalSplice

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalCarrier

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalSplice
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPostBootstrap
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem physical_carrier_neg_num_cast (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "physical_carrier_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               physical_carrier_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.natCast_mul,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem physical_even_square_local (m : Nat) :
    (2 * m) * (2 * m) = 2 * (2 * m * m) := by ac_rfl

private theorem physical_even_succ_square_local (m : Nat) :
    (2 * m + 1) * (2 * m + 1) =
      2 * (2 * m * m + 2 * m) + 1 := by
  rw [Nat.add_mul, Nat.mul_add, physical_even_square_local]
  omega

private theorem physical_two_m_mul_succ_local (m : Nat) :
    2 * m * (m + 1) = 2 * m * m + 2 * m := by
  rw [Nat.mul_add]
  omega

private theorem physical_odd_succ_square_local (m : Nat) :
    (2 * m + 1 + 1) * (2 * m + 1 + 1) =
      2 * (2 * m * (m + 1) + 2 * m + 1) + 2 := by
  have hform : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  rw [hform, physical_even_square_local]
  have hexpand : 2 * (m + 1) = 2 * m + 2 := by omega
  rw [hexpand, Nat.add_mul, physical_two_m_mul_succ_local]
  omega

private theorem physical_peak_square_local (m : Nat) :
    2 * (m + 3) * (m + 3) = 2 * m * m + 12 * m + 18 := by
  have hfactor : 2 * (m + 3) = 2 * m + 6 := by omega
  have hfirst : 2 * m * (m + 3) = 2 * m * m + 6 * m := by
    rw [Nat.mul_add]
    omega
  have hsix : 6 * (m + 3) = 6 * m + 18 := by omega
  rw [hfactor, Nat.add_mul, hfirst, hsix]
  omega

private abbrev PhysicalCarrierPE := RingNormaliser.PolyExpr

private def pProfileOneSubL : PhysicalCarrierPE :=
  let u : PhysicalCarrierPE := .var 0
  let w := .add (.const 1) (.neg u)
  .add
    (.add (.mul (.mul w w) w)
      (.neg (.mul (.const 3) (.mul w w))))
    (.add (.mul (.const 15) w) (.neg (.const 5)))

private def pProfileOneSubR : PhysicalCarrierPE :=
  let u : PhysicalCarrierPE := .var 0
  .add (.const 8)
    (.neg (.add (.mul (.const 12) u) (.mul (.mul u u) u)))

private theorem pProfileOneSub_normal :
    RingNormaliser.normalize pProfileOneSubL =
      RingNormaliser.normalize pProfileOneSubR := by
  decide

private theorem profile_oneSub_identity (u : Q') :
    lowerSixRecoveryCubicProfile (oneSub u) ≈
      Q'.ofNat 8 + -(Q'.ofNat 12 * u + (u * u) * u) := by
  simpa [pProfileOneSubL, pProfileOneSubR,
    lowerSixRecoveryCubicProfile, oneSub,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pProfileOneSubL pProfileOneSubR pProfileOneSub_normal (fun _ => u))

/-- Reciprocal Bernoulli turns one explicit division-free budget into the
sign of a recovery mode slope.  The statement retains the full cubic profile;
no profile floor is hidden in this transport lemma. -/
theorem lowerSixRecoveryModeSlope_nonnegative_of_bernDen_budget
    {k n : Nat}
    (hbudget :
      Q'.ofNat 8 * Q'.ofNat (n + 1) ≤
        (Q'.ofNat n * lowerSixRecoveryCubicProfile (harmW k)) *
          bernDen (harmU k) (2 * n + 1)) :
    (0 : Q') ≤ lowerSixRecoveryModeSlope k n := by
  let u := harmU k
  let w := harmW k
  let m := 2 * n + 1
  let B := bernDen u m
  let A := Q'.ofNat n * lowerSixRecoveryCubicProfile w
  let C := Q'.ofNat 8 *
    (Q'.ofNat (n + 1) * qpow w m)
  have hu0 : (0 : Q') ≤ u := by
    dsimp only [u]
    exact harmU_nonneg k
  have hu1 : u ≤ (1 : Q') := by
    dsimp only [u]
    exact harmU_le_one k
  have hpow : qpow w m * B ≤ (1 : Q') := by
    dsimp only [w, B, u, m]
    exact oneSub_pow_mul_bernDen_le hu0 hu1 _
  have hcoef0 : (0 : Q') ≤ Q'.ofNat 8 * Q'.ofNat (n + 1) :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
      (ExpNeg.ofNat_nonneg' _)
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.ofNat 8 * Q'.ofNat (n + 1)) hpow hcoef0
  have hleft : C * B ≈
      (Q'.ofNat 8 * Q'.ofNat (n + 1)) * (qpow w m * B) := by
    dsimp only [C]
    physical_carrier_ring
  have hright :
      (Q'.ofNat 8 * Q'.ofNat (n + 1)) * (1 : Q') ≈
        Q'.ofNat 8 * Q'.ofNat (n + 1) :=
    Q'.mul_one_eqv _
  have hCB : C * B ≤ Q'.ofNat 8 * Q'.ofNat (n + 1) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  have hAB : C * B ≤ A * B := by
    dsimp only [A, B, w, u, m] at hbudget ⊢
    exact Q'.le_trans' _ _ _ hCB hbudget
  have hCA : C ≤ A :=
    BakryEmery.le_of_mul_le_mul_right_pos (bernDen_pos hu0 m) hAB
  have hcubic : (0 : Q') ≤ lowerSixRecoveryCubicSlope w n := by
    change (0 : Q') ≤ A + -C
    exact Q'.sub_nonneg_of_le hCA
  have hslope := lowerSixRecoveryModeSlope_eqv_cubicSlope k n
  dsimp only [w] at hcubic
  exact Q'.le_trans' _ _ _ hcubic (Q'.ge_of_eqv hslope)

/-- On the unit interval the exact recovery cubic loses at most `13u` from
its value eight at `w = 1`.  The exact loss is `12u + u^3`; retaining that
identity makes the coefficient thirteen an in-substrate theorem rather than
a sampled constant. -/
theorem lowerSixRecoveryCubicProfile_oneSub_ge_linear
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) :
    Q'.ofNat 8 + -(Q'.ofNat 13 * u) ≤
      lowerSixRecoveryCubicProfile (oneSub u) := by
  have huu : u * u ≤ (1 : Q') * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg hu1 hu1 Q'.zero_le_one hu0
  have hcubeRaw := Q'.mul_le_mul_of_nonneg_right _ _ u huu hu0
  have hcube : (u * u) * u ≤ u :=
    Q'.le_trans' _ _ _ hcubeRaw (Q'.le_of_eqv (Q'.one_mul_eqv u))
  have hdebtRaw := Q'.add_le_add_left (Q'.ofNat 12 * u) _ _ hcube
  have hdebtEq : Q'.ofNat 12 * u + u ≈ Q'.ofNat 13 * u := by
    refine Q'.eqv_trans _
      (Q'.ofNat 12 * u + (1 : Q') * u) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.one_mul_eqv u))
    refine Q'.eqv_trans _
      ((Q'.ofNat 12 + (1 : Q')) * u) _
      (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ u (by decide)
  have hdebt : Q'.ofNat 12 * u + (u * u) * u ≤ Q'.ofNat 13 * u :=
    Q'.le_trans' _ _ _ hdebtRaw (Q'.le_of_eqv hdebtEq)
  have hneg := Q'.neg_le_neg hdebt
  have hadd := Q'.add_le_add_left (Q'.ofNat 8) _ _ hneg
  have hprofile := profile_oneSub_identity u
  exact Q'.le_trans' _ _ _ hadd (Q'.ge_of_eqv hprofile)

/-- A linearized, denominator-cleared Bernoulli budget is sufficient for the
mode-slope sign.  This is the form whose harmonic specialization becomes a
natural-number inequality. -/
theorem lowerSixRecoveryModeSlope_nonnegative_of_linear_bernDen_budget
    {k n : Nat}
    (hbudget :
      Q'.ofNat 8 * Q'.ofNat (n + 1) ≤
        (Q'.ofNat n *
            (Q'.ofNat 8 + -(Q'.ofNat 13 * harmU k))) *
          bernDen (harmU k) (2 * n + 1)) :
    (0 : Q') ≤ lowerSixRecoveryModeSlope k n := by
  have hu0 := harmU_nonneg k
  have hu1 := harmU_le_one k
  have hp := lowerSixRecoveryCubicProfile_oneSub_ge_linear hu0 hu1
  change Q'.ofNat 8 + -(Q'.ofNat 13 * harmU k) ≤
    lowerSixRecoveryCubicProfile (harmW k) at hp
  have hn0 : (0 : Q') ≤ Q'.ofNat n := ExpNeg.ofNat_nonneg' _
  have hB0 : (0 : Q') ≤ bernDen (harmU k) (2 * n + 1) :=
    Q'.le_of_lt (bernDen_pos hu0 _)
  have hscaleN := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat n) hp hn0
  have hscaleB := Q'.mul_le_mul_of_nonneg_right _ _
    (bernDen (harmU k) (2 * n + 1)) hscaleN hB0
  apply lowerSixRecoveryModeSlope_nonnegative_of_bernDen_budget
  exact Q'.le_trans' _ _ _ hbudget hscaleB

/-- Clearing the single harmonic reciprocal turns the linear Bernoulli budget
into an integer inequality.  The explicit `13 ≤ 8D` hypothesis certifies that
the profile floor has a nonnegative cleared numerator. -/
private theorem linear_bernDen_budget_of_nat
    {k n : Nat} (h13 : 13 ≤ 8 * (k + 2))
    (hnat :
      8 * (n + 1) * ((k + 2) * (k + 2)) ≤
        n * (8 * (k + 2) - 13) * ((k + 2) + (2 * n + 1))) :
    Q'.ofNat 8 * Q'.ofNat (n + 1) ≤
      (Q'.ofNat n *
          (Q'.ofNat 8 + -(Q'.ofNat 13 * harmU k))) *
        bernDen (harmU k) (2 * n + 1) := by
  show
    (Q'.ofNat 8 * Q'.ofNat (n + 1)).num *
        (((Q'.ofNat n *
            (Q'.ofNat 8 + -(Q'.ofNat 13 * harmU k))) *
          bernDen (harmU k) (2 * n + 1)).den : Int) ≤
      ((Q'.ofNat n *
          (Q'.ofNat 8 + -(Q'.ofNat 13 * harmU k))) *
        bernDen (harmU k) (2 * n + 1)).num *
          ((Q'.ofNat 8 * Q'.ofNat (n + 1)).den : Int)
  unfold harmU unit bernDen
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.add_num_cast, Q'.add_den_cast,
    Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
    physical_carrier_neg_num_cast,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.mul_one, Int.one_mul]
  push_cast
  have hnatInt :
      Int.ofNat (8 * (n + 1) * ((k + 2) * (k + 2))) ≤
        Int.ofNat
          (n * (8 * (k + 2) - 13) * ((k + 2) + (2 * n + 1))) :=
    Int.ofNat_le.mpr hnat
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natCast_add] at hnatInt
  rw [Int.ofNat_sub h13] at hnatInt
  simpa only [Int.sub_eq_add_neg] using hnatInt

/-- A factorized natural-number payment for the linearized Bernoulli budget.
The quadratic hypothesis is deliberately subtraction-free. -/
private theorem physical_linear_bern_budget_nat
    {D n : Nat} (hD13 : 13 ≤ D) (hn1 : 1 ≤ n)
    (hquad : D + 3 * n ≤ 2 * n * n) :
    8 * (n + 1) * (D * D) ≤
      n * (8 * D - 13) * (D + (2 * n + 1)) := by
  let A := n * (D + (2 * n + 1))
  let B := (n + 1) * D
  let E := A - B
  let P := 8 * D - 13
  have hAform : A = n * D + (2 * n * n + n) := by
    dsimp only [A]
    simp only [Nat.mul_add, Nat.mul_one]
    ac_rfl
  have hBform : B = n * D + D := by
    dsimp only [B]
    simp only [Nat.add_mul, Nat.one_mul]
  have hB4A : B + 4 * n ≤ A := by
    rw [hAform, hBform]
    omega
  have hBA : B ≤ A := Nat.le_trans (Nat.le_add_right B (4 * n)) hB4A
  have hBE : B + E = A := by
    dsimp only [E]
    exact Nat.add_sub_of_le hBA
  have h4nE : 4 * n ≤ E := by omega
  have hP13 : P + 13 = 8 * D := by
    dsimp only [P]
    exact Nat.sub_add_cancel (by omega)
  have h7DP : 7 * D ≤ P := by omega
  have hnstep : n + 1 ≤ 2 * n := by omega
  have hB2 : B ≤ 2 * n * D := by
    dsimp only [B]
    exact Nat.mul_le_mul_right D hnstep
  have hB13 : B * 13 ≤ 26 * n * D := by
    have hs := Nat.mul_le_mul_right 13 hB2
    calc
      B * 13 ≤ (2 * n * D) * 13 := hs
      _ = 26 * n * D := by ac_rfl
  have h26 : 26 * n * D ≤ (4 * n) * (7 * D) := by
    have hnum : 26 * n ≤ 28 * n := Nat.mul_le_mul_right n (by omega)
    have hs := Nat.mul_le_mul_right D hnum
    calc
      26 * n * D ≤ 28 * n * D := hs
      _ = (4 * n) * (7 * D) := by ac_rfl
  have hEP : (4 * n) * (7 * D) ≤ E * P :=
    Nat.mul_le_mul h4nE h7DP
  have hpay : B * 13 ≤ E * P :=
    Nat.le_trans hB13 (Nat.le_trans h26 hEP)
  have hleft : B * (8 * D) = B * P + B * 13 := by
    rw [← hP13, Nat.mul_add]
  have hright : A * P = B * P + E * P := by
    rw [← hBE, Nat.add_mul]
  have hmain : B * (8 * D) ≤ A * P := by
    rw [hleft, hright]
    exact Nat.add_le_add_left hpay _
  calc
    8 * (n + 1) * (D * D) = B * (8 * D) := by
      dsimp only [B]
      ac_rfl
    _ ≤ A * P := hmain
    _ = n * (8 * D - 13) * (D + (2 * n + 1)) := by
      dsimp only [A, P]
      ac_rfl

/-- At the physical complement peak, the next-scale carrier has already
crossed zero.  This supplies the carrier hypothesis required by both signed
bands of the exact physical splice. -/
theorem lowerSixRecoveryLinearCarrier_physicalPeak_nonnegative
    {k c : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c) :
    (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1)
      (lowerSixRecoveryPhysicalPeakIndex c) := by
  let r := lowerSixRecoveryPhysicalPeakIndex c
  let n := r + 1
  let D := k + 3
  have hc36 := lowerSixWithinCenterCell_center_ge_thirtySix hk hcell
  have hD13 : 13 ≤ D := by dsimp only [D]; omega
  have hn1 : 1 ≤ n := by
    dsimp only [n, r]
    unfold lowerSixRecoveryPhysicalPeakIndex
    omega
  have hquad : D + 3 * n ≤ 2 * n * n := by
    have hpar : c % 2 = 0 ∨ c % 2 = 1 := by omega
    rcases hpar with heven | hodd
    · let m := c / 2
      have hc : c = 2 * m := by dsimp only [m]; omega
      have hupper := hcell.2.2.2
      rw [hc, physical_even_succ_square_local] at hupper
      have hDup : D ≤ 2 * m * m + 2 * m - 1 := by
        dsimp only [D]
        omega
      have hn : n = m + 3 := by
        dsimp only [n, r]
        unfold lowerSixRecoveryPhysicalPeakIndex
        rw [hc]
        omega
      rw [hn, physical_peak_square_local]
      omega
    · let m := c / 2
      have hc : c = 2 * m + 1 := by dsimp only [m]; omega
      have hupper := hcell.2.2.2
      rw [hc, physical_odd_succ_square_local] at hupper
      rw [physical_two_m_mul_succ_local] at hupper
      have hDup : D ≤ 2 * m * m + 4 * m + 1 := by
        dsimp only [D]
        omega
      have hn : n = m + 3 := by
        dsimp only [n, r]
        unfold lowerSixRecoveryPhysicalPeakIndex
        rw [hc]
        omega
      rw [hn, physical_peak_square_local]
      omega
  have hnat :
      8 * (n + 1) * (D * D) ≤
        n * (8 * D - 13) * (D + (2 * n + 1)) :=
    physical_linear_bern_budget_nat hD13 hn1 hquad
  have hbudget :
      Q'.ofNat 8 * Q'.ofNat (n + 1) ≤
        (Q'.ofNat n *
            (Q'.ofNat 8 + -(Q'.ofNat 13 * harmU (k + 1)))) *
          bernDen (harmU (k + 1)) (2 * n + 1) := by
    apply linear_bernDen_budget_of_nat
    · omega
    · dsimp only [D] at hnat
      have hkD : k + 1 + 2 = k + 3 := by omega
      rw [hkD]
      exact hnat
  have hslope : (0 : Q') ≤ lowerSixRecoveryModeSlope (k + 1) n :=
    lowerSixRecoveryModeSlope_nonnegative_of_linear_bernDen_budget hbudget
  dsimp only [n] at hslope
  exact lowerSixRecoveryLinearCarrier_nonnegative_of_slope hslope

/-- The exact numerator immediately before a proposed prefix crossing is
enough to certify the favorable physical middle band. -/
theorem lowerSixRecoveryClearedAbelPhysicalMiddle_nonpositive
    {k c s : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hrs : lowerSixRecoveryPhysicalPeakIndex c ≤ s)
    (hbefore : s = lowerSixRecoveryPhysicalPeakIndex c ∨
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) s ≤
        (0 : Q')) :
    lowerSixRecoveryClearedAbelMiddle k
      (lowerSixRecoveryPhysicalPeakIndex c) s ≤ (0 : Q') := by
  let r := lowerSixRecoveryPhysicalPeakIndex c
  have hr1 : 1 ≤ r := lowerSixRecoveryPhysicalPeakIndex_pos hcell.2.1
  have hcarrier : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) r := by
    dsimp only [r]
    exact lowerSixRecoveryLinearCarrier_physicalPeak_nonnegative hk hcell
  have hbeforePrefix : s = r ∨
      lowerSixRecoveryNextCarrierPrefix k (s - 1) ≤ (0 : Q') := by
    rcases hbefore with hEq | hnum
    · exact Or.inl hEq
    · right
      have hs1 : 1 ≤ s := Nat.le_trans hr1 hrs
      apply lowerSixRecoveryNextCarrierPrefix_nonpositive_of_numerator
      simpa only [Nat.sub_add_cancel hs1] using hnum
  apply lowerSixRecoveryClearedAbelMiddle_nonpositive hrs hr1
    (lowerSixRecoveryPhysicalPeakIndex_threshold hcell) hcarrier
    hbeforePrefix

/-- The exact numerator at a proposed crossing certifies the full physical
falling tail as nonnegative. -/
theorem lowerSixRecoveryClearedAbelPhysicalTail_nonnegative
    {k c s L : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hrs : lowerSixRecoveryPhysicalPeakIndex c ≤ s)
    (hafter : (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (s + 1)) :
    (0 : Q') ≤ lowerSixRecoveryClearedAbelTail k s L := by
  let r := lowerSixRecoveryPhysicalPeakIndex c
  have hr1 : 1 ≤ r := lowerSixRecoveryPhysicalPeakIndex_pos hcell.2.1
  have hcarrier : (0 : Q') ≤ lowerSixRecoveryLinearCarrier (k + 1) r := by
    dsimp only [r]
    exact lowerSixRecoveryLinearCarrier_physicalPeak_nonnegative hk hcell
  have hprefix : (0 : Q') ≤ lowerSixRecoveryNextCarrierPrefix k s :=
    lowerSixRecoveryNextCarrierPrefix_nonnegative_of_numerator hafter
  exact lowerSixRecoveryClearedAbelTail_nonnegative hrs hr1
    (lowerSixRecoveryPhysicalPeakIndex_threshold hcell) hcarrier hprefix

/-- The literal terminal numerator together with all three physical variation
bands.  Naming the expression prevents the elaborator from expanding the very
large carrier numerator merely to state later payment theorems. -/
def lowerSixRecoveryClearedAbelPhysicalDebt (k c s : Nat) : Q' :=
  lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1)
        ((2 * c - 1) + 1) *
      lowerSixRecoveryComplementScaleIncrement k (2 * c - 1) +
    (lowerSixRecoveryClearedAbelHead k
        (lowerSixRecoveryPhysicalPeakIndex c) +
      (lowerSixRecoveryClearedAbelMiddle k
          (lowerSixRecoveryPhysicalPeakIndex c) s +
        lowerSixRecoveryClearedAbelTail k s (2 * c - 1)))

/-- The physical three-band debt is exactly the original cleared Abel debt;
this is a lossless coordinate change, not an estimate. -/
theorem lowerSixRecoveryClearedAbelDebt_eqv_physicalDebt
    {k c s : Nat}
    (hrs : lowerSixRecoveryPhysicalPeakIndex c ≤ s)
    (hsL : s ≤ 2 * c - 1) :
    lowerSixRecoveryClearedAbelDebt k c ≈
      lowerSixRecoveryClearedAbelPhysicalDebt k c s := by
  have hsplit :=
    lowerSixRecoveryClearedAbelVariationSum_eqv_threeBand
      (k := k) (c := c)
      (r := lowerSixRecoveryPhysicalPeakIndex c) (s := s) hrs hsL
  unfold lowerSixRecoveryClearedAbelDebt
    lowerSixRecoveryClearedAbelPhysicalDebt
  exact Q'.add_eqv_congr_left _ _ _ hsplit

/-- Lossless consumer for the physical three-band splice.  The hypothesis is
the literal terminal numerator plus all three variation bands, so in
particular the favorable middle band is retained rather than discarded. -/
theorem lowerSixRecoveryLinearPayment_of_physicalThreeBandPayment
    {k c s : Nat} (hc : 1 ≤ c)
    (hrs : lowerSixRecoveryPhysicalPeakIndex c ≤ s)
    (hsL : s ≤ 2 * c - 1)
    (hpay : lowerSixRecoveryClearedAbelPhysicalDebt k c s +
          -(lowerSixRecoveryTerminalDrop k (2 * c) *
            lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) ≤
        lowerSixRecoveryLinearScaleReserve k c *
          lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) :
    -lowerSixRecoveryLinearDriftDebt k c ≤
      lowerSixRecoveryLinearScaleReserve k c := by
  apply lowerSixRecoveryLinearPayment_of_clearedAbelPayment hc
  have hdebt := lowerSixRecoveryClearedAbelDebt_eqv_physicalDebt
    (k := k) hrs hsL
  have hleft := Q'.add_eqv_congr' hdebt (Q'.eqv_refl
    (-(lowerSixRecoveryTerminalDrop k (2 * c) *
      lowerSixRecoveryLinearCarrierPrefixDen (k + 1))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hpay

/-- Post-bootstrap physical specialization of the lossless payment consumer.
Besides paying the original drift debt, it records the certified signs of the
middle and tail bands at the same numerator crossing. -/
theorem lowerSixRecoveryLinearPayment_of_physicalCrossingPayment
    {k c s : Nat} (hk : 648 ≤ k)
    (hcell : LowerSixWithinCenterCell (k + 2) c)
    (hrs : lowerSixRecoveryPhysicalPeakIndex c ≤ s)
    (hsL : s ≤ 2 * c - 1)
    (hbefore : s = lowerSixRecoveryPhysicalPeakIndex c ∨
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) s ≤
        (0 : Q'))
    (hafter : (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (s + 1))
    (hpay : lowerSixRecoveryClearedAbelPhysicalDebt k c s +
          -(lowerSixRecoveryTerminalDrop k (2 * c) *
            lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) ≤
        lowerSixRecoveryLinearScaleReserve k c *
          lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) :
    (-lowerSixRecoveryLinearDriftDebt k c ≤
        lowerSixRecoveryLinearScaleReserve k c) ∧
      lowerSixRecoveryClearedAbelMiddle k
          (lowerSixRecoveryPhysicalPeakIndex c) s ≤ (0 : Q') ∧
      (0 : Q') ≤
        lowerSixRecoveryClearedAbelTail k s (2 * c - 1) := by
  refine ⟨lowerSixRecoveryLinearPayment_of_physicalThreeBandPayment
      (Nat.le_trans (by decide) hcell.2.1) hrs hsL hpay, ?_, ?_⟩
  · exact lowerSixRecoveryClearedAbelPhysicalMiddle_nonpositive
      hk hcell hrs hbefore
  · exact lowerSixRecoveryClearedAbelPhysicalTail_nonnegative
      hk hcell hrs hafter

#print axioms lowerSixRecoveryModeSlope_nonnegative_of_bernDen_budget
#print axioms lowerSixRecoveryCubicProfile_oneSub_ge_linear
#print axioms lowerSixRecoveryModeSlope_nonnegative_of_linear_bernDen_budget
#print axioms lowerSixRecoveryLinearCarrier_physicalPeak_nonnegative
#print axioms lowerSixRecoveryClearedAbelPhysicalMiddle_nonpositive
#print axioms lowerSixRecoveryClearedAbelPhysicalTail_nonnegative
#print axioms lowerSixRecoveryClearedAbelDebt_eqv_physicalDebt
#print axioms lowerSixRecoveryLinearPayment_of_physicalThreeBandPayment
#print axioms lowerSixRecoveryLinearPayment_of_physicalCrossingPayment

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalCarrier
