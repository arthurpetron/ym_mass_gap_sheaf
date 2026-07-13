/-
A negative cubic mode cell cannot occur on the negative-slope branch of the
moving proof window.  The negative branch has carrier magnitude at most one,
whereas the profile mass is at least four.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicTerminalPrefix

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicNegativeBranch

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMovingDeterminantThetaDirichlet
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubic
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCrossing
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCarrierSuffix
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointPhysical
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem two_m_mul_succ (m : Nat) :
    2 * m * (m + 1) = 2 * m * m + 2 * m := by
  rw [Nat.mul_add]
  omega

/-- Every mode in the half-center window satisfies the coarse but sufficient
denominator bound `D ≤ 3n²`. -/
theorem harmonicDen_le_three_mode_square {k n : Nat} (hk : 48 ≤ k)
    (hnLeft : thetaWindowLeft k ≤ n) :
    k + 2 ≤ 3 * n * n := by
  rcases thetaWindowCenter_band_data hk with
    ⟨M, r, hc, hD, hr⟩ | ⟨M, r, hc, hD, hr⟩
  · let m := M + 5
    have hleft : thetaWindowLeft k = m := by
      unfold thetaWindowLeft
      rw [hc]
      dsimp only [m]
      omega
    have hmn : m ≤ n := by omega
    have hmm : m * m ≤ n * n := Nat.mul_le_mul hmn hmn
    have hm2 : 2 * m ≤ m * m := by
      have h := Nat.mul_le_mul_right m (show 2 ≤ m by omega)
      simpa [Nat.mul_comm] using h
    have hrm : r ≤ 2 * m := by dsimp only [m]; omega
    rw [hD]
    calc
      2 * m * m + r ≤ 2 * (m * m) + 2 * m := by
        simpa [Nat.mul_assoc] using Nat.add_le_add_left hrm (2 * m * m)
      _ ≤ 2 * (m * m) + m * m := Nat.add_le_add_left hm2 _
      _ = 3 * (m * m) := by omega
      _ ≤ 3 * (n * n) := Nat.mul_le_mul_left 3 hmm
      _ = 3 * n * n := by simp [Nat.mul_assoc]
  · let m := M + 5
    have hleft : thetaWindowLeft k = m := by
      unfold thetaWindowLeft
      rw [hc]
      dsimp only [m]
      omega
    have hmn : m ≤ n := by omega
    have hmm : m * m ≤ n * n := Nat.mul_le_mul hmn hmn
    have hm5 : 5 * m ≤ m * m := by
      have h := Nat.mul_le_mul_right m (show 5 ≤ m by omega)
      simpa [Nat.mul_comm] using h
    have hrm : r ≤ 2 * m + 1 := by dsimp only [m]; omega
    rw [hD, two_m_mul_succ]
    have hfour : 4 * m + 1 ≤ m * m :=
      Nat.le_trans (by omega) hm5
    calc
      2 * m * m + 2 * m + r ≤
          2 * m * m + 2 * m + (2 * m + 1) :=
        Nat.add_le_add_left hrm _
      _ = 2 * (m * m) + (4 * m + 1) := by
        simp only [Nat.mul_assoc]
        omega
      _ ≤ 2 * (m * m) + m * m := Nat.add_le_add_left hfour _
      _ = 3 * (m * m) := by omega
      _ ≤ 3 * (n * n) := Nat.mul_le_mul_left 3 hmm
      _ = 3 * n * n := by simp [Nat.mul_assoc]

private theorem harmU_mul_den (k : Nat) :
    harmU k * Q'.ofNat (k + 2) ≈ (1 : Q') := by
  unfold harmU unit
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mkPos_num, Q'.mkPos_den,
    Q'.ofNat_num_cast, Q'.ofNat_den_cast, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]

private theorem scaled_square_bound {D n : Nat} (h : D ≤ 3 * n * n) :
    Q'.ofNat 4 * Q'.ofNat D ≤
      Q'.ofNat 12 * (Q'.ofNat n * Q'.ofNat n) := by
  have hnat : 4 * D ≤ 12 * (n * n) := by
    calc
      4 * D ≤ 4 * (3 * n * n) := Nat.mul_le_mul_left 4 h
      _ = (4 * 3) * (n * n) := by ac_rfl
      _ = 12 * (n * n) := rfl
  show (Q'.ofNat 4 * Q'.ofNat D).num *
      ((Q'.ofNat 12 * (Q'.ofNat n * Q'.ofNat n)).den : Int) ≤
    (Q'.ofNat 12 * (Q'.ofNat n * Q'.ofNat n)).num *
      ((Q'.ofNat 4 * Q'.ofNat D).den : Int)
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one]
  exact_mod_cast hnat

private theorem threeFactor_nonnegative_le_one {k n : Nat}
    (hk : 38 ≤ k) (hn : n ≤ thetaWindowCenter k) :
    (0 : Q') ≤ thetaThreeFactorLower (harmW k) n ∧
      thetaThreeFactorLower (harmW k) n ≤ (1 : Q') := by
  let L := thetaLinearBernoulliFactor (harmW k) n
  have hL0 : (0 : Q') ≤ L :=
    thetaLinearBernoulliFactor_nonnegative_on_window hk hn
  have hLL0 : (0 : Q') ≤ L * L := Q'.mul_nonneg _ _ hL0 hL0
  have hT1 : thetaThreeFactorLower (harmW k) n ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (qpow_odd_ge_threeFactor (harmW_nonneg k) (harmW_le_one k) n hL0)
      (HeatKernelGap.qpow_le_one (harmW_nonneg k) (harmW_le_one k) _)
  constructor
  · change (0 : Q') ≤ (L * L) * harmW k
    exact Q'.mul_nonneg _ _ hLL0 (harmW_nonneg k)
  · exact hT1

/-- On the negative branch the cubic right carrier is bounded below by `-1`. -/
private theorem neg_one_le_rightCarrier {k n : Nat}
    (hk : 38 ≤ k) (hn : n ≤ thetaWindowCenter k) :
    -(1 : Q') ≤ thetaCubicRightCarrier k n := by
  let T := thetaThreeFactorLower (harmW k) n
  have hT := (threeFactor_nonnegative_le_one hk hn).2
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (n + 1)) hT
    (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
  have hneg := Q'.neg_le_neg hmul
  have hadd := Q'.add_le_add_left (Q'.ofNat n) _ _ hneg
  have hnp1 : Q'.ofNat (n + 1) ≈ Q'.ofNat n + 1 :=
    Q'.ofNat_add_eqv n 1
  have hright :
      Q'.ofNat n + -(Q'.ofNat (n + 1) * (1 : Q')) ≈ -(1 : Q') := by
    refine Q'.eqv_trans _
      (Q'.ofNat n + -((Q'.ofNat n + 1) * (1 : Q'))) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_right _ _ (1 : Q') hnp1))
    · refine Q'.eqv_trans _ (Q'.ofNat n + -(Q'.ofNat n + 1)) _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv _))) ?_
      refine Q'.eqv_trans _ (Q'.ofNat n + (-Q'.ofNat n + -(1 : Q'))) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_eqv _ _)) ?_
      refine Q'.eqv_trans _ ((Q'.ofNat n + -Q'.ofNat n) + -(1 : Q')) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ ((0 : Q') + -(1 : Q')) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv _)) ?_
      exact YMGap.Constructive.QPoly.q_zero_add_eqv _
  unfold thetaCubicRightCarrier
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hright) hadd

private theorem rightCarrier_square_le_one_of_negative {k n : Nat}
    (hk : 38 ≤ k) (hn : n ≤ thetaWindowCenter k)
    (hR : thetaCubicRightCarrier k n < (0 : Q')) :
    thetaCubicRightCarrier k n * thetaCubicRightCarrier k n ≤ (1 : Q') := by
  let R := thetaCubicRightCarrier k n
  have hm1 : -(1 : Q') ≤ R := neg_one_le_rightCarrier hk hn
  have hR0 : R ≤ (0 : Q') := Q'.le_of_lt hR
  have hneg0 : (0 : Q') ≤ -R := by
    have h := Q'.neg_le_neg hR0
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv)) h
  have hneg1 : -R ≤ (1 : Q') := by
    have h := Q'.neg_le_neg hm1
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv 1))
  have hsq : (-R) * (-R) ≤ (1 : Q') * 1 :=
    Q'.mul_le_mul_of_nonneg hneg1 hneg1 (by decide) hneg0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by ring_qeqv))
    (Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv (Q'.mul_one_eqv 1)))

/-- The profile contribution at every mode in the half-center window is at
least four. -/
theorem four_le_profile_mode_square {k n : Nat} (hk : 48 ≤ k)
    (hnLeft : thetaWindowLeft k ≤ n) :
    (Q'.ofNat 4 : Q') ≤
      sevenDirichletProfile k * (Q'.ofNat n * Q'.ofNat n) := by
  let U := harmU k
  let N2 := Q'.ofNat n * Q'.ofNat n
  have hden := harmonicDen_le_three_mode_square hk hnLeft
  have hnat : 4 * (k + 2) ≤ 12 * (n * n) := by
    calc
      4 * (k + 2) ≤ 4 * (3 * n * n) := Nat.mul_le_mul_left 4 hden
      _ = (4 * 3) * (n * n) := by ac_rfl
      _ = 12 * (n * n) := rfl
  have hbase : (Q'.ofNat 4 : Q') ≤ (U * Q'.ofNat 12) * N2 := by
    unfold U harmU SummableInverseSquare.unit N2
    show (Q'.ofNat 4).num *
          (((Q'.mkPos 1 (k + 2) (by omega) * Q'.ofNat 12) *
            (Q'.ofNat n * Q'.ofNat n)).den : Int) ≤
        ((Q'.mkPos 1 (k + 2) (by omega) * Q'.ofNat 12) *
            (Q'.ofNat n * Q'.ofNat n)).num *
          ((Q'.ofNat 4).den : Int)
    simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
      Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
      Int.mul_one, Int.one_mul]
    exact_mod_cast hnat
  have hU0 : (0 : Q') ≤ U := harmU_nonneg k
  have hUU0 : (0 : Q') ≤ U * U := Q'.mul_nonneg _ _ hU0 hU0
  have hinner : Q'.ofNat 12 ≤ (Q'.ofNat 12 + U) + U * U :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg _ _ hU0)
      (Q'.add_le_self_of_nonneg _ _ hUU0)
  have hprof : U * Q'.ofNat 12 ≤ sevenDirichletProfile k := by
    unfold sevenDirichletProfile U
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hU0
  have hN20 : (0 : Q') ≤ N2 := by
    unfold N2
    exact Q'.mul_nonneg _ _
      (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
      (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hbase
    (Q'.mul_le_mul_of_nonneg_right _ _ N2 hprof hN20)

/-- A negative cubic cell in the physical window is necessarily already on
the nonnegative-slope branch. -/
theorem thetaCubicNegativeCell_rightCarrier_nonnegative {k n : Nat}
    (hk : 48 ≤ k) (hnLeft : thetaWindowLeft k ≤ n)
    (hnCenter : n ≤ thetaWindowCenter k)
    (hcell : thetaCubicModeCell k n < (0 : Q')) :
    (0 : Q') ≤ thetaCubicRightCarrier k n := by
  by_cases hR : thetaCubicRightCarrier k n < (0 : Q')
  · have hsq := rightCarrier_square_le_one_of_negative
      (show 38 ≤ k by omega) hnCenter hR
    have hfour := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 4) hsq
      (by decide)
    have hfour1 : Q'.ofNat 4 *
        (thetaCubicRightCarrier k n * thetaCubicRightCarrier k n) ≤
        Q'.ofNat 4 :=
      Q'.le_trans' _ _ _ hfour (Q'.le_of_eqv (Q'.mul_one_eqv _))
    have hprofile := four_le_profile_mode_square hk hnLeft
    have hpay : Q'.ofNat 4 *
          (thetaCubicRightCarrier k n * thetaCubicRightCarrier k n) ≤
        sevenDirichletProfile k * (Q'.ofNat n * Q'.ofNat n) :=
      Q'.le_trans' _ _ _ hfour1 hprofile
    have hnonneg : (0 : Q') ≤ thetaCubicModeCell k n := by
      unfold thetaCubicModeCell
      exact Q'.sub_nonneg_of_le hpay
    exact False.elim ((Int.not_lt.mpr hnonneg) hcell)
  · show (0 : Int) * ((thetaCubicRightCarrier k n).den : Int) ≤
      (thetaCubicRightCarrier k n).num * (((0 : Q').den) : Int)
    exact Int.le_of_not_gt hR

#print axioms harmonicDen_le_three_mode_square
#print axioms four_le_profile_mode_square
#print axioms thetaCubicNegativeCell_rightCarrier_nonnegative

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicNegativeBranch
