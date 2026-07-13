/-
Nonnegativity of the actual full physical cubic window at every scale beyond
the separately checked first center band.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullPhysicalClosure

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCrossing
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointClosure
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointPhysical
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands

local infix:50 " ≈ " => Q'.eqv

private theorem evenDen_eqv {D M r : Nat}
    (h : D = 2 * (M + 5) * (M + 5) + r) :
    Q'.ofNat D ≈
      Q'.ofNat 2 * ((Q'.ofNat M + 5) * (Q'.ofNat M + 5)) +
        Q'.ofNat r := by
  show (Q'.ofNat D).num *
      ((Q'.ofNat 2 * ((Q'.ofNat M + 5) * (Q'.ofNat M + 5)) +
        Q'.ofNat r).den : Int) =
    (Q'.ofNat 2 * ((Q'.ofNat M + 5) * (Q'.ofNat M + 5)) +
      Q'.ofNat r).num * ((Q'.ofNat D).den : Int)
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    show (5 : Q').num = 5 from rfl,
    show ((5 : Q').den : Int) = 1 from rfl,
    Int.mul_one]
  have h' : D = 2 * ((M + 5) * (M + 5)) + r := by
    simpa [Nat.mul_assoc] using h
  exact_mod_cast h'

private theorem oddDen_eqv {D M r : Nat}
    (h : D = 2 * (M + 5) * (M + 6) + r) :
    Q'.ofNat D ≈
      Q'.ofNat 2 * ((Q'.ofNat M + 5) * ((Q'.ofNat M + 5) + 1)) +
        Q'.ofNat r := by
  show (Q'.ofNat D).num *
      ((Q'.ofNat 2 * ((Q'.ofNat M + 5) * ((Q'.ofNat M + 5) + 1)) +
        Q'.ofNat r).den : Int) =
    (Q'.ofNat 2 * ((Q'.ofNat M + 5) * ((Q'.ofNat M + 5) + 1)) +
      Q'.ofNat r).num * ((Q'.ofNat D).den : Int)
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    show (5 : Q').num = 5 from rfl,
    show ((5 : Q').den : Int) = 1 from rfl,
    show (1 : Q').num = 1 from rfl,
    show ((1 : Q').den : Int) = 1 from rfl,
    Int.mul_one]
  have hm6 : M + 5 + 1 = M + 6 := by omega
  have h' : D = 2 * ((M + 5) * (M + 5 + 1)) + r := by
    simpa [Nat.mul_assoc, hm6] using h
  exact_mod_cast h'

private theorem evenRemainder_le {M r : Nat} (h : r ≤ 2 * M + 9) :
    Q'.ofNat r ≤ Q'.ofNat 2 * Q'.ofNat M + 9 := by
  show (Q'.ofNat r).num *
      ((Q'.ofNat 2 * Q'.ofNat M + 9).den : Int) ≤
    (Q'.ofNat 2 * Q'.ofNat M + 9).num *
      ((Q'.ofNat r).den : Int)
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    show (9 : Q').num = 9 from rfl,
    show ((9 : Q').den : Int) = 1 from rfl,
    Int.mul_one]
  exact_mod_cast h

private theorem oddRemainder_le {M r : Nat} (h : r ≤ 2 * M + 11) :
    Q'.ofNat r ≤ Q'.ofNat 2 * Q'.ofNat M + 11 := by
  show (Q'.ofNat r).num *
      ((Q'.ofNat 2 * Q'.ofNat M + 11).den : Int) ≤
    (Q'.ofNat 2 * Q'.ofNat M + 11).num *
      ((Q'.ofNat r).den : Int)
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.add_num_cast,
    Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast,
    show (11 : Q').num = 11 from rfl,
    show ((11 : Q').den : Int) = 1 from rfl,
    Int.mul_one]
  exact_mod_cast h

theorem thetaCubicClearedBlock_eqv_congr {D D' X X' : Q'}
    (hD : D ≈ D') (hX : X ≈ X') (count : Nat) :
    thetaCubicClearedBlock D X count ≈
      thetaCubicClearedBlock D' X' count := by
  unfold thetaCubicClearedBlock
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro j
  exact thetaCubicClearedCell_eqv_congr hD
    (Q'.add_eqv_congr_right _ _ (Q'.ofNat j) hX)

private theorem ofNat_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Q') < Q'.ofNat n := by
  show (0 : Int) * ((Q'.ofNat n).den : Int) <
    (Q'.ofNat n).num * (((0 : Q').den) : Int)
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    show ((0 : Q').den : Int) = 1 from rfl,
    Int.mul_one]
  exact Int.ofNat_lt.mpr hn

private theorem modeBlock_nonnegative_of_cleared {k start count : Nat}
    (hclear : (0 : Q') ≤ thetaCubicClearedBlock
      (Q'.ofNat (k + 2)) (Q'.ofNat start) count) :
    (0 : Q') ≤ thetaCubicModeBlock k start count := by
  let D := Q'.ofNat (k + 2)
  let C := qcube D
  have hscale := thetaCubicModeBlock_mul_denSix k start count
  have hscaled : (0 : Q') ≤
      thetaCubicModeBlock k start count * (C * C) :=
    Q'.le_trans' _ _ _ hclear (Q'.ge_of_eqv hscale)
  have hD : (0 : Q') < D := ofNat_pos_of_pos (by omega)
  have hC : (0 : Q') < C := by
    unfold C qcube
    exact Q'.mul_pos (Q'.mul_pos hD hD) hD
  have hCC : (0 : Q') < C * C := Q'.mul_pos hC hC
  have hzero : (0 : Q') * (C * C) ≤
      thetaCubicModeBlock k start count * (C * C) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.zero_mul_eqv _)) hscaled
  have hcomm : (C * C) * (0 : Q') ≤
      (C * C) * thetaCubicModeBlock k start count :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv (C * C) 0))
      (Q'.le_trans' _ _ _ hzero
        (Q'.le_of_eqv
          (Q'.mul_comm_eqv (thetaCubicModeBlock k start count) (C * C))))
  exact Q'.le_of_mul_le_mul_left hcomm hCC

def thetaCubicFullModeBlock (k : Nat) : Q' :=
  thetaCubicModeBlock k (thetaWindowLeft k)
    (thetaWindowCenter k - thetaWindowLeft k + 1)

/-- The complete physical cubic block is nonnegative at every `k ≥ 48`. -/
theorem thetaCubicFullModeBlock_nonnegative {k : Nat} (hk : 48 ≤ k) :
    (0 : Q') ≤ thetaCubicFullModeBlock k := by
  rcases thetaWindowCenter_band_data hk with
    ⟨M, r, hc, hDnat, hr⟩ | ⟨M, r, hc, hDnat, hr⟩
  · have hleft : thetaWindowLeft k = M + 5 := by
      unfold thetaWindowLeft
      rw [hc]
      omega
    have hcount : thetaWindowCenter k - thetaWindowLeft k + 1 = M + 6 := by
      rw [hc, hleft]
      omega
    have hr0 : (0 : Q') ≤ Q'.ofNat r :=
      YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat r
    have hclear0 := thetaCubicEvenClearedBlock_nonnegative
      (M := M) (r := Q'.ofNat r) hr0 (evenRemainder_le hr)
    have hD := evenDen_eqv hDnat
    have hX : Q'.ofNat (M + 5) ≈ Q'.ofNat M + 5 :=
      Q'.ofNat_add_eqv M 5
    have hblocks := thetaCubicClearedBlock_eqv_congr hD hX (M + 6)
    have hclear : (0 : Q') ≤ thetaCubicClearedBlock
        (Q'.ofNat (k + 2)) (Q'.ofNat (M + 5)) (M + 6) :=
      Q'.le_trans' _ _ _ hclear0 (Q'.ge_of_eqv hblocks)
    unfold thetaCubicFullModeBlock
    rw [hleft, hc]
    have hcount' : 2 * (M + 5) - (M + 5) + 1 = M + 6 := by omega
    rw [hcount']
    exact modeBlock_nonnegative_of_cleared hclear
  · have hleft : thetaWindowLeft k = M + 5 := by
      unfold thetaWindowLeft
      rw [hc]
      omega
    have hcount : thetaWindowCenter k - thetaWindowLeft k + 1 = M + 7 := by
      rw [hc, hleft]
      omega
    have hr0 : (0 : Q') ≤ Q'.ofNat r :=
      YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat r
    have hclear0 := thetaCubicOddClearedBlock_nonnegative
      (M := M) (r := Q'.ofNat r) hr0 (oddRemainder_le hr)
    have hD := oddDen_eqv hDnat
    have hX : Q'.ofNat (M + 5) ≈ Q'.ofNat M + 5 :=
      Q'.ofNat_add_eqv M 5
    have hblocks := thetaCubicClearedBlock_eqv_congr hD hX (M + 7)
    have hclear : (0 : Q') ≤ thetaCubicClearedBlock
        (Q'.ofNat (k + 2)) (Q'.ofNat (M + 5)) (M + 7) :=
      Q'.le_trans' _ _ _ hclear0 (Q'.ge_of_eqv hblocks)
    unfold thetaCubicFullModeBlock
    rw [hleft, hc]
    have hcount' : 2 * (M + 5) + 1 - (M + 5) + 1 = M + 7 := by omega
    rw [hcount']
    exact modeBlock_nonnegative_of_cleared hclear

#print axioms thetaCubicClearedBlock_eqv_congr
#print axioms thetaCubicFullModeBlock
#print axioms thetaCubicFullModeBlock_nonnegative

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullPhysicalClosure
