/- Staged Schur/operator closure for harmonic scales thirteen through sixteen. -/

import YMGap.Continuum.SevenAnchorWindowRetune
import YMGap.Continuum.HarmonicSchurRotationK101112
import YMGap.Continuum.HarmonicMassRatioK13
import YMGap.Continuum.HarmonicMassRatioK14
import YMGap.Continuum.HarmonicMassRatioK15
import YMGap.Continuum.HarmonicMassRatioK16
import YMGap.Continuum.HarmonicFixedSixFloorK17

namespace YMGap.Continuum.HarmonicSchurRotationK1316

set_option maxHeartbeats 18000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK101112
open YMGap.Continuum.HarmonicWeightDriftFence

local infix:50 " ≈ " => Q'.eqv

private theorem rotated_shell_scale_eqv (a b scale ca cb : Q')
    (ha : ((Q'.mkPos 4 5 (by decide) * Q'.mkPos 4 5 (by decide)) * scale) ≈ ca)
    (hb : ((Q'.mkPos 3 5 (by decide) * Q'.mkPos 3 5 (by decide)) * scale) ≈ cb) :
    rot11 a b * scale ≈ ca * a + cb * b := by
  unfold rot11
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ scale) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ a scale) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv a scale)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ scale a)) ?_
    exact Q'.mul_eqv_congr_right _ _ a ha
  · refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ b scale) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv b scale)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ scale b)) ?_
    exact Q'.mul_eqv_congr_right _ _ b hb

private theorem shell_spacing_stage_of_ratio
    (k : Nat) (p q old total shellScale C : Q')
    (hcoeff : old + p ≈ total)
    (hnext : harmonicSpacing (k + 1) * C ≈ total)
    (hold : harmonicSpacing k * C ≈ shellScale)
    (hrotOld :
      (Q'.mkPos 4 5 (by decide) * Q'.mkPos 4 5 (by decide)) * shellScale ≈ old)
    (hrotNew :
      (Q'.mkPos 3 5 (by decide) * Q'.mkPos 3 5 (by decide)) * shellScale ≈ q)
    (hCpos : (0 : Q') < C)
    (hratio : p * harmonicMass k ≤ q * harmonicMass (k + 1)) :
    harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k := by
  have hadd := Q'.add_le_add_left (old * harmonicMass k) _ _ hratio
  have hsum : total * harmonicMass k ≤
      old * harmonicMass k + q * harmonicMass (k + 1) := by
    have hleft : old * harmonicMass k + p * harmonicMass k ≈
        total * harmonicMass k := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv old p (harmonicMass k))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ hcoeff
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hadd
  have hleft : (harmonicMass k * harmonicSpacing (k + 1)) * C ≈
      total * harmonicMass k := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicMass k) (harmonicSpacing (k + 1)) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicMass k) _ _ hnext) ?_
    exact Q'.mul_comm_eqv _ _
  have hright : (harmonicShell k * harmonicSpacing k) * C ≈
      old * harmonicMass k + q * harmonicMass (k + 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicShell k) (harmonicSpacing k) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicShell k) _ _ hold) ?_
    unfold harmonicShell
    exact rotated_shell_scale_eqv _ _ _ _ _ hrotOld hrotNew
  have hmul : (harmonicMass k * harmonicSpacing (k + 1)) * C ≤
      (harmonicShell k * harmonicSpacing k) * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hright))
  exact BakryEmery.le_of_mul_le_mul_right_pos hCpos hmul

/-! ## Cached exact mass-ratio certificates -/

theorem harmonicMass_ratio_k13 :
    Q'.ofNat 1529 * harmonicMass 13 ≤ Q'.ofNat 2304 * harmonicMass 14 :=
  HarmonicMassRatioK13.harmonicMass_ratio_k13
theorem harmonicMass_ratio_k14 :
    Q'.ofNat 1776 * harmonicMass 14 ≤ Q'.ofNat 2601 * harmonicMass 15 :=
  HarmonicMassRatioK14.harmonicMass_ratio_k14
theorem harmonicMass_ratio_k15 :
    Q'.ofNat 2041 * harmonicMass 15 ≤ Q'.ofNat 2916 * harmonicMass 16 :=
  HarmonicMassRatioK15.harmonicMass_ratio_k15
theorem harmonicMass_ratio_k16 :
    Q'.ofNat 2324 * harmonicMass 16 ≤ Q'.ofNat 3249 * harmonicMass 17 :=
  HarmonicMassRatioK16.harmonicMass_ratio_k16

/-! ## Exact spacing stages -/

theorem harmonicMass_shell_spacing_stage_k13 :
    harmonicMass 13 * harmonicSpacing 14 ≤ harmonicShell 13 * harmonicSpacing 13 := by
  exact shell_spacing_stage_of_ratio 13
    (Q'.ofNat 1529) (Q'.ofNat 2304) (Q'.ofNat 4096)
    (Q'.ofNat 5625) (Q'.ofNat 6400) (Q'.ofNat 1440000)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k13
theorem harmonicMass_shell_spacing_stage_k14 :
    harmonicMass 14 * harmonicSpacing 15 ≤ harmonicShell 14 * harmonicSpacing 14 := by
  exact shell_spacing_stage_of_ratio 14
    (Q'.ofNat 1776) (Q'.ofNat 2601) (Q'.ofNat 4624)
    (Q'.ofNat 6400) (Q'.ofNat 7225) (Q'.ofNat 1849600)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k14
theorem harmonicMass_shell_spacing_stage_k15 :
    harmonicMass 15 * harmonicSpacing 16 ≤ harmonicShell 15 * harmonicSpacing 15 := by
  exact shell_spacing_stage_of_ratio 15
    (Q'.ofNat 2041) (Q'.ofNat 2916) (Q'.ofNat 5184)
    (Q'.ofNat 7225) (Q'.ofNat 8100) (Q'.ofNat 2340900)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k15
theorem harmonicMass_shell_spacing_stage_k16 :
    harmonicMass 16 * harmonicSpacing 17 ≤ harmonicShell 16 * harmonicSpacing 16 := by
  exact shell_spacing_stage_of_ratio 16
    (Q'.ofNat 2324) (Q'.ofNat 3249) (Q'.ofNat 5776)
    (Q'.ofNat 8100) (Q'.ofNat 9025) (Q'.ofNat 2924100)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k16

/-! ## Schur and operator prefix -/

theorem harmonicSchur_spacing_k13 :
    harmonicSchurAll 13 * harmonicSpacing 14 ≤ harmonicMass 14 * harmonicSpacing 13 :=
  harmonicSchur_spacing_of_stage 13 harmonicMass_shell_spacing_stage_k13
theorem harmonicSchur_spacing_k14 :
    harmonicSchurAll 14 * harmonicSpacing 15 ≤ harmonicMass 15 * harmonicSpacing 14 :=
  harmonicSchur_spacing_of_stage 14 harmonicMass_shell_spacing_stage_k14
theorem harmonicSchur_spacing_k15 :
    harmonicSchurAll 15 * harmonicSpacing 16 ≤ harmonicMass 16 * harmonicSpacing 15 :=
  harmonicSchur_spacing_of_stage 15 harmonicMass_shell_spacing_stage_k15
theorem harmonicSchur_spacing_k16 :
    harmonicSchurAll 16 * harmonicSpacing 17 ≤ harmonicMass 17 * harmonicSpacing 16 :=
  harmonicSchur_spacing_of_stage 16 harmonicMass_shell_spacing_stage_k16

theorem harmonicSchur_spacing_initial_seventeen {k : Nat} (hk : k ≤ 16) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk12 : k ≤ 12
  · exact harmonicSchur_spacing_initial_thirteen hk12
  · have cases : k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact harmonicSchur_spacing_k13
    · exact harmonicSchur_spacing_k14
    · exact harmonicSchur_spacing_k15
    · exact harmonicSchur_spacing_k16

theorem harmonic_operator_spacing_k13 :
    harmonicHead 13 * harmonicSpacing 14 ≤
      (harmonicErosionAll 13 + harmonicMass 14) * harmonicSpacing 13 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 13)
    (harmonicErosionAll_nonneg 13) (Q'.le_of_lt (harmonicSpacing_pos 14))
    (harmonicSpacing_contracts 13) (harmonicCoupling_size_all 13)
    harmonicSchur_spacing_k13
theorem harmonic_operator_spacing_k14 :
    harmonicHead 14 * harmonicSpacing 15 ≤
      (harmonicErosionAll 14 + harmonicMass 15) * harmonicSpacing 14 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 14)
    (harmonicErosionAll_nonneg 14) (Q'.le_of_lt (harmonicSpacing_pos 15))
    (harmonicSpacing_contracts 14) (harmonicCoupling_size_all 14)
    harmonicSchur_spacing_k14
theorem harmonic_operator_spacing_k15 :
    harmonicHead 15 * harmonicSpacing 16 ≤
      (harmonicErosionAll 15 + harmonicMass 16) * harmonicSpacing 15 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 15)
    (harmonicErosionAll_nonneg 15) (Q'.le_of_lt (harmonicSpacing_pos 16))
    (harmonicSpacing_contracts 15) (harmonicCoupling_size_all 15)
    harmonicSchur_spacing_k15
theorem harmonic_operator_spacing_k16 :
    harmonicHead 16 * harmonicSpacing 17 ≤
      (harmonicErosionAll 16 + harmonicMass 17) * harmonicSpacing 16 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 16)
    (harmonicErosionAll_nonneg 16) (Q'.le_of_lt (harmonicSpacing_pos 17))
    (harmonicSpacing_contracts 16) (harmonicCoupling_size_all 16)
    harmonicSchur_spacing_k16

theorem harmonic_operator_spacing_initial_seventeen {k : Nat} (hk : k ≤ 16) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k) (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_seventeen hk)

end YMGap.Continuum.HarmonicSchurRotationK1316

#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicMass_ratio_k13
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicMass_ratio_k14
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicMass_ratio_k15
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicMass_ratio_k16
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicMass_shell_spacing_stage_k13
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicMass_shell_spacing_stage_k14
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicMass_shell_spacing_stage_k15
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicMass_shell_spacing_stage_k16
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicSchur_spacing_k13
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicSchur_spacing_k14
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicSchur_spacing_k15
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicSchur_spacing_k16
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonicSchur_spacing_initial_seventeen
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonic_operator_spacing_k13
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonic_operator_spacing_k14
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonic_operator_spacing_k15
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonic_operator_spacing_k16
#print axioms YMGap.Continuum.HarmonicSchurRotationK1316.harmonic_operator_spacing_initial_seventeen
