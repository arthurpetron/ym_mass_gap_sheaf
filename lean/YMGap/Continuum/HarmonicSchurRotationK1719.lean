/- Staged Schur/operator closure for harmonic scales seventeen through nineteen. -/

import YMGap.Continuum.HarmonicSchurRotationK1316
import YMGap.Continuum.HarmonicMassRatiosK1719

namespace YMGap.Continuum.HarmonicSchurRotationK1719

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicMassRatiosK1719
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK1316
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

/-! ## Exact spacing stages -/

theorem harmonicMass_shell_spacing_stage_k17 :
    harmonicMass 17 * harmonicSpacing 18 ≤ harmonicShell 17 * harmonicSpacing 17 := by
  exact shell_spacing_stage_of_ratio 17
    (Q'.ofNat 2625) (Q'.ofNat 3600) (Q'.ofNat 6400)
    (Q'.ofNat 9025) (Q'.ofNat 10000) (Q'.ofNat 3610000)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k17

theorem harmonicMass_shell_spacing_stage_k18 :
    harmonicMass 18 * harmonicSpacing 19 ≤ harmonicShell 18 * harmonicSpacing 18 := by
  exact shell_spacing_stage_of_ratio 18
    (Q'.ofNat 2944) (Q'.ofNat 3969) (Q'.ofNat 7056)
    (Q'.ofNat 10000) (Q'.ofNat 11025) (Q'.ofNat 4410000)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k18

theorem harmonicMass_shell_spacing_stage_k19 :
    harmonicMass 19 * harmonicSpacing 20 ≤ harmonicShell 19 * harmonicSpacing 19 := by
  exact shell_spacing_stage_of_ratio 19
    (Q'.ofNat 3281) (Q'.ofNat 4356) (Q'.ofNat 7744)
    (Q'.ofNat 11025) (Q'.ofNat 12100) (Q'.ofNat 5336100)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k19

/-! ## Schur and operator prefix through scale nineteen -/

theorem harmonicSchur_spacing_k17 :
    harmonicSchurAll 17 * harmonicSpacing 18 ≤ harmonicMass 18 * harmonicSpacing 17 :=
  harmonicSchur_spacing_of_stage 17 harmonicMass_shell_spacing_stage_k17

theorem harmonicSchur_spacing_k18 :
    harmonicSchurAll 18 * harmonicSpacing 19 ≤ harmonicMass 19 * harmonicSpacing 18 :=
  harmonicSchur_spacing_of_stage 18 harmonicMass_shell_spacing_stage_k18

theorem harmonicSchur_spacing_k19 :
    harmonicSchurAll 19 * harmonicSpacing 20 ≤ harmonicMass 20 * harmonicSpacing 19 :=
  harmonicSchur_spacing_of_stage 19 harmonicMass_shell_spacing_stage_k19

theorem harmonicSchur_spacing_initial_twenty {k : Nat} (hk : k ≤ 19) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk16 : k ≤ 16
  · exact harmonicSchur_spacing_initial_seventeen hk16
  · have cases : k = 17 ∨ k = 18 ∨ k = 19 := by omega
    rcases cases with rfl | rfl | rfl
    · exact harmonicSchur_spacing_k17
    · exact harmonicSchur_spacing_k18
    · exact harmonicSchur_spacing_k19

theorem harmonic_operator_spacing_k17 :
    harmonicHead 17 * harmonicSpacing 18 ≤
      (harmonicErosionAll 17 + harmonicMass 18) * harmonicSpacing 17 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 17)
    (harmonicErosionAll_nonneg 17) (Q'.le_of_lt (harmonicSpacing_pos 18))
    (harmonicSpacing_contracts 17) (harmonicCoupling_size_all 17)
    harmonicSchur_spacing_k17

theorem harmonic_operator_spacing_k18 :
    harmonicHead 18 * harmonicSpacing 19 ≤
      (harmonicErosionAll 18 + harmonicMass 19) * harmonicSpacing 18 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 18)
    (harmonicErosionAll_nonneg 18) (Q'.le_of_lt (harmonicSpacing_pos 19))
    (harmonicSpacing_contracts 18) (harmonicCoupling_size_all 18)
    harmonicSchur_spacing_k18

theorem harmonic_operator_spacing_k19 :
    harmonicHead 19 * harmonicSpacing 20 ≤
      (harmonicErosionAll 19 + harmonicMass 20) * harmonicSpacing 19 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 19)
    (harmonicErosionAll_nonneg 19) (Q'.le_of_lt (harmonicSpacing_pos 20))
    (harmonicSpacing_contracts 19) (harmonicCoupling_size_all 19)
    harmonicSchur_spacing_k19

theorem harmonic_operator_spacing_initial_twenty {k : Nat} (hk : k ≤ 19) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k) (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_twenty hk)

end YMGap.Continuum.HarmonicSchurRotationK1719

#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonicMass_shell_spacing_stage_k17
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonicMass_shell_spacing_stage_k18
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonicMass_shell_spacing_stage_k19
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonicSchur_spacing_k17
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonicSchur_spacing_k18
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonicSchur_spacing_k19
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonicSchur_spacing_initial_twenty
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonic_operator_spacing_k17
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonic_operator_spacing_k18
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonic_operator_spacing_k19
#print axioms YMGap.Continuum.HarmonicSchurRotationK1719.harmonic_operator_spacing_initial_twenty
