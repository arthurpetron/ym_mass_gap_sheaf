/-
Staged Schur/operator closure for harmonic scales eight and nine.

The expensive facts are cached only as division-free D/A determinant
comparisons.  Existing quotient transport turns them into mass ratios, and
small exact integer scalings turn those ratios into the shell/spacing stages.
-/

import YMGap.Continuum.FiveAnchorWindowRetune

namespace YMGap.Continuum.HarmonicSchurRotationK89

set_option maxHeartbeats 3200000
set_option maxRecDepth 70000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiveAnchorWindowRetune
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicSchurRotationIdentity
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

/-! ## Division-free closed checks -/

theorem harmonicMass_DA_cross_k8 :
    (Q'.ofNat 564 * (harmonicD 8 - harmonicA 8)) * harmonicD 9 ≤
      (Q'.ofNat 1089 * (harmonicD 9 - harmonicA 9)) * harmonicD 8 := by
  decide

theorem harmonicMass_DA_cross_k9 :
    (Q'.ofNat 721 * (harmonicD 9 - harmonicA 9)) * harmonicD 10 ≤
      (Q'.ofNat 1296 * (harmonicD 10 - harmonicA 10)) * harmonicD 9 := by
  decide

theorem harmonicMass_ratio_k8 :
    Q'.ofNat 564 * harmonicMass 8 ≤ Q'.ofNat 1089 * harmonicMass 9 :=
  harmonicMass_ratio_of_DA_cross 8 (Q'.ofNat 564) (Q'.ofNat 1089)
    harmonicMass_DA_cross_k8

theorem harmonicMass_ratio_k9 :
    Q'.ofNat 721 * harmonicMass 9 ≤ Q'.ofNat 1296 * harmonicMass 10 :=
  harmonicMass_ratio_of_DA_cross 9 (Q'.ofNat 721) (Q'.ofNat 1296)
    harmonicMass_DA_cross_k9

/-! ## Exact ratio-to-spacing transport -/

private theorem harmonicMass_shell_spacing_stage_k8_of_ratio
    (hratio : Q'.ofNat 564 * harmonicMass 8 ≤
      Q'.ofNat 1089 * harmonicMass 9) :
    harmonicMass 8 * harmonicSpacing 9 ≤
      harmonicShell 8 * harmonicSpacing 8 := by
  have hadd := Q'.add_le_add_left
    (Q'.ofNat 1936 * harmonicMass 8) _ _ hratio
  have hsum : Q'.ofNat 2500 * harmonicMass 8 ≤
      Q'.ofNat 1936 * harmonicMass 8 + Q'.ofNat 1089 * harmonicMass 9 := by
    have hleft : Q'.ofNat 1936 * harmonicMass 8 +
        Q'.ofNat 564 * harmonicMass 8 ≈ Q'.ofNat 2500 * harmonicMass 8 := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 1936) (Q'.ofNat 564)
          (harmonicMass 8))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hadd
  let C := Q'.ofNat 302500
  have hleft : (harmonicMass 8 * harmonicSpacing 9) * C ≈
      Q'.ofNat 2500 * harmonicMass 8 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicMass 8) (harmonicSpacing 9) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicMass 8) _ _
        (by decide : harmonicSpacing 9 * C ≈ Q'.ofNat 2500)) ?_
    exact Q'.mul_comm_eqv _ _
  have hright : (harmonicShell 8 * harmonicSpacing 8) * C ≈
      Q'.ofNat 1936 * harmonicMass 8 + Q'.ofNat 1089 * harmonicMass 9 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicShell 8) (harmonicSpacing 8) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicShell 8) _ _
        (by decide : harmonicSpacing 8 * C ≈ Q'.ofNat 3025)) ?_
    unfold harmonicShell
    exact rotated_shell_scale_eqv _ _ _ _ _ (by decide) (by decide)
  have hmul : (harmonicMass 8 * harmonicSpacing 9) * C ≤
      (harmonicShell 8 * harmonicSpacing 8) * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hright))
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide : (0 : Q') < C) hmul

private theorem harmonicMass_shell_spacing_stage_k9_of_ratio
    (hratio : Q'.ofNat 721 * harmonicMass 9 ≤
      Q'.ofNat 1296 * harmonicMass 10) :
    harmonicMass 9 * harmonicSpacing 10 ≤
      harmonicShell 9 * harmonicSpacing 9 := by
  have hadd := Q'.add_le_add_left
    (Q'.ofNat 2304 * harmonicMass 9) _ _ hratio
  have hsum : Q'.ofNat 3025 * harmonicMass 9 ≤
      Q'.ofNat 2304 * harmonicMass 9 + Q'.ofNat 1296 * harmonicMass 10 := by
    have hleft : Q'.ofNat 2304 * harmonicMass 9 +
        Q'.ofNat 721 * harmonicMass 9 ≈ Q'.ofNat 3025 * harmonicMass 9 := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 2304) (Q'.ofNat 721)
          (harmonicMass 9))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hadd
  let C := Q'.ofNat 435600
  have hleft : (harmonicMass 9 * harmonicSpacing 10) * C ≈
      Q'.ofNat 3025 * harmonicMass 9 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicMass 9) (harmonicSpacing 10) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicMass 9) _ _
        (by decide : harmonicSpacing 10 * C ≈ Q'.ofNat 3025)) ?_
    exact Q'.mul_comm_eqv _ _
  have hright : (harmonicShell 9 * harmonicSpacing 9) * C ≈
      Q'.ofNat 2304 * harmonicMass 9 + Q'.ofNat 1296 * harmonicMass 10 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicShell 9) (harmonicSpacing 9) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicShell 9) _ _
        (by decide : harmonicSpacing 9 * C ≈ Q'.ofNat 3600)) ?_
    unfold harmonicShell
    exact rotated_shell_scale_eqv _ _ _ _ _ (by decide) (by decide)
  have hmul : (harmonicMass 9 * harmonicSpacing 10) * C ≤
      (harmonicShell 9 * harmonicSpacing 9) * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hright))
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide : (0 : Q') < C) hmul

theorem harmonicMass_shell_spacing_stage_k8 :
    harmonicMass 8 * harmonicSpacing 9 ≤ harmonicShell 8 * harmonicSpacing 8 :=
  harmonicMass_shell_spacing_stage_k8_of_ratio harmonicMass_ratio_k8

theorem harmonicMass_shell_spacing_stage_k9 :
    harmonicMass 9 * harmonicSpacing 10 ≤ harmonicShell 9 * harmonicSpacing 9 :=
  harmonicMass_shell_spacing_stage_k9_of_ratio harmonicMass_ratio_k9

/-! ## Schur and operator prefix -/

theorem harmonicSchur_spacing_k8 :
    harmonicSchurAll 8 * harmonicSpacing 9 ≤
      harmonicMass 9 * harmonicSpacing 8 :=
  harmonicSchur_spacing_of_stage 8 harmonicMass_shell_spacing_stage_k8

theorem harmonicSchur_spacing_k9 :
    harmonicSchurAll 9 * harmonicSpacing 10 ≤
      harmonicMass 10 * harmonicSpacing 9 :=
  harmonicSchur_spacing_of_stage 9 harmonicMass_shell_spacing_stage_k9

theorem harmonicSchur_spacing_initial_ten {k : Nat} (hk : k ≤ 9) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk7 : k ≤ 7
  · exact harmonicSchur_spacing_initial_eight hk7
  · have cases : k = 8 ∨ k = 9 := by omega
    rcases cases with rfl | rfl
    · exact harmonicSchur_spacing_k8
    · exact harmonicSchur_spacing_k9

theorem harmonic_operator_spacing_k8 :
    harmonicHead 8 * harmonicSpacing 9 ≤
      (harmonicErosionAll 8 + harmonicMass 9) * harmonicSpacing 8 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 8)
    (harmonicErosionAll_nonneg 8)
    (Q'.le_of_lt (harmonicSpacing_pos 9))
    (harmonicSpacing_contracts 8)
    (harmonicCoupling_size_all 8)
    harmonicSchur_spacing_k8

theorem harmonic_operator_spacing_k9 :
    harmonicHead 9 * harmonicSpacing 10 ≤
      (harmonicErosionAll 9 + harmonicMass 10) * harmonicSpacing 9 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 9)
    (harmonicErosionAll_nonneg 9)
    (Q'.le_of_lt (harmonicSpacing_pos 10))
    (harmonicSpacing_contracts 9)
    (harmonicCoupling_size_all 9)
    harmonicSchur_spacing_k9

theorem harmonic_operator_spacing_initial_ten {k : Nat} (hk : k ≤ 9) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k)
    (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_ten hk)

end YMGap.Continuum.HarmonicSchurRotationK89

#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicMass_DA_cross_k8
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicMass_DA_cross_k9
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicMass_ratio_k8
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicMass_ratio_k9
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicMass_shell_spacing_stage_k8
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicMass_shell_spacing_stage_k9
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicSchur_spacing_k8
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicSchur_spacing_k9
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonicSchur_spacing_initial_ten
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonic_operator_spacing_k8
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonic_operator_spacing_k9
#print axioms YMGap.Continuum.HarmonicSchurRotationK89.harmonic_operator_spacing_initial_ten
