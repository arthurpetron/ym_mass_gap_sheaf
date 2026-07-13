/- Staged Schur/operator closure for harmonic scales twenty through twenty-three. -/

import YMGap.Continuum.HarmonicSchurRotationK1719
import YMGap.Continuum.HarmonicMassRatiosK2023

namespace YMGap.Continuum.HarmonicSchurRotationK2023

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicMassRatiosK2023
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK1719
open YMGap.Continuum.HarmonicWeightDriftFence

/-! ## Exact spacing stages -/

theorem harmonicMass_shell_spacing_stage_k20 :
    harmonicMass 20 * harmonicSpacing 21 ≤ harmonicShell 20 * harmonicSpacing 20 := by
  exact shell_spacing_stage_of_ratio 20
    (Q'.ofNat 3636) (Q'.ofNat 4761) (Q'.ofNat 8464)
    (Q'.ofNat 12100) (Q'.ofNat 13225) (Q'.ofNat 6400900)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k20

theorem harmonicMass_shell_spacing_stage_k21 :
    harmonicMass 21 * harmonicSpacing 22 ≤ harmonicShell 21 * harmonicSpacing 21 := by
  exact shell_spacing_stage_of_ratio 21
    (Q'.ofNat 4009) (Q'.ofNat 5184) (Q'.ofNat 9216)
    (Q'.ofNat 13225) (Q'.ofNat 14400) (Q'.ofNat 7617600)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k21

theorem harmonicMass_shell_spacing_stage_k22 :
    harmonicMass 22 * harmonicSpacing 23 ≤ harmonicShell 22 * harmonicSpacing 22 := by
  exact shell_spacing_stage_of_ratio 22
    (Q'.ofNat 4400) (Q'.ofNat 5625) (Q'.ofNat 10000)
    (Q'.ofNat 14400) (Q'.ofNat 15625) (Q'.ofNat 9000000)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k22

theorem harmonicMass_shell_spacing_stage_k23 :
    harmonicMass 23 * harmonicSpacing 24 ≤ harmonicShell 23 * harmonicSpacing 23 := by
  exact shell_spacing_stage_of_ratio 23
    (Q'.ofNat 4809) (Q'.ofNat 6084) (Q'.ofNat 10816)
    (Q'.ofNat 15625) (Q'.ofNat 16900) (Q'.ofNat 10562500)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k23

/-! ## Schur and operator prefix through scale twenty-three -/

theorem harmonicSchur_spacing_k20 :
    harmonicSchurAll 20 * harmonicSpacing 21 ≤ harmonicMass 21 * harmonicSpacing 20 :=
  harmonicSchur_spacing_of_stage 20 harmonicMass_shell_spacing_stage_k20

theorem harmonicSchur_spacing_k21 :
    harmonicSchurAll 21 * harmonicSpacing 22 ≤ harmonicMass 22 * harmonicSpacing 21 :=
  harmonicSchur_spacing_of_stage 21 harmonicMass_shell_spacing_stage_k21

theorem harmonicSchur_spacing_k22 :
    harmonicSchurAll 22 * harmonicSpacing 23 ≤ harmonicMass 23 * harmonicSpacing 22 :=
  harmonicSchur_spacing_of_stage 22 harmonicMass_shell_spacing_stage_k22

theorem harmonicSchur_spacing_k23 :
    harmonicSchurAll 23 * harmonicSpacing 24 ≤ harmonicMass 24 * harmonicSpacing 23 :=
  harmonicSchur_spacing_of_stage 23 harmonicMass_shell_spacing_stage_k23

theorem harmonicSchur_spacing_initial_twenty_four {k : Nat} (hk : k ≤ 23) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk19 : k ≤ 19
  · exact harmonicSchur_spacing_initial_twenty hk19
  · have cases : k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact harmonicSchur_spacing_k20
    · exact harmonicSchur_spacing_k21
    · exact harmonicSchur_spacing_k22
    · exact harmonicSchur_spacing_k23

theorem harmonic_operator_spacing_k20 :
    harmonicHead 20 * harmonicSpacing 21 ≤
      (harmonicErosionAll 20 + harmonicMass 21) * harmonicSpacing 20 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 20)
    (harmonicErosionAll_nonneg 20) (Q'.le_of_lt (harmonicSpacing_pos 21))
    (harmonicSpacing_contracts 20) (harmonicCoupling_size_all 20)
    harmonicSchur_spacing_k20

theorem harmonic_operator_spacing_k21 :
    harmonicHead 21 * harmonicSpacing 22 ≤
      (harmonicErosionAll 21 + harmonicMass 22) * harmonicSpacing 21 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 21)
    (harmonicErosionAll_nonneg 21) (Q'.le_of_lt (harmonicSpacing_pos 22))
    (harmonicSpacing_contracts 21) (harmonicCoupling_size_all 21)
    harmonicSchur_spacing_k21

theorem harmonic_operator_spacing_k22 :
    harmonicHead 22 * harmonicSpacing 23 ≤
      (harmonicErosionAll 22 + harmonicMass 23) * harmonicSpacing 22 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 22)
    (harmonicErosionAll_nonneg 22) (Q'.le_of_lt (harmonicSpacing_pos 23))
    (harmonicSpacing_contracts 22) (harmonicCoupling_size_all 22)
    harmonicSchur_spacing_k22

theorem harmonic_operator_spacing_k23 :
    harmonicHead 23 * harmonicSpacing 24 ≤
      (harmonicErosionAll 23 + harmonicMass 24) * harmonicSpacing 23 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 23)
    (harmonicErosionAll_nonneg 23) (Q'.le_of_lt (harmonicSpacing_pos 24))
    (harmonicSpacing_contracts 23) (harmonicCoupling_size_all 23)
    harmonicSchur_spacing_k23

theorem harmonic_operator_spacing_initial_twenty_four {k : Nat} (hk : k ≤ 23) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k) (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_twenty_four hk)

end YMGap.Continuum.HarmonicSchurRotationK2023

#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicMass_shell_spacing_stage_k20
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicMass_shell_spacing_stage_k21
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicMass_shell_spacing_stage_k22
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicMass_shell_spacing_stage_k23
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicSchur_spacing_k20
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicSchur_spacing_k21
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicSchur_spacing_k22
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicSchur_spacing_k23
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonicSchur_spacing_initial_twenty_four
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonic_operator_spacing_k20
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonic_operator_spacing_k21
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonic_operator_spacing_k22
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonic_operator_spacing_k23
#print axioms YMGap.Continuum.HarmonicSchurRotationK2023.harmonic_operator_spacing_initial_twenty_four
