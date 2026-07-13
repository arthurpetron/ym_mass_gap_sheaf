/- Staged Schur/operator closure for harmonic scales thirty-three through thirty-seven. -/

import YMGap.Continuum.HarmonicSchurRotationK2832
import YMGap.Continuum.HarmonicMassRatiosK3337

namespace YMGap.Continuum.HarmonicSchurRotationK3337

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicMassRatiosK3337
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK1719
open YMGap.Continuum.HarmonicSchurRotationK2832
open YMGap.Continuum.HarmonicWeightDriftFence

theorem harmonicMass_shell_spacing_stage_k33 :
    harmonicMass 33 * harmonicSpacing 34 ≤ harmonicShell 33 * harmonicSpacing 33 := by
  exact shell_spacing_stage_of_ratio 33
    (Q'.ofNat 9889) (Q'.ofNat 11664) (Q'.ofNat 20736)
    (Q'.ofNat 30625) (Q'.ofNat 32400) (Q'.ofNat 39690000)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k33
theorem harmonicMass_shell_spacing_stage_k34 :
    harmonicMass 34 * harmonicSpacing 35 ≤ harmonicShell 34 * harmonicSpacing 34 := by
  exact shell_spacing_stage_of_ratio 34
    (Q'.ofNat 10496) (Q'.ofNat 12321) (Q'.ofNat 21904)
    (Q'.ofNat 32400) (Q'.ofNat 34225) (Q'.ofNat 44355600)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k34
theorem harmonicMass_shell_spacing_stage_k35 :
    harmonicMass 35 * harmonicSpacing 36 ≤ harmonicShell 35 * harmonicSpacing 35 := by
  exact shell_spacing_stage_of_ratio 35
    (Q'.ofNat 11121) (Q'.ofNat 12996) (Q'.ofNat 23104)
    (Q'.ofNat 34225) (Q'.ofNat 36100) (Q'.ofNat 49420900)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k35
theorem harmonicMass_shell_spacing_stage_k36 :
    harmonicMass 36 * harmonicSpacing 37 ≤ harmonicShell 36 * harmonicSpacing 36 := by
  exact shell_spacing_stage_of_ratio 36
    (Q'.ofNat 11764) (Q'.ofNat 13689) (Q'.ofNat 24336)
    (Q'.ofNat 36100) (Q'.ofNat 38025) (Q'.ofNat 54908100)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k36
theorem harmonicMass_shell_spacing_stage_k37 :
    harmonicMass 37 * harmonicSpacing 38 ≤ harmonicShell 37 * harmonicSpacing 37 := by
  exact shell_spacing_stage_of_ratio 37
    (Q'.ofNat 12425) (Q'.ofNat 14400) (Q'.ofNat 25600)
    (Q'.ofNat 38025) (Q'.ofNat 40000) (Q'.ofNat 60840000)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k37

theorem harmonicSchur_spacing_k33 : harmonicSchurAll 33 * harmonicSpacing 34 ≤
    harmonicMass 34 * harmonicSpacing 33 :=
  harmonicSchur_spacing_of_stage 33 harmonicMass_shell_spacing_stage_k33
theorem harmonicSchur_spacing_k34 : harmonicSchurAll 34 * harmonicSpacing 35 ≤
    harmonicMass 35 * harmonicSpacing 34 :=
  harmonicSchur_spacing_of_stage 34 harmonicMass_shell_spacing_stage_k34
theorem harmonicSchur_spacing_k35 : harmonicSchurAll 35 * harmonicSpacing 36 ≤
    harmonicMass 36 * harmonicSpacing 35 :=
  harmonicSchur_spacing_of_stage 35 harmonicMass_shell_spacing_stage_k35
theorem harmonicSchur_spacing_k36 : harmonicSchurAll 36 * harmonicSpacing 37 ≤
    harmonicMass 37 * harmonicSpacing 36 :=
  harmonicSchur_spacing_of_stage 36 harmonicMass_shell_spacing_stage_k36
theorem harmonicSchur_spacing_k37 : harmonicSchurAll 37 * harmonicSpacing 38 ≤
    harmonicMass 38 * harmonicSpacing 37 :=
  harmonicSchur_spacing_of_stage 37 harmonicMass_shell_spacing_stage_k37

theorem harmonicSchur_spacing_initial_thirty_eight {k : Nat} (hk : k ≤ 37) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk32 : k ≤ 32
  · exact harmonicSchur_spacing_initial_thirty_three hk32
  · have cases : k = 33 ∨ k = 34 ∨ k = 35 ∨ k = 36 ∨ k = 37 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · exact harmonicSchur_spacing_k33
    · exact harmonicSchur_spacing_k34
    · exact harmonicSchur_spacing_k35
    · exact harmonicSchur_spacing_k36
    · exact harmonicSchur_spacing_k37

theorem harmonic_operator_spacing_k33 : harmonicHead 33 * harmonicSpacing 34 ≤
    (harmonicErosionAll 33 + harmonicMass 34) * harmonicSpacing 33 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 33) (harmonicErosionAll_nonneg 33)
    (Q'.le_of_lt (harmonicSpacing_pos 34)) (harmonicSpacing_contracts 33)
    (harmonicCoupling_size_all 33) harmonicSchur_spacing_k33
theorem harmonic_operator_spacing_k34 : harmonicHead 34 * harmonicSpacing 35 ≤
    (harmonicErosionAll 34 + harmonicMass 35) * harmonicSpacing 34 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 34) (harmonicErosionAll_nonneg 34)
    (Q'.le_of_lt (harmonicSpacing_pos 35)) (harmonicSpacing_contracts 34)
    (harmonicCoupling_size_all 34) harmonicSchur_spacing_k34
theorem harmonic_operator_spacing_k35 : harmonicHead 35 * harmonicSpacing 36 ≤
    (harmonicErosionAll 35 + harmonicMass 36) * harmonicSpacing 35 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 35) (harmonicErosionAll_nonneg 35)
    (Q'.le_of_lt (harmonicSpacing_pos 36)) (harmonicSpacing_contracts 35)
    (harmonicCoupling_size_all 35) harmonicSchur_spacing_k35
theorem harmonic_operator_spacing_k36 : harmonicHead 36 * harmonicSpacing 37 ≤
    (harmonicErosionAll 36 + harmonicMass 37) * harmonicSpacing 36 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 36) (harmonicErosionAll_nonneg 36)
    (Q'.le_of_lt (harmonicSpacing_pos 37)) (harmonicSpacing_contracts 36)
    (harmonicCoupling_size_all 36) harmonicSchur_spacing_k36
theorem harmonic_operator_spacing_k37 : harmonicHead 37 * harmonicSpacing 38 ≤
    (harmonicErosionAll 37 + harmonicMass 38) * harmonicSpacing 37 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 37) (harmonicErosionAll_nonneg 37)
    (Q'.le_of_lt (harmonicSpacing_pos 38)) (harmonicSpacing_contracts 37)
    (harmonicCoupling_size_all 37) harmonicSchur_spacing_k37

theorem harmonic_operator_spacing_initial_thirty_eight {k : Nat} (hk : k ≤ 37) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k) (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_thirty_eight hk)

end YMGap.Continuum.HarmonicSchurRotationK3337

#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicMass_shell_spacing_stage_k33
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicMass_shell_spacing_stage_k34
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicMass_shell_spacing_stage_k35
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicMass_shell_spacing_stage_k36
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicMass_shell_spacing_stage_k37
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicSchur_spacing_k33
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicSchur_spacing_k34
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicSchur_spacing_k35
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicSchur_spacing_k36
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicSchur_spacing_k37
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonicSchur_spacing_initial_thirty_eight
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonic_operator_spacing_k33
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonic_operator_spacing_k34
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonic_operator_spacing_k35
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonic_operator_spacing_k36
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonic_operator_spacing_k37
#print axioms YMGap.Continuum.HarmonicSchurRotationK3337.harmonic_operator_spacing_initial_thirty_eight
