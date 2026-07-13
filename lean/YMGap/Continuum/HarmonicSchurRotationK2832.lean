/- Staged Schur/operator closure for harmonic scales twenty-eight through thirty-two. -/

import YMGap.Continuum.HarmonicSchurRotationK2427
import YMGap.Continuum.HarmonicMassRatiosK2832

namespace YMGap.Continuum.HarmonicSchurRotationK2832

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicMassRatiosK2832
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK1719
open YMGap.Continuum.HarmonicSchurRotationK2427
open YMGap.Continuum.HarmonicWeightDriftFence

theorem harmonicMass_shell_spacing_stage_k28 :
    harmonicMass 28 * harmonicSpacing 29 ≤ harmonicShell 28 * harmonicSpacing 28 := by
  exact shell_spacing_stage_of_ratio 28
    (Q'.ofNat 7124) (Q'.ofNat 8649) (Q'.ofNat 15376)
    (Q'.ofNat 22500) (Q'.ofNat 24025) (Q'.ofNat 21622500)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k28

theorem harmonicMass_shell_spacing_stage_k29 :
    harmonicMass 29 * harmonicSpacing 30 ≤ harmonicShell 29 * harmonicSpacing 29 := by
  exact shell_spacing_stage_of_ratio 29
    (Q'.ofNat 7641) (Q'.ofNat 9216) (Q'.ofNat 16384)
    (Q'.ofNat 24025) (Q'.ofNat 25600) (Q'.ofNat 24601600)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k29

theorem harmonicMass_shell_spacing_stage_k30 :
    harmonicMass 30 * harmonicSpacing 31 ≤ harmonicShell 30 * harmonicSpacing 30 := by
  exact shell_spacing_stage_of_ratio 30
    (Q'.ofNat 8176) (Q'.ofNat 9801) (Q'.ofNat 17424)
    (Q'.ofNat 25600) (Q'.ofNat 27225) (Q'.ofNat 27878400)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k30

theorem harmonicMass_shell_spacing_stage_k31 :
    harmonicMass 31 * harmonicSpacing 32 ≤ harmonicShell 31 * harmonicSpacing 31 := by
  exact shell_spacing_stage_of_ratio 31
    (Q'.ofNat 8729) (Q'.ofNat 10404) (Q'.ofNat 18496)
    (Q'.ofNat 27225) (Q'.ofNat 28900) (Q'.ofNat 31472100)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k31

theorem harmonicMass_shell_spacing_stage_k32 :
    harmonicMass 32 * harmonicSpacing 33 ≤ harmonicShell 32 * harmonicSpacing 32 := by
  exact shell_spacing_stage_of_ratio 32
    (Q'.ofNat 9300) (Q'.ofNat 11025) (Q'.ofNat 19600)
    (Q'.ofNat 28900) (Q'.ofNat 30625) (Q'.ofNat 35402500)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k32

theorem harmonicSchur_spacing_k28 :
    harmonicSchurAll 28 * harmonicSpacing 29 ≤ harmonicMass 29 * harmonicSpacing 28 :=
  harmonicSchur_spacing_of_stage 28 harmonicMass_shell_spacing_stage_k28
theorem harmonicSchur_spacing_k29 :
    harmonicSchurAll 29 * harmonicSpacing 30 ≤ harmonicMass 30 * harmonicSpacing 29 :=
  harmonicSchur_spacing_of_stage 29 harmonicMass_shell_spacing_stage_k29
theorem harmonicSchur_spacing_k30 :
    harmonicSchurAll 30 * harmonicSpacing 31 ≤ harmonicMass 31 * harmonicSpacing 30 :=
  harmonicSchur_spacing_of_stage 30 harmonicMass_shell_spacing_stage_k30
theorem harmonicSchur_spacing_k31 :
    harmonicSchurAll 31 * harmonicSpacing 32 ≤ harmonicMass 32 * harmonicSpacing 31 :=
  harmonicSchur_spacing_of_stage 31 harmonicMass_shell_spacing_stage_k31
theorem harmonicSchur_spacing_k32 :
    harmonicSchurAll 32 * harmonicSpacing 33 ≤ harmonicMass 33 * harmonicSpacing 32 :=
  harmonicSchur_spacing_of_stage 32 harmonicMass_shell_spacing_stage_k32

theorem harmonicSchur_spacing_initial_thirty_three {k : Nat} (hk : k ≤ 32) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk27 : k ≤ 27
  · exact harmonicSchur_spacing_initial_twenty_eight hk27
  · have cases : k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 ∨ k = 32 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · exact harmonicSchur_spacing_k28
    · exact harmonicSchur_spacing_k29
    · exact harmonicSchur_spacing_k30
    · exact harmonicSchur_spacing_k31
    · exact harmonicSchur_spacing_k32

theorem harmonic_operator_spacing_k28 :
    harmonicHead 28 * harmonicSpacing 29 ≤
      (harmonicErosionAll 28 + harmonicMass 29) * harmonicSpacing 28 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 28)
    (harmonicErosionAll_nonneg 28) (Q'.le_of_lt (harmonicSpacing_pos 29))
    (harmonicSpacing_contracts 28) (harmonicCoupling_size_all 28)
    harmonicSchur_spacing_k28
theorem harmonic_operator_spacing_k29 :
    harmonicHead 29 * harmonicSpacing 30 ≤
      (harmonicErosionAll 29 + harmonicMass 30) * harmonicSpacing 29 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 29)
    (harmonicErosionAll_nonneg 29) (Q'.le_of_lt (harmonicSpacing_pos 30))
    (harmonicSpacing_contracts 29) (harmonicCoupling_size_all 29)
    harmonicSchur_spacing_k29
theorem harmonic_operator_spacing_k30 :
    harmonicHead 30 * harmonicSpacing 31 ≤
      (harmonicErosionAll 30 + harmonicMass 31) * harmonicSpacing 30 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 30)
    (harmonicErosionAll_nonneg 30) (Q'.le_of_lt (harmonicSpacing_pos 31))
    (harmonicSpacing_contracts 30) (harmonicCoupling_size_all 30)
    harmonicSchur_spacing_k30
theorem harmonic_operator_spacing_k31 :
    harmonicHead 31 * harmonicSpacing 32 ≤
      (harmonicErosionAll 31 + harmonicMass 32) * harmonicSpacing 31 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 31)
    (harmonicErosionAll_nonneg 31) (Q'.le_of_lt (harmonicSpacing_pos 32))
    (harmonicSpacing_contracts 31) (harmonicCoupling_size_all 31)
    harmonicSchur_spacing_k31
theorem harmonic_operator_spacing_k32 :
    harmonicHead 32 * harmonicSpacing 33 ≤
      (harmonicErosionAll 32 + harmonicMass 33) * harmonicSpacing 32 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 32)
    (harmonicErosionAll_nonneg 32) (Q'.le_of_lt (harmonicSpacing_pos 33))
    (harmonicSpacing_contracts 32) (harmonicCoupling_size_all 32)
    harmonicSchur_spacing_k32

theorem harmonic_operator_spacing_initial_thirty_three {k : Nat} (hk : k ≤ 32) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k) (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_thirty_three hk)

end YMGap.Continuum.HarmonicSchurRotationK2832

#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicMass_shell_spacing_stage_k28
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicMass_shell_spacing_stage_k29
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicMass_shell_spacing_stage_k30
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicMass_shell_spacing_stage_k31
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicMass_shell_spacing_stage_k32
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicSchur_spacing_k28
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicSchur_spacing_k29
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicSchur_spacing_k30
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicSchur_spacing_k31
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicSchur_spacing_k32
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonicSchur_spacing_initial_thirty_three
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonic_operator_spacing_k28
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonic_operator_spacing_k29
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonic_operator_spacing_k30
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonic_operator_spacing_k31
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonic_operator_spacing_k32
#print axioms YMGap.Continuum.HarmonicSchurRotationK2832.harmonic_operator_spacing_initial_thirty_three
