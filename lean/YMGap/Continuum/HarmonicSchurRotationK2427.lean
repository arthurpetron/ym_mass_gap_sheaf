/- Staged Schur/operator closure for harmonic scales twenty-four through twenty-seven. -/

import YMGap.Continuum.HarmonicSchurRotationK2023
import YMGap.Continuum.HarmonicMassRatiosK2427

namespace YMGap.Continuum.HarmonicSchurRotationK2427

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicMassRatiosK2427
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK1719
open YMGap.Continuum.HarmonicSchurRotationK2023
open YMGap.Continuum.HarmonicWeightDriftFence

theorem harmonicMass_shell_spacing_stage_k24 :
    harmonicMass 24 * harmonicSpacing 25 ≤ harmonicShell 24 * harmonicSpacing 24 := by
  exact shell_spacing_stage_of_ratio 24
    (Q'.ofNat 5236) (Q'.ofNat 6561) (Q'.ofNat 11664)
    (Q'.ofNat 16900) (Q'.ofNat 18225) (Q'.ofNat 12320100)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k24

theorem harmonicMass_shell_spacing_stage_k25 :
    harmonicMass 25 * harmonicSpacing 26 ≤ harmonicShell 25 * harmonicSpacing 25 := by
  exact shell_spacing_stage_of_ratio 25
    (Q'.ofNat 5681) (Q'.ofNat 7056) (Q'.ofNat 12544)
    (Q'.ofNat 18225) (Q'.ofNat 19600) (Q'.ofNat 14288400)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k25

theorem harmonicMass_shell_spacing_stage_k26 :
    harmonicMass 26 * harmonicSpacing 27 ≤ harmonicShell 26 * harmonicSpacing 26 := by
  exact shell_spacing_stage_of_ratio 26
    (Q'.ofNat 6144) (Q'.ofNat 7569) (Q'.ofNat 13456)
    (Q'.ofNat 19600) (Q'.ofNat 21025) (Q'.ofNat 16483600)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k26

theorem harmonicMass_shell_spacing_stage_k27 :
    harmonicMass 27 * harmonicSpacing 28 ≤ harmonicShell 27 * harmonicSpacing 27 := by
  exact shell_spacing_stage_of_ratio 27
    (Q'.ofNat 6625) (Q'.ofNat 8100) (Q'.ofNat 14400)
    (Q'.ofNat 21025) (Q'.ofNat 22500) (Q'.ofNat 18922500)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k27

theorem harmonicSchur_spacing_k24 :
    harmonicSchurAll 24 * harmonicSpacing 25 ≤ harmonicMass 25 * harmonicSpacing 24 :=
  harmonicSchur_spacing_of_stage 24 harmonicMass_shell_spacing_stage_k24
theorem harmonicSchur_spacing_k25 :
    harmonicSchurAll 25 * harmonicSpacing 26 ≤ harmonicMass 26 * harmonicSpacing 25 :=
  harmonicSchur_spacing_of_stage 25 harmonicMass_shell_spacing_stage_k25
theorem harmonicSchur_spacing_k26 :
    harmonicSchurAll 26 * harmonicSpacing 27 ≤ harmonicMass 27 * harmonicSpacing 26 :=
  harmonicSchur_spacing_of_stage 26 harmonicMass_shell_spacing_stage_k26
theorem harmonicSchur_spacing_k27 :
    harmonicSchurAll 27 * harmonicSpacing 28 ≤ harmonicMass 28 * harmonicSpacing 27 :=
  harmonicSchur_spacing_of_stage 27 harmonicMass_shell_spacing_stage_k27

theorem harmonicSchur_spacing_initial_twenty_eight {k : Nat} (hk : k ≤ 27) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk23 : k ≤ 23
  · exact harmonicSchur_spacing_initial_twenty_four hk23
  · have cases : k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · exact harmonicSchur_spacing_k24
    · exact harmonicSchur_spacing_k25
    · exact harmonicSchur_spacing_k26
    · exact harmonicSchur_spacing_k27

theorem harmonic_operator_spacing_k24 :
    harmonicHead 24 * harmonicSpacing 25 ≤
      (harmonicErosionAll 24 + harmonicMass 25) * harmonicSpacing 24 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 24)
    (harmonicErosionAll_nonneg 24) (Q'.le_of_lt (harmonicSpacing_pos 25))
    (harmonicSpacing_contracts 24) (harmonicCoupling_size_all 24)
    harmonicSchur_spacing_k24
theorem harmonic_operator_spacing_k25 :
    harmonicHead 25 * harmonicSpacing 26 ≤
      (harmonicErosionAll 25 + harmonicMass 26) * harmonicSpacing 25 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 25)
    (harmonicErosionAll_nonneg 25) (Q'.le_of_lt (harmonicSpacing_pos 26))
    (harmonicSpacing_contracts 25) (harmonicCoupling_size_all 25)
    harmonicSchur_spacing_k25
theorem harmonic_operator_spacing_k26 :
    harmonicHead 26 * harmonicSpacing 27 ≤
      (harmonicErosionAll 26 + harmonicMass 27) * harmonicSpacing 26 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 26)
    (harmonicErosionAll_nonneg 26) (Q'.le_of_lt (harmonicSpacing_pos 27))
    (harmonicSpacing_contracts 26) (harmonicCoupling_size_all 26)
    harmonicSchur_spacing_k26
theorem harmonic_operator_spacing_k27 :
    harmonicHead 27 * harmonicSpacing 28 ≤
      (harmonicErosionAll 27 + harmonicMass 28) * harmonicSpacing 27 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 27)
    (harmonicErosionAll_nonneg 27) (Q'.le_of_lt (harmonicSpacing_pos 28))
    (harmonicSpacing_contracts 27) (harmonicCoupling_size_all 27)
    harmonicSchur_spacing_k27

theorem harmonic_operator_spacing_initial_twenty_eight {k : Nat} (hk : k ≤ 27) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k) (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_twenty_eight hk)

end YMGap.Continuum.HarmonicSchurRotationK2427

#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicMass_shell_spacing_stage_k24
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicMass_shell_spacing_stage_k25
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicMass_shell_spacing_stage_k26
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicMass_shell_spacing_stage_k27
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicSchur_spacing_k24
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicSchur_spacing_k25
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicSchur_spacing_k26
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicSchur_spacing_k27
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonicSchur_spacing_initial_twenty_eight
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonic_operator_spacing_k24
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonic_operator_spacing_k25
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonic_operator_spacing_k26
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonic_operator_spacing_k27
#print axioms YMGap.Continuum.HarmonicSchurRotationK2427.harmonic_operator_spacing_initial_twenty_eight
