/-
Staged Schur/operator closure for harmonic scales ten through twelve.

Each closed check is a division-free cross determinant in the exact
Dirichlet numerator/normalizer pair.  A generic exact scaling lemma converts
the resulting mass ratio into the rotated shell/spacing comparison.
-/

import YMGap.Continuum.SixAnchorWindowRetune
import YMGap.Continuum.HarmonicSchurRotationK89

namespace YMGap.Continuum.HarmonicSchurRotationK101112

set_option maxHeartbeats 8000000
set_option maxRecDepth 140000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicSchurRotationIdentity
open YMGap.Continuum.HarmonicSchurRotationK89
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

/-- Generic exact normalization transport used by the three new scales. -/
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

/-! ## Division-free determinant checks and mass ratios -/

theorem harmonicMass_DA_cross_k10 :
    (Q'.ofNat 896 * (harmonicD 10 - harmonicA 10)) * harmonicD 11 ≤
      (Q'.ofNat 1521 * (harmonicD 11 - harmonicA 11)) * harmonicD 10 := by
  decide

theorem harmonicMass_DA_cross_k11 :
    (Q'.ofNat 1089 * (harmonicD 11 - harmonicA 11)) * harmonicD 12 ≤
      (Q'.ofNat 1764 * (harmonicD 12 - harmonicA 12)) * harmonicD 11 := by
  decide

theorem harmonicMass_DA_cross_k12 :
    (Q'.ofNat 1300 * (harmonicD 12 - harmonicA 12)) * harmonicD 13 ≤
      (Q'.ofNat 2025 * (harmonicD 13 - harmonicA 13)) * harmonicD 12 := by
  decide

theorem harmonicMass_ratio_k10 :
    Q'.ofNat 896 * harmonicMass 10 ≤ Q'.ofNat 1521 * harmonicMass 11 :=
  harmonicMass_ratio_of_DA_cross 10 (Q'.ofNat 896) (Q'.ofNat 1521)
    harmonicMass_DA_cross_k10

theorem harmonicMass_ratio_k11 :
    Q'.ofNat 1089 * harmonicMass 11 ≤ Q'.ofNat 1764 * harmonicMass 12 :=
  harmonicMass_ratio_of_DA_cross 11 (Q'.ofNat 1089) (Q'.ofNat 1764)
    harmonicMass_DA_cross_k11

theorem harmonicMass_ratio_k12 :
    Q'.ofNat 1300 * harmonicMass 12 ≤ Q'.ofNat 2025 * harmonicMass 13 :=
  harmonicMass_ratio_of_DA_cross 12 (Q'.ofNat 1300) (Q'.ofNat 2025)
    harmonicMass_DA_cross_k12

/-! ## Exact shell/spacing stages -/

theorem harmonicMass_shell_spacing_stage_k10 :
    harmonicMass 10 * harmonicSpacing 11 ≤
      harmonicShell 10 * harmonicSpacing 10 := by
  exact shell_spacing_stage_of_ratio 10
    (Q'.ofNat 896) (Q'.ofNat 1521) (Q'.ofNat 2704)
    (Q'.ofNat 3600) (Q'.ofNat 4225) (Q'.ofNat 608400)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k10

theorem harmonicMass_shell_spacing_stage_k11 :
    harmonicMass 11 * harmonicSpacing 12 ≤
      harmonicShell 11 * harmonicSpacing 11 := by
  exact shell_spacing_stage_of_ratio 11
    (Q'.ofNat 1089) (Q'.ofNat 1764) (Q'.ofNat 3136)
    (Q'.ofNat 4225) (Q'.ofNat 4900) (Q'.ofNat 828100)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k11

theorem harmonicMass_shell_spacing_stage_k12 :
    harmonicMass 12 * harmonicSpacing 13 ≤
      harmonicShell 12 * harmonicSpacing 12 := by
  exact shell_spacing_stage_of_ratio 12
    (Q'.ofNat 1300) (Q'.ofNat 2025) (Q'.ofNat 3600)
    (Q'.ofNat 4900) (Q'.ofNat 5625) (Q'.ofNat 1102500)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    harmonicMass_ratio_k12

/-! ## Schur and operator initial-thirteen prefix -/

theorem harmonicSchur_spacing_k10 :
    harmonicSchurAll 10 * harmonicSpacing 11 ≤
      harmonicMass 11 * harmonicSpacing 10 :=
  harmonicSchur_spacing_of_stage 10 harmonicMass_shell_spacing_stage_k10

theorem harmonicSchur_spacing_k11 :
    harmonicSchurAll 11 * harmonicSpacing 12 ≤
      harmonicMass 12 * harmonicSpacing 11 :=
  harmonicSchur_spacing_of_stage 11 harmonicMass_shell_spacing_stage_k11

theorem harmonicSchur_spacing_k12 :
    harmonicSchurAll 12 * harmonicSpacing 13 ≤
      harmonicMass 13 * harmonicSpacing 12 :=
  harmonicSchur_spacing_of_stage 12 harmonicMass_shell_spacing_stage_k12

theorem harmonicSchur_spacing_initial_thirteen {k : Nat} (hk : k ≤ 12) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk9 : k ≤ 9
  · exact harmonicSchur_spacing_initial_ten hk9
  · have cases : k = 10 ∨ k = 11 ∨ k = 12 := by omega
    rcases cases with rfl | rfl | rfl
    · exact harmonicSchur_spacing_k10
    · exact harmonicSchur_spacing_k11
    · exact harmonicSchur_spacing_k12

theorem harmonic_operator_spacing_k10 :
    harmonicHead 10 * harmonicSpacing 11 ≤
      (harmonicErosionAll 10 + harmonicMass 11) * harmonicSpacing 10 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 10)
    (harmonicErosionAll_nonneg 10) (Q'.le_of_lt (harmonicSpacing_pos 11))
    (harmonicSpacing_contracts 10) (harmonicCoupling_size_all 10)
    harmonicSchur_spacing_k10

theorem harmonic_operator_spacing_k11 :
    harmonicHead 11 * harmonicSpacing 12 ≤
      (harmonicErosionAll 11 + harmonicMass 12) * harmonicSpacing 11 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 11)
    (harmonicErosionAll_nonneg 11) (Q'.le_of_lt (harmonicSpacing_pos 12))
    (harmonicSpacing_contracts 11) (harmonicCoupling_size_all 11)
    harmonicSchur_spacing_k11

theorem harmonic_operator_spacing_k12 :
    harmonicHead 12 * harmonicSpacing 13 ≤
      (harmonicErosionAll 12 + harmonicMass 13) * harmonicSpacing 12 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 12)
    (harmonicErosionAll_nonneg 12) (Q'.le_of_lt (harmonicSpacing_pos 13))
    (harmonicSpacing_contracts 12) (harmonicCoupling_size_all 12)
    harmonicSchur_spacing_k12

theorem harmonic_operator_spacing_initial_thirteen {k : Nat} (hk : k ≤ 12) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k) (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_thirteen hk)

end YMGap.Continuum.HarmonicSchurRotationK101112

#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_DA_cross_k10
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_DA_cross_k11
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_DA_cross_k12
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_ratio_k10
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_ratio_k11
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_ratio_k12
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_shell_spacing_stage_k10
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_shell_spacing_stage_k11
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicMass_shell_spacing_stage_k12
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicSchur_spacing_k10
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicSchur_spacing_k11
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicSchur_spacing_k12
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonicSchur_spacing_initial_thirteen
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonic_operator_spacing_k10
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonic_operator_spacing_k11
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonic_operator_spacing_k12
#print axioms YMGap.Continuum.HarmonicSchurRotationK101112.harmonic_operator_spacing_initial_thirteen
