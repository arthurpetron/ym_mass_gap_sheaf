/-
Staged Schur/spacing closure for the widened harmonic prefix.

The 3-4-5 rotation preserves the determinant.  Therefore its scalar Schur
complement times the positive shell entry is exactly the product of the two
unrotated masses.  This removes the large reciprocal expression from the
closed `k=6,7` comparisons: only `mass_k * spacing_(k+1) <= shell_k * spacing_k`
is decided at each scale.
-/

import YMGap.Continuum.FourAnchorWindowRetune

namespace YMGap.Continuum.HarmonicSchurRotationIdentity

set_option maxHeartbeats 2200000
set_option maxRecDepth 50000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FusedOffDiagonalCompression
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.FourAnchorWindowRetune

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-- The rational 3-4-5 rotation preserves the two-by-two determinant. -/
theorem rotated_mass_det (a b : Q') :
    rot00 a b * rot11 a b + -(rot01 a b * rot01 a b) ≈ a * b :=
  rotated_det a b

/-- Multiplying a scalar Schur complement by its shell denominator recovers
the determinant, without any division remaining. -/
theorem schurMass_mul_shell (head shell coupling : Q')
    (hshell : (0 : Q') < shell) :
    schurMass head shell coupling hshell * shell ≈
      head * shell + -(coupling * coupling) := by
  unfold schurMass shellLoss
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv head
    (-(Q'.divPos (coupling * coupling) shell hshell)) shell) ?_
  refine Q'.add_eqv_congr_left (head * shell) _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.neg_mul_eqv (Q'.divPos (coupling * coupling) shell hshell) shell) ?_
  exact Q'.neg_eqv_congr _ _
    (Q'.divPos_mul_eqv (coupling * coupling) shell hshell)

/-- Exact determinant identity for the actual harmonic Schur mass. -/
theorem harmonicSchur_mul_shell (k : Nat) :
    harmonicSchurAll k * harmonicShell k ≈
      harmonicMass k * harmonicMass (k + 1) := by
  refine Q'.eqv_trans _ _ _
    (schurMass_mul_shell (harmonicHead k) (harmonicShell k)
      (harmonicCoupling k) (harmonicShell_pos_all k)) ?_
  unfold harmonicHead harmonicShell harmonicCoupling
  exact rotated_mass_det (harmonicMass k) (harmonicMass (k + 1))

/-- A division-free mass/shell spacing comparison implies the original Schur
spacing law. -/
theorem harmonicSchur_spacing_of_stage (k : Nat)
    (hstage : harmonicMass k * harmonicSpacing (k + 1) ≤
      harmonicShell k * harmonicSpacing k) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (harmonicMass (k + 1))
    hstage (Q'.le_of_lt (harmonicMass_pos_all (k + 1)))
  have hleft :
      (harmonicSchurAll k * harmonicSpacing (k + 1)) * harmonicShell k ≈
        harmonicMass (k + 1) *
          (harmonicMass k * harmonicSpacing (k + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicSchurAll k)
        (harmonicSpacing (k + 1)) (harmonicShell k)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicSchurAll k) _ _
        (Q'.mul_comm_eqv (harmonicSpacing (k + 1)) (harmonicShell k))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (harmonicSchurAll k)
        (harmonicShell k) (harmonicSpacing (k + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (harmonicSpacing (k + 1))
        (harmonicSchur_mul_shell k)) ?_
    ring_qeqv
  have hright :
      (harmonicMass (k + 1) * harmonicSpacing k) * harmonicShell k ≈
        harmonicMass (k + 1) *
          (harmonicShell k * harmonicSpacing k) := by
    ring_qeqv
  have hmul :
      (harmonicSchurAll k * harmonicSpacing (k + 1)) * harmonicShell k ≤
        (harmonicMass (k + 1) * harmonicSpacing k) * harmonicShell k :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.eqv_symm hright)))
  exact BakryEmery.le_of_mul_le_mul_right_pos (harmonicShell_pos_all k) hmul

private theorem scalar_mul_divPos_eqv (c p d : Q') (hd : (0 : Q') < d) :
    c * Q'.divPos p d hd ≈ Q'.divPos (c * p) d hd := by
  unfold Q'.divPos
  exact Q'.eqv_symm (Q'.mul_assoc_eqv c p (Q'.recipPos d hd))

/-- Cross-multiplying the exact Dirichlet quotients removes both normalizer
divisions from a comparison of consecutive harmonic masses. -/
theorem harmonicMass_ratio_of_DA_cross (k : Nat) (p q : Q')
    (hcross : (p * (harmonicD k - harmonicA k)) * harmonicD (k + 1) ≤
      (q * (harmonicD (k + 1) - harmonicA (k + 1))) * harmonicD k) :
    p * harmonicMass k ≤ q * harmonicMass (k + 1) := by
  have hquot := FusionMarginMono.divPos_le_divPos_of_cross
    (p * (harmonicD k - harmonicA k)) (harmonicD k)
    (q * (harmonicD (k + 1) - harmonicA (k + 1))) (harmonicD (k + 1))
    (harmonicD_pos k) (harmonicD_pos (k + 1)) hcross
  have hleft : p * harmonicMass k ≈
      Q'.divPos (p * (harmonicD k - harmonicA k))
        (harmonicD k) (harmonicD_pos k) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left p _ _ (harmonicMass_eq_DA k)) ?_
    exact scalar_mul_divPos_eqv p _ _ _
  have hright : q * harmonicMass (k + 1) ≈
      Q'.divPos (q * (harmonicD (k + 1) - harmonicA (k + 1)))
        (harmonicD (k + 1)) (harmonicD_pos (k + 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left q _ _ (harmonicMass_eq_DA (k + 1))) ?_
    exact scalar_mul_divPos_eqv q _ _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hquot (Q'.ge_of_eqv hright))

/-- Small, division-free closed comparison underlying the `k=6` stage. -/
theorem harmonicMass_DA_cross_k6 :
    (Q'.ofNat 304 * (harmonicD 6 - harmonicA 6)) * harmonicD 7 ≤
      (Q'.ofNat 729 * (harmonicD 7 - harmonicA 7)) * harmonicD 6 := by
  decide

/-- Small, division-free closed comparison underlying the `k=7` stage. -/
theorem harmonicMass_DA_cross_k7 :
    (Q'.ofNat 17 * (harmonicD 7 - harmonicA 7)) * harmonicD 8 ≤
      (Q'.ofNat 36 * (harmonicD 8 - harmonicA 8)) * harmonicD 7 := by
  decide

theorem harmonicMass_ratio_k6 :
    Q'.ofNat 304 * harmonicMass 6 ≤ Q'.ofNat 729 * harmonicMass 7 :=
  harmonicMass_ratio_of_DA_cross 6 (Q'.ofNat 304) (Q'.ofNat 729)
    harmonicMass_DA_cross_k6

theorem harmonicMass_ratio_k7 :
    Q'.ofNat 17 * harmonicMass 7 ≤ Q'.ofNat 36 * harmonicMass 8 :=
  harmonicMass_ratio_of_DA_cross 7 (Q'.ofNat 17) (Q'.ofNat 36)
    harmonicMass_DA_cross_k7

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

private theorem harmonicMass_shell_spacing_stage_k6_of_ratio
    (hratio : Q'.ofNat 304 * harmonicMass 6 ≤
      Q'.ofNat 729 * harmonicMass 7) :
    harmonicMass 6 * harmonicSpacing 7 ≤
      harmonicShell 6 * harmonicSpacing 6 := by
  have hadd := Q'.add_le_add_left
    (Q'.ofNat 1296 * harmonicMass 6) _ _ hratio
  have hsum : Q'.ofNat 1600 * harmonicMass 6 ≤
      Q'.ofNat 1296 * harmonicMass 6 + Q'.ofNat 729 * harmonicMass 7 := by
    have hleft : Q'.ofNat 1296 * harmonicMass 6 +
        Q'.ofNat 304 * harmonicMass 6 ≈ Q'.ofNat 1600 * harmonicMass 6 := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 1296) (Q'.ofNat 304)
          (harmonicMass 6))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hadd
  let C := Q'.ofNat 129600
  have hleft : (harmonicMass 6 * harmonicSpacing 7) * C ≈
      Q'.ofNat 1600 * harmonicMass 6 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicMass 6) (harmonicSpacing 7) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicMass 6) _ _
        (by decide : harmonicSpacing 7 * C ≈ Q'.ofNat 1600)) ?_
    exact Q'.mul_comm_eqv _ _
  have hright : (harmonicShell 6 * harmonicSpacing 6) * C ≈
      Q'.ofNat 1296 * harmonicMass 6 + Q'.ofNat 729 * harmonicMass 7 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicShell 6) (harmonicSpacing 6) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicShell 6) _ _
        (by decide : harmonicSpacing 6 * C ≈ Q'.ofNat 2025)) ?_
    unfold harmonicShell
    exact rotated_shell_scale_eqv _ _ _ _ _ (by decide) (by decide)
  have hmul : (harmonicMass 6 * harmonicSpacing 7) * C ≤
      (harmonicShell 6 * harmonicSpacing 6) * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hright))
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide : (0 : Q') < C) hmul

private theorem harmonicMass_shell_spacing_stage_k7_of_ratio
    (hratio : Q'.ofNat 17 * harmonicMass 7 ≤
      Q'.ofNat 36 * harmonicMass 8) :
    harmonicMass 7 * harmonicSpacing 8 ≤
      harmonicShell 7 * harmonicSpacing 7 := by
  have hadd := Q'.add_le_add_left
    (Q'.ofNat 64 * harmonicMass 7) _ _ hratio
  have hsum : Q'.ofNat 81 * harmonicMass 7 ≤
      Q'.ofNat 64 * harmonicMass 7 + Q'.ofNat 36 * harmonicMass 8 := by
    have hleft : Q'.ofNat 64 * harmonicMass 7 +
        Q'.ofNat 17 * harmonicMass 7 ≈ Q'.ofNat 81 * harmonicMass 7 := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 64) (Q'.ofNat 17)
          (harmonicMass 7))) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hadd
  let C := Q'.ofNat 8100
  have hleft : (harmonicMass 7 * harmonicSpacing 8) * C ≈
      Q'.ofNat 81 * harmonicMass 7 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicMass 7) (harmonicSpacing 8) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicMass 7) _ _
        (by decide : harmonicSpacing 8 * C ≈ Q'.ofNat 81)) ?_
    exact Q'.mul_comm_eqv _ _
  have hright : (harmonicShell 7 * harmonicSpacing 7) * C ≈
      Q'.ofNat 64 * harmonicMass 7 + Q'.ofNat 36 * harmonicMass 8 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (harmonicShell 7) (harmonicSpacing 7) C) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (harmonicShell 7) _ _
        (by decide : harmonicSpacing 7 * C ≈ Q'.ofNat 100)) ?_
    unfold harmonicShell
    exact rotated_shell_scale_eqv _ _ _ _ _ (by decide) (by decide)
  have hmul : (harmonicMass 7 * harmonicSpacing 8) * C ≤
      (harmonicShell 7 * harmonicSpacing 7) * C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hright))
  exact BakryEmery.le_of_mul_le_mul_right_pos (by decide : (0 : Q') < C) hmul

/-- Cached division-free comparison at `k=6`. -/
theorem harmonicMass_shell_spacing_stage_k6 :
    harmonicMass 6 * harmonicSpacing 7 ≤
      harmonicShell 6 * harmonicSpacing 6 :=
  harmonicMass_shell_spacing_stage_k6_of_ratio harmonicMass_ratio_k6

/-- Cached division-free comparison at `k=7`. -/
theorem harmonicMass_shell_spacing_stage_k7 :
    harmonicMass 7 * harmonicSpacing 8 ≤
      harmonicShell 7 * harmonicSpacing 7 :=
  harmonicMass_shell_spacing_stage_k7_of_ratio harmonicMass_ratio_k7

theorem harmonicSchur_spacing_k6 :
    harmonicSchurAll 6 * harmonicSpacing 7 ≤
      harmonicMass 7 * harmonicSpacing 6 :=
  harmonicSchur_spacing_of_stage 6 harmonicMass_shell_spacing_stage_k6

theorem harmonicSchur_spacing_k7 :
    harmonicSchurAll 7 * harmonicSpacing 8 ≤
      harmonicMass 8 * harmonicSpacing 7 :=
  harmonicSchur_spacing_of_stage 7 harmonicMass_shell_spacing_stage_k7

theorem harmonicSchur_spacing_initial_eight {k : Nat} (hk : k ≤ 7) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  by_cases hk5 : k ≤ 5
  · exact harmonicSchur_spacing_initial_six hk5
  · have cases : k = 6 ∨ k = 7 := by omega
    rcases cases with rfl | rfl
    · exact harmonicSchur_spacing_k6
    · exact harmonicSchur_spacing_k7

theorem harmonic_operator_spacing_k6 :
    harmonicHead 6 * harmonicSpacing 7 ≤
      (harmonicErosionAll 6 + harmonicMass 7) * harmonicSpacing 6 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 6)
    (harmonicErosionAll_nonneg 6)
    (Q'.le_of_lt (harmonicSpacing_pos 7))
    (harmonicSpacing_contracts 6)
    (harmonicCoupling_size_all 6)
    harmonicSchur_spacing_k6

theorem harmonic_operator_spacing_k7 :
    harmonicHead 7 * harmonicSpacing 8 ≤
      (harmonicErosionAll 7 + harmonicMass 8) * harmonicSpacing 7 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 7)
    (harmonicErosionAll_nonneg 7)
    (Q'.le_of_lt (harmonicSpacing_pos 8))
    (harmonicSpacing_contracts 7)
    (harmonicCoupling_size_all 7)
    harmonicSchur_spacing_k7

theorem harmonic_operator_spacing_initial_eight {k : Nat} (hk : k ≤ 7) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k)
    (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_eight hk)

end YMGap.Continuum.HarmonicSchurRotationIdentity

#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.rotated_mass_det
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.schurMass_mul_shell
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicSchur_mul_shell
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicSchur_spacing_of_stage
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicMass_ratio_of_DA_cross
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicMass_DA_cross_k6
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicMass_DA_cross_k7
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicMass_ratio_k6
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicMass_ratio_k7
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicMass_shell_spacing_stage_k6
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicMass_shell_spacing_stage_k7
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicSchur_spacing_k6
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicSchur_spacing_k7
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonicSchur_spacing_initial_eight
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonic_operator_spacing_k6
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonic_operator_spacing_k7
#print axioms YMGap.Continuum.HarmonicSchurRotationIdentity.harmonic_operator_spacing_initial_eight
