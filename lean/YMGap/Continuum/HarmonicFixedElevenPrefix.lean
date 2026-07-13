/- Fixed eleven-anchor PF2 prefix at harmonic scales 29 through 33. -/

import YMGap.Continuum.HarmonicFixedTenPrefix

namespace YMGap.Continuum.HarmonicFixedElevenPrefix

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFixedTenPrefix
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SevenAnchorWindowRetune
open YMGap.Continuum.ThreeAnchorWindowRetune

local infix:50 " ≈ " => Q'.eqv

private def twelveElevenths : Q' := Q'.mkPos 12 11 (by decide)

/-- Exact coefficient ratio `c₁₁/c₁₀=(12/11)w²³`. -/
def tailRatio11 (w : Q') : Q' := twelveElevenths * qpow w 23

private def ratio11P : Poly := monoP twelveElevenths 23

theorem coeffW_eleven_eq_tailRatio11_mul_ten (w : Q') :
    coeffW w 11 ≈ tailRatio11 w * coeffW w 10 := by
  have hc11 := hcoeff w 11
  have hq : tailRatio11 w ≈ eval ratio11P w := by
    unfold tailRatio11 ratio11P
    exact Q'.eqv_symm (eval_monoP twelveElevenths w 23)
  have hc10 := hcoeff w 10
  refine Q'.eqv_trans _ _ _ hc11 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 11) (pmul ratio11P (coeffPoly 10)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc10)

theorem adjacent_tail11_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) {a : Nat} (ha : 10 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio11 w * (coeffW w a * coeffW w a) := by
  by_cases h10 : a = 10
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 10) _ _
        (coeffW_eleven_eq_tailRatio11_mul_ten w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha11 : 10 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 10) (N := a) ha11
    have hr : coeffW w (a + 1) * coeffW w 10 ≤ coeffW w a * coeffW w 11 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc10p := FusionResidualBound.coeffW_pos hwp 10
    have hR : coeffW w 11 * (coeffW w a * coeffW w a) ≈
        coeffW w 10 * (tailRatio11 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (coeffW_eleven_eq_tailRatio11_mul_ten w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 10 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 10 * (tailRatio11 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc10p

theorem fixed_eleven_all_later_cutoffs {w R : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hR0 : (0 : Q') ≤ R)
    (hhead : adjCorr w 11 ≤ R * coordNormSq w 10)
    (hratio : tailRatio11 w ≤ R) (M : Nat) :
    adjCorr w (11 + M) ≤ R * coordNormSq w (11 + M) := by
  apply fixed_anchor_all_later_cutoffs 10 M hw0 hR0 hhead
  intro a ha
  exact Q'.le_trans' _ _ _ (adjacent_tail11_le hw0 hw1 hwp (by omega))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hratio
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 a) (coeffW_nonneg hw0 a)))

theorem fixed_eleven_checks_k29 :
    adjCorr (harmW 29) 11 ≤ retuneCube (harmW 29) * coordNormSq (harmW 29) 10 ∧
      tailRatio11 (harmW 29) ≤ retuneCube (harmW 29) := by constructor <;> decide
theorem fixed_eleven_checks_k30 :
    adjCorr (harmW 30) 11 ≤ retuneCube (harmW 30) * coordNormSq (harmW 30) 10 ∧
      tailRatio11 (harmW 30) ≤ retuneCube (harmW 30) := by constructor <;> decide
theorem fixed_eleven_checks_k31 :
    adjCorr (harmW 31) 11 ≤ retuneCube (harmW 31) * coordNormSq (harmW 31) 10 ∧
      tailRatio11 (harmW 31) ≤ retuneCube (harmW 31) := by constructor <;> decide
theorem fixed_eleven_checks_k32 :
    adjCorr (harmW 32) 11 ≤ retuneCube (harmW 32) * coordNormSq (harmW 32) 10 ∧
      tailRatio11 (harmW 32) ≤ retuneCube (harmW 32) := by constructor <;> decide
theorem fixed_eleven_checks_k33 :
    adjCorr (harmW 33) 11 ≤ retuneCube (harmW 33) * coordNormSq (harmW 33) 10 ∧
      tailRatio11 (harmW 33) ≤ retuneCube (harmW 33) := by constructor <;> decide

/-- Counterexample to the extrapolated four-scale endpoint `4a-11`: for
`a=11` that endpoint is 33, but the head still holds there. -/
theorem four_scale_endpoint_law_a11_refuted :
    adjCorr (harmW 33) 11 ≤ retuneCube (harmW 33) * coordNormSq (harmW 33) 10 :=
  fixed_eleven_checks_k33.1

theorem fixed_eleven_head_k34_fails :
    ¬ adjCorr (harmW 34) 11 ≤
      retuneCube (harmW 34) * coordNormSq (harmW 34) 10 := by decide

private theorem retuneCube_nonneg (w : Q') (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ retuneCube w := by
  unfold retuneCube retuneBase
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)) 3

theorem harmonic_retune_cutoff_k29 :
    adjCorr (harmW 29) (Ncut 29) ≤ retuneCube (harmW 29) * coordNormSq (harmW 29) (Ncut 29) := by
  simpa [Ncut] using fixed_eleven_all_later_cutoffs
    (harmW_nonneg 29) (harmW_le_one 29) (harmW_pos 29)
    (retuneCube_nonneg _ (harmW_nonneg 29)) fixed_eleven_checks_k29.1 fixed_eleven_checks_k29.2 950
theorem harmonic_retune_cutoff_k30 :
    adjCorr (harmW 30) (Ncut 30) ≤ retuneCube (harmW 30) * coordNormSq (harmW 30) (Ncut 30) := by
  simpa [Ncut] using fixed_eleven_all_later_cutoffs
    (harmW_nonneg 30) (harmW_le_one 30) (harmW_pos 30)
    (retuneCube_nonneg _ (harmW_nonneg 30)) fixed_eleven_checks_k30.1 fixed_eleven_checks_k30.2 1013
theorem harmonic_retune_cutoff_k31 :
    adjCorr (harmW 31) (Ncut 31) ≤ retuneCube (harmW 31) * coordNormSq (harmW 31) (Ncut 31) := by
  simpa [Ncut] using fixed_eleven_all_later_cutoffs
    (harmW_nonneg 31) (harmW_le_one 31) (harmW_pos 31)
    (retuneCube_nonneg _ (harmW_nonneg 31)) fixed_eleven_checks_k31.1 fixed_eleven_checks_k31.2 1078
theorem harmonic_retune_cutoff_k32 :
    adjCorr (harmW 32) (Ncut 32) ≤ retuneCube (harmW 32) * coordNormSq (harmW 32) (Ncut 32) := by
  simpa [Ncut] using fixed_eleven_all_later_cutoffs
    (harmW_nonneg 32) (harmW_le_one 32) (harmW_pos 32)
    (retuneCube_nonneg _ (harmW_nonneg 32)) fixed_eleven_checks_k32.1 fixed_eleven_checks_k32.2 1145
theorem harmonic_retune_cutoff_k33 :
    adjCorr (harmW 33) (Ncut 33) ≤ retuneCube (harmW 33) * coordNormSq (harmW 33) (Ncut 33) := by
  simpa [Ncut] using fixed_eleven_all_later_cutoffs
    (harmW_nonneg 33) (harmW_le_one 33) (harmW_pos 33)
    (retuneCube_nonneg _ (harmW_nonneg 33)) fixed_eleven_checks_k33.1 fixed_eleven_checks_k33.2 1214

private theorem harmonic_lamPW_le_retune_of_cutoff (k : Nat)
    (hcorr : adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k)) :
    lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k) := by
  have heq : lamPW (harmW k) (Ncut k) 1 ≈
      Q'.divPos (adjCorr (harmW k) (Ncut k))
        (coordNormSq (harmW k) (Ncut k))
        (coordNormSq_pos (harmW_nonneg k) (Ncut k)) :=
    Q'.eqv_trans _ _ _
      (lamPW_eq_vacNorm_p2 (harmW_nonneg k) (harmW_le_one k) (Ncut k) 0)
      (vacNorm_fundamental_eq_ratio (harmW_nonneg k) (harmW_le_one k) (Ncut k))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.divPos_le_of_le_mul _ _ _ hcorr)

theorem harmonic_lamPW_le_retune_k29 :
    lamPW (harmW 29) (Ncut 29) 1 ≤ retuneCube (harmW 29) :=
  harmonic_lamPW_le_retune_of_cutoff 29 harmonic_retune_cutoff_k29
theorem harmonic_lamPW_le_retune_k30 :
    lamPW (harmW 30) (Ncut 30) 1 ≤ retuneCube (harmW 30) :=
  harmonic_lamPW_le_retune_of_cutoff 30 harmonic_retune_cutoff_k30
theorem harmonic_lamPW_le_retune_k31 :
    lamPW (harmW 31) (Ncut 31) 1 ≤ retuneCube (harmW 31) :=
  harmonic_lamPW_le_retune_of_cutoff 31 harmonic_retune_cutoff_k31
theorem harmonic_lamPW_le_retune_k32 :
    lamPW (harmW 32) (Ncut 32) 1 ≤ retuneCube (harmW 32) :=
  harmonic_lamPW_le_retune_of_cutoff 32 harmonic_retune_cutoff_k32
theorem harmonic_lamPW_le_retune_k33 :
    lamPW (harmW 33) (Ncut 33) 1 ≤ retuneCube (harmW 33) :=
  harmonic_lamPW_le_retune_of_cutoff 33 harmonic_retune_cutoff_k33

private theorem harmonic_mass_floor_of_lamPW (k : Nat)
    (h : lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k)) :
    (1 : Q') - retuneCube (harmW k) ≤ harmonicMass k := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

theorem harmonicMass_k29_eleven_floor :
    (1 : Q') - retuneCube (harmW 29) ≤ harmonicMass 29 :=
  harmonic_mass_floor_of_lamPW 29 harmonic_lamPW_le_retune_k29
theorem harmonicMass_k30_eleven_floor :
    (1 : Q') - retuneCube (harmW 30) ≤ harmonicMass 30 :=
  harmonic_mass_floor_of_lamPW 30 harmonic_lamPW_le_retune_k30
theorem harmonicMass_k31_eleven_floor :
    (1 : Q') - retuneCube (harmW 31) ≤ harmonicMass 31 :=
  harmonic_mass_floor_of_lamPW 31 harmonic_lamPW_le_retune_k31
theorem harmonicMass_k32_eleven_floor :
    (1 : Q') - retuneCube (harmW 32) ≤ harmonicMass 32 :=
  harmonic_mass_floor_of_lamPW 32 harmonic_lamPW_le_retune_k32
theorem harmonicMass_k33_eleven_floor :
    (1 : Q') - retuneCube (harmW 33) ≤ harmonicMass 33 :=
  harmonic_mass_floor_of_lamPW 33 harmonic_lamPW_le_retune_k33

end YMGap.Continuum.HarmonicFixedElevenPrefix

#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.coeffW_eleven_eq_tailRatio11_mul_ten
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.adjacent_tail11_le
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.fixed_eleven_all_later_cutoffs
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.fixed_eleven_checks_k29
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.fixed_eleven_checks_k30
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.fixed_eleven_checks_k31
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.fixed_eleven_checks_k32
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.fixed_eleven_checks_k33
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.four_scale_endpoint_law_a11_refuted
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.fixed_eleven_head_k34_fails
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_retune_cutoff_k29
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_retune_cutoff_k30
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_retune_cutoff_k31
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_retune_cutoff_k32
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_retune_cutoff_k33
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_lamPW_le_retune_k29
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_lamPW_le_retune_k30
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_lamPW_le_retune_k31
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_lamPW_le_retune_k32
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonic_lamPW_le_retune_k33
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonicMass_k29_eleven_floor
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonicMass_k30_eleven_floor
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonicMass_k31_eleven_floor
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonicMass_k32_eleven_floor
#print axioms YMGap.Continuum.HarmonicFixedElevenPrefix.harmonicMass_k33_eleven_floor
