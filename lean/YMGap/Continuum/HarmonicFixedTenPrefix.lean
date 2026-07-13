/- Fixed ten-anchor PF2 prefix at harmonic scales 25 through 28. -/

import YMGap.Continuum.HarmonicFixedNinePrefix

namespace YMGap.Continuum.HarmonicFixedTenPrefix

set_option maxHeartbeats 9000000
set_option maxRecDepth 220000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.SevenAnchorWindowRetune
open YMGap.Continuum.ThreeAnchorWindowRetune

local infix:50 " ≈ " => Q'.eqv

private def elevenTenths : Q' := Q'.mkPos 11 10 (by decide)

/-- Exact coefficient ratio `c₁₀/c₉=(11/10)w²¹`. -/
def tailRatio10 (w : Q') : Q' := elevenTenths * qpow w 21

private def ratio10P : Poly := monoP elevenTenths 21

theorem coeffW_ten_eq_tailRatio10_mul_nine (w : Q') :
    coeffW w 10 ≈ tailRatio10 w * coeffW w 9 := by
  have hc10 := hcoeff w 10
  have hq : tailRatio10 w ≈ eval ratio10P w := by
    unfold tailRatio10 ratio10P
    exact Q'.eqv_symm (eval_monoP elevenTenths w 21)
  have hc9 := hcoeff w 9
  refine Q'.eqv_trans _ _ _ hc10 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 10) (pmul ratio10P (coeffPoly 9)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc9)

theorem adjacent_tail10_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) {a : Nat} (ha : 9 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio10 w * (coeffW w a * coeffW w a) := by
  by_cases h9 : a = 9
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 9) _ _
        (coeffW_ten_eq_tailRatio10_mul_nine w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha10 : 9 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 9) (N := a) ha10
    have hr : coeffW w (a + 1) * coeffW w 9 ≤ coeffW w a * coeffW w 10 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc9p := FusionResidualBound.coeffW_pos hwp 9
    have hR : coeffW w 10 * (coeffW w a * coeffW w a) ≈
        coeffW w 9 * (tailRatio10 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (coeffW_ten_eq_tailRatio10_mul_nine w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 9 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 9 * (tailRatio10 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc9p

private def edgeTailFrom (b : Nat) (w : Q') (j : Nat) : Q' :=
  coeffW w (b + 1 + j) * coeffW w (b + 1 + j + 1)

private def squareTailFrom (b : Nat) (w : Q') (j : Nat) : Q' :=
  coeffW w (b + 1 + j) * coeffW w (b + 1 + j)

/-- Generic fixed-head assembler.  `b` is the last diagonal head index and
`b+1` is the number of head edges. -/
theorem fixed_anchor_all_later_cutoffs (b M : Nat) {w R : Q'}
    (hw0 : (0 : Q') ≤ w) (hR0 : (0 : Q') ≤ R)
    (hhead : adjCorr w (b + 1) ≤ R * coordNormSq w b)
    (htail : ∀ a, b + 1 ≤ a →
      coeffW w a * coeffW w (a + 1) ≤ R * (coeffW w a * coeffW w a)) :
    adjCorr w (b + 1 + M) ≤ R * coordNormSq w (b + 1 + M) := by
  have hterm : ∀ j, edgeTailFrom b w j ≤ R * squareTailFrom b w j := by
    intro j
    exact htail (b + 1 + j) (by omega)
  have hsum : fsum (edgeTailFrom b w) M ≤
      R * fsum (squareTailFrom b w) M := by
    have hs : fsum (edgeTailFrom b w) M ≤
        fsum (fun j => R * squareTailFrom b w j) M := by
      rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
      exact CharacterTail.finSum_le_termwise _ _ hterm M
    have hf : R * fsum (squareTailFrom b w) M ≈
        fsum (fun j => R * squareTailFrom b w j) M := by
      rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
      exact const_mul_finSum (squareTailFrom b w) R M
    exact Q'.le_trans' _ _ _ hs (Q'.ge_of_eqv hf)
  have hA : adjCorr w (b + 1 + M) ≈
      adjCorr w (b + 1) + fsum (edgeTailFrom b w) M := by
    unfold adjCorr edgeTailFrom
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW w a * coeffW w (a + 1)) (b + 1) M
  have hD : coordNormSq w (b + 1 + M) ≈
      coordNormSq w b + fsum (squareTailFrom b w) (M + 1) := by
    unfold coordNormSq squareTailFrom
    rw [show b + 1 + M + 1 = b + 1 + (M + 1) by omega]
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW w a * coeffW w a) (b + 1) (M + 1)
  have hsquare0 : ∀ j, (0 : Q') ≤ squareTailFrom b w j := by
    intro j
    unfold squareTailFrom
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg hw0 (b + 1 + j)) (coeffW_nonneg hw0 (b + 1 + j))
  have htailPrefix : fsum (squareTailFrom b w) M ≤
      fsum (squareTailFrom b w) (M + 1) :=
    AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
  have hprefix : coordNormSq w b + fsum (squareTailFrom b w) M ≤
      coordNormSq w (b + 1 + M) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left (coordNormSq w b) _ _ htailPrefix)
      (Q'.ge_of_eqv hD)
  have hpaid : adjCorr w (b + 1) + fsum (edgeTailFrom b w) M ≤
      R * coordNormSq w b + R * fsum (squareTailFrom b w) M :=
    AFRateCalibration.q_add_le_add hhead hsum
  have hcollect : R * coordNormSq w b + R * fsum (squareTailFrom b w) M ≈
      R * (coordNormSq w b + fsum (squareTailFrom b w) M) :=
    Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
    (Q'.le_trans' _ _ _ hpaid
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hR0)))

theorem fixed_ten_all_later_cutoffs {w R : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hR0 : (0 : Q') ≤ R)
    (hhead : adjCorr w 10 ≤ R * coordNormSq w 9)
    (hratio : tailRatio10 w ≤ R) (M : Nat) :
    adjCorr w (10 + M) ≤ R * coordNormSq w (10 + M) := by
  apply fixed_anchor_all_later_cutoffs 9 M hw0 hR0 hhead
  intro a ha
  exact Q'.le_trans' _ _ _ (adjacent_tail10_le hw0 hw1 hwp (by omega))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hratio
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 a) (coeffW_nonneg hw0 a)))

/-! ## Exact point checks and endpoint fence -/

theorem fixed_ten_checks_k25 :
    adjCorr (harmW 25) 10 ≤ retuneCube (harmW 25) * coordNormSq (harmW 25) 9 ∧
      tailRatio10 (harmW 25) ≤ retuneCube (harmW 25) := by
  constructor <;> decide

theorem fixed_ten_checks_k26 :
    adjCorr (harmW 26) 10 ≤ retuneCube (harmW 26) * coordNormSq (harmW 26) 9 ∧
      tailRatio10 (harmW 26) ≤ retuneCube (harmW 26) := by
  constructor <;> decide

theorem fixed_ten_checks_k27 :
    adjCorr (harmW 27) 10 ≤ retuneCube (harmW 27) * coordNormSq (harmW 27) 9 ∧
      tailRatio10 (harmW 27) ≤ retuneCube (harmW 27) := by
  constructor <;> decide

theorem fixed_ten_checks_k28 :
    adjCorr (harmW 28) 10 ≤ retuneCube (harmW 28) * coordNormSq (harmW 28) 9 ∧
      tailRatio10 (harmW 28) ≤ retuneCube (harmW 28) := by
  constructor <;> decide

theorem fixed_ten_head_k29_fails :
    ¬ adjCorr (harmW 29) 10 ≤
      retuneCube (harmW 29) * coordNormSq (harmW 29) 9 := by
  decide

private theorem retuneCube_nonneg (w : Q') (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ retuneCube w := by
  unfold retuneCube retuneBase
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)) 3

theorem harmonic_retune_cutoff_k25 :
    adjCorr (harmW 25) (Ncut 25) ≤
      retuneCube (harmW 25) * coordNormSq (harmW 25) (Ncut 25) := by
  simpa [Ncut] using fixed_ten_all_later_cutoffs
    (harmW_nonneg 25) (harmW_le_one 25) (harmW_pos 25)
    (retuneCube_nonneg _ (harmW_nonneg 25))
    fixed_ten_checks_k25.1 fixed_ten_checks_k25.2 719

theorem harmonic_retune_cutoff_k26 :
    adjCorr (harmW 26) (Ncut 26) ≤
      retuneCube (harmW 26) * coordNormSq (harmW 26) (Ncut 26) := by
  simpa [Ncut] using fixed_ten_all_later_cutoffs
    (harmW_nonneg 26) (harmW_le_one 26) (harmW_pos 26)
    (retuneCube_nonneg _ (harmW_nonneg 26))
    fixed_ten_checks_k26.1 fixed_ten_checks_k26.2 774

theorem harmonic_retune_cutoff_k27 :
    adjCorr (harmW 27) (Ncut 27) ≤
      retuneCube (harmW 27) * coordNormSq (harmW 27) (Ncut 27) := by
  simpa [Ncut] using fixed_ten_all_later_cutoffs
    (harmW_nonneg 27) (harmW_le_one 27) (harmW_pos 27)
    (retuneCube_nonneg _ (harmW_nonneg 27))
    fixed_ten_checks_k27.1 fixed_ten_checks_k27.2 831

theorem harmonic_retune_cutoff_k28 :
    adjCorr (harmW 28) (Ncut 28) ≤
      retuneCube (harmW 28) * coordNormSq (harmW 28) (Ncut 28) := by
  simpa [Ncut] using fixed_ten_all_later_cutoffs
    (harmW_nonneg 28) (harmW_le_one 28) (harmW_pos 28)
    (retuneCube_nonneg _ (harmW_nonneg 28))
    fixed_ten_checks_k28.1 fixed_ten_checks_k28.2 890

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
  have hratio : Q'.divPos (adjCorr (harmW k) (Ncut k))
        (coordNormSq (harmW k) (Ncut k))
        (coordNormSq_pos (harmW_nonneg k) (Ncut k)) ≤ retuneCube (harmW k) :=
    Q'.divPos_le_of_le_mul _ _ _ hcorr
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hratio

theorem harmonic_lamPW_le_retune_k25 :
    lamPW (harmW 25) (Ncut 25) 1 ≤ retuneCube (harmW 25) :=
  harmonic_lamPW_le_retune_of_cutoff 25 harmonic_retune_cutoff_k25
theorem harmonic_lamPW_le_retune_k26 :
    lamPW (harmW 26) (Ncut 26) 1 ≤ retuneCube (harmW 26) :=
  harmonic_lamPW_le_retune_of_cutoff 26 harmonic_retune_cutoff_k26
theorem harmonic_lamPW_le_retune_k27 :
    lamPW (harmW 27) (Ncut 27) 1 ≤ retuneCube (harmW 27) :=
  harmonic_lamPW_le_retune_of_cutoff 27 harmonic_retune_cutoff_k27
theorem harmonic_lamPW_le_retune_k28 :
    lamPW (harmW 28) (Ncut 28) 1 ≤ retuneCube (harmW 28) :=
  harmonic_lamPW_le_retune_of_cutoff 28 harmonic_retune_cutoff_k28

private theorem harmonic_mass_floor_of_lamPW (k : Nat)
    (h : lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k)) :
    (1 : Q') - retuneCube (harmW k) ≤ harmonicMass k := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

theorem harmonicMass_k25_ten_floor :
    (1 : Q') - retuneCube (harmW 25) ≤ harmonicMass 25 :=
  harmonic_mass_floor_of_lamPW 25 harmonic_lamPW_le_retune_k25
theorem harmonicMass_k26_ten_floor :
    (1 : Q') - retuneCube (harmW 26) ≤ harmonicMass 26 :=
  harmonic_mass_floor_of_lamPW 26 harmonic_lamPW_le_retune_k26
theorem harmonicMass_k27_ten_floor :
    (1 : Q') - retuneCube (harmW 27) ≤ harmonicMass 27 :=
  harmonic_mass_floor_of_lamPW 27 harmonic_lamPW_le_retune_k27
theorem harmonicMass_k28_ten_floor :
    (1 : Q') - retuneCube (harmW 28) ≤ harmonicMass 28 :=
  harmonic_mass_floor_of_lamPW 28 harmonic_lamPW_le_retune_k28

end YMGap.Continuum.HarmonicFixedTenPrefix

#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.coeffW_ten_eq_tailRatio10_mul_nine
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.adjacent_tail10_le
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.fixed_anchor_all_later_cutoffs
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.fixed_ten_all_later_cutoffs
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.fixed_ten_checks_k25
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.fixed_ten_checks_k26
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.fixed_ten_checks_k27
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.fixed_ten_checks_k28
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.fixed_ten_head_k29_fails
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonic_retune_cutoff_k25
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonic_retune_cutoff_k26
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonic_retune_cutoff_k27
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonic_retune_cutoff_k28
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonic_lamPW_le_retune_k25
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonic_lamPW_le_retune_k26
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonic_lamPW_le_retune_k27
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonic_lamPW_le_retune_k28
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonicMass_k25_ten_floor
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonicMass_k26_ten_floor
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonicMass_k27_ten_floor
#print axioms YMGap.Continuum.HarmonicFixedTenPrefix.harmonicMass_k28_ten_floor
