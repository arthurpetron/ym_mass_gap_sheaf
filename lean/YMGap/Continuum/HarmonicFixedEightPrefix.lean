/-
Fixed eight-anchor PF2 correlation prefix at the four harmonic points
`w_k=(k+1)/(k+2)`, `17 ≤ k ≤ 20`.  The head and tail-ratio facts are
closed rational checks; all later cutoffs are handled symbolically.
-/

import YMGap.Continuum.SevenAnchorWindowRetune

namespace YMGap.Continuum.HarmonicFixedEightPrefix

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

private def nineEighths : Q' := Q'.mkPos 9 8 (by decide)

/-- Exact coefficient ratio `c₈/c₇=(9/8)w¹⁷`. -/
def tailRatio8 (w : Q') : Q' := nineEighths * qpow w 17

private def ratio8P : Poly := monoP nineEighths 17

theorem coeffW_eight_eq_tailRatio8_mul_seven (w : Q') :
    coeffW w 8 ≈ tailRatio8 w * coeffW w 7 := by
  have hc8 := hcoeff w 8
  have hq : tailRatio8 w ≈ eval ratio8P w := by
    unfold tailRatio8 ratio8P
    exact Q'.eqv_symm (eval_monoP nineEighths w 17)
  have hc7 := hcoeff w 7
  refine Q'.eqv_trans _ _ _ hc8 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 8) (pmul ratio8P (coeffPoly 7)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc7)

/-- PF2 propagates the fixed eighth coefficient ratio to every later edge. -/
theorem adjacent_tail8_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) {a : Nat} (ha : 7 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio8 w * (coeffW w a * coeffW w a) := by
  by_cases h7 : a = 7
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 7) _ _
        (coeffW_eight_eq_tailRatio8_mul_seven w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha8 : 7 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 7) (N := a) ha8
    have hr : coeffW w (a + 1) * coeffW w 7 ≤ coeffW w a * coeffW w 8 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc7p := FusionResidualBound.coeffW_pos hwp 7
    have hR : coeffW w 8 * (coeffW w a * coeffW w a) ≈
        coeffW w 7 * (tailRatio8 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (coeffW_eight_eq_tailRatio8_mul_seven w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 7 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 7 * (tailRatio8 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc7p

private def edgeTail8 (w : Q') (j : Nat) : Q' :=
  coeffW w (8 + j) * coeffW w (8 + j + 1)

private def squareTail8 (w : Q') (j : Nat) : Q' :=
  coeffW w (8 + j) * coeffW w (8 + j)

private theorem fixed_eight_tail_sum_le {w R : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hratio : tailRatio8 w ≤ R) (M : Nat) :
    fsum (edgeTail8 w) M ≤ R * fsum (squareTail8 w) M := by
  have hterm : ∀ j, edgeTail8 w j ≤ R * squareTail8 w j := by
    intro j
    have ht := adjacent_tail8_le hw0 hw1 hwp (a := 8 + j) (by omega)
    exact Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hratio
        (Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (8 + j)) (coeffW_nonneg hw0 (8 + j))))
  have hsum : fsum (edgeTail8 w) M ≤
      fsum (fun j => R * squareTail8 w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : R * fsum (squareTail8 w) M ≈
      fsum (fun j => R * squareTail8 w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum (squareTail8 w) R M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

/-- Generic fixed-eight assembler: one exact head check and one exact ratio
check control every cutoff at least eight. -/
theorem fixed_eight_all_later_cutoffs {w R : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hR0 : (0 : Q') ≤ R)
    (hhead : adjCorr w 8 ≤ R * coordNormSq w 7)
    (hratio : tailRatio8 w ≤ R) (M : Nat) :
    adjCorr w (8 + M) ≤ R * coordNormSq w (8 + M) := by
  have hA : adjCorr w (8 + M) ≈
      adjCorr w 8 + fsum (edgeTail8 w) M := by
    unfold adjCorr edgeTail8
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW w a * coeffW w (a + 1)) 8 M
  have hD : coordNormSq w (8 + M) ≈
      coordNormSq w 7 + fsum (squareTail8 w) (M + 1) := by
    unfold coordNormSq squareTail8
    rw [show 8 + M + 1 = 8 + (M + 1) by omega]
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW w a * coeffW w a) 8 (M + 1)
  have hsquare0 : ∀ j, (0 : Q') ≤ squareTail8 w j := by
    intro j
    unfold squareTail8
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg hw0 (8 + j)) (coeffW_nonneg hw0 (8 + j))
  have htailPrefix : fsum (squareTail8 w) M ≤ fsum (squareTail8 w) (M + 1) :=
    AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
  have hprefix : coordNormSq w 7 + fsum (squareTail8 w) M ≤
      coordNormSq w (8 + M) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left (coordNormSq w 7) _ _ htailPrefix)
      (Q'.ge_of_eqv hD)
  have hpaid : adjCorr w 8 + fsum (edgeTail8 w) M ≤
      R * coordNormSq w 7 + R * fsum (squareTail8 w) M :=
    AFRateCalibration.q_add_le_add hhead
      (fixed_eight_tail_sum_le hw0 hw1 hwp hratio M)
  have hcollect : R * coordNormSq w 7 + R * fsum (squareTail8 w) M ≈
      R * (coordNormSq w 7 + fsum (squareTail8 w) M) :=
    Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
    (Q'.le_trans' _ _ _ hpaid
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hR0)))

/-! ## Closed point checks and the first failed head -/

theorem fixed_eight_checks_k17 :
    adjCorr (harmW 17) 8 ≤ retuneCube (harmW 17) * coordNormSq (harmW 17) 7 ∧
      tailRatio8 (harmW 17) ≤ retuneCube (harmW 17) := by
  constructor <;> decide

theorem fixed_eight_checks_k18 :
    adjCorr (harmW 18) 8 ≤ retuneCube (harmW 18) * coordNormSq (harmW 18) 7 ∧
      tailRatio8 (harmW 18) ≤ retuneCube (harmW 18) := by
  constructor <;> decide

theorem fixed_eight_checks_k19 :
    adjCorr (harmW 19) 8 ≤ retuneCube (harmW 19) * coordNormSq (harmW 19) 7 ∧
      tailRatio8 (harmW 19) ≤ retuneCube (harmW 19) := by
  constructor <;> decide

theorem fixed_eight_checks_k20 :
    adjCorr (harmW 20) 8 ≤ retuneCube (harmW 20) * coordNormSq (harmW 20) 7 ∧
      tailRatio8 (harmW 20) ≤ retuneCube (harmW 20) := by
  constructor <;> decide

/-- The same eighth head genuinely fails at the next harmonic point. -/
theorem fixed_eight_head_k21_fails :
    ¬ adjCorr (harmW 21) 8 ≤
      retuneCube (harmW 21) * coordNormSq (harmW 21) 7 := by
  decide

private theorem retuneCube_nonneg (w : Q') (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ retuneCube w := by
  unfold retuneCube retuneBase
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)) 3

theorem harmonic_retune_cutoff_k17 :
    adjCorr (harmW 17) (Ncut 17) ≤
      retuneCube (harmW 17) * coordNormSq (harmW 17) (Ncut 17) := by
  simpa [Ncut] using fixed_eight_all_later_cutoffs
    (harmW_nonneg 17) (harmW_le_one 17) (harmW_pos 17)
    (retuneCube_nonneg _ (harmW_nonneg 17))
    fixed_eight_checks_k17.1 fixed_eight_checks_k17.2 353

theorem harmonic_retune_cutoff_k18 :
    adjCorr (harmW 18) (Ncut 18) ≤
      retuneCube (harmW 18) * coordNormSq (harmW 18) (Ncut 18) := by
  simpa [Ncut] using fixed_eight_all_later_cutoffs
    (harmW_nonneg 18) (harmW_le_one 18) (harmW_pos 18)
    (retuneCube_nonneg _ (harmW_nonneg 18))
    fixed_eight_checks_k18.1 fixed_eight_checks_k18.2 392

theorem harmonic_retune_cutoff_k19 :
    adjCorr (harmW 19) (Ncut 19) ≤
      retuneCube (harmW 19) * coordNormSq (harmW 19) (Ncut 19) := by
  simpa [Ncut] using fixed_eight_all_later_cutoffs
    (harmW_nonneg 19) (harmW_le_one 19) (harmW_pos 19)
    (retuneCube_nonneg _ (harmW_nonneg 19))
    fixed_eight_checks_k19.1 fixed_eight_checks_k19.2 433

theorem harmonic_retune_cutoff_k20 :
    adjCorr (harmW 20) (Ncut 20) ≤
      retuneCube (harmW 20) * coordNormSq (harmW 20) (Ncut 20) := by
  simpa [Ncut] using fixed_eight_all_later_cutoffs
    (harmW_nonneg 20) (harmW_le_one 20) (harmW_pos 20)
    (retuneCube_nonneg _ (harmW_nonneg 20))
    fixed_eight_checks_k20.1 fixed_eight_checks_k20.2 476

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

theorem harmonic_lamPW_le_retune_k17 :
    lamPW (harmW 17) (Ncut 17) 1 ≤ retuneCube (harmW 17) :=
  harmonic_lamPW_le_retune_of_cutoff 17 harmonic_retune_cutoff_k17

theorem harmonic_lamPW_le_retune_k18 :
    lamPW (harmW 18) (Ncut 18) 1 ≤ retuneCube (harmW 18) :=
  harmonic_lamPW_le_retune_of_cutoff 18 harmonic_retune_cutoff_k18

theorem harmonic_lamPW_le_retune_k19 :
    lamPW (harmW 19) (Ncut 19) 1 ≤ retuneCube (harmW 19) :=
  harmonic_lamPW_le_retune_of_cutoff 19 harmonic_retune_cutoff_k19

theorem harmonic_lamPW_le_retune_k20 :
    lamPW (harmW 20) (Ncut 20) 1 ≤ retuneCube (harmW 20) :=
  harmonic_lamPW_le_retune_of_cutoff 20 harmonic_retune_cutoff_k20

private theorem harmonic_mass_floor_of_lamPW (k : Nat)
    (h : lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k)) :
    (1 : Q') - retuneCube (harmW k) ≤ harmonicMass k := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

theorem harmonicMass_k17_eight_floor :
    (1 : Q') - retuneCube (harmW 17) ≤ harmonicMass 17 :=
  harmonic_mass_floor_of_lamPW 17 harmonic_lamPW_le_retune_k17

theorem harmonicMass_k18_eight_floor :
    (1 : Q') - retuneCube (harmW 18) ≤ harmonicMass 18 :=
  harmonic_mass_floor_of_lamPW 18 harmonic_lamPW_le_retune_k18

theorem harmonicMass_k19_eight_floor :
    (1 : Q') - retuneCube (harmW 19) ≤ harmonicMass 19 :=
  harmonic_mass_floor_of_lamPW 19 harmonic_lamPW_le_retune_k19

theorem harmonicMass_k20_eight_floor :
    (1 : Q') - retuneCube (harmW 20) ≤ harmonicMass 20 :=
  harmonic_mass_floor_of_lamPW 20 harmonic_lamPW_le_retune_k20

end YMGap.Continuum.HarmonicFixedEightPrefix

#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.coeffW_eight_eq_tailRatio8_mul_seven
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.adjacent_tail8_le
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.fixed_eight_all_later_cutoffs
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.fixed_eight_checks_k17
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.fixed_eight_checks_k18
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.fixed_eight_checks_k19
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.fixed_eight_checks_k20
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.fixed_eight_head_k21_fails
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonic_retune_cutoff_k17
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonic_retune_cutoff_k18
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonic_retune_cutoff_k19
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonic_retune_cutoff_k20
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonic_lamPW_le_retune_k17
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonic_lamPW_le_retune_k18
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonic_lamPW_le_retune_k19
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonic_lamPW_le_retune_k20
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonicMass_k17_eight_floor
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonicMass_k18_eight_floor
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonicMass_k19_eight_floor
#print axioms YMGap.Continuum.HarmonicFixedEightPrefix.harmonicMass_k20_eight_floor
