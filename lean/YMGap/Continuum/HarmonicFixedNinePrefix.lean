/-
Fixed nine-anchor PF2 correlation prefix at harmonic scales 21 through 24.
The ninth head first fails at scale 25; that endpoint is banked exactly.
-/

import YMGap.Continuum.HarmonicFixedEightPrefix

namespace YMGap.Continuum.HarmonicFixedNinePrefix

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

private def tenNinths : Q' := Q'.mkPos 10 9 (by decide)

/-- Exact coefficient ratio `c₉/c₈=(10/9)w¹⁹`. -/
def tailRatio9 (w : Q') : Q' := tenNinths * qpow w 19

private def ratio9P : Poly := monoP tenNinths 19

theorem coeffW_nine_eq_tailRatio9_mul_eight (w : Q') :
    coeffW w 9 ≈ tailRatio9 w * coeffW w 8 := by
  have hc9 := hcoeff w 9
  have hq : tailRatio9 w ≈ eval ratio9P w := by
    unfold tailRatio9 ratio9P
    exact Q'.eqv_symm (eval_monoP tenNinths w 19)
  have hc8 := hcoeff w 8
  refine Q'.eqv_trans _ _ _ hc9 ?_
  refine Q'.eqv_trans _ _ _
    (poly_eqv (coeffPoly 9) (pmul ratio9P (coeffPoly 8)) w (by decide)) ?_
  exact Q'.eqv_symm (hEvalMul hq hc8)

/-- PF2 propagates the fixed ninth ratio to every later edge. -/
theorem adjacent_tail9_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w) {a : Nat} (ha : 8 ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      tailRatio9 w * (coeffW w a * coeffW w a) := by
  by_cases h8 : a = 8
  · subst a
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coeffW w 8) _ _
        (coeffW_nine_eq_tailRatio9_mul_eight w)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.mul_assoc_eqv _ _ _
  · have ha9 : 8 < a := by omega
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := 8) (N := a) ha9
    have hr : coeffW w (a + 1) * coeffW w 8 ≤ coeffW w a * coeffW w 9 :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hc8p := FusionResidualBound.coeffW_pos hwp 8
    have hR : coeffW w 9 * (coeffW w a * coeffW w a) ≈
        coeffW w 8 * (tailRatio9 w * (coeffW w a * coeffW w a)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (coeffW_nine_eq_tailRatio9_mul_eight w)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    have hcancel : coeffW w 8 * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w 8 * (tailRatio9 w * (coeffW w a * coeffW w a)) :=
      Q'.le_trans' _ _ _ hsq (Q'.le_of_eqv hR)
    exact Q'.le_of_mul_le_mul_left hcancel hc8p

private def edgeTail9 (w : Q') (j : Nat) : Q' :=
  coeffW w (9 + j) * coeffW w (9 + j + 1)

private def squareTail9 (w : Q') (j : Nat) : Q' :=
  coeffW w (9 + j) * coeffW w (9 + j)

private theorem fixed_nine_tail_sum_le {w R : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hratio : tailRatio9 w ≤ R) (M : Nat) :
    fsum (edgeTail9 w) M ≤ R * fsum (squareTail9 w) M := by
  have hterm : ∀ j, edgeTail9 w j ≤ R * squareTail9 w j := by
    intro j
    have ht := adjacent_tail9_le hw0 hw1 hwp (a := 9 + j) (by omega)
    exact Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hratio
        (Q'.mul_nonneg _ _
          (coeffW_nonneg hw0 (9 + j)) (coeffW_nonneg hw0 (9 + j))))
  have hsum : fsum (edgeTail9 w) M ≤
      fsum (fun j => R * squareTail9 w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : R * fsum (squareTail9 w) M ≈
      fsum (fun j => R * squareTail9 w j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum (squareTail9 w) R M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

/-- A fixed ninth head plus its PF2 tail controls every cutoff at least nine. -/
theorem fixed_nine_all_later_cutoffs {w R : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hR0 : (0 : Q') ≤ R)
    (hhead : adjCorr w 9 ≤ R * coordNormSq w 8)
    (hratio : tailRatio9 w ≤ R) (M : Nat) :
    adjCorr w (9 + M) ≤ R * coordNormSq w (9 + M) := by
  have hA : adjCorr w (9 + M) ≈
      adjCorr w 9 + fsum (edgeTail9 w) M := by
    unfold adjCorr edgeTail9
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW w a * coeffW w (a + 1)) 9 M
  have hD : coordNormSq w (9 + M) ≈
      coordNormSq w 8 + fsum (squareTail9 w) (M + 1) := by
    unfold coordNormSq squareTail9
    rw [show 9 + M + 1 = 9 + (M + 1) by omega]
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW w a * coeffW w a) 9 (M + 1)
  have hsquare0 : ∀ j, (0 : Q') ≤ squareTail9 w j := by
    intro j
    unfold squareTail9
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg hw0 (9 + j)) (coeffW_nonneg hw0 (9 + j))
  have htailPrefix : fsum (squareTail9 w) M ≤ fsum (squareTail9 w) (M + 1) :=
    AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
  have hprefix : coordNormSq w 8 + fsum (squareTail9 w) M ≤
      coordNormSq w (9 + M) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left (coordNormSq w 8) _ _ htailPrefix)
      (Q'.ge_of_eqv hD)
  have hpaid : adjCorr w 9 + fsum (edgeTail9 w) M ≤
      R * coordNormSq w 8 + R * fsum (squareTail9 w) M :=
    AFRateCalibration.q_add_le_add hhead
      (fixed_nine_tail_sum_le hw0 hw1 hwp hratio M)
  have hcollect : R * coordNormSq w 8 + R * fsum (squareTail9 w) M ≈
      R * (coordNormSq w 8 + fsum (squareTail9 w) M) :=
    Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
    (Q'.le_trans' _ _ _ hpaid
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hR0)))

/-! ## Exact harmonic-point window and the first failed head -/

theorem fixed_nine_checks_k21 :
    adjCorr (harmW 21) 9 ≤ retuneCube (harmW 21) * coordNormSq (harmW 21) 8 ∧
      tailRatio9 (harmW 21) ≤ retuneCube (harmW 21) := by
  constructor <;> decide

theorem fixed_nine_checks_k22 :
    adjCorr (harmW 22) 9 ≤ retuneCube (harmW 22) * coordNormSq (harmW 22) 8 ∧
      tailRatio9 (harmW 22) ≤ retuneCube (harmW 22) := by
  constructor <;> decide

theorem fixed_nine_checks_k23 :
    adjCorr (harmW 23) 9 ≤ retuneCube (harmW 23) * coordNormSq (harmW 23) 8 ∧
      tailRatio9 (harmW 23) ≤ retuneCube (harmW 23) := by
  constructor <;> decide

theorem fixed_nine_checks_k24 :
    adjCorr (harmW 24) 9 ≤ retuneCube (harmW 24) * coordNormSq (harmW 24) 8 ∧
      tailRatio9 (harmW 24) ≤ retuneCube (harmW 24) := by
  constructor <;> decide

theorem fixed_nine_head_k25_fails :
    ¬ adjCorr (harmW 25) 9 ≤
      retuneCube (harmW 25) * coordNormSq (harmW 25) 8 := by
  decide

private theorem retuneCube_nonneg (w : Q') (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ retuneCube w := by
  unfold retuneCube retuneBase
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)) 3

theorem harmonic_retune_cutoff_k21 :
    adjCorr (harmW 21) (Ncut 21) ≤
      retuneCube (harmW 21) * coordNormSq (harmW 21) (Ncut 21) := by
  simpa [Ncut] using fixed_nine_all_later_cutoffs
    (harmW_nonneg 21) (harmW_le_one 21) (harmW_pos 21)
    (retuneCube_nonneg _ (harmW_nonneg 21))
    fixed_nine_checks_k21.1 fixed_nine_checks_k21.2 520

theorem harmonic_retune_cutoff_k22 :
    adjCorr (harmW 22) (Ncut 22) ≤
      retuneCube (harmW 22) * coordNormSq (harmW 22) (Ncut 22) := by
  simpa [Ncut] using fixed_nine_all_later_cutoffs
    (harmW_nonneg 22) (harmW_le_one 22) (harmW_pos 22)
    (retuneCube_nonneg _ (harmW_nonneg 22))
    fixed_nine_checks_k22.1 fixed_nine_checks_k22.2 567

theorem harmonic_retune_cutoff_k23 :
    adjCorr (harmW 23) (Ncut 23) ≤
      retuneCube (harmW 23) * coordNormSq (harmW 23) (Ncut 23) := by
  simpa [Ncut] using fixed_nine_all_later_cutoffs
    (harmW_nonneg 23) (harmW_le_one 23) (harmW_pos 23)
    (retuneCube_nonneg _ (harmW_nonneg 23))
    fixed_nine_checks_k23.1 fixed_nine_checks_k23.2 616

theorem harmonic_retune_cutoff_k24 :
    adjCorr (harmW 24) (Ncut 24) ≤
      retuneCube (harmW 24) * coordNormSq (harmW 24) (Ncut 24) := by
  simpa [Ncut] using fixed_nine_all_later_cutoffs
    (harmW_nonneg 24) (harmW_le_one 24) (harmW_pos 24)
    (retuneCube_nonneg _ (harmW_nonneg 24))
    fixed_nine_checks_k24.1 fixed_nine_checks_k24.2 667

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

theorem harmonic_lamPW_le_retune_k21 :
    lamPW (harmW 21) (Ncut 21) 1 ≤ retuneCube (harmW 21) :=
  harmonic_lamPW_le_retune_of_cutoff 21 harmonic_retune_cutoff_k21

theorem harmonic_lamPW_le_retune_k22 :
    lamPW (harmW 22) (Ncut 22) 1 ≤ retuneCube (harmW 22) :=
  harmonic_lamPW_le_retune_of_cutoff 22 harmonic_retune_cutoff_k22

theorem harmonic_lamPW_le_retune_k23 :
    lamPW (harmW 23) (Ncut 23) 1 ≤ retuneCube (harmW 23) :=
  harmonic_lamPW_le_retune_of_cutoff 23 harmonic_retune_cutoff_k23

theorem harmonic_lamPW_le_retune_k24 :
    lamPW (harmW 24) (Ncut 24) 1 ≤ retuneCube (harmW 24) :=
  harmonic_lamPW_le_retune_of_cutoff 24 harmonic_retune_cutoff_k24

private theorem harmonic_mass_floor_of_lamPW (k : Nat)
    (h : lamPW (harmW k) (Ncut k) 1 ≤ retuneCube (harmW k)) :
    (1 : Q') - retuneCube (harmW k) ≤ harmonicMass k := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg h)

theorem harmonicMass_k21_nine_floor :
    (1 : Q') - retuneCube (harmW 21) ≤ harmonicMass 21 :=
  harmonic_mass_floor_of_lamPW 21 harmonic_lamPW_le_retune_k21

theorem harmonicMass_k22_nine_floor :
    (1 : Q') - retuneCube (harmW 22) ≤ harmonicMass 22 :=
  harmonic_mass_floor_of_lamPW 22 harmonic_lamPW_le_retune_k22

theorem harmonicMass_k23_nine_floor :
    (1 : Q') - retuneCube (harmW 23) ≤ harmonicMass 23 :=
  harmonic_mass_floor_of_lamPW 23 harmonic_lamPW_le_retune_k23

theorem harmonicMass_k24_nine_floor :
    (1 : Q') - retuneCube (harmW 24) ≤ harmonicMass 24 :=
  harmonic_mass_floor_of_lamPW 24 harmonic_lamPW_le_retune_k24

end YMGap.Continuum.HarmonicFixedNinePrefix

#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.coeffW_nine_eq_tailRatio9_mul_eight
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.adjacent_tail9_le
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.fixed_nine_all_later_cutoffs
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.fixed_nine_checks_k21
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.fixed_nine_checks_k22
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.fixed_nine_checks_k23
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.fixed_nine_checks_k24
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.fixed_nine_head_k25_fails
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonic_retune_cutoff_k21
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonic_retune_cutoff_k22
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonic_retune_cutoff_k23
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonic_retune_cutoff_k24
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonic_lamPW_le_retune_k21
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonic_lamPW_le_retune_k22
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonic_lamPW_le_retune_k23
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonic_lamPW_le_retune_k24
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonicMass_k21_nine_floor
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonicMass_k22_nine_floor
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonicMass_k23_nine_floor
#print axioms YMGap.Continuum.HarmonicFixedNinePrefix.harmonicMass_k24_nine_floor
