/-
Fixed-point six-anchor lower mass bound at the first scale beyond the
seven-anchor window.  This avoids reducing the full cutoff-361 quotient.
-/

import YMGap.Continuum.SixAnchorWindowRetune
import YMGap.Continuum.SevenAnchorWindowRetune

namespace YMGap.Continuum.HarmonicFixedSixFloorK17

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
open YMGap.Continuum.SixAnchorWindowRetune

local infix:50 " ≈ " => Q'.eqv

def fixedRate17 : Q' := Q'.mkPos 14 15 (by decide)

/-- The six-coordinate head has enough exact slack at `w=18/19`. -/
theorem fixed_six_head_k17 :
    adjCorr (harmW 17) 6 ≤ fixedRate17 * coordNormSq (harmW 17) 5 := by
  decide

/-- The PF2 tail ratio at the same fixed point lies below `14/15`. -/
theorem tailRatio6_le_fixedRate17 :
    tailRatio6 (harmW 17) ≤ fixedRate17 := by
  decide

private def edgeTail17 (j : Nat) : Q' :=
  coeffW (harmW 17) (6 + j) * coeffW (harmW 17) (6 + j + 1)

private def squareTail17 (j : Nat) : Q' :=
  coeffW (harmW 17) (6 + j) * coeffW (harmW 17) (6 + j)

private theorem fixed_tail_sum_le (M : Nat) :
    fsum edgeTail17 M ≤ fixedRate17 * fsum squareTail17 M := by
  have hterm : ∀ j, edgeTail17 j ≤ fixedRate17 * squareTail17 j := by
    intro j
    have ht := adjacent_tail6_le (harmW_nonneg 17) (harmW_le_one 17)
      (harmW_pos 17) (a := 6 + j) (by omega)
    exact Q'.le_trans' _ _ _ ht
      (Q'.mul_le_mul_of_nonneg_right _ _ _ tailRatio6_le_fixedRate17
        (Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg 17) (6 + j))
          (coeffW_nonneg (harmW_nonneg 17) (6 + j))))
  have hsum : fsum edgeTail17 M ≤
      fsum (fun j => fixedRate17 * squareTail17 j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : fixedRate17 * fsum squareTail17 M ≈
      fsum (fun j => fixedRate17 * squareTail17 j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum squareTail17 fixedRate17 M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

/-- A fixed head plus the symbolic PF2 tail controls every cutoff beyond six. -/
theorem fixed_six_all_later_cutoffs (M : Nat) :
    adjCorr (harmW 17) (6 + M) ≤
      fixedRate17 * coordNormSq (harmW 17) (6 + M) := by
  have hA : adjCorr (harmW 17) (6 + M) ≈
      adjCorr (harmW 17) 6 + fsum edgeTail17 M := by
    unfold adjCorr edgeTail17
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW (harmW 17) a * coeffW (harmW 17) (a + 1)) 6 M
  have hD : coordNormSq (harmW 17) (6 + M) ≈
      coordNormSq (harmW 17) 5 + fsum squareTail17 (M + 1) := by
    unfold coordNormSq squareTail17
    rw [show 6 + M + 1 = 6 + (M + 1) by omega]
    exact FusionCoreStepRoundH.fsum_split_at
      (fun a => coeffW (harmW 17) a * coeffW (harmW 17) a) 6 (M + 1)
  have hsquare0 : ∀ j, (0 : Q') ≤ squareTail17 j := by
    intro j
    unfold squareTail17
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg 17) (6 + j))
      (coeffW_nonneg (harmW_nonneg 17) (6 + j))
  have htailPrefix : fsum squareTail17 M ≤ fsum squareTail17 (M + 1) :=
    AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
  have hprefix : coordNormSq (harmW 17) 5 + fsum squareTail17 M ≤
      coordNormSq (harmW 17) (6 + M) :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_left (coordNormSq (harmW 17) 5) _ _ htailPrefix)
      (Q'.ge_of_eqv hD)
  have hpaid : adjCorr (harmW 17) 6 + fsum edgeTail17 M ≤
      fixedRate17 * coordNormSq (harmW 17) 5 +
        fixedRate17 * fsum squareTail17 M :=
    AFRateCalibration.q_add_le_add fixed_six_head_k17 (fixed_tail_sum_le M)
  have hcollect : fixedRate17 * coordNormSq (harmW 17) 5 +
      fixedRate17 * fsum squareTail17 M ≈
      fixedRate17 * (coordNormSq (harmW 17) 5 + fsum squareTail17 M) :=
    Q'.eqv_symm (Q'.mul_add_eqv _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
    (Q'.le_trans' _ _ _ hpaid
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix (by decide))))

theorem fixed_six_cutoff_k17 :
    adjCorr (harmW 17) (Ncut 17) ≤
      fixedRate17 * coordNormSq (harmW 17) (Ncut 17) := by
  simpa [Ncut] using fixed_six_all_later_cutoffs 355

/-- Exact mass floor needed by the `k=16` Schur rotation. -/
theorem harmonicMass_k17_fixed_floor :
    Q'.mkPos 1 15 (by decide) ≤ harmonicMass 17 := by
  have heq : lamPW (harmW 17) (Ncut 17) 1 ≈
      Q'.divPos (adjCorr (harmW 17) (Ncut 17))
        (coordNormSq (harmW 17) (Ncut 17))
        (coordNormSq_pos (harmW_nonneg 17) (Ncut 17)) :=
    Q'.eqv_trans _ _ _
      (lamPW_eq_vacNorm_p2 (harmW_nonneg 17) (harmW_le_one 17) (Ncut 17) 0)
      (vacNorm_fundamental_eq_ratio (harmW_nonneg 17) (harmW_le_one 17) (Ncut 17))
  have hratio : Q'.divPos (adjCorr (harmW 17) (Ncut 17))
        (coordNormSq (harmW 17) (Ncut 17))
        (coordNormSq_pos (harmW_nonneg 17) (Ncut 17)) ≤ fixedRate17 :=
    Q'.divPos_le_of_le_mul _ _ _ fixed_six_cutoff_k17
  have hlam : lamPW (harmW 17) (Ncut 17) 1 ≤ fixedRate17 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hratio
  have hsub := Q'.add_le_add_left (1 : Q') _ _ (Q'.neg_le_neg hlam)
  unfold harmonicMass
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hsub

end YMGap.Continuum.HarmonicFixedSixFloorK17

#print axioms YMGap.Continuum.HarmonicFixedSixFloorK17.fixed_six_head_k17
#print axioms YMGap.Continuum.HarmonicFixedSixFloorK17.tailRatio6_le_fixedRate17
#print axioms YMGap.Continuum.HarmonicFixedSixFloorK17.fixed_six_all_later_cutoffs
#print axioms YMGap.Continuum.HarmonicFixedSixFloorK17.fixed_six_cutoff_k17
#print axioms YMGap.Continuum.HarmonicFixedSixFloorK17.harmonicMass_k17_fixed_floor
