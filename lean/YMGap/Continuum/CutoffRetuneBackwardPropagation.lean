/-
Backward propagation of a later-cutoff retune certificate.

PF2 makes the adjacent Rayleigh quotient monotone in the Peter--Weyl cutoff.
Consequently, a retune bound checked at any later cutoff propagates to every
earlier cutoff after clearing and cancelling the strictly positive diagonal
normalizer.  Combining this with the harmonic theta/Pascal growing-head
certificate gives the retune inequality at every finite cutoff on every
harmonic coupling, rather than only at the physical quadratic cutoff or in
the symbolic tail.
-/

import YMGap.Continuum.CutoffCorrelationMonotone
import YMGap.Continuum.EndpointCutoffTwoParameter
import YMGap.Continuum.FusedSpectralCarrierBridge
import YMGap.Continuum.HarmonicThetaPascalClosure

namespace YMGap.Continuum.CutoffRetuneBackwardPropagation

set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicThetaPascalClosure
open YMGap.Continuum.QuadraticCutoffSchedule

local infix:50 " ≈ " => Q'.eqv

/-- A scalar correlation bound at cutoff `M` propagates to every earlier
cutoff `N`.  The proof is division-free until the final cancellation of the
strictly positive later diagonal norm. -/
theorem correlation_bound_of_later_cutoff {w R : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwp : (0 : Q') < w) {N M : Nat} (hNM : N ≤ M)
    (hM : adjCorr w M ≤ R * coordNormSq w M) :
    adjCorr w N ≤ R * coordNormSq w N := by
  obtain ⟨tail, rfl⟩ := Nat.le.dest hNM
  let DN := coordNormSq w N
  let DM := coordNormSq w (N + tail)
  let AN := adjCorr w N
  let AM := adjCorr w (N + tail)
  have hcross : AN * DM ≤ AM * DN :=
    finite_cutoff_tail_compare hw0 hw1 hwp N tail
  have hDN0 : (0 : Q') ≤ DN := coordNormSq_nonneg hw0 N
  have hpaid : AM * DN ≤ (R * DM) * DN :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hM hDN0
  have hleft : DM * AN ≈ AN * DM := Q'.mul_comm_eqv _ _
  have hright : (R * DM) * DN ≈ DM * (R * DN) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ DN (Q'.mul_comm_eqv R DM)) ?_
    exact Q'.mul_assoc_eqv DM R DN
  have hcleared : DM * AN ≤ DM * (R * DN) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hcross
        (Q'.le_trans' _ _ _ hpaid (Q'.le_of_eqv hright)))
  exact Q'.le_of_mul_le_mul_left hcleared (coordNormSq_pos hw0 (N + tail))

/-- Retune-specialized backward propagation. -/
theorem retune_bound_of_later_cutoff {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwp : (0 : Q') < w) {N M : Nat} (hNM : N ≤ M)
    (hM : adjCorr w M ≤ retuneCube w * coordNormSq w M) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N :=
  correlation_bound_of_later_cutoff hw0 hw1 hwp hNM hM

/-- **All harmonic couplings, all finite cutoffs.**  Below the growing
anchor this uses backward PF2 propagation from the exact theta/Pascal head;
at and above the anchor it uses the already-certified symbolic PF2 tail. -/
theorem harmonic_retune_all_cutoffs (k N : Nat) :
    adjCorr (harmW k) N ≤
      retuneCube (harmW k) * coordNormSq (harmW k) N := by
  let b := growingAnchor k + 1
  by_cases hNb : N ≤ b
  · apply retune_bound_of_later_cutoff
      (harmW_nonneg k) (harmW_le_one k) (harmW_pos k) hNb
    simpa [b] using harmonic_growing_anchor_all_later_retune k 0
  · have hbN : b ≤ N := by omega
    obtain ⟨tail, htail⟩ := Nat.le.dest hbN
    rw [← htail]
    simpa [b, Nat.add_assoc] using
      harmonic_growing_anchor_all_later_retune k tail

/-- Normalized fundamental Peter--Weyl form at an arbitrary cutoff on the
harmonic schedule. -/
theorem harmonic_lamPW_all_cutoffs (k N : Nat) :
    lamPW (harmW k) N 1 ≤ retuneCube (harmW k) := by
  have heq : lamPW (harmW k) N 1 ≈
      Q'.divPos (adjCorr (harmW k) N) (coordNormSq (harmW k) N)
        (coordNormSq_pos (harmW_nonneg k) N) :=
    Q'.eqv_trans _ _ _
      (lamPW_eq_vacNorm_p2 (harmW_nonneg k) (harmW_le_one k) N 0)
      (vacNorm_fundamental_eq_ratio (harmW_nonneg k) (harmW_le_one k) N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.divPos_le_of_le_mul _ _ _ (harmonic_retune_all_cutoffs k N))

end YMGap.Continuum.CutoffRetuneBackwardPropagation

#print axioms YMGap.Continuum.CutoffRetuneBackwardPropagation.correlation_bound_of_later_cutoff
#print axioms YMGap.Continuum.CutoffRetuneBackwardPropagation.retune_bound_of_later_cutoff
#print axioms YMGap.Continuum.CutoffRetuneBackwardPropagation.harmonic_retune_all_cutoffs
#print axioms YMGap.Continuum.CutoffRetuneBackwardPropagation.harmonic_lamPW_all_cutoffs
