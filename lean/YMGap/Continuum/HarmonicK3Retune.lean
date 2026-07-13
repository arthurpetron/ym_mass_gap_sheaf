/-
The first harmonic scale beyond the two-anchor window.

At `k = 3`, `harmW 3 = 4/5`.  The first three adjacent edges admit a
slightly strengthened exact certificate: they are paid for by the diagonal
coordinates `0,1,2` only.  Consequently the symbolic tail can start at mode
three and pay each edge `c_a c_(a+1)` with the previously unused square
`c_a^2`.  In particular `c_2^2` is not counted twice.
-/

import YMGap.Continuum.HarmonicThetaRatioExtension
import YMGap.Continuum.HarmonicWeightDriftFence

namespace YMGap.Continuum.HarmonicK3Retune

set_option maxHeartbeats 1200000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedSchurSpacingBridge
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicThetaRatioExtension
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private def w3 : Q' := harmW 3
private def r3 : Q' := retuneCube w3

private def edge3 (j : Nat) : Q' :=
  coeffW w3 (3 + j) * coeffW w3 (3 + j + 1)

private def square3 (j : Nat) : Q' :=
  coeffW w3 (3 + j) * coeffW w3 (3 + j)

/-- The exact three-anchor head has spare diagonal mass: all edges with left
endpoint below three are bounded using only `c_0^2+c_1^2+c_2^2`.  The omitted
`c_3^2` is the first square available to the symbolic tail. -/
theorem k3_strengthened_head :
    adjCorr w3 3 ≤ r3 * coordNormSq w3 2 := by
  unfold w3 r3 adjCorr coordNormSq harmW harmU
    ReciprocalBernoulliUpper.oneSub unit coeffW dimQ c4 retuneCube retuneBase
  decide

/-- The crude consecutive-coefficient estimate is already below the retune
factor at `w=4/5`. -/
theorem k3_crude_ratio_le_retune :
    Q'.ofNat 2 * qpow w3 5 ≤ r3 := by
  unfold w3 r3 harmW harmU ReciprocalBernoulliUpper.oneSub unit
    retuneCube retuneBase
  decide

/-- Every tail edge starting at mode three is paid for by its left diagonal
square.  This is a genuinely symbolic statement in `a`, not a cutoff check. -/
theorem k3_tail_edge_le (a : Nat) (ha : 3 ≤ a) :
    coeffW w3 a * coeffW w3 (a + 1) ≤
      r3 * (coeffW w3 a * coeffW w3 a) := by
  have hc0 : (0 : Q') ≤ coeffW w3 a :=
    coeffW_nonneg (harmW_nonneg 3) a
  have hnext0 := coeffW_succ_ratio (harmW_nonneg 3) (harmW_le_one 3)
    a (by omega : 1 ≤ a)
  have hnext : coeffW w3 (a + 1) ≤ r3 * coeffW w3 a :=
    Q'.le_trans' _ _ _ hnext0
      (Q'.mul_le_mul_of_nonneg_right _ _ _ k3_crude_ratio_le_retune hc0)
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _ _ hnext hc0
  refine Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (coeffW w3 a) r3 (coeffW w3 a))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (coeffW w3 a)
      (Q'.mul_comm_eqv (coeffW w3 a) r3)) ?_
  exact Q'.mul_assoc_eqv r3 (coeffW w3 a) (coeffW w3 a)

/-- The whole arbitrary-length tail is charged to the disjoint diagonal
window beginning at mode three. -/
theorem k3_tail_sum_le (M : Nat) :
    fsum edge3 M ≤ r3 * fsum square3 M := by
  have hterm : ∀ j, edge3 j ≤ r3 * square3 j := by
    intro j
    unfold edge3 square3
    exact k3_tail_edge_le (3 + j) (by omega)
  have hsum : fsum edge3 M ≤ fsum (fun j => r3 * square3 j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact CharacterTail.finSum_le_termwise _ _ hterm M
  have hfactor : r3 * fsum square3 M ≈
      fsum (fun j => r3 * square3 j) M := by
    rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
    exact const_mul_finSum square3 r3 M
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hfactor)

private theorem k3_short_cutoffs {N : Nat} (hN : N ≤ 3) :
    adjCorr w3 N ≤ r3 * coordNormSq w3 N := by
  have cases : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · unfold w3 r3 adjCorr coordNormSq harmW harmU
      ReciprocalBernoulliUpper.oneSub unit coeffW dimQ c4 retuneCube retuneBase
    decide
  · unfold w3 r3 adjCorr coordNormSq harmW harmU
      ReciprocalBernoulliUpper.oneSub unit coeffW dimQ c4 retuneCube retuneBase
    decide
  · unfold w3 r3 adjCorr coordNormSq harmW harmU
      ReciprocalBernoulliUpper.oneSub unit coeffW dimQ c4 retuneCube retuneBase
    decide
  · have hdiag : coordNormSq w3 2 ≤ coordNormSq w3 3 := by
      unfold coordNormSq
      exact AFRateCalibration.fsum_le_of_le
        (fun i => Q'.mul_nonneg _ _
          (coeffW_nonneg (harmW_nonneg 3) i)
          (coeffW_nonneg (harmW_nonneg 3) i)) (by omega)
    have hr0 : (0 : Q') ≤ r3 := by
      unfold r3 retuneCube retuneBase
      exact qpow_nonneg _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.zero_le_add _ _ (by decide) (harmW_nonneg 3))) 3
    exact Q'.le_trans' _ _ _ k3_strengthened_head
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hdiag hr0)

/-- **All-cutoff closure of the first uncovered harmonic scale.**

For `N=3+M`, the strengthened head uses precisely the diagonal prefix of
length three, while the `M` remaining adjacent edges use the `M` left squares
starting at mode three.  The final square `c_N^2` is unused, so no diagonal
coordinate is charged twice. -/
theorem k3_retune_all_cutoffs (N : Nat) :
    adjCorr (harmW 3) N ≤
      retuneCube (harmW 3) * coordNormSq (harmW 3) N := by
  change adjCorr w3 N ≤ r3 * coordNormSq w3 N
  rcases Nat.le_total N 3 with hsmall | hlarge
  · exact k3_short_cutoffs hsmall
  · obtain ⟨M, rfl⟩ := Nat.le.dest hlarge
    have hA : adjCorr w3 (3 + M) ≈ adjCorr w3 3 + fsum edge3 M := by
      unfold adjCorr edge3
      exact FusionCoreStepRoundH.fsum_split_at
        (fun a => coeffW w3 a * coeffW w3 (a + 1)) 3 M
    have hD : coordNormSq w3 (3 + M) ≈
        coordNormSq w3 2 + fsum square3 (M + 1) := by
      unfold coordNormSq square3
      rw [show 3 + M + 1 = 3 + (M + 1) by omega]
      exact FusionCoreStepRoundH.fsum_split_at
        (fun a => coeffW w3 a * coeffW w3 a) 3 (M + 1)
    have hsquare0 : ∀ j, (0 : Q') ≤ square3 j := by
      intro j
      unfold square3
      exact Q'.mul_nonneg _ _
        (coeffW_nonneg (harmW_nonneg 3) (3 + j))
        (coeffW_nonneg (harmW_nonneg 3) (3 + j))
    have htailPrefix : fsum square3 M ≤ fsum square3 (M + 1) :=
      AFRateCalibration.fsum_le_of_le hsquare0 (by omega)
    have hprefix : coordNormSq w3 2 + fsum square3 M ≤
        coordNormSq w3 (3 + M) := by
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_left (coordNormSq w3 2) _ _ htailPrefix)
        (Q'.ge_of_eqv hD)
    have hr0 : (0 : Q') ≤ r3 := by
      unfold r3 retuneCube retuneBase
      exact qpow_nonneg _
        (Q'.mul_nonneg _ _ (by decide)
          (Q'.zero_le_add _ _ (by decide) (harmW_nonneg 3))) 3
    have hpaid : adjCorr w3 3 + fsum edge3 M ≤
        r3 * coordNormSq w3 2 + r3 * fsum square3 M :=
      AFRateCalibration.q_add_le_add k3_strengthened_head (k3_tail_sum_le M)
    have hcollect : r3 * coordNormSq w3 2 + r3 * fsum square3 M ≈
        r3 * (coordNormSq w3 2 + fsum square3 M) := by
      refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm
        (Q'.mul_add_eqv r3 (coordNormSq w3 2) (fsum square3 M)))
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hA)
      (Q'.le_trans' _ _ _ hpaid
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollect)
          (Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hr0)))

/-- Exact quotient form, with positivity supplied by the vacuum coordinate. -/
theorem k3_retune_ratio_all_cutoffs (N : Nat) :
    Q'.divPos
        (adjCorr (harmW 3) N)
        (coordNormSq (harmW 3) N)
        (coordNormSq_pos (harmW_nonneg 3) N) ≤
      retuneCube (harmW 3) := by
  exact Q'.divPos_le_of_le_mul _ _ _ (k3_retune_all_cutoffs N)

/-- The fundamental fused transfer eigenvalue obeys the same exact bound at
every finite cutoff. -/
theorem k3_lamPW_le_retune (N : Nat) :
    lamPW (harmW 3) N 1 ≤ retuneCube (harmW 3) := by
  have hv := vacNorm_fundamental_eq_ratio
    (harmW_nonneg 3) (harmW_le_one 3) N
  have hlam := lamPW_eq_vacNorm_p2
    (harmW_nonneg 3) (harmW_le_one 3) N 0
  have heq : lamPW (harmW 3) N 1 ≈
      Q'.divPos (adjCorr (harmW 3) N) (coordNormSq (harmW 3) N)
        (coordNormSq_pos (harmW_nonneg 3) N) :=
    Q'.eqv_trans _ _ _ hlam hv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (k3_retune_ratio_all_cutoffs N)

/-- At the actual quadratic cutoff, the operator mass has the exact positive
retune floor. -/
theorem harmonicMass_k3_retune_floor :
    (1 : Q') - retuneCube (harmW 3) ≤ harmonicMass 3 := by
  unfold harmonicMass
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (k3_lamPW_le_retune (Ncut 3)))

/-- The exact harmonic retune prefix is now four scales long. -/
theorem initial_four_retune {k : Nat} (hk : k ≤ 3) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact initial_three_retune (by decide)
  · exact initial_three_retune (by decide)
  · exact initial_three_retune (by decide)
  · exact k3_retune_all_cutoffs (Ncut 3)

/-- The next genuine Schur/spacing comparison, at the newly covered scale. -/
theorem harmonicSchur_spacing_k3 :
    harmonicSchurAll 3 * harmonicSpacing 4 ≤
      harmonicMass 4 * harmonicSpacing 3 := by
  decide

/-- The exact Schur/spacing prefix likewise extends from `k≤2` to `k≤3`. -/
theorem harmonicSchur_spacing_initial_four {k : Nat} (hk : k ≤ 3) :
    harmonicSchurAll k * harmonicSpacing (k + 1) ≤
      harmonicMass (k + 1) * harmonicSpacing k := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact harmonicSchur_spacing_initial_three (by decide)
  · exact harmonicSchur_spacing_initial_three (by decide)
  · exact harmonicSchur_spacing_initial_three (by decide)
  · exact harmonicSchur_spacing_k3

/-- Full coupled-operator/spacing consequence at `k=3`, with the exact Schur
erosion rather than a scalar surrogate. -/
theorem harmonic_operator_spacing_k3 :
    harmonicHead 3 * harmonicSpacing 4 ≤
      (harmonicErosionAll 3 + harmonicMass 4) * harmonicSpacing 3 := by
  exact spacing_cross_of_schur (harmonicShell_pos_all 3)
    (harmonicErosionAll_nonneg 3)
    (Q'.le_of_lt (harmonicSpacing_pos 4))
    (harmonicSpacing_contracts 3)
    (harmonicCoupling_size_all 3)
    harmonicSchur_spacing_k3

/-- Coupled-operator/spacing law on the complete four-scale prefix. -/
theorem harmonic_operator_spacing_initial_four {k : Nat} (hk : k ≤ 3) :
    harmonicHead k * harmonicSpacing (k + 1) ≤
      (harmonicErosionAll k + harmonicMass (k + 1)) * harmonicSpacing k := by
  exact spacing_cross_of_schur (harmonicShell_pos_all k)
    (harmonicErosionAll_nonneg k)
    (Q'.le_of_lt (harmonicSpacing_pos (k + 1)))
    (harmonicSpacing_contracts k)
    (harmonicCoupling_size_all k)
    (harmonicSchur_spacing_initial_four hk)

end YMGap.Continuum.HarmonicK3Retune

#print axioms YMGap.Continuum.HarmonicK3Retune.k3_strengthened_head
#print axioms YMGap.Continuum.HarmonicK3Retune.k3_crude_ratio_le_retune
#print axioms YMGap.Continuum.HarmonicK3Retune.k3_tail_edge_le
#print axioms YMGap.Continuum.HarmonicK3Retune.k3_tail_sum_le
#print axioms YMGap.Continuum.HarmonicK3Retune.k3_retune_all_cutoffs
#print axioms YMGap.Continuum.HarmonicK3Retune.k3_retune_ratio_all_cutoffs
#print axioms YMGap.Continuum.HarmonicK3Retune.k3_lamPW_le_retune
#print axioms YMGap.Continuum.HarmonicK3Retune.harmonicMass_k3_retune_floor
#print axioms YMGap.Continuum.HarmonicK3Retune.initial_four_retune
#print axioms YMGap.Continuum.HarmonicK3Retune.harmonicSchur_spacing_k3
#print axioms YMGap.Continuum.HarmonicK3Retune.harmonicSchur_spacing_initial_four
#print axioms YMGap.Continuum.HarmonicK3Retune.harmonic_operator_spacing_k3
#print axioms YMGap.Continuum.HarmonicK3Retune.harmonic_operator_spacing_initial_four
