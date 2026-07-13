/-
Finite-central-block reduction for the harmonic theta quotient.

The new bulk-theta estimate controls diagonal squares beyond `Ncut k`.  This
module also controls the adjacent numerator leakage (by the exact two-term
AM--GM square identity), and shows that any retained central-block correlation
bound extends to every larger cutoff with an explicit `+4/(k+2)^2` loss.
-/

import YMGap.Continuum.HarmonicBulkThetaTail
import YMGap.Constructive.CRealAlg
import YMGap.Continuum.EndpointCutoffTwoParameter
import YMGap.Continuum.TwoAnchorBlockCorrBound
import YMGap.Continuum.TwoAnchorBlockCorrBound

namespace YMGap.Continuum.HarmonicThetaRatioExtension

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.QuadraticCutoffSchedule
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicBulkThetaTail
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.TwoAnchorBlockCorrBound
open YMGap.Continuum.TwoAnchorBlockCorrBound

local infix:50 " ≈ " => Q'.eqv

/-- Adjacent numerator leakage beyond the retained quadratic block. -/
def adjTailWindow (k M : Nat) : Q' :=
  finSum (fun j => coeffW (harmW k) (Ncut k + j) *
    coeffW (harmW k) (Ncut k + j + 1)) M

theorem adjCorr_cutoff_split_eqv (k M : Nat) :
    adjCorr (harmW k) (Ncut k + M) ≈
      adjCorr (harmW k) (Ncut k) + adjTailWindow k M := by
  unfold adjCorr adjTailWindow
  rw [MovingCutoff.fsum_eq_finSum, MovingCutoff.fsum_eq_finSum]
  exact YMGap.Constructive.finSum_split
    (fun a => coeffW (harmW k) a * coeffW (harmW k) (a + 1))
    (Ncut k) M

private theorem adjTerm_le_two_squares (x y : Q')
    (hxy : (0 : Q') ≤ x * y) :
    x * y ≤ x * x + y * y := by
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg (x * y) (x * y) hxy)
    (CRealAlg.amgm_two x y)

private theorem shiftedSqWindow_le_double_invSq (k M : Nat) :
    finSum (fun j => coeffSqTerm k (Ncut k + j + 1)) M ≤
      Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
  let f := fun j => coeffSqTerm k (Ncut k + j)
  have hnonneg : ∀ j, (0 : Q') ≤ f j := by
    intro j
    unfold f coeffSqTerm
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) _) (coeffW_nonneg (harmW_nonneg k) _)
  have hsplit := YMGap.Constructive.finSum_split f 1 M
  have hhead : (0 : Q') ≤ finSum f 1 := by
    show (0 : Q') ≤ (0 : Q') + f 0
    exact Q'.zero_le_add _ _ (Q'.le_refl' 0) (hnonneg 0)
  have hshift_le : finSum (fun j => f (1 + j)) M ≤ finSum f (1 + M) := by
    have hadd := Q'.add_le_self_of_nonneg
      (finSum (fun j => f (1 + j)) M) (finSum f 1) hhead
    have hcomm : finSum (fun j => f (1 + j)) M + finSum f 1 ≈
        finSum f 1 + finSum (fun j => f (1 + j)) M := Q'.add_comm_eqv _ _
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) (Q'.ge_of_eqv hsplit))
  have hreindex :
      finSum (fun j => coeffSqTerm k (Ncut k + j + 1)) M ≈
        finSum (fun j => f (1 + j)) M := by
    exact finSum_eqv_congr _ _ (fun j => by
      unfold f
      rw [show Ncut k + j + 1 = Ncut k + (1 + j) by omega]
      exact Q'.eqv_refl _) M
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreindex)
    (Q'.le_trans' _ _ _ hshift_le
      (bulkThetaWindow_le_two_mul_invSq k (1 + M)))

/-- The adjacent numerator leakage costs at most four inverse-square units.
The deliberately simple constant comes from `xy ≤ x²+y²` and two diagonal
tail windows, each bounded by `2/(k+2)²`. -/
theorem adjTailWindow_le_four_invSq (k M : Nat) :
    adjTailWindow k M ≤ Q'.ofNat 4 * invSqTerm 2 (by decide) k := by
  let X := fun j => coeffSqTerm k (Ncut k + j)
  let Y := fun j => coeffSqTerm k (Ncut k + j + 1)
  have hterm : ∀ j,
      coeffW (harmW k) (Ncut k + j) * coeffW (harmW k) (Ncut k + j + 1) ≤
        X j + Y j := by
    intro j
    apply adjTerm_le_two_squares
    exact Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) _)
      (coeffW_nonneg (harmW_nonneg k) _)
  have hsum := CharacterTail.finSum_le_termwise _ _ hterm M
  have hadd : finSum (fun j => X j + Y j) M ≈ finSum X M + finSum Y M :=
    RationalTail.finSum_add X Y M
  have hX : finSum X M ≤ Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
    exact bulkThetaWindow_le_two_mul_invSq k M
  have hY : finSum Y M ≤ Q'.ofNat 2 * invSqTerm 2 (by decide) k := by
    exact shiftedSqWindow_le_double_invSq k M
  have hsumXY : finSum X M + finSum Y M ≤
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) +
        (Q'.ofNat 2 * invSqTerm 2 (by decide) k) :=
    AFRateCalibration.q_add_le_add hX hY
  have hcollapse :
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) +
          (Q'.ofNat 2 * invSqTerm 2 (by decide) k) ≈
        Q'.ofNat 4 * invSqTerm 2 (by decide) k := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 2) (Q'.ofNat 2) _)) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hadd)
      (Q'.le_trans' _ _ _ hsumXY (Q'.le_of_eqv hcollapse)))

/-- The retained diagonal norm is monotone under a cutoff extension. -/
theorem coordNormSq_cutoff_le_extension (k M : Nat) :
    coordNormSq (harmW k) (Ncut k) ≤
      coordNormSq (harmW k) (Ncut k + M) := by
  unfold coordNormSq
  exact AFRateCalibration.fsum_le_of_le
    (fun i => Q'.mul_nonneg _ _
      (coeffW_nonneg (harmW_nonneg k) i)
      (coeffW_nonneg (harmW_nonneg k) i)) (by omega)

/-- **Central-block-to-all-cutoffs harmonic quotient bridge.**  If the retained
quadratic block has correlation constant `retuneCube + C/(k+2)^2`, then every
larger finite cutoff has the same form with the exact updated constant `C+4`.
This isolates the remaining task to the finite central block. -/
theorem central_bound_extends
    (C : Q') (hC : (0 : Q') ≤ C) (k M : Nat)
    (hcentral :
      adjCorr (harmW k) (Ncut k) ≤
        (retuneCube (harmW k) + C * invSqTerm 2 (by decide) k) *
          coordNormSq (harmW k) (Ncut k)) :
    adjCorr (harmW k) (Ncut k + M) ≤
      (retuneCube (harmW k) + (C + Q'.ofNat 4) * invSqTerm 2 (by decide) k) *
        coordNormSq (harmW k) (Ncut k + M) := by
  let I := invSqTerm 2 (by decide) k
  let D0 := coordNormSq (harmW k) (Ncut k)
  let D := coordNormSq (harmW k) (Ncut k + M)
  let R := retuneCube (harmW k) + C * I
  have hD0D : D0 ≤ D := coordNormSq_cutoff_le_extension k M
  have hR0 : (0 : Q') ≤ R := by
    unfold R
    exact Q'.zero_le_add _ _
      (qpow_nonneg _ (Q'.mul_nonneg _ _ (by decide)
        (Q'.zero_le_add _ _ (by decide) (harmW_nonneg k))) 3)
      (Q'.mul_nonneg _ _ hC (unit_nonneg _ _))
  have hRD : R * D0 ≤ R * D :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hD0D hR0
  have hD1 : (1 : Q') ≤ D :=
    EndpointCutoffTwoParameter.coordNormSq_ge_one (harmW_nonneg k) _
  have hI0 : (0 : Q') ≤ I := unit_nonneg _ _
  have h4I0 : (0 : Q') ≤ Q'.ofNat 4 * I :=
    Q'.mul_nonneg _ _ (by decide) hI0
  have h4Iscale : Q'.ofNat 4 * I ≤ (Q'.ofNat 4 * I) * D := by
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hD1 h4I0)
  have hsplit := adjCorr_cutoff_split_eqv k M
  have htail := adjTailWindow_le_four_invSq k M
  have hmain : adjCorr (harmW k) (Ncut k + M) ≤ R * D + (Q'.ofNat 4 * I) * D := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    refine Q'.le_trans' _ _ _
      (AFRateCalibration.q_add_le_add hcentral htail) ?_
    exact AFRateCalibration.q_add_le_add hRD h4Iscale
  refine Q'.le_trans' _ _ _ hmain (Q'.le_of_eqv ?_)
  unfold R I D
  -- `(retune + C I)D + (4 I)D = (retune + (C+4)I)D`.
  show _ ≈ _
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv
      (retuneCube (harmW k) + C * invSqTerm 2 (by decide) k)
      (Q'.ofNat 4 * invSqTerm 2 (by decide) k)
      (coordNormSq (harmW k) (Ncut k + M)))) ?_
  refine Q'.mul_eqv_congr_right _ _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (retuneCube (harmW k))
      (C * invSqTerm 2 (by decide) k)
      (Q'.ofNat 4 * invSqTerm 2 (by decide) k)) ?_
  exact Q'.add_eqv_congr_left (retuneCube (harmW k)) _ _
    (Q'.eqv_symm
      (Q'.add_mul_eqv C (Q'.ofNat 4) (invSqTerm 2 (by decide) k)))

/-- Quotient presentation of `central_bound_extends`, with denominator
positivity derived from its vacuum summand. -/
theorem central_ratio_bound_extends
    (C : Q') (hC : (0 : Q') ≤ C) (k M : Nat)
    (hcentral :
      adjCorr (harmW k) (Ncut k) ≤
        (retuneCube (harmW k) + C * invSqTerm 2 (by decide) k) *
          coordNormSq (harmW k) (Ncut k)) :
    Q'.divPos
        (adjCorr (harmW k) (Ncut k + M))
        (coordNormSq (harmW k) (Ncut k + M))
        (FusedRatioCorridor.pos_of_one_le
          (EndpointCutoffTwoParameter.coordNormSq_ge_one
            (harmW_nonneg k) (Ncut k + M))) ≤
      retuneCube (harmW k) +
        (C + Q'.ofNat 4) * invSqTerm 2 (by decide) k := by
  exact Q'.divPos_le_of_le_mul _ _ _
    (central_bound_extends C hC k M hcentral)

/-- Closed first harmonic scale (`harmW 0 = 1/2`): the existing strong-window
central theorem and the new leakage bridge give an unconditional all-extension
quotient bound with constant four. -/
theorem first_scale_ratio_bound (M : Nat) :
    Q'.divPos
        (adjCorr (harmW 0) (Ncut 0 + M))
        (coordNormSq (harmW 0) (Ncut 0 + M))
        (FusedRatioCorridor.pos_of_one_le
          (EndpointCutoffTwoParameter.coordNormSq_ge_one
            (harmW_nonneg 0) (Ncut 0 + M))) ≤
      retuneCube (harmW 0) +
        Q'.ofNat 4 * invSqTerm 2 (by decide) 0 := by
  have hwHalf : harmW 0 ≤ Q'.mkPos 1 2 (by decide) := by
    unfold harmW harmU ReciprocalBernoulliUpper.oneSub unit
    decide
  have hc := arbitrary_truncation_retune (harmW_nonneg 0) hwHalf (Ncut 0)
  have hcentral : adjCorr (harmW 0) (Ncut 0) ≤
      (retuneCube (harmW 0) + (0 : Q') * invSqTerm 2 (by decide) 0) *
        coordNormSq (harmW 0) (Ncut 0) := by
    have hbase : retuneCube (harmW 0) +
        (0 : Q') * invSqTerm 2 (by decide) 0 ≈ retuneCube (harmW 0) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (retuneCube (harmW 0)) _ 0
          (Q'.zero_mul_eqv _)) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' _)
    exact Q'.le_trans' _ _ _ hc
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ hbase))
  have h := central_ratio_bound_extends (0 : Q') (Q'.le_refl' 0) 0 M hcentral
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by
    refine Q'.add_eqv_congr_left (retuneCube (harmW 0)) _ _ ?_
    exact Q'.mul_eqv_congr_right
      ((0 : Q') + Q'.ofNat 4) (Q'.ofNat 4)
      (invSqTerm 2 (by decide) 0)
      (Q'.eqv_of_eq (Q'.zero_add' (Q'.ofNat 4)))))

/-! ## Closed harmonic prefix from the unconditional two-anchor theorem -/

/-- The first three harmonic weights lie in the exact two-anchor window:
`k≤2 → harmW k≤3/4`. -/
theorem harmW_le_blockCap_of_le_two {k : Nat} (hk : k ≤ 2) :
    harmW k ≤ blockCap := by
  have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · unfold harmW harmU ReciprocalBernoulliUpper.oneSub unit blockCap
    decide
  · unfold harmW harmU ReciprocalBernoulliUpper.oneSub unit blockCap
    decide
  · unfold harmW harmU ReciprocalBernoulliUpper.oneSub unit blockCap
    decide

/-- **Unconditional retained harmonic quotient for `k=0,1,2`.**  No leakage
term is needed: the new all-`N` two-anchor certificate applies directly at the
quadratic cutoff. -/
theorem initial_three_retune {k : Nat} (hk : k ≤ 2) :
    adjCorr (harmW k) (Ncut k) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (Ncut k) :=
  arbitrary_truncation_retune_two_anchor (harmW_nonneg k)
    (harmW_le_blockCap_of_le_two hk) (Ncut k)

/-! ## A fixed three-anchor PF2 route and its exact obstruction -/

/-- Tail step required by a fixed three-anchor localization: after retaining
`c₀,c₁,c₂`, the first omitted ratio must already lie below the retune factor. -/
def threeAnchorTailStep (k : Nat) : Prop :=
  coeffW (harmW k) 3 ≤
    retuneCube (harmW k) * coeffW (harmW k) 2

/-- At the first scale beyond the two-anchor window, the three-anchor tail step
does hold exactly. -/
theorem threeAnchorTailStep_k3 : threeAnchorTailStep 3 := by
  unfold threeAnchorTailStep harmW harmU ReciprocalBernoulliUpper.oneSub unit
    coeffW dimQ c4 retuneCube retuneBase
  decide

/-- The corresponding retained three-coordinate head block is positive at
`k=3`; together with the previous tail step this verifies that adding one
anchor is the correct local mechanism at the first uncovered scale. -/
theorem threeAnchorHead_k3 :
    coeffW (harmW 3) 0 * coeffW (harmW 3) 1 +
        coeffW (harmW 3) 1 * coeffW (harmW 3) 2 ≤
      retuneCube (harmW 3) *
        (coeffW (harmW 3) 0 * coeffW (harmW 3) 0 +
          coeffW (harmW 3) 1 * coeffW (harmW 3) 1 +
          coeffW (harmW 3) 2 * coeffW (harmW 3) 2) := by
  unfold harmW harmU ReciprocalBernoulliUpper.oneSub unit coeffW dimQ c4
    retuneCube retuneBase
  decide

/-- **Kernel-checked obstruction to a fixed three-anchor campaign.**  At the
closed harmonic scale `k=18` (`w=19/20`), the first omitted ratio after mode
two already exceeds the retune factor.  Thus PF2 ratio monotonicity cannot
close all `k≥3` with a fixed three-coordinate block; the number of retained
anchors must grow with the harmonic scale. -/
theorem fixed_three_anchor_not_uniform : ¬ threeAnchorTailStep 18 := by
  unfold threeAnchorTailStep harmW harmU ReciprocalBernoulliUpper.oneSub unit
    coeffW dimQ c4 retuneCube retuneBase
  decide

/-- The exact two-anchor theorem closes the first three harmonic scales with
no inverse-square defect: `harmW k ≤ 3/4` for `k≤2`. -/
theorem first_three_scales_exact {k : Nat} (hk : k ≤ 2) (M : Nat) :
    Q'.divPos
        (adjCorr (harmW k) (Ncut k + M))
        (coordNormSq (harmW k) (Ncut k + M))
        (FusedRatioCorridor.pos_of_one_le
          (EndpointCutoffTwoParameter.coordNormSq_ge_one
            (harmW_nonneg k) (Ncut k + M))) ≤
      retuneCube (harmW k) := by
  have hwc : harmW k ≤ blockCap := by
    have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · unfold harmW harmU blockCap ReciprocalBernoulliUpper.oneSub unit
      decide
    · unfold harmW harmU blockCap ReciprocalBernoulliUpper.oneSub unit
      decide
    · unfold harmW harmU blockCap ReciprocalBernoulliUpper.oneSub unit
      decide
  exact Q'.divPos_le_of_le_mul _ _ _
    (arbitrary_truncation_retune_two_anchor
      (harmW_nonneg k) hwc (Ncut k + M))

end YMGap.Continuum.HarmonicThetaRatioExtension

#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.adjCorr_cutoff_split_eqv
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.adjTailWindow_le_four_invSq
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.coordNormSq_cutoff_le_extension
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.central_bound_extends
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.central_ratio_bound_extends
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.first_scale_ratio_bound
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.harmW_le_blockCap_of_le_two
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.initial_three_retune
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.threeAnchorTailStep_k3
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.threeAnchorHead_k3
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.fixed_three_anchor_not_uniform
#print axioms YMGap.Continuum.HarmonicThetaRatioExtension.first_three_scales_exact
