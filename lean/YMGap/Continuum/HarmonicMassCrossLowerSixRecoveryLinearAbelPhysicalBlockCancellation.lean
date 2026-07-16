/-
# Physical block cancellation in the cleared linear Abel payment

The favorable middle band of the physical splice cannot be discarded.  This
module first recombines the middle and tail losslessly into one suffix block,
then banks an exact same-center fence where the full payment succeeds while
the strengthened payment obtained by deleting the strictly negative middle
band fails.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalCarrier

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalBlockCancellation

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryDropCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelCumulativePayment
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalCarrier
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalSplice
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelRisingSplice

local infix:50 " ≈ " => Q'.eqv

/-- The complete cleared variation suffix beginning at `r`. -/
def lowerSixRecoveryClearedAbelSuffixVariation
    (k r L : Nat) : Q' :=
  finSum (fun d =>
    lowerSixRecoveryClearedAbelVariationTerm k (r + d)) (L - r)

/-- The middle and tail bands must be treated as one block: their sum is
exactly the unsplit suffix and is independent of the chosen crossing. -/
theorem lowerSixRecoveryClearedAbelMiddle_add_tail_eqv_suffixVariation
    {k r s L : Nat} (hrs : r ≤ s) (hsL : s ≤ L) :
    lowerSixRecoveryClearedAbelMiddle k r s +
        lowerSixRecoveryClearedAbelTail k s L ≈
      lowerSixRecoveryClearedAbelSuffixVariation k r L := by
  let f := fun d => lowerSixRecoveryClearedAbelVariationTerm k (r + d)
  have hshape : (s - r) + (L - s) = L - r := by omega
  have hsplit := YMGap.Constructive.finSum_split f (s - r) (L - s)
  rw [hshape] at hsplit
  have hshift : ∀ d,
      f ((s - r) + d) ≈
        lowerSixRecoveryClearedAbelVariationTerm k (s + d) := by
    intro d
    have hrsEq : r + (s - r) = s := Nat.add_sub_of_le hrs
    dsimp only [f]
    rw [← Nat.add_assoc, hrsEq]
    exact Q'.eqv_refl _
  have htail := RationalTail.finSum_eqv_congr
    (fun d => f ((s - r) + d))
    (fun d => lowerSixRecoveryClearedAbelVariationTerm k (s + d))
    hshift (L - s)
  unfold lowerSixRecoveryClearedAbelMiddle
    lowerSixRecoveryClearedAbelTail
    lowerSixRecoveryClearedAbelSuffixVariation
  dsimp only [f] at hsplit htail ⊢
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr_left _ _ _ htail))

/-- Terminal numerator plus the losslessly recombined physical suffix. -/
def lowerSixRecoveryClearedAbelPhysicalSuffixBlock
    (k c : Nat) : Q' :=
  let r := lowerSixRecoveryPhysicalPeakIndex c
  let L := 2 * c - 1
  lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (L + 1) *
      lowerSixRecoveryComplementScaleIncrement k L +
    lowerSixRecoveryClearedAbelSuffixVariation k r L

private theorem physical_block_reorder (T H M R V : Q')
    (hMR : M + R ≈ V) :
    T + (H + (M + R)) ≈ H + (T + V) := by
  refine Q'.eqv_trans _ (T + (H + V)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left T _ _
      (Q'.add_eqv_congr_left H _ _ hMR)
  refine Q'.eqv_trans _ ((T + H) + V) _
    (Q'.eqv_symm (Q'.add_assoc_eqv T H V)) ?_
  refine Q'.eqv_trans _ ((H + T) + V) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ V (Q'.add_comm_eqv T H)
  · exact Q'.add_assoc_eqv H T V

/-- The complete physical debt is the rising head plus one coupled suffix
block.  No sign or magnitude is lost in this cancellation. -/
theorem lowerSixRecoveryClearedAbelPhysicalDebt_eqv_head_add_suffixBlock
    {k c s : Nat}
    (hrs : lowerSixRecoveryPhysicalPeakIndex c ≤ s)
    (hsL : s ≤ 2 * c - 1) :
    lowerSixRecoveryClearedAbelPhysicalDebt k c s ≈
      lowerSixRecoveryClearedAbelHead k
          (lowerSixRecoveryPhysicalPeakIndex c) +
        lowerSixRecoveryClearedAbelPhysicalSuffixBlock k c := by
  have hsuffix :=
    lowerSixRecoveryClearedAbelMiddle_add_tail_eqv_suffixVariation
      (k := k) (r := lowerSixRecoveryPhysicalPeakIndex c)
      (s := s) (L := 2 * c - 1) hrs hsL
  unfold lowerSixRecoveryClearedAbelPhysicalDebt
    lowerSixRecoveryClearedAbelPhysicalSuffixBlock
  exact physical_block_reorder _ _ _ _ _ hsuffix

/-- The stronger debt obtained by deleting the middle band.  The closed fence
below shows that this is not a valid uniform replacement for the physical
debt. -/
def lowerSixRecoveryClearedAbelNoMiddleDebt
    (k c s : Nat) : Q' :=
  let r := lowerSixRecoveryPhysicalPeakIndex c
  let L := 2 * c - 1
  lowerSixRecoveryLinearCarrierPrefixNumerator (k + 1) (L + 1) *
      lowerSixRecoveryComplementScaleIncrement k L +
    (lowerSixRecoveryClearedAbelHead k r +
      lowerSixRecoveryClearedAbelTail k s L)

private theorem physical_middle_insertion (T H M R : Q') :
    T + (H + (M + R)) ≈ (T + (H + R)) + M := by
  refine Q'.eqv_trans _ (T + ((H + M) + R)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left T _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv H M R))
  refine Q'.eqv_trans _ ((T + (H + M)) + R) _
    (Q'.eqv_symm (Q'.add_assoc_eqv T (H + M) R)) ?_
  refine Q'.eqv_trans _ (((T + H) + M) + R) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ R
      (Q'.eqv_symm (Q'.add_assoc_eqv T H M))
  refine Q'.eqv_trans _ ((T + H) + (M + R)) _
    (Q'.add_assoc_eqv (T + H) M R) ?_
  refine Q'.eqv_trans _ ((T + H) + (R + M)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left (T + H) _ _ (Q'.add_comm_eqv M R)
  refine Q'.eqv_trans _ (((T + H) + R) + M) _
    (Q'.eqv_symm (Q'.add_assoc_eqv (T + H) R M)) ?_
  exact Q'.add_eqv_congr_right _ _ M (Q'.add_assoc_eqv T H R)

/-- Exact relation between the true physical debt and the invalid
middle-deleted strengthening. -/
theorem lowerSixRecoveryClearedAbelPhysicalDebt_eqv_noMiddle_add_middle
    (k c s : Nat) :
    lowerSixRecoveryClearedAbelPhysicalDebt k c s ≈
      lowerSixRecoveryClearedAbelNoMiddleDebt k c s +
        lowerSixRecoveryClearedAbelMiddle k
          (lowerSixRecoveryPhysicalPeakIndex c) s := by
  unfold lowerSixRecoveryClearedAbelPhysicalDebt
    lowerSixRecoveryClearedAbelNoMiddleDebt
  exact physical_middle_insertion _ _ _ _

/-! ## Exact denominator-cleared payment residual -/

/-- Reserve minus the literal physical payment debt, in the single positive
prefix-denominator coordinate. -/
def lowerSixRecoveryClearedAbelPhysicalPaymentResidual
    (k c s : Nat) : Q' :=
  let D := lowerSixRecoveryLinearCarrierPrefixDen (k + 1)
  lowerSixRecoveryLinearScaleReserve k c * D +
    -(lowerSixRecoveryClearedAbelPhysicalDebt k c s +
      -(lowerSixRecoveryTerminalDrop k (2 * c) * D))

private theorem drift_of_neg_drift_eqv
    (D A T : Q') (h : -D ≈ A + -T) :
    D ≈ -A + T := by
  refine Q'.eqv_trans _ (-(-D)) _
    (Q'.eqv_symm (Q'.neg_neg_eqv D)) ?_
  refine Q'.eqv_trans _ (-(A + -T)) _
    (Q'.neg_eqv_congr _ _ h) ?_
  refine Q'.eqv_trans _ (-A + -(-T)) _
    (Q'.neg_add_eqv A (-T)) ?_
  exact Q'.add_eqv_congr_left (-A) _ _ (Q'.neg_neg_eqv T)

private theorem neg_add_pos_eqv_neg_sub (A B : Q') :
    -A + B ≈ -(A + -B) := by
  exact Q'.eqv_symm (Q'.eqv_trans _ (-A + -(-B)) _
    (Q'.neg_add_eqv A (-B))
    (Q'.add_eqv_congr_left (-A) _ _ (Q'.neg_neg_eqv B)))

private theorem physical_payment_residual_algebra
    (R A T D P : Q') (hAP : A * D ≈ P) :
    (R + (-A + T)) * D ≈
      R * D + -(P + -(T * D)) := by
  refine Q'.eqv_trans _
    (R * D + (-A + T) * D) _ (Q'.add_mul_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (R * D + ((-A) * D + T * D)) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_mul_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (R * D + (-(A * D) + T * D)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.neg_mul_eqv A D))
  refine Q'.eqv_trans _
    (R * D + (-P + T * D)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.neg_eqv_congr _ _ hAP))
  exact Q'.add_eqv_congr_left _ _ _ (neg_add_pos_eqv_neg_sub P (T * D))

/-- The denominator-cleared payment residual is exactly the original
fixed-center drop multiplied by the positive clearing denominator.  This
pins the normalization and prevents a hidden strengthening or weakening. -/
theorem lowerSixRecoveryFixedCenterDrop_mul_den_eqv_physicalPaymentResidual
    {k c s : Nat} (hc : 1 ≤ c)
    (hrs : lowerSixRecoveryPhysicalPeakIndex c ≤ s)
    (hsL : s ≤ 2 * c - 1) :
    lowerSixFixedCenterDrop k c *
        lowerSixRecoveryLinearCarrierPrefixDen (k + 1) ≈
      lowerSixRecoveryClearedAbelPhysicalPaymentResidual k c s := by
  let D := lowerSixRecoveryLinearCarrierPrefixDen (k + 1)
  let R := lowerSixRecoveryLinearScaleReserve k c
  let A := lowerSixRecoveryLinearComplementDebt k c
  let T := lowerSixRecoveryTerminalDrop k (2 * c)
  let P := lowerSixRecoveryClearedAbelPhysicalDebt k c s
  let F := lowerSixFixedCenterDrop k c
  let E := lowerSixRecoveryLinearDriftDebt k c
  have hF : F ≈ R + E := by
    dsimp only [F, R, E]
    exact lowerSixFixedCenterDrop_eqv_linearReserve_add_debt k c
  have hneg : -E ≈ A + -T := by
    dsimp only [E, A, T]
    exact neg_lowerSixRecoveryLinearDriftDebt_eqv_complementDebt_sub_terminal
      k c
  have hE : E ≈ -A + T := drift_of_neg_drift_eqv E A T hneg
  have hclear : A * D ≈ P := by
    refine Q'.eqv_trans _ (lowerSixRecoveryClearedAbelDebt k c) _ ?_ ?_
    · dsimp only [A, D]
      exact lowerSixRecoveryLinearComplementDebt_mul_den_eqv_clearedAbel hc
    · dsimp only [P]
      exact lowerSixRecoveryClearedAbelDebt_eqv_physicalDebt hrs hsL
  refine Q'.eqv_trans _ ((R + E) * D) _
    (Q'.mul_eqv_congr_right _ _ D hF) ?_
  refine Q'.eqv_trans _ ((R + (-A + T)) * D) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ D
      (Q'.add_eqv_congr_left R _ _ hE)
  dsimp only [R, A, T, D, P]
  exact Q'.eqv_trans _ _ _
    (physical_payment_residual_algebra R A T D P hclear)
    (Q'.eqv_refl _)

/-- Consequently the displayed physical `hpay` inequality is equivalent,
not merely sufficient, to the original fixed-center sign. -/
theorem lowerSixRecoveryPhysicalThreeBandPayment_iff_fixedCenterDrop_nonnegative
    {k c s : Nat} (hc : 1 ≤ c)
    (hrs : lowerSixRecoveryPhysicalPeakIndex c ≤ s)
    (hsL : s ≤ 2 * c - 1) :
    (lowerSixRecoveryClearedAbelPhysicalDebt k c s +
          -(lowerSixRecoveryTerminalDrop k (2 * c) *
            lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) ≤
        lowerSixRecoveryLinearScaleReserve k c *
          lowerSixRecoveryLinearCarrierPrefixDen (k + 1)) ↔
      (0 : Q') ≤ lowerSixFixedCenterDrop k c := by
  let D := lowerSixRecoveryLinearCarrierPrefixDen (k + 1)
  let F := lowerSixFixedCenterDrop k c
  let P := lowerSixRecoveryClearedAbelPhysicalPaymentResidual k c s
  have hDpos : (0 : Q') < D := by
    dsimp only [D]
    exact lowerSixRecoveryLinearCarrierPrefixDen_pos (k + 1)
  have hD0 : (0 : Q') ≤ D := Q'.le_of_lt hDpos
  have hFP : F * D ≈ P := by
    dsimp only [F, D, P]
    exact lowerSixRecoveryFixedCenterDrop_mul_den_eqv_physicalPaymentResidual
      hc hrs hsL
  constructor
  · intro hpay
    have hP0 : (0 : Q') ≤ P := by
      dsimp only [P]
      unfold lowerSixRecoveryClearedAbelPhysicalPaymentResidual
      exact Q'.sub_nonneg_of_le hpay
    have hFD0 : (0 : Q') ≤ F * D :=
      Q'.le_trans' _ _ _ hP0 (Q'.ge_of_eqv hFP)
    have hDF0 : (0 : Q') ≤ D * F :=
      Q'.le_trans' _ _ _ hFD0
        (Q'.ge_of_eqv (Q'.mul_comm_eqv D F))
    exact Q'.nonneg_of_mul_pos hDpos hDF0
  · intro hF0
    have hFD0 : (0 : Q') ≤ F * D := Q'.mul_nonneg _ _ hF0 hD0
    have hP0 : (0 : Q') ≤ P :=
      Q'.le_trans' _ _ _ hFD0 (Q'.le_of_eqv hFP)
    dsimp only [P] at hP0
    unfold lowerSixRecoveryClearedAbelPhysicalPaymentResidual at hP0
    exact Q'.le_of_sub_nonneg hP0

/-! ## Exact fence: the middle band is load-bearing -/

theorem lowerSixRecoveryNoMiddleFence_sameCenterCell :
    LowerSixWithinCenterCell (126 + 2) 16 := by
  unfold LowerSixWithinCenterCell
  decide

theorem lowerSixRecoveryNoMiddleFence_before :
    lowerSixRecoveryLinearCarrierPrefixNumerator 127 11 ≤ (0 : Q') := by
  decide

theorem lowerSixRecoveryNoMiddleFence_after :
    (0 : Q') ≤
      lowerSixRecoveryLinearCarrierPrefixNumerator 127 (11 + 1) := by
  decide

/-- At this exact same-center crossing the middle band is strictly favorable. -/
theorem lowerSixRecoveryNoMiddleFence_middle_strictly_negative :
    lowerSixRecoveryClearedAbelMiddle 126
      (lowerSixRecoveryPhysicalPeakIndex 16) 11 < (0 : Q') := by
  decide

/-- The full, lossless cleared payment succeeds at the same exact cell. -/
theorem lowerSixRecoveryNoMiddleFence_full_payment :
    lowerSixRecoveryClearedAbelPhysicalDebt 126 16 11 +
          -(lowerSixRecoveryTerminalDrop 126 (2 * 16) *
            lowerSixRecoveryLinearCarrierPrefixDen 127) ≤
        lowerSixRecoveryLinearScaleReserve 126 16 *
          lowerSixRecoveryLinearCarrierPrefixDen 127 := by
  decide

/-- Deleting the strictly negative middle band makes that successful payment
false.  Thus any uniform proof must retain it or supply an equally sharp block
cancellation. -/
theorem lowerSixRecoveryNoMiddleFence_truncated_payment_fails :
    ¬ (lowerSixRecoveryClearedAbelNoMiddleDebt 126 16 11 +
          -(lowerSixRecoveryTerminalDrop 126 (2 * 16) *
            lowerSixRecoveryLinearCarrierPrefixDen 127) ≤
        lowerSixRecoveryLinearScaleReserve 126 16 *
          lowerSixRecoveryLinearCarrierPrefixDen 127) := by
  decide

#print axioms lowerSixRecoveryClearedAbelMiddle_add_tail_eqv_suffixVariation
#print axioms lowerSixRecoveryClearedAbelPhysicalDebt_eqv_head_add_suffixBlock
#print axioms lowerSixRecoveryClearedAbelPhysicalDebt_eqv_noMiddle_add_middle
#print axioms lowerSixRecoveryFixedCenterDrop_mul_den_eqv_physicalPaymentResidual
#print axioms lowerSixRecoveryPhysicalThreeBandPayment_iff_fixedCenterDrop_nonnegative
#print axioms lowerSixRecoveryNoMiddleFence_sameCenterCell
#print axioms lowerSixRecoveryNoMiddleFence_before
#print axioms lowerSixRecoveryNoMiddleFence_after
#print axioms lowerSixRecoveryNoMiddleFence_middle_strictly_negative
#print axioms lowerSixRecoveryNoMiddleFence_full_payment
#print axioms lowerSixRecoveryNoMiddleFence_truncated_payment_fails

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryLinearAbelPhysicalBlockCancellation
