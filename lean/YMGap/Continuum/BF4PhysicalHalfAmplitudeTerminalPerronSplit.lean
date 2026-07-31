/-
# AF/Faraut Perron budget for the physical terminal split

The physical half-amplitude perturbation layer allocates the exact squared
projective budget

  terminalSpread^2 <= 257/256.

The existing AF/Faraut argument pays `1/64` at depth `46*bits+5`.  One
additional nonlinear Markov step pays one further factor `1/4`; hence
depth `46*bits+6` gives the exact terminal remainder `1/256`.

This file proves that arithmetic constructively and turns a same-kernel
Perron comparison

  spread^2 <= 1 + C_bits^2 q^(m-2)

into the terminal field required by
`MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows`.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
import YMGap.Continuum.BF4FarautJointCarrierAFBudget

namespace YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalPerronSplit

open YMGap.Constructive
open YMGap.Continuum.BF4FarautJointCarrierAFBudget
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.RationalCrossRatioDiameter

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact one-more-step budget -/

/-- The terminal half of the split projective budget is `1/256` above one. -/
def farautTerminalSplitTolerance : Q' :=
  Q'.mkPos 1 256 (by decide)

/-- One more step than the calibrated `1/64` Harnack depth. -/
def farautTerminalSplitRequiredDepth (bits : Nat) : Nat :=
  46 * bits + 6

theorem farautTerminalSplitRequiredDepth_sub_two (bits : Nat) :
    farautTerminalSplitRequiredDepth bits - 2 =
      46 * bits + 4 := by
  unfold farautTerminalSplitRequiredDepth
  omega

theorem one_add_farautTerminalSplitTolerance_eqv_splitProjectiveCeiling :
    (1 : Q') + farautTerminalSplitTolerance ≈
      splitProjectiveCeiling := by
  unfold farautTerminalSplitTolerance splitProjectiveCeiling
  decide

/-- If `q <= 1/4`, four surplus powers after the Faraut cost leave exactly
the terminal tolerance `1/256`. -/
theorem fourPow_mul_qPow_le_terminalSplitTolerance
    {q : Q'} (hq0 : (0 : Q') ≤ q)
    (hqQuarter : q ≤ quarter)
    (K r : Nat) (hKr : K + 4 ≤ r) :
    four ^ K * q ^ r ≤
      farautTerminalSplitTolerance := by
  have hstrong :
      four ^ (K + 1) * q ^ r ≤
        farautHarnackTolerance :=
    fourPow_mul_qPow_le_harnackTolerance
      hq0 hqQuarter (K + 1) r (by omega)
  have hscaled :
      quarter *
          (four ^ (K + 1) * q ^ r) ≤
        quarter * farautHarnackTolerance :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hstrong (by
        unfold quarter
        decide)
  have hcancel :
      quarter * four ^ (K + 1) ≈
        four ^ K := by
    calc
      quarter * four ^ (K + 1) ≈
          quarter * (four ^ K * four ^ 1) :=
        Q'.mul_eqv_congr_left quarter _ _
          (Q'.pow_add_eqv four K 1)
      _ ≈
          (quarter * four ^ K) * four ^ 1 :=
        Q'.eqv_symm
          (Q'.mul_assoc_eqv
            quarter (four ^ K) (four ^ 1))
      _ ≈
          (four ^ K * quarter) * four ^ 1 :=
        Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_comm_eqv
            quarter (four ^ K))
      _ ≈
          four ^ K * (quarter * four ^ 1) :=
        Q'.mul_assoc_eqv
          (four ^ K) quarter (four ^ 1)
      _ ≈ four ^ K * 1 :=
        Q'.mul_eqv_congr_left
          (four ^ K) _ _ (by
            unfold quarter four
            decide)
      _ ≈ four ^ K :=
        Q'.mul_one_eqv _
  have hleft :
      quarter *
          (four ^ (K + 1) * q ^ r) ≈
        four ^ K * q ^ r := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          quarter (four ^ (K + 1)) (q ^ r)))
      (Q'.mul_eqv_congr_right _ _ _
        hcancel)
  have hright :
      quarter * farautHarnackTolerance ≈
        farautTerminalSplitTolerance := by
    unfold quarter farautHarnackTolerance
      farautTerminalSplitTolerance
    decide
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv hright))

/-! ## 2. Spacing-uniform Faraut/Perron terminal estimate -/

/-- At the exact terminal depth, the full two-sided retained Faraut cost
leaves a remainder at most `1/256`. -/
theorem faraut_perron_terminal_split_requiredDepth
    (bits : Nat) (qS : Q')
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter) :
    farautPerronSquare bits *
        qS ^
          (farautTerminalSplitRequiredDepth bits - 2) ≤
      farautTerminalSplitTolerance := by
  have hcap := farautPerronSquare_le_cap bits
  have hqpow :
      (0 : Q') ≤
        qS ^
          (farautTerminalSplitRequiredDepth bits - 2) :=
    Q'.pow_nonneg qS qS_nonnegative _
  have hproduct :
      farautPerronSquare bits *
          qS ^
            (farautTerminalSplitRequiredDepth bits - 2) ≤
        four ^ (46 * bits) *
          qS ^
            (farautTerminalSplitRequiredDepth bits - 2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hcap hqpow
  have hdepth :
      46 * bits + 4 ≤
        farautTerminalSplitRequiredDepth bits - 2 := by
    rw [farautTerminalSplitRequiredDepth_sub_two]
    exact Nat.le_refl _
  exact Q'.le_trans' _ _ _ hproduct
    (fourPow_mul_qPow_le_terminalSplitTolerance
      qS_nonnegative qS_le_quarter
      (46 * bits)
      (farautTerminalSplitRequiredDepth bits - 2)
      hdepth)

/-- Every larger physical depth inherits the same `1/256` terminal
remainder. -/
theorem faraut_perron_terminal_split_of_available_depth
    (bits : Nat) (qS : Q') (m : Nat)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautTerminalSplitRequiredDepth bits ≤ m) :
    farautPerronSquare bits *
        qS ^ (m - 2) ≤
      farautTerminalSplitTolerance := by
  have hcap := farautPerronSquare_le_cap bits
  have hqpow :
      (0 : Q') ≤ qS ^ (m - 2) :=
    Q'.pow_nonneg qS qS_nonnegative _
  have hproduct :
      farautPerronSquare bits *
          qS ^ (m - 2) ≤
        four ^ (46 * bits) *
          qS ^ (m - 2) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hcap hqpow
  have hdepth :
      46 * bits + 4 ≤ m - 2 := by
    unfold farautTerminalSplitRequiredDepth at depth_available
    omega
  exact Q'.le_trans' _ _ _ hproduct
    (fourPow_mul_qPow_le_terminalSplitTolerance
      qS_nonnegative qS_le_quarter
      (46 * bits) (m - 2) hdepth)

/-! ## 3. Direct producer for the terminal certificate field -/

/-- A same-terminal-kernel Perron estimate at the sharpened AF depth proves
exactly the squared-spread field consumed by the terminal-floor/error
certificate. -/
theorem terminal_spread_square_le_split_of_farautPerron
    {Source Target : Type}
    {kernel : Source → Target → Q'}
    {sources : List Source} {targets : List Target}
    (certificate :
      FiniteCrossRatioDiameterCertificate
        kernel sources targets)
    (bits : Nat) (qS : Q') (m : Nat)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (qS_le_quarter : qS ≤ quarter)
    (depth_available :
      farautTerminalSplitRequiredDepth bits ≤ m)
    (projectivePerron :
      certificate.spread * certificate.spread ≤
        (1 : Q') +
          farautPerronSquare bits *
            qS ^ (m - 2)) :
    certificate.spread * certificate.spread ≤
      splitProjectiveCeiling := by
  have hremainder :
      farautPerronSquare bits *
          qS ^ (m - 2) ≤
        farautTerminalSplitTolerance :=
    faraut_perron_terminal_split_of_available_depth
      bits qS m qS_nonnegative qS_le_quarter
      depth_available
  have hadd :
      (1 : Q') +
          farautPerronSquare bits *
            qS ^ (m - 2) ≤
        (1 : Q') + farautTerminalSplitTolerance :=
    Q'.add_le_add_left 1 _ _ hremainder
  exact Q'.le_trans' _ _ _ projectivePerron
    (Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        one_add_farautTerminalSplitTolerance_eqv_splitProjectiveCeiling))

/-- Scale-varying form of the sharpened terminal Perron theorem. -/
theorem terminal_spread_square_le_split_family
    {Source Target : Nat → Type}
    {kernel :
      ∀ scale, Source scale → Target scale → Q'}
    {sources : ∀ scale, List (Source scale)}
    {targets : ∀ scale, List (Target scale)}
    (certificate :
      ∀ scale,
        FiniteCrossRatioDiameterCertificate
          (kernel scale) (sources scale) (targets scale))
    (bits m : Nat → Nat) (qS : Nat → Q')
    (qS_nonnegative :
      ∀ scale, (0 : Q') ≤ qS scale)
    (qS_le_quarter :
      ∀ scale, qS scale ≤ quarter)
    (depth_available :
      ∀ scale,
        farautTerminalSplitRequiredDepth
            (bits scale) ≤
          m scale)
    (projectivePerron :
      ∀ scale,
        (certificate scale).spread *
            (certificate scale).spread ≤
          (1 : Q') +
            farautPerronSquare (bits scale) *
              qS scale ^ (m scale - 2)) :
    ∀ scale,
      (certificate scale).spread *
          (certificate scale).spread ≤
        splitProjectiveCeiling :=
  fun scale =>
    terminal_spread_square_le_split_of_farautPerron
      (certificate scale)
      (bits scale) (qS scale) (m scale)
      (qS_nonnegative scale)
      (qS_le_quarter scale)
      (depth_available scale)
      (projectivePerron scale)

end YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalPerronSplit

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalPerronSplit.fourPow_mul_qPow_le_terminalSplitTolerance
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalPerronSplit.faraut_perron_terminal_split_requiredDepth
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalPerronSplit.faraut_perron_terminal_split_of_available_depth
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalPerronSplit.terminal_spread_square_le_split_of_farautPerron
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalPerronSplit.terminal_spread_square_le_split_family
