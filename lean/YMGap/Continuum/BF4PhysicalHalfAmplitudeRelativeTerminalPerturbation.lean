/-
# Relative terminal-kernel perturbation for the physical BF4 amplitude

An exact terminal-smoothing identity is stronger than the physical
finite-cutoff comparison is likely to provide.  This file proves the robust
replacement.

Suppose a nonnegative physical kernel `A` and an ideal grouped kernel `G`
obey

  lower * G <= A <= upper * G,
  upper <= errorSpread * lower.

If `G` has projective spread `terminalSpread`, then `A` has projective spread
`errorSpread * terminalSpread`.  The proof is division-free and permits
zeros.  The spacing-uniform BF4 package combines this perturbative spread
with the exact terminal-smoothing certificate and feeds both posterior
eighths.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalSmoothingBridge
import YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination

namespace YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4AnchoredProjectiveProfileHarnack
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4PhysicalHalfAmplitudeProjectiveClosure
open YMGap.Continuum.BF4PhysicalHalfAmplitudeTerminalSmoothingBridge
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4TerminalSmoothingProjective
open YMGap.Continuum.RationalCrossRatioDiameter
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic relative-envelope theorem -/

/-- A two-sided multiplicative comparison enlarges projective spread by at
most the comparison spread. -/
theorem crossRatio_of_relative_kernel_envelope
    {Source Target : Type}
    (physical ideal : Source → Target → Q')
    (sources : List Source) (targets : List Target)
    (terminalSpread lower upper errorSpread : Q')
    (physical_nonnegative :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          (0 : Q') ≤ physical source target)
    (ideal_nonnegative :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          (0 : Q') ≤ ideal source target)
    (lower_nonnegative : (0 : Q') ≤ lower)
    (upper_nonnegative : (0 : Q') ≤ upper)
    (errorSpread_nonnegative :
      (0 : Q') ≤ errorSpread)
    (terminalSpread_nonnegative :
      (0 : Q') ≤ terminalSpread)
    (upper_le_error_lower :
      upper ≤ errorSpread * lower)
    (lower_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          lower * ideal source target ≤
            physical source target)
    (upper_bound :
      ∀ source, source ∈ sources →
        ∀ target, target ∈ targets →
          physical source target ≤
            upper * ideal source target)
    (ideal_cross_ratio :
      ∀ first, first ∈ sources →
        ∀ second, second ∈ sources →
          ∀ left, left ∈ targets →
            ∀ right, right ∈ targets →
              ideal first left * ideal second right ≤
                (terminalSpread * terminalSpread) *
                  (ideal first right *
                    ideal second left)) :
    ∀ first, first ∈ sources →
      ∀ second, second ∈ sources →
        ∀ left, left ∈ targets →
          ∀ right, right ∈ targets →
            physical first left * physical second right ≤
              ((errorSpread * terminalSpread) *
                  (errorSpread * terminalSpread)) *
                (physical first right *
                  physical second left) := by
  intro first first_mem second second_mem
    left left_mem right right_mem
  let idealForward :=
    ideal first left * ideal second right
  let idealReverse :=
    ideal first right * ideal second left
  let terminalSquare :=
    terminalSpread * terminalSpread
  let errorSquare :=
    errorSpread * errorSpread
  let lowerSquare :=
    lower * lower
  let upperSquare :=
    upper * upper
  have hupperFirst :=
    upper_bound first first_mem left left_mem
  have hupperSecond :=
    upper_bound second second_mem right right_mem
  have hupperIdealFirst_nonnegative :
      (0 : Q') ≤ upper * ideal first left :=
    Q'.mul_nonneg _ _ upper_nonnegative
      (ideal_nonnegative first first_mem left left_mem)
  have hphysicalSecond_nonnegative :
      (0 : Q') ≤ physical second right :=
    physical_nonnegative second second_mem right right_mem
  have hphysical_to_upper :
      physical first left * physical second right ≤
        (upper * ideal first left) *
          (upper * ideal second right) :=
    Q'.mul_le_mul_of_nonneg
      hupperFirst hupperSecond
      hupperIdealFirst_nonnegative
      hphysicalSecond_nonnegative
  have hupper_reindex :
      (upper * ideal first left) *
          (upper * ideal second right) ≈
        upperSquare * idealForward := by
    dsimp [upperSquare, idealForward]
    q_ring
  have hterminalSquare_nonnegative :
      (0 : Q') ≤ terminalSquare :=
    Q'.mul_nonneg _ _
      terminalSpread_nonnegative
      terminalSpread_nonnegative
  have hupperSquare_nonnegative :
      (0 : Q') ≤ upperSquare :=
    Q'.mul_nonneg _ _
      upper_nonnegative upper_nonnegative
  have hidealCross :=
    ideal_cross_ratio
      first first_mem second second_mem
      left left_mem right right_mem
  have hidealScaled :
      upperSquare * idealForward ≤
        upperSquare *
          (terminalSquare * idealReverse) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hidealCross hupperSquare_nonnegative
  have herrorLower_nonnegative :
      (0 : Q') ≤ errorSpread * lower :=
    Q'.mul_nonneg _ _
      errorSpread_nonnegative lower_nonnegative
  have hupperSquare_le :
      upperSquare ≤ errorSquare * lowerSquare := by
    have hmul :=
      Q'.mul_le_mul_of_nonneg
        upper_le_error_lower
        upper_le_error_lower
        herrorLower_nonnegative
        upper_nonnegative
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (by
        dsimp [upperSquare, errorSquare, lowerSquare]
        q_ring))
  have hidealReverse_nonnegative :
      (0 : Q') ≤ idealReverse :=
    Q'.mul_nonneg _ _
      (ideal_nonnegative first first_mem right right_mem)
      (ideal_nonnegative second second_mem left left_mem)
  have htail_nonnegative :
      (0 : Q') ≤ terminalSquare * idealReverse :=
    Q'.mul_nonneg _ _
      hterminalSquare_nonnegative
      hidealReverse_nonnegative
  have hbudgetScaled :
      upperSquare *
          (terminalSquare * idealReverse) ≤
        (errorSquare * lowerSquare) *
          (terminalSquare * idealReverse) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _
      hupperSquare_le htail_nonnegative
  have hlowerFirst :=
    lower_bound first first_mem right right_mem
  have hlowerSecond :=
    lower_bound second second_mem left left_mem
  have hlowerIdealSecond_nonnegative :
      (0 : Q') ≤ lower * ideal second left :=
    Q'.mul_nonneg _ _ lower_nonnegative
      (ideal_nonnegative second second_mem left left_mem)
  have hlowerProduct :
      (lower * ideal first right) *
          (lower * ideal second left) ≤
        physical first right * physical second left :=
    Q'.mul_le_mul_of_nonneg
      hlowerFirst hlowerSecond
      (physical_nonnegative first first_mem right right_mem)
      hlowerIdealSecond_nonnegative
  have hlower_reindex :
      lowerSquare * idealReverse ≈
        (lower * ideal first right) *
          (lower * ideal second left) := by
    dsimp [lowerSquare, idealReverse]
    q_ring
  have hlowerReverse :
      lowerSquare * idealReverse ≤
        physical first right * physical second left :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv hlower_reindex)
      hlowerProduct
  have hcoefficient_nonnegative :
      (0 : Q') ≤ errorSquare * terminalSquare :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        errorSpread_nonnegative errorSpread_nonnegative)
      hterminalSquare_nonnegative
  have hreverseScaled :
      (errorSquare * terminalSquare) *
          (lowerSquare * idealReverse) ≤
        (errorSquare * terminalSquare) *
          (physical first right * physical second left) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hlowerReverse hcoefficient_nonnegative
  refine Q'.le_trans' _ _ _ hphysical_to_upper
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hupper_reindex)
      (Q'.le_trans' _ _ _ hidealScaled
        (Q'.le_trans' _ _ _ hbudgetScaled
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv ?_)
            (Q'.le_trans' _ _ _ hreverseScaled
              (Q'.le_of_eqv ?_))))))
  · dsimp [errorSquare, lowerSquare,
      terminalSquare, idealReverse]
    q_ring
  · dsimp [errorSquare, terminalSquare]
    q_ring

/-! ## 2. An explicit split of the `65/64` budget -/

/-- Equal rational budget allocated to terminal smoothing and to the
physical/ideal perturbation. -/
def splitProjectiveCeiling : Q' :=
  Q'.mkPos 257 256 (by decide)

theorem splitProjectiveCeiling_nonnegative :
    (0 : Q') ≤ splitProjectiveCeiling := by
  decide

/-- Two squared spreads bounded by `257/256` fit strictly inside the final
`65/64` squared-spread budget. -/
theorem combined_spread_square_le_of_split
    {errorSpread terminalSpread : Q'}
    (terminalSpread_nonnegative :
      (0 : Q') ≤ terminalSpread)
    (error_square_le :
      errorSpread * errorSpread ≤
        splitProjectiveCeiling)
    (terminal_square_le :
      terminalSpread * terminalSpread ≤
        splitProjectiveCeiling) :
    (errorSpread * terminalSpread) *
        (errorSpread * terminalSpread) ≤
      anchoredProjectiveCeiling := by
  have hterminalSquare_nonnegative :
      (0 : Q') ≤ terminalSpread * terminalSpread :=
    Q'.mul_nonneg _ _
      terminalSpread_nonnegative
      terminalSpread_nonnegative
  have hsplit_nonnegative :
      (0 : Q') ≤ splitProjectiveCeiling :=
    splitProjectiveCeiling_nonnegative
  have hproduct :
      (errorSpread * errorSpread) *
          (terminalSpread * terminalSpread) ≤
        splitProjectiveCeiling *
          splitProjectiveCeiling :=
    Q'.mul_le_mul_of_nonneg
      error_square_le terminal_square_le
      hsplit_nonnegative
      hterminalSquare_nonnegative
  refine Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv ?_)
      hproduct)
    ?_
  · q_ring
  unfold splitProjectiveCeiling
    anchoredProjectiveCeiling
  decide

/-! ## 3. From an entry estimate to the multiplicative envelope -/

/-- A relative absolute entry error gives the exact two-sided
multiplicative envelope used above. -/
theorem multiplicative_envelope_of_relative_abs_error
    (physical ideal delta : Q')
    (error :
      Q'.abs (physical + -ideal) ≤
        delta * ideal) :
    ((1 : Q') + -delta) * ideal ≤ physical ∧
      physical ≤ ((1 : Q') + delta) * ideal := by
  have hupperRaw :
      physical ≤ ideal + delta * ideal :=
    ExpNeg.le_add_of_abs_sub_le error
  have hcommuted :
      Q'.abs (ideal + -physical) ≤
        delta * ideal := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (ExpNeg.abs_sub_comm
            physical ideal)))
      error
  have hlowerRaw :
      ideal ≤ physical + delta * ideal :=
    ExpNeg.le_add_of_abs_sub_le hcommuted
  have hlowerRawComm :
      ideal ≤ delta * ideal + physical :=
    Q'.le_trans' _ _ _
      hlowerRaw
      (Q'.le_of_eqv
        (Q'.add_comm_eqv physical (delta * ideal)))
  have hlower :
      ideal + -(delta * ideal) ≤ physical :=
    Q'.sub_le_of_le_add hlowerRawComm
  have hlowerFactor :
      ((1 : Q') + -delta) * ideal ≈
        ideal + -(delta * ideal) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (1 : Q') (-delta) ideal) ?_
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv ideal)
      (Q'.neg_mul_eqv delta ideal)
  have hupperFactor :
      ideal + delta * ideal ≈
        ((1 : Q') + delta) * ideal := by
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (1 : Q') delta ideal) ?_)
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv ideal)
      (Q'.eqv_refl (delta * ideal))
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hlowerFactor) hlower
  · exact Q'.le_trans' _ _ _
      hupperRaw (Q'.le_of_eqv hupperFactor)

/-- One part in `2048` is the explicit physical/ideal relative entry
tolerance used by the split projective budget. -/
def physicalRelativeErrorTolerance : Q' :=
  Q'.mkPos 1 2048 (by decide)

/-- Exact ratio `(1+delta)/(1-delta)` for
`delta = 1/2048`. -/
def physicalRelativeErrorSpread : Q' :=
  Q'.mkPos 2049 2047 (by decide)

theorem physicalRelativeLower_nonnegative :
    (0 : Q') ≤
      (1 : Q') + -physicalRelativeErrorTolerance := by
  decide

theorem physicalRelativeUpper_nonnegative :
    (0 : Q') ≤
      (1 : Q') + physicalRelativeErrorTolerance := by
  decide

theorem physicalRelativeErrorSpread_nonnegative :
    (0 : Q') ≤ physicalRelativeErrorSpread := by
  decide

theorem physicalRelativeUpper_le_spread_mul_lower :
    (1 : Q') + physicalRelativeErrorTolerance ≤
      physicalRelativeErrorSpread *
        ((1 : Q') + -physicalRelativeErrorTolerance) := by
  decide

theorem physicalRelativeErrorSpread_square_le_split :
    physicalRelativeErrorSpread *
        physicalRelativeErrorSpread ≤
      splitProjectiveCeiling := by
  decide

/-- An absolute `delta * floor` estimate becomes the required relative
estimate whenever `floor` is a pointwise lower bound for the ideal entry. -/
theorem relative_abs_error_of_floor
    {physical ideal floor delta : Q'}
    (delta_nonnegative : (0 : Q') ≤ delta)
    (floor_le_ideal : floor ≤ ideal)
    (absolute_error :
      Q'.abs (physical + -ideal) ≤
        delta * floor) :
    Q'.abs (physical + -ideal) ≤
      delta * ideal := by
  exact Q'.le_trans' _ _ _
    absolute_error
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      floor_le_ideal delta_nonnegative)

/-! ## 4. Spacing-uniform approximate terminal factorization -/

/-- The physical half-amplitude is uniformly trapped in a multiplicative
window around one terminal-smoothed positive kernel. -/
structure MatchedPhysicalHalfAmplitudeApproxTerminalSmoothingRows
    (Middle : Nat → Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  middles :
    ∀ scale, List (Middle scale)
  prefixWeight :
    ∀ scale, EdgeLabelling → Middle scale → Q'
  terminal :
    ∀ scale, Middle scale → EdgeLabelling → Q'
  prefixRows :
    ∀ scale,
      PositivePrefixRows
        (prefixWeight scale)
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (middles scale)
  terminalCertificate :
    ∀ scale,
      FiniteCrossRatioDiameterCertificate
        (terminal scale)
        (middles scale)
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
  lower :
    Nat → Q'
  upper :
    Nat → Q'
  errorSpread :
    Nat → Q'
  lower_nonnegative :
    ∀ scale, (0 : Q') ≤ lower scale
  upper_nonnegative :
    ∀ scale, (0 : Q') ≤ upper scale
  errorSpread_nonnegative :
    ∀ scale, (0 : Q') ≤ errorSpread scale
  upper_le_error_lower :
    ∀ scale,
      upper scale ≤
        errorSpread scale * lower scale
  combined_spread_square_le :
    ∀ scale,
      (errorSpread scale *
          (terminalCertificate scale).spread) *
          (errorSpread scale *
            (terminalCertificate scale).spread) ≤
        anchoredProjectiveCeiling
  physical_lower :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            lower scale *
                terminalSmoothedKernel
                  (prefixWeight scale)
                  (terminal scale)
                  (middles scale)
                  source boundary ≤
              centralHalfAmplitude
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) source boundary
  physical_upper :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            centralHalfAmplitude
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) source boundary ≤
              upper scale *
                terminalSmoothedKernel
                  (prefixWeight scale)
                  (terminal scale)
                  (middles scale)
                  source boundary

namespace MatchedPhysicalHalfAmplitudeApproxTerminalSmoothingRows

/-- Relative terminal comparison supplies the one physical half-amplitude
projective field with the product spread. -/
def toHalfAmplitudeProjectiveRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalHalfAmplitudeApproxTerminalSmoothingRows
        Middle family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedHalfAmplitudeProjectiveRows
      family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.calibrated_harnack
  spread := fun scale =>
    data.errorSpread scale *
      (data.terminalCertificate scale).spread
  spread_square_le := data.combined_spread_square_le
  half_amplitude_cross_ratio := by
    intro scale
    let ideal :=
      terminalSmoothedKernel
        (data.prefixWeight scale)
        (data.terminal scale)
        (data.middles scale)
    let idealCertificate :=
      terminalSmoothedCertificate
        (data.terminalCertificate scale)
        (data.prefixRows scale)
    exact
      crossRatio_of_relative_kernel_envelope
        (centralHalfAmplitude
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        ideal
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (data.terminalCertificate scale).spread
        (data.lower scale)
        (data.upper scale)
        (data.errorSpread scale)
        (fun source _ boundary _ =>
          centralHalfAmplitude_nonnegative
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) source boundary)
        (fun source source_mem boundary boundary_mem =>
          Q'.le_of_lt
            (idealCertificate.strictlyPositive
              source source_mem boundary boundary_mem))
        (data.lower_nonnegative scale)
        (data.upper_nonnegative scale)
        (data.errorSpread_nonnegative scale)
        (Q'.le_of_lt
          (data.terminalCertificate scale).spread_pos)
        (data.upper_le_error_lower scale)
        (data.physical_lower scale)
        (data.physical_upper scale)
        idealCertificate.crossRatioBound

/-- The approximate physical/terminal comparison therefore inhabits both
spacing-uniform physical rowwise eighths. -/
def toRowwiseEighthEstimates
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalHalfAmplitudeApproxTerminalSmoothingRows
        Middle family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toHalfAmplitudeProjectiveRows
    |>.toRowwiseEighthEstimates

end MatchedPhysicalHalfAmplitudeApproxTerminalSmoothingRows

/-! ## 5. The concrete terminal-floor / entry-error interface -/

/-- The two analytic estimates still required from the grouped physical
BF4 kernel:

1. the terminal-smoothed ideal kernel has a positive scale-dependent
   pointwise floor;
2. the physical-minus-ideal entry error is at most `1/2048` of that floor.

The floor may shrink with the cutoff and carrier size.  This is the
division-free form of an `epsilon / N` estimate: no reciprocal and no
strict positivity cancellation is needed in the downstream proof. -/
structure MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows
    (Middle : Nat → Type)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  calibrated_harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale) 0
  middles :
    ∀ scale, List (Middle scale)
  prefixWeight :
    ∀ scale, EdgeLabelling → Middle scale → Q'
  terminal :
    ∀ scale, Middle scale → EdgeLabelling → Q'
  prefixRows :
    ∀ scale,
      PositivePrefixRows
        (prefixWeight scale)
        (centralPositiveHalfStates
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
        (middles scale)
  terminalCertificate :
    ∀ scale,
      FiniteCrossRatioDiameterCertificate
        (terminal scale)
        (middles scale)
        (centralBoundaryChannels
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale))
  terminal_spread_square_le_split :
    ∀ scale,
      (terminalCertificate scale).spread *
          (terminalCertificate scale).spread ≤
        splitProjectiveCeiling
  idealFloor :
    Nat → Q'
  ideal_floor :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            idealFloor scale ≤
              terminalSmoothedKernel
                (prefixWeight scale)
                (terminal scale)
                (middles scale)
                source boundary
  physical_error :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        ∀ boundary,
          boundary ∈
              centralBoundaryChannels
                (matchedAllSpinCutoff family coupling scale)
                (halfExtent scale) →
            Q'.abs
                (centralHalfAmplitude
                    (matchedAllSpinWeight family coupling scale)
                    (matchedAllSpinCutoff family coupling scale)
                    (halfExtent scale) source boundary +
                  -terminalSmoothedKernel
                    (prefixWeight scale)
                    (terminal scale)
                    (middles scale)
                    source boundary) ≤
              physicalRelativeErrorTolerance *
                idealFloor scale

namespace MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows

/-- The terminal floor and `1/2048` absolute entry estimate construct the
two-sided relative terminal perturbation package with no division. -/
def toApproxTerminalSmoothingRows
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows
        Middle family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicalHalfAmplitudeApproxTerminalSmoothingRows
      Middle family law spacing coupling
      halfExtent diagonalOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  calibrated_harnack := data.calibrated_harnack
  middles := data.middles
  prefixWeight := data.prefixWeight
  terminal := data.terminal
  prefixRows := data.prefixRows
  terminalCertificate := data.terminalCertificate
  lower := fun _ =>
    (1 : Q') + -physicalRelativeErrorTolerance
  upper := fun _ =>
    (1 : Q') + physicalRelativeErrorTolerance
  errorSpread := fun _ =>
    physicalRelativeErrorSpread
  lower_nonnegative := fun _ =>
    physicalRelativeLower_nonnegative
  upper_nonnegative := fun _ =>
    physicalRelativeUpper_nonnegative
  errorSpread_nonnegative := fun _ =>
    physicalRelativeErrorSpread_nonnegative
  upper_le_error_lower := fun _ =>
    physicalRelativeUpper_le_spread_mul_lower
  combined_spread_square_le := fun scale =>
    combined_spread_square_le_of_split
      (Q'.le_of_lt
        (data.terminalCertificate scale).spread_pos)
      physicalRelativeErrorSpread_square_le_split
      (data.terminal_spread_square_le_split scale)
  physical_lower := by
    intro scale source source_mem boundary boundary_mem
    let physical :=
      centralHalfAmplitude
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) source boundary
    let ideal :=
      terminalSmoothedKernel
        (data.prefixWeight scale)
        (data.terminal scale)
        (data.middles scale)
        source boundary
    have hrelative :
        Q'.abs (physical + -ideal) ≤
          physicalRelativeErrorTolerance * ideal :=
      relative_abs_error_of_floor
        (by decide)
        (data.ideal_floor
          scale source source_mem boundary boundary_mem)
        (data.physical_error
          scale source source_mem boundary boundary_mem)
    exact
      (multiplicative_envelope_of_relative_abs_error
        physical ideal
        physicalRelativeErrorTolerance
        hrelative).1
  physical_upper := by
    intro scale source source_mem boundary boundary_mem
    let physical :=
      centralHalfAmplitude
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale) source boundary
    let ideal :=
      terminalSmoothedKernel
        (data.prefixWeight scale)
        (data.terminal scale)
        (data.middles scale)
        source boundary
    have hrelative :
        Q'.abs (physical + -ideal) ≤
          physicalRelativeErrorTolerance * ideal :=
      relative_abs_error_of_floor
        (by decide)
        (data.ideal_floor
          scale source source_mem boundary boundary_mem)
        (data.physical_error
          scale source source_mem boundary boundary_mem)
    exact
      (multiplicative_envelope_of_relative_abs_error
        physical ideal
        physicalRelativeErrorTolerance
        hrelative).2

/-- The concrete terminal floor and entry estimate therefore discharge
both spacing-uniform physical `1/8` fields. -/
def toRowwiseEighthEstimates
    {Middle : Nat → Type}
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows
        Middle family law spacing coupling
        halfExtent diagonalOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling
      halfExtent diagonalOrder (fun _ => 0) :=
  data.toApproxTerminalSmoothingRows
    |>.toRowwiseEighthEstimates

end MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows

end YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation.crossRatio_of_relative_kernel_envelope
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation.combined_spread_square_le_of_split
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation.multiplicative_envelope_of_relative_abs_error
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation.relative_abs_error_of_floor
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation.MatchedPhysicalHalfAmplitudeApproxTerminalSmoothingRows.toHalfAmplitudeProjectiveRows
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation.MatchedPhysicalHalfAmplitudeApproxTerminalSmoothingRows.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation.MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows.toApproxTerminalSmoothingRows
#print axioms YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation.MatchedPhysicalHalfAmplitudeTerminalFloorErrorRows.toRowwiseEighthEstimates
