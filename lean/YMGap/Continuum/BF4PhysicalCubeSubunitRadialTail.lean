/-
# Adaptive Gaussian radial tail at every positive subunit nome

The all-subunit BF4 self-return envelope has a nome-dependent prefactor but
the same Gaussian Casimir exponent as the strong-coupling envelope.  A
computed power cutoff chooses enough exponent gain to absorb the degree-twelve
shell growth.  Past the corresponding computed radius, the radial envelope
contracts by one half per shell.  Its actual (not unit-normalized) seed then
gives an explicit tolerance cutoff.

This is a finite radial summation theorem.  It makes no coupling-uniform,
operator-gap, continuum, or Clay claim.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4PhysicalCubeGaussianReturn
open YMGap.Continuum.BF4PhysicalCubeSubunitBoundarySumBound
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.PositiveContractionResidual
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero,
               Int.zero_add];
             try ac_rfl))

/-- The shell-counted all-subunit self-return envelope. -/
def subunitRadialEnvelope (w : Q') (radius : Nat) : Q' :=
  (subunitBoundaryFactor w * Q'.ofNat ((radius + 1) ^ 12)) *
    qpow w (gaussianExponent radius)

theorem subunitRadialEnvelope_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (radius : Nat) :
    (0 : Q') ≤ subunitRadialEnvelope w radius := by
  unfold subunitRadialEnvelope
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (subunitBoundaryFactor_nonnegative hw0)
      (zero_le_ofNat _))
    (qpow_nonneg w (Q'.le_of_lt hw0) _)

/-- `2^-13`: after the degree-twelve shell loss `2^12`, this leaves a
one-half contraction. -/
def subunitRadialPowerTarget : Q' := Q'.mkPos 1 8192 (by decide)

/-- Computed exponent gain sufficient at the literal nome. -/
def subunitRadialGain (w : Q') : Nat :=
  HKConvGen.powBaseCutoff w subunitRadialPowerTarget

/-- Radius after which one shell supplies the computed exponent gain. -/
def subunitRadialOnset (w : Q') : Nat :=
  Nat.max 1400 (36 * subunitRadialGain w)

private theorem qpow_eqv_pow (w : Q') : ∀ exponent,
    qpow w exponent ≈ w ^ exponent
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      have ih := qpow_eqv_pow w exponent
      show qpow w exponent * w ≈ w * w ^ exponent
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ w ih)
        (Q'.mul_comm_eqv (w ^ exponent) w)

theorem subunitRadialGain_power_le_target
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    qpow w (subunitRadialGain w) ≤ subunitRadialPowerTarget := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (qpow_eqv_pow w (subunitRadialGain w)))
    (HKConvGen.pow_base_le_cutoff hw0 hw1 (by
      unfold subunitRadialPowerTarget
      decide))

theorem subunitRadialGain_rate_le_half
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Q'.ofNat 4096 * qpow w (subunitRadialGain w) ≤ HalfPow.half := by
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (subunitRadialGain_power_le_target hw0 hw1)
      (zero_le_ofNat 4096))
    (Q'.le_of_eqv (by
      unfold subunitRadialPowerTarget HalfPow.half
      decide))

/-- At the computed onset, the next Gaussian exponent gains at least the
computed number of nome powers. -/
theorem subunitRadial_gaussianExponent_succ_gain
    (w : Q') (radius : Nat) (hradius : subunitRadialOnset w ≤ radius) :
    subunitRadialGain w + gaussianExponent radius ≤
      gaussianExponent (radius + 1) := by
  have hgain : 36 * subunitRadialGain w ≤ radius :=
    Nat.le_trans (Nat.le_max_right 1400 (36 * subunitRadialGain w)) hradius
  simp only [gaussianExponent, Nat.add_mul, Nat.mul_add, Nat.one_mul,
    Nat.mul_one]
  omega

private theorem natCast_mul (a b : Nat) :
    Q'.ofNat (a * b) ≈ Q'.ofNat a * Q'.ofNat b := by
  show Int.ofNat (a * b) * (1 : Int) =
    (Int.ofNat a * Int.ofNat b) * (1 : Int)
  rfl

/-- Every shell past the computed onset contracts by one half. -/
theorem subunitRadialEnvelope_succ_le_half
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius : Nat) (hradius : subunitRadialOnset w ≤ radius) :
    subunitRadialEnvelope w (radius + 1) ≤
      HalfPow.half * subunitRadialEnvelope w radius := by
  let gain := subunitRadialGain w
  have hdim : (radius + 1 + 1) ^ 12 ≤
      4096 * (radius + 1) ^ 12 := by
    have h := Nat.pow_le_pow_left
      (by omega : radius + 1 + 1 ≤ 2 * (radius + 1)) 12
    simpa only [Nat.mul_pow] using h
  have hd := Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hdim)
    (Q'.le_of_eqv (natCast_mul 4096 ((radius + 1) ^ 12)))
  have hp := qpow_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) _ _
    (subunitRadial_gaussianExponent_succ_gain w radius hradius)
  have h1 := Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hd
      (subunitBoundaryFactor_nonnegative hw0))
    (qpow_nonneg w (Q'.le_of_lt hw0) (gaussianExponent (radius + 1)))
  have h2 := Q'.mul_le_mul_of_nonneg_left _ _ _ hp
    (Q'.mul_nonneg _ _ (subunitBoundaryFactor_nonnegative hw0)
      (Q'.mul_nonneg _ _ (zero_le_ofNat 4096)
        (zero_le_ofNat ((radius + 1) ^ 12))))
  refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 ?_)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
      (qpow_add w gain (gaussianExponent radius)))) ?_
  refine Q'.le_trans' _
    ((Q'.ofNat 4096 * qpow w gain) * subunitRadialEnvelope w radius) _ ?_ ?_
  · apply Q'.le_of_eqv
    unfold subunitRadialEnvelope gain
    q_ring
  · exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (subunitRadialGain_rate_le_half hw0 hw1)
      (subunitRadialEnvelope_nonnegative hw0 radius)

private theorem twice_half (value : Q') :
    Q'.ofNat 2 * (HalfPow.half * value) ≈ value := by
  refine Q'.eqv_trans _ ((Q'.ofNat 2 * HalfPow.half) * value) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.eqv_trans _ (1 * value) _
    (Q'.mul_eqv_congr_right _ _ value (by decide))
    (Q'.one_mul_eqv value)

private theorem double_eqv (value : Q') :
    value + value ≈ Q'.ofNat 2 * value := by
  refine Q'.eqv_trans _ ((1 : Q') * value + 1 * value) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.one_mul_eqv value))
      (Q'.eqv_symm (Q'.one_mul_eqv value))
  exact Q'.eqv_trans _ ((1 + 1) * value) _
    (Q'.eqv_symm (Q'.add_mul_eqv 1 1 value))
    (Q'.mul_eqv_congr_right _ _ value (by decide))

/-- Every finite radial tail beyond the computed onset is bounded by twice
its actual first envelope value. -/
theorem subunitRadialEnvelope_tail_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (start : Nat) (hstart : subunitRadialOnset w ≤ start) (count : Nat) :
    finSum (fun offset => subunitRadialEnvelope w (start + offset)) count ≤
      Q'.ofNat 2 * subunitRadialEnvelope w start := by
  apply CharacterTail.geom_series_le
    (fun offset => subunitRadialEnvelope w (start + offset))
    (subunitRadialEnvelope w start) HalfPow.half
    (Q'.ofNat 2 * subunitRadialEnvelope w start)
    HalfPow.half_nonneg
    (Q'.mul_nonneg _ _ (zero_le_ofNat 2)
      (subunitRadialEnvelope_nonnegative hw0 start))
    (Q'.le_refl' _) ?_ ?_ count
  · intro offset
    simpa only [Nat.add_assoc] using
      subunitRadialEnvelope_succ_le_half hw0 hw1 (start + offset) (by omega)
  · have he : HalfPow.half *
        (Q'.ofNat 2 * subunitRadialEnvelope w start) ≈
          subunitRadialEnvelope w start := by
      exact Q'.eqv_trans _ _ _ (by q_ring) (twice_half _)
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) he)
        (double_eqv _))

/-- The actual radial-tail seed; no normalization to one is imposed. -/
def subunitRadialSeedBudget (w : Q') : Q' :=
  Q'.ofNat 2 * subunitRadialEnvelope w (subunitRadialOnset w)

theorem subunitRadialSeedBudget_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) :
    (0 : Q') ≤ subunitRadialSeedBudget w :=
  Q'.mul_nonneg _ _ (zero_le_ofNat 2)
    (subunitRadialEnvelope_nonnegative hw0 (subunitRadialOnset w))

/-- Computed number of half-contractions needed to pay a tolerance from the
actual nome-dependent seed. -/
def subunitRadialTailOffset (w epsilon : Q') : Nat :=
  PositiveContractionResidual.geometricCutoff
    HalfPow.half (subunitRadialSeedBudget w) epsilon

/-- Explicit radial threshold for the requested tolerance. -/
def subunitRadialTailCutoff (w epsilon : Q') : Nat :=
  subunitRadialOnset w + subunitRadialTailOffset w epsilon

theorem subunitRadialOnset_le_tailCutoff (w epsilon : Q') :
    subunitRadialOnset w ≤ subunitRadialTailCutoff w epsilon := by
  unfold subunitRadialTailCutoff
  omega

theorem subunitRadialEnvelope_geometric
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (offset : Nat) :
    subunitRadialEnvelope w (subunitRadialOnset w + offset) ≤
      HalfPow.half ^ offset *
        subunitRadialEnvelope w (subunitRadialOnset w) := by
  have h := CharacterTail.geom_dom
    (fun index => subunitRadialEnvelope w (subunitRadialOnset w + index))
    (subunitRadialEnvelope w (subunitRadialOnset w)) HalfPow.half
    HalfPow.half_nonneg (Q'.le_refl' _)
    (fun index => by
      simpa only [Nat.add_assoc] using
        subunitRadialEnvelope_succ_le_half hw0 hw1
          (subunitRadialOnset w + index) (by omega))
    offset
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

/-- Every finite radial tail from the explicit tolerance cutoff is at most
that tolerance, with the literal nome-dependent seed retained. -/
theorem subunitRadialTailCutoff_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) (count : Nat) :
    finSum
        (fun offset => subunitRadialEnvelope w
          (subunitRadialTailCutoff w epsilon + offset)) count ≤
      epsilon := by
  let shift := subunitRadialTailOffset w epsilon
  have htail := subunitRadialEnvelope_tail_le hw0 hw1
    (subunitRadialTailCutoff w epsilon)
    (by unfold subunitRadialTailCutoff; omega) count
  have hgeom := subunitRadialEnvelope_geometric hw0 hw1 shift
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hgeom
    (zero_le_ofNat 2)
  have hseed :
      Q'.ofNat 2 *
          (HalfPow.half ^ shift *
            subunitRadialEnvelope w (subunitRadialOnset w)) ≈
        HalfPow.half ^ shift * subunitRadialSeedBudget w := by
    unfold subunitRadialSeedBudget
    q_ring
  have hcut := PositiveContractionResidual.geometric_bound
    HalfPow.half_nonneg (by decide : HalfPow.half < (1 : Q'))
    (subunitRadialSeedBudget_nonnegative hw0) hepsilon shift
    (by exact Nat.le_refl _)
  refine Q'.le_trans' _ _ _ htail ?_
  change Q'.ofNat 2 *
      subunitRadialEnvelope w (subunitRadialOnset w + shift) ≤ epsilon
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hseed) hcut)

end YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail

#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialEnvelope
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialEnvelope_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialPowerTarget
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialGain
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialOnset
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialGain_power_le_target
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialGain_rate_le_half
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadial_gaussianExponent_succ_gain
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialEnvelope_succ_le_half
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialEnvelope_tail_le
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialSeedBudget
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialSeedBudget_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialTailOffset
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialTailCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialOnset_le_tailCutoff
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialEnvelope_geometric
#print axioms YMGap.Continuum.BF4PhysicalCubeSubunitRadialTail.subunitRadialTailCutoff_bound
