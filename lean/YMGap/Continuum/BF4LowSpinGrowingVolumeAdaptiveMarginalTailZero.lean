/-
# Tail zero for the adaptive low-spin reference marginal

The minimum-row replication theorem gives an adaptive reference whose
effective multiplicity is semantically equal to `volume + 1`.  This module
turns its reciprocal marginal bound into a located epsilon/rate statement:
for positive rational `epsilon`, every volume at least `epsilon.den` has
adaptive reference marginal at most `epsilon`.

This is a constructive fixed-coupling, cutoff-one, growing-volume tail-zero
theorem.  The reference state is selected separately at every volume.  Thus
the result does not identify a fixed observable or the prescribed spin-cube
ray, and it does not prove a bottleneck, a cofinal gap, a continuum limit, or
the Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMarginalTailZero

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Reciprocal-count arithmetic with an explicit modulus -/

private theorem one_le_epsilon_mul_ofNat_succ_of_den_le
    {epsilon : Q'} (hepsilon : (0 : Q') < epsilon)
    {volume : Nat} (hvolume : epsilon.den ≤ volume) :
    (1 : Q') ≤ epsilon * Q'.ofNat (volume + 1) := by
  have hnum : (0 : Int) < epsilon.num := Q'.num_pos_of_pos hepsilon
  show (1 : Q').num *
        ((epsilon * Q'.ofNat (volume + 1)).den : Int) ≤
      (epsilon * Q'.ofNat (volume + 1)).num *
        ((1 : Q').den : Int)
  show (1 : Int) *
        ((epsilon * Q'.ofNat (volume + 1)).den : Int) ≤
      (epsilon.num * ((volume + 1 : Nat) : Int)) * (1 : Int)
  rw [Q'.mul_den_cast]
  change (1 : Int) * ((epsilon.den : Int) * 1) ≤
    (epsilon.num * ((volume + 1 : Nat) : Int)) * 1
  simp only [Int.one_mul, Int.mul_one]
  have hden : (epsilon.denPred + 1 : Int) ≤ (volume : Int) := by
    exact Int.ofNat_le.mpr hvolume
  have honeNum : (1 : Int) ≤ epsilon.num := by omega
  have hvolumeNonnegative : (0 : Int) ≤ (volume : Int) :=
    Int.natCast_nonneg volume
  have hscaled : (volume : Int) ≤ epsilon.num * (volume : Int) := by
    have := Int.mul_le_mul_of_nonneg_right honeNum hvolumeNonnegative
    simpa only [Int.one_mul] using this
  have hsucc : epsilon.num * (volume : Int) ≤
      epsilon.num * ((volume + 1 : Nat) : Int) := by
    apply Int.mul_le_mul_of_nonneg_left
    · exact Int.ofNat_le.mpr (Nat.le_succ volume)
    · omega
  exact Int.le_trans hden (Int.le_trans hscaled hsucc)

/-! ## 2. Located tail zero for the varying minimum-row state -/

/-- Explicit epsilon/rate data for the stationary marginal of the adaptive
minimum-row low-spin state.  The selected state is allowed to vary with the
volume. -/
structure LowSpinCentralAdaptiveReferenceMarginalTailZero
    (w : Q') (hw : (0 : Q') < w) : Type where
  rate : Q' → Nat
  marginal_le : ∀ epsilon, (0 : Q') < epsilon →
    ∀ volume, rate epsilon ≤ volume →
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralAdaptiveReferenceState w hw volume) ≤
        epsilon

theorem lowSpinCentralAdaptiveReferenceMarginal_le_epsilon
    (w : Q') (hw : (0 : Q') < w)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (volume : Nat) (hvolume : epsilon.den ≤ volume) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralAdaptiveReferenceState w hw volume) ≤
      epsilon := by
  let effective :=
    lowSpinCentralAdaptiveEffectiveMultiplicity w hw volume
  have heffectivePos : (0 : Q') < effective :=
    (lowSpinCentralAdaptivePositiveRawReplication
      w hw volume).effectiveMultiplicity_pos
  have heffective : effective ≈ Q'.ofNat (volume + 1) :=
    lowSpinCentralAdaptiveEffectiveMultiplicity_eqv_count w hw volume
  have honeCount :
      (1 : Q') ≤ epsilon * Q'.ofNat (volume + 1) :=
    one_le_epsilon_mul_ofNat_succ_of_den_le hepsilon hvolume
  have hepsilonEffective :
      epsilon * effective ≈ epsilon * Q'.ofNat (volume + 1) :=
    Q'.mul_eqv_congr_left epsilon effective
      (Q'.ofNat (volume + 1)) heffective
  have honeEffective : (1 : Q') ≤ epsilon * effective :=
    Q'.le_trans' _ _ _ honeCount
      (Q'.le_of_eqv (Q'.eqv_symm hepsilonEffective))
  have hreciprocal : Q'.divPos 1 effective heffectivePos ≤ epsilon :=
    Q'.divPos_le_of_le_mul 1 effective heffectivePos honeEffective
  exact Q'.le_trans' _ _ _
    (lowSpinCentralAdaptiveReferenceMarginal_le_reciprocalEffective
      w hw volume)
    hreciprocal

/-- The denominator of `epsilon` is a constructive modulus for the adaptive
reference marginal. -/
def lowSpinCentralAdaptiveReferenceMarginalTailZero
    (w : Q') (hw : (0 : Q') < w) :
    LowSpinCentralAdaptiveReferenceMarginalTailZero w hw where
  rate epsilon := epsilon.den
  marginal_le := by
    intro epsilon hepsilon volume hvolume
    exact lowSpinCentralAdaptiveReferenceMarginal_le_epsilon
      w hw epsilon hepsilon volume hvolume

end YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMarginalTailZero

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMarginalTailZero.lowSpinCentralAdaptiveReferenceMarginal_le_epsilon
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMarginalTailZero.lowSpinCentralAdaptiveReferenceMarginalTailZero
