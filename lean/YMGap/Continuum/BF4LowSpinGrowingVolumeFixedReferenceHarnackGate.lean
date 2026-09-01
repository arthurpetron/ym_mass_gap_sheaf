/-
# Fixed-reference Harnack gate for growing low-spin replication

The adaptive minimum-row theorem identifies the exact remaining comparison
needed by the literal slice-zero source.  If one positive rational ceiling,
independent of the volume, bounds the slice-zero raw row by that ceiling times
the adaptive minimum raw row, then the reciprocal ceiling is a common floor
for every replica/reference row ratio.

This module compiles that single Harnack input into a linear lower bound on
the fixed-source effective multiplicity and an explicit epsilon/rate tail-zero
theorem for the fixed slice-zero stationary marginal.  It does not construct
the Harnack input.  In particular, no finite-carrier time-translation symmetry,
cofinal spin-cube identification, conductance bound, gap, continuum limit, or
Clay theorem is asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMarginalTailZero

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate

set_option maxRecDepth 500000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinGrowingVolumeAdaptiveMinimumReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeReflectedCarrier
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate
open YMGap.Continuum.BF4VolumeParametricPositiveRawReplicationGate.CentralPositiveRawReplicationListAt
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact missing uniform comparison -/

/-- A volume-uniform comparison of the literal slice-zero raw row with the
constructively selected minimum low-spin raw row. -/
structure LowSpinCentralFixedAdaptiveRawRowHarnack
    (w : Q') (hw : (0 : Q') < w) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  fixed_le_ceiling_mul_adaptive : ∀ volume,
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralReferenceState volume) ≤
      ceiling *
        centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralAdaptiveReferenceState w hw volume)

namespace LowSpinCentralFixedAdaptiveRawRowHarnack

theorem ceiling_pos
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw) :
    (0 : Q') < harnack.ceiling :=
  Q'.pos_of_lt_of_le (by decide) harnack.one_le_ceiling

/-- Reciprocal of the uniform row-comparison ceiling. -/
def reciprocalFloor
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw) : Q' :=
  Q'.divPos 1 harnack.ceiling harnack.ceiling_pos

theorem reciprocalFloor_pos
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw) :
    (0 : Q') < harnack.reciprocalFloor :=
  Q'.divPos_pos 1 harnack.ceiling harnack.ceiling_pos (by decide)

theorem reciprocalFloor_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw) :
    harnack.reciprocalFloor ≤ 1 := by
  unfold reciprocalFloor
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ harnack.one_le_ceiling
    (Q'.ge_of_eqv (Q'.one_mul_eqv harnack.ceiling))

theorem scaledFixedReferenceRawRow_le_adaptive
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw)
    (volume : Nat) :
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralReferenceState volume) *
        harnack.reciprocalFloor ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralAdaptiveReferenceState w hw volume) := by
  let fixedRow :=
    centralPhysicalPositiveRawRowMass
      w (Q'.le_of_lt hw) 1 (volume + 1)
      (lowSpinCentralReferenceState volume)
  let adaptiveRow :=
    centralPhysicalPositiveRawRowMass
      w (Q'.le_of_lt hw) 1 (volume + 1)
      (lowSpinCentralAdaptiveReferenceState w hw volume)
  have hrow : fixedRow ≤ adaptiveRow * harnack.ceiling :=
    Q'.le_trans' _ _ _
      (harnack.fixed_le_ceiling_mul_adaptive volume)
      (Q'.le_of_eqv (Q'.mul_comm_eqv harnack.ceiling adaptiveRow))
  have hdiv :
      Q'.divPos fixedRow harnack.ceiling harnack.ceiling_pos ≤
        adaptiveRow :=
    Q'.divPos_le_of_le_mul fixedRow harnack.ceiling
      harnack.ceiling_pos hrow
  have hscaled :
      fixedRow * harnack.reciprocalFloor ≈
        Q'.divPos fixedRow harnack.ceiling harnack.ceiling_pos := by
    unfold reciprocalFloor Q'.divPos
    exact Q'.mul_eqv_congr_left fixedRow _ _
      (Q'.one_mul_eqv
        (Q'.recipPos harnack.ceiling harnack.ceiling_pos))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled) hdiv

theorem scaledFixedReferenceRawRow_le_replica
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw)
    (volume : Nat) {state : EdgeLabelling}
    (hstate : state ∈ lowSpinCentralLowerStates volume) :
    centralPhysicalPositiveRawRowMass
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralReferenceState volume) *
        harnack.reciprocalFloor ≤
      centralPhysicalPositiveRawRowMass
        w (Q'.le_of_lt hw) 1 (volume + 1) state := by
  exact Q'.le_trans' _ _ _
    (harnack.scaledFixedReferenceRawRow_le_adaptive volume)
    (lowSpinCentralAdaptiveReferenceRawRow_le_replica
      w hw volume hstate)

/-! ## 2. Compilation into the literal fixed-reference ratio floor -/

theorem reciprocalFloor_le_computedRawRowRatioFloor
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw)
    (volume : Nat) :
    harnack.reciprocalFloor ≤
      lowSpinCentralComputedRawRowRatioFloor w hw volume := by
  exact
    lower_le_rawRowRatioFloor_of_scaledReferenceRawRow_le
      (lowSpinCentralPositiveRawReplication w hw volume)
      harnack.reciprocalFloor harnack.reciprocalFloor_le_one
      (fun state hstate =>
        harnack.scaledFixedReferenceRawRow_le_replica volume hstate)

theorem count_mul_reciprocalFloor_le_effectiveMultiplicity
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw)
    (volume : Nat) :
    Q'.ofNat (volume + 1) * harnack.reciprocalFloor ≤
      lowSpinCentralComputedEffectiveMultiplicity w hw volume := by
  unfold lowSpinCentralComputedEffectiveMultiplicity
    effectiveMultiplicity
  rw [lowSpinCentralPositiveRawReplication_count w hw volume]
  exact Q'.mul_le_mul_of_nonneg_left
    harnack.reciprocalFloor
    (lowSpinCentralPositiveRawReplication w hw volume).rawRowRatioFloor
    (Q'.ofNat (volume + 1))
    (harnack.reciprocalFloor_le_computedRawRowRatioFloor volume)
    (Q'.le_of_lt (Q'.ofNat_succ_pos volume))

/-! ## 3. Explicit fixed-reference marginal tail -/

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
  have hden : (epsilon.denPred + 1 : Int) ≤ (volume : Int) :=
    Int.ofNat_le.mpr hvolume
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

theorem fixedReferenceMarginal_le_epsilon
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (volume : Nat)
    (hvolume : (epsilon * harnack.reciprocalFloor).den ≤ volume) :
    centralPhysicalRowMarginal
        w (Q'.le_of_lt hw) 1 (volume + 1)
        (lowSpinCentralReferenceState volume) ≤
      epsilon := by
  let effective :=
    lowSpinCentralComputedEffectiveMultiplicity w hw volume
  have heffectivePos : (0 : Q') < effective :=
    lowSpinCentralComputedEffectiveMultiplicity_pos w hw volume
  have hcount :
      Q'.ofNat (volume + 1) * harnack.reciprocalFloor ≤ effective :=
    harnack.count_mul_reciprocalFloor_le_effectiveMultiplicity volume
  have hepsilonFloor :
      (0 : Q') < epsilon * harnack.reciprocalFloor :=
    Q'.mul_pos hepsilon harnack.reciprocalFloor_pos
  have honeCount :
      (1 : Q') ≤
        (epsilon * harnack.reciprocalFloor) *
          Q'.ofNat (volume + 1) :=
    one_le_epsilon_mul_ofNat_succ_of_den_le
      hepsilonFloor hvolume
  have hreassociate :
      (epsilon * harnack.reciprocalFloor) *
          Q'.ofNat (volume + 1) ≈
        epsilon *
          (Q'.ofNat (volume + 1) * harnack.reciprocalFloor) := by
    refine Q'.eqv_trans _
      (epsilon *
        (harnack.reciprocalFloor * Q'.ofNat (volume + 1))) _ ?_ ?_
    · exact Q'.mul_assoc_eqv _ _ _
    exact Q'.mul_eqv_congr_left epsilon _ _
      (Q'.mul_comm_eqv harnack.reciprocalFloor
        (Q'.ofNat (volume + 1)))
  have honeScaled :
      (1 : Q') ≤ epsilon *
        (Q'.ofNat (volume + 1) * harnack.reciprocalFloor) :=
    Q'.le_trans' _ _ _ honeCount (Q'.le_of_eqv hreassociate)
  have hscaledEffective :
      epsilon *
          (Q'.ofNat (volume + 1) * harnack.reciprocalFloor) ≤
        epsilon * effective :=
    Q'.mul_le_mul_of_nonneg_left _ _ epsilon hcount
      (Q'.le_of_lt hepsilon)
  have honeEffective : (1 : Q') ≤ epsilon * effective :=
    Q'.le_trans' _ _ _ honeScaled hscaledEffective
  have hreciprocal : Q'.divPos 1 effective heffectivePos ≤ epsilon :=
    Q'.divPos_le_of_le_mul 1 effective heffectivePos honeEffective
  exact Q'.le_trans' _ _ _
    (lowSpinCentralReferenceMarginal_le_reciprocalEffectiveMultiplicity
      w hw volume)
    hreciprocal

/-- Located epsilon/rate data for the fixed slice-zero reference marginal,
conditional on the one uniform raw-row Harnack comparison. -/
structure FixedReferenceMarginalTailZero
    (w : Q') (hw : (0 : Q') < w) : Type where
  rate : Q' → Nat
  marginal_le : ∀ epsilon, (0 : Q') < epsilon →
    ∀ volume, rate epsilon ≤ volume →
      centralPhysicalRowMarginal
          w (Q'.le_of_lt hw) 1 (volume + 1)
          (lowSpinCentralReferenceState volume) ≤
        epsilon

def toFixedReferenceMarginalTailZero
    {w : Q'} {hw : (0 : Q') < w}
    (harnack : LowSpinCentralFixedAdaptiveRawRowHarnack w hw) :
    FixedReferenceMarginalTailZero w hw where
  rate epsilon := (epsilon * harnack.reciprocalFloor).den
  marginal_le := by
    intro epsilon hepsilon volume hvolume
    exact harnack.fixedReferenceMarginal_le_epsilon
      epsilon hepsilon volume hvolume

end LowSpinCentralFixedAdaptiveRawRowHarnack

end YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate.LowSpinCentralFixedAdaptiveRawRowHarnack.reciprocalFloor_le_computedRawRowRatioFloor
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate.LowSpinCentralFixedAdaptiveRawRowHarnack.count_mul_reciprocalFloor_le_effectiveMultiplicity
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate.LowSpinCentralFixedAdaptiveRawRowHarnack.fixedReferenceMarginal_le_epsilon
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeFixedReferenceHarnackGate.LowSpinCentralFixedAdaptiveRawRowHarnack.toFixedReferenceMarginalTailZero
