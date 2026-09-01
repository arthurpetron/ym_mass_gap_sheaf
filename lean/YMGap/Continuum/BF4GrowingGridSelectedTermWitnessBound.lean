/-
# The selected growing-grid witness is uniformly bounded

The growing closed-surface grid has `K + 1` replicas, and the selected-term
comparison gives the explicit lower witness

```text
  (K + 1) * min(1, coeffW(anchor, K)^6 / residualCeiling).
```

This module audits that witness rather than mistaking positivity for useful
asymptotics.  The strong-coupling coefficient reserve gives geometric
quarter-decay, the residual ceiling is at least one, and therefore the
displayed quantity is at most one for every cutoff.  This does **not** upper
bound the computed effective multiplicity: it proves only that the currently
selected single summand cannot by itself establish divergence.  A sharper
full-row comparison or a different replica family remains necessary.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Constructive.GeomBeatsLinear
import YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor
import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4GrowingGridSelectedTermRowFloor
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundI
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HKPos
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem geoPow_eq_pow_local (value : Q') :
    ∀ exponent : Nat, geoPow value exponent = value ^ exponent
  | 0 => rfl
  | exponent + 1 => by
      unfold geoPow
      rw [Q'.pow_succ, geoPow_eq_pow_local value exponent]

/-! ## 1. Quarter decay and the linear prefactor -/

/-- The anchor heat-kernel coefficient inherits the all-spin quarter-decay
bound from the constructive fusion reserve. -/
theorem anchorCoeff_le_quarterPow (spin : Nat) :
    coeffW anchorCoupling spin ≤
      (Q'.mkPos 1 4 (by decide)) ^ spin := by
  have h := leg_geo
    (w := anchorCoupling) (by decide) (by decide) (by decide) 0 spin
  rw [Nat.zero_add, coeffW_zero,
    geoPow_eq_pow_local (Q'.mkPos 1 4 (by decide)) spin] at h
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv
      (Q'.mul_one_eqv ((Q'.mkPos 1 4 (by decide)) ^ spin)))

/-- The quarter-geometric coefficient absorbs the growing factor `K + 1`.
This is the exact elementary obstruction to extracting divergence from the
selected coefficient alone. -/
theorem ofNat_succ_mul_quarterPow_le_one : ∀ cutoff : Nat,
    Q'.ofNat (cutoff + 1) *
        (Q'.mkPos 1 4 (by decide)) ^ cutoff ≤ (1 : Q')
  | 0 => by decide
  | cutoff + 1 => by
      let quarter : Q' := Q'.mkPos 1 4 (by decide)
      have hstep : Q'.ofNat (cutoff + 2) * quarter ≤
          Q'.ofNat (cutoff + 1) :=
        ofNat_succ_succ_mul_le (s := quarter)
          (by decide) (by decide) cutoff
      have hpow0 : (0 : Q') ≤ quarter ^ cutoff :=
        Q'.pow_nonneg quarter (by decide) cutoff
      have hscaled :
          (Q'.ofNat (cutoff + 2) * quarter) * quarter ^ cutoff ≤
            Q'.ofNat (cutoff + 1) * quarter ^ cutoff :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hstep hpow0
      have hregroup :
          Q'.ofNat (cutoff + 2) * quarter ^ (cutoff + 1) ≈
            (Q'.ofNat (cutoff + 2) * quarter) * quarter ^ cutoff := by
        rw [Q'.pow_succ]
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (Q'.ofNat (cutoff + 2)) quarter (quarter ^ cutoff))
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hregroup)
        (Q'.le_trans' _ _ _ hscaled
          (ofNat_succ_mul_quarterPow_le_one cutoff))

/-- Consequently the growing linear factor times the anchor coefficient is
already at most one. -/
theorem ofNat_succ_mul_anchorCoeff_le_one (cutoff : Nat) :
    Q'.ofNat (cutoff + 1) * coeffW anchorCoupling cutoff ≤ (1 : Q') := by
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    (anchorCoeff_le_quarterPow cutoff)
    (zero_le_ofNat (cutoff + 1))
  exact Q'.le_trans' _ _ _ hscaled
    (ofNat_succ_mul_quarterPow_le_one cutoff)

/-! ## 2. The selected floor is smaller than the sixth coefficient power -/

private theorem one_pow_eqv_one_local : ∀ exponent : Nat,
    ((1 : Q') ^ exponent) ≈ (1 : Q')
  | 0 => Q'.eqv_refl 1
  | exponent + 1 => by
      rw [Q'.pow_succ]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 1 _ _
          (one_pow_eqv_one_local exponent))
        (Q'.one_mul_eqv 1)

theorem centralSpinCubeResidualCarrierCeiling_ge_one :
    (1 : Q') ≤ centralSpinCubeResidualCarrierCeiling := by
  have hbase : (1 : Q') ≤ 1 + anchorDecoratedFaceEnvelope :=
    Q'.add_le_self_of_nonneg 1 anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative
  have hpow := CRealLog.pow_le_pow_base
    (1 : Q') (1 + anchorDecoratedFaceEnvelope) (by decide) hbase 66
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm (one_pow_eqv_one_local 66))) hpow

/-- The minimum and the denominator in the selected floor can only decrease
the sixth coefficient power. -/
theorem growingGridSelectedCommonFloor_le_anchorCoeffPowSix (cutoff : Nat) :
    growingGridSelectedCommonFloor cutoff ≤
      (coeffW anchorCoupling cutoff) ^ 6 := by
  let numerator := (coeffW anchorCoupling cutoff) ^ 6
  let ceiling := centralSpinCubeResidualCarrierCeiling
  have hnumerator0 : (0 : Q') ≤ numerator :=
    Q'.pow_nonneg _ (coeffW_nonneg (by decide) cutoff) 6
  have hdenominator : (0 : Q') < ceiling :=
    centralSpinCubeResidualCarrierCeiling_pos
  have hmul : numerator ≤ numerator * ceiling := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv numerator)))
      (Q'.mul_le_mul_of_nonneg_left 1 ceiling numerator
        centralSpinCubeResidualCarrierCeiling_ge_one hnumerator0)
  have hratio : Q'.divPos numerator ceiling hdenominator ≤ numerator := by
    apply Q'.divPos_le_of_le_mul
    exact hmul
  unfold growingGridSelectedCommonFloor gridReplicaSelectedFloor
  exact Q'.le_trans' _ _ _ (Q'.min_le_right' _ _) hratio

/-! ## 3. Capstone: the selected effective witness is bounded -/

/-- **Selected-witness obstruction.**  The explicit lower witness supplied
by the selected grid summand is uniformly at most one.  The actual computed
effective multiplicity may be larger; any proof of its divergence must use
additional raw-row mass, not this selected term alone. -/
theorem growingGrid_selectedEffectiveWitness_le_one (cutoff : Nat) :
    Q'.ofNat (cutoff + 1) * growingGridSelectedCommonFloor cutoff ≤
      (1 : Q') := by
  have hfloor := growingGridSelectedCommonFloor_le_anchorCoeffPowSix cutoff
  have hscaledFloor := Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor
    (zero_le_ofNat (cutoff + 1))
  have hcoeff0 : (0 : Q') ≤ coeffW anchorCoupling cutoff :=
    coeffW_nonneg (by decide) cutoff
  have hcoeffOne : coeffW anchorCoupling cutoff ≤ (1 : Q') := by
    exact Q'.le_trans' _ _ _ (anchorCoeff_le_quarterPow cutoff)
      (HKPos.pow_le_one (by decide) (by decide) cutoff)
  have hsix : (coeffW anchorCoupling cutoff) ^ 6 ≤
      coeffW anchorCoupling cutoff := by
    simpa only [show 6 = 5 + 1 by omega] using
      (HKPos.pow_succ_le_self hcoeff0 hcoeffOne 5)
  have hscaledSix := Q'.mul_le_mul_of_nonneg_left _ _ _ hsix
    (zero_le_ofNat (cutoff + 1))
  exact Q'.le_trans' _ _ _ hscaledFloor
    (Q'.le_trans' _ _ _ hscaledSix
      (ofNat_succ_mul_anchorCoeff_le_one cutoff))

/-- The selected witness actually inherits a geometric quarter-power upper
bound.  The linear factor is absorbed by one quarter-power; five further
copies remain from the sixth coefficient power. -/
theorem growingGrid_selectedEffectiveWitness_le_quarterPow (cutoff : Nat) :
    Q'.ofNat (cutoff + 1) * growingGridSelectedCommonFloor cutoff ≤
      (Q'.mkPos 1 4 (by decide)) ^ cutoff := by
  let quarter : Q' := Q'.mkPos 1 4 (by decide)
  let coefficient := coeffW anchorCoupling cutoff
  let quarterPow := quarter ^ cutoff
  have hfloor := growingGridSelectedCommonFloor_le_anchorCoeffPowSix cutoff
  have hscaledFloor := Q'.mul_le_mul_of_nonneg_left _ _ _ hfloor
    (zero_le_ofNat (cutoff + 1))
  have hcoefficient0 : (0 : Q') ≤ coefficient :=
    coeffW_nonneg (by decide) cutoff
  have hquarterPow0 : (0 : Q') ≤ quarterPow :=
    Q'.pow_nonneg quarter (by decide) cutoff
  have hcoefficientLe : coefficient ≤ quarterPow := by
    exact anchorCoeff_le_quarterPow cutoff
  have hsixLe : coefficient ^ 6 ≤ quarterPow ^ 6 :=
    CRealLog.pow_le_pow_base coefficient quarterPow
      hcoefficient0 hcoefficientLe 6
  have hscaledSix := Q'.mul_le_mul_of_nonneg_left _ _ _ hsixLe
    (zero_le_ofNat (cutoff + 1))
  have hregroup :
      Q'.ofNat (cutoff + 1) * quarterPow ^ 6 ≈
        (Q'.ofNat (cutoff + 1) * quarterPow) * quarterPow ^ 5 := by
    rw [show 6 = 5 + 1 by omega, Q'.pow_succ]
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (Q'.ofNat (cutoff + 1)) quarterPow (quarterPow ^ 5))
  have hlinear : Q'.ofNat (cutoff + 1) * quarterPow ≤ (1 : Q') := by
    exact ofNat_succ_mul_quarterPow_le_one cutoff
  have hremaining0 : (0 : Q') ≤ quarterPow ^ 5 :=
    Q'.pow_nonneg quarterPow hquarterPow0 5
  have habsorb :
      (Q'.ofNat (cutoff + 1) * quarterPow) * quarterPow ^ 5 ≤
        (1 : Q') * quarterPow ^ 5 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hlinear hremaining0
  have hquarterPowOne : quarterPow ≤ (1 : Q') := by
    exact HKPos.pow_le_one (by decide) (by decide) cutoff
  have hremainingLe : quarterPow ^ 5 ≤ quarterPow := by
    simpa only [show 5 = 4 + 1 by omega] using
      (HKPos.pow_succ_le_self hquarterPow0 hquarterPowOne 4)
  exact Q'.le_trans' _ _ _ hscaledFloor
    (Q'.le_trans' _ _ _ hscaledSix
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
        (Q'.le_trans' _ _ _ habsorb
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.one_mul_eqv (quarterPow ^ 5)))
            hremainingLe))))

/-- Explicit located-zero modulus for the selected witness.  Once the cutoff
is at least `epsilon.den`, the witness is at most `epsilon`. -/
theorem growingGrid_selectedEffectiveWitness_le_epsilon
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (cutoff : Nat) (hcutoff : epsilon.den ≤ cutoff) :
    Q'.ofNat (cutoff + 1) * growingGridSelectedCommonFloor cutoff ≤
      epsilon := by
  have hselected :=
    growingGrid_selectedEffectiveWitness_le_quarterPow cutoff
  have hquarterHalf :
      (Q'.mkPos 1 4 (by decide)) ^ cutoff ≤
        HalfPow.half ^ cutoff :=
    CRealLog.pow_le_pow_base
      (Q'.mkPos 1 4 (by decide)) HalfPow.half
      (by decide) (by decide) cutoff
  have hhalfTail : HalfPow.half ^ cutoff ≤
      HalfPow.half ^ epsilon.den := by
    have h := ExpNeg.pow_half_antitone epsilon.den
      (cutoff - epsilon.den)
    rwa [Nat.add_sub_of_le hcutoff] at h
  exact Q'.le_trans' _ _ _ hselected
    (Q'.le_trans' _ _ _ hquarterHalf
      (Q'.le_trans' _ _ _ hhalfTail
        (HalfPow.pow_half_le epsilon hepsilon)))

end YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound

#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound.anchorCoeff_le_quarterPow
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound.ofNat_succ_mul_anchorCoeff_le_one
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound.centralSpinCubeResidualCarrierCeiling_ge_one
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound.growingGridSelectedCommonFloor_le_anchorCoeffPowSix
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound.growingGrid_selectedEffectiveWitness_le_one
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound.growingGrid_selectedEffectiveWitness_le_quarterPow
#print axioms
  YMGap.Continuum.BF4GrowingGridSelectedTermWitnessBound.growingGrid_selectedEffectiveWitness_le_epsilon
