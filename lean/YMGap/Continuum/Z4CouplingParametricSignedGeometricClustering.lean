/-
# Common geometric rate for arbitrary-cutoff signed covariances

The all-cutoff signed estimate has temporal factor

  `anchorDecoratedEffectiveRatio^(2 * shift + 6) * 2`.

This file extracts the observable-independent rate
`anchorDecoratedDoubledTimeRate = (1/4)^2 = 1/16 < 1`, leaving an explicit
presentation-dependent positive prefactor.
-/

import YMGap.Continuum.Z4CouplingParametricTwoBlockSignedCovariance
import YMGap.Continuum.FusionQuotientCollapse

namespace YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.Z4CouplingParametricTwoBlockSignedCovariance
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

def anchorDecoratedDoubledTimeRate : Q' :=
  anchorDecoratedEffectiveRatio * anchorDecoratedEffectiveRatio

theorem anchorDecoratedDoubledTimeRate_eqv_sixteenth :
    anchorDecoratedDoubledTimeRate ≈ Q'.mkPos 1 16 (by decide) := by
  unfold anchorDecoratedDoubledTimeRate
  refine Q'.eqv_trans _
    (Q'.mkPos 1 4 (by decide) * Q'.mkPos 1 4 (by decide)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        anchorDecoratedEffectiveRatio_eqv_quarter)
      (Q'.mul_eqv_congr_left _ _ _
        anchorDecoratedEffectiveRatio_eqv_quarter)
  · decide

theorem anchorDecoratedDoubledTimeRate_pos :
    (0 : Q') < anchorDecoratedDoubledTimeRate := by
  exact Q'.pos_of_lt_of_le
    (by decide : (0 : Q') < Q'.mkPos 1 16 (by decide))
    (Q'.ge_of_eqv anchorDecoratedDoubledTimeRate_eqv_sixteenth)

theorem anchorDecoratedDoubledTimeRate_nonnegative :
    (0 : Q') ≤ anchorDecoratedDoubledTimeRate :=
  Q'.le_of_lt anchorDecoratedDoubledTimeRate_pos

theorem anchorDecoratedDoubledTimeRate_lt_one :
    anchorDecoratedDoubledTimeRate < (1 : Q') := by
  exact Q'.lt_of_le_of_lt
    (Q'.le_of_eqv anchorDecoratedDoubledTimeRate_eqv_sixteenth)
    (by decide)

private theorem pow_mul_self_local (w : Q') :
    ∀ n : Nat, (w * w) ^ n ≈ w ^ n * w ^ n
  | 0 => Q'.eqv_symm (Q'.one_mul_eqv 1)
  | n + 1 => by
      show (w * w) * (w * w) ^ n ≈
        (w * w ^ n) * (w * w ^ n)
      refine Q'.eqv_trans _
        ((w * w) * (w ^ n * w ^ n)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _ (pow_mul_self_local w n)
      · ring_qeqv

private theorem decoratedDoubledPower_eqv_ratePower (shift : Nat) :
    anchorDecoratedEffectiveRatio ^ (shift + shift) ≈
      anchorDecoratedDoubledTimeRate ^ shift := by
  refine Q'.eqv_trans _
    (anchorDecoratedEffectiveRatio ^ shift *
      anchorDecoratedEffectiveRatio ^ shift) _
    (Q'.pow_add_eqv anchorDecoratedEffectiveRatio shift shift) ?_
  exact Q'.eqv_symm
    (pow_mul_self_local anchorDecoratedEffectiveRatio shift)

theorem anchorDecoratedTemporalTail_eqv_geometric (shift : Nat) :
    anchorDecoratedEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2 ≈
      (anchorDecoratedEffectiveRatio ^ 6 * Q'.ofNat 2) *
        anchorDecoratedDoubledTimeRate ^ shift := by
  have hexponent : shift + shift + 6 = 6 + (shift + shift) := by omega
  rw [hexponent]
  refine Q'.eqv_trans _
    ((anchorDecoratedEffectiveRatio ^ 6 *
        anchorDecoratedEffectiveRatio ^ (shift + shift)) * Q'.ofNat 2) _
    ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.pow_add_eqv anchorDecoratedEffectiveRatio 6 (shift + shift))
  refine Q'.eqv_trans _
    ((anchorDecoratedEffectiveRatio ^ 6 *
        anchorDecoratedDoubledTimeRate ^ shift) * Q'.ofNat 2) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (decoratedDoubledPower_eqv_ratePower shift))
  · ring_qeqv

def couplingParametricStrictSignedRawPrefactor
    (rootCount : Nat)
    (leftStates rightStates : List (List Bool))
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  (coefficientL1 leftStates leftCoefficient *
      coefficientL1 rightStates rightCoefficient) *
    (Q'.ofNat rootCount *
      (anchorDecoratedEffectiveRatio ^ 6 * Q'.ofNat 2))

def couplingParametricStrictSignedPositivePrefactor
    (rootCount : Nat)
    (leftStates rightStates : List (List Bool))
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  (1 : Q') + couplingParametricStrictSignedRawPrefactor rootCount
    leftStates rightStates leftCoefficient rightCoefficient

private theorem coefficientL1_nonnegative_any
    (states : List (List Bool)) (coefficient : List Bool → Q') :
    (0 : Q') ≤ coefficientL1 states coefficient := by
  unfold coefficientL1
  exact listQSum_nonnegative_on _ states
    (fun state hstate => Q'.abs_nonneg (coefficient state))

theorem couplingParametricStrictSignedRawPrefactor_nonnegative
    (rootCount : Nat)
    (leftStates rightStates : List (List Bool))
    (leftCoefficient rightCoefficient : List Bool → Q') :
    (0 : Q') ≤ couplingParametricStrictSignedRawPrefactor rootCount
      leftStates rightStates leftCoefficient rightCoefficient := by
  unfold couplingParametricStrictSignedRawPrefactor
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (coefficientL1_nonnegative_any leftStates leftCoefficient)
      (coefficientL1_nonnegative_any rightStates rightCoefficient))
    (Q'.mul_nonneg _ _
      (YMGap.Constructive.ExpNeg.ofNat_nonneg' rootCount)
      (Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedEffectiveRatio
          anchorDecoratedEffectiveRatio_nonnegative 6)
        (YMGap.Constructive.ExpNeg.ofNat_nonneg' 2)))

theorem couplingParametricStrictSignedPositivePrefactor_pos
    (rootCount : Nat)
    (leftStates rightStates : List (List Bool))
    (leftCoefficient rightCoefficient : List Bool → Q') :
    (0 : Q') < couplingParametricStrictSignedPositivePrefactor rootCount
      leftStates rightStates leftCoefficient rightCoefficient := by
  have hone : (0 : Q') < (1 : Q') := by decide
  exact Q'.pos_of_lt_of_le hone
    (Q'.add_le_self_of_nonneg (1 : Q') _
      (couplingParametricStrictSignedRawPrefactor_nonnegative rootCount
        leftStates rightStates leftCoefficient rightCoefficient))

theorem couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_geometric
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs
        (couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
          hcoupling cutoff hadmissible hroots
          leftCoefficient rightCoefficient) ≤
      couplingParametricStrictSignedPositivePrefactor roots.length
          (strictJointFingerprintSpace roots.length)
          (strictJointFingerprintSpace roots.length)
          leftCoefficient rightCoefficient *
        anchorDecoratedDoubledTimeRate ^ shift := by
  have hraw :=
    couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_l1
      hcoupling hle cutoff hadmissible hroots
      leftCoefficient rightCoefficient
  let leftL1 := coefficientL1
    (strictJointFingerprintSpace roots.length) leftCoefficient
  let rightL1 := coefficientL1
    (strictJointFingerprintSpace roots.length) rightCoefficient
  let rawPrefactor := couplingParametricStrictSignedRawPrefactor roots.length
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    leftCoefficient rightCoefficient
  let positivePrefactor :=
    couplingParametricStrictSignedPositivePrefactor roots.length
      (strictJointFingerprintSpace roots.length)
      (strictJointFingerprintSpace roots.length)
      leftCoefficient rightCoefficient
  let ratePower := anchorDecoratedDoubledTimeRate ^ shift
  have hfactor :
      (leftL1 * rightL1) *
          couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
            roots.length shift ≈
        rawPrefactor * ratePower := by
    unfold couplingParametricKStrictDoubledTimeNormalizedCovarianceEpsilon
      rawPrefactor couplingParametricStrictSignedRawPrefactor
      leftL1 rightL1 ratePower
    refine Q'.eqv_trans _
      (coefficientL1
          (strictJointFingerprintSpace roots.length) leftCoefficient *
        coefficientL1
          (strictJointFingerprintSpace roots.length) rightCoefficient *
        (Q'.ofNat roots.length *
          ((anchorDecoratedEffectiveRatio ^ 6 * Q'.ofNat 2) *
            anchorDecoratedDoubledTimeRate ^ shift))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (anchorDecoratedTemporalTail_eqv_geometric shift))
    · ring_qeqv
  have htoRaw :
      Q'.abs
          (couplingParametricKStrictDoubledTimeNormalizedSignedCovariance
            hcoupling cutoff hadmissible hroots
            leftCoefficient rightCoefficient) ≤
        rawPrefactor * ratePower :=
    Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hfactor)
  have hprefactor : rawPrefactor ≤ positivePrefactor := by
    unfold positivePrefactor
      couplingParametricStrictSignedPositivePrefactor
    refine Q'.le_trans' _ (rawPrefactor + (1 : Q')) _
      (Q'.add_le_self_of_nonneg rawPrefactor 1 Q'.zero_le_one) ?_
    exact Q'.le_of_eqv (Q'.add_comm_eqv rawPrefactor 1)
  refine Q'.le_trans' _ _ _ htoRaw ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ ratePower hprefactor
    (Q'.pow_nonneg anchorDecoratedDoubledTimeRate
      anchorDecoratedDoubledTimeRate_nonnegative shift)

#print axioms anchorDecoratedDoubledTimeRate_eqv_sixteenth
#print axioms anchorDecoratedDoubledTimeRate_lt_one
#print axioms anchorDecoratedTemporalTail_eqv_geometric
#print axioms couplingParametricStrictSignedPositivePrefactor_pos
#print axioms couplingParametricKStrictDoubledTimeNormalizedSignedCovariance_abs_le_geometric

end YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
