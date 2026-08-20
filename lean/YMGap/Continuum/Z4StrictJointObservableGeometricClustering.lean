/-
# A common geometric rate for strict centered-cylinder moments

The two-block estimate naturally appears with exponent `2 * shift + 6`.
This module factors it into a presentation-dependent positive prefactor and
the common geometric rate

  `anchorDoubledTimeRate = anchorEffectiveRatio^2 < 1`.

Consequently every fixed rational strict-cylinder presentation has ordinary
centered covariance bounded by `C(F,G) * rate^shift`.  The prefactor may
depend on the finite observables; the rate does not depend on them or on the
ambient volume.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockObservableCovariance
import YMGap.Continuum.FusionQuotientCollapse

namespace YMGap.Continuum.Z4StrictJointObservableGeometricClustering

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockObservableCovariance
open YMGap.Continuum.Z4CanonicalTwoBlockSignedCovariance
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

def anchorDoubledTimeRate : Q' :=
  anchorEffectiveRatio * anchorEffectiveRatio

theorem anchorDoubledTimeRate_pos :
    (0 : Q') < anchorDoubledTimeRate := by
  have hratio : (0 : Q') < anchorEffectiveRatio :=
    Q'.pos_of_lt_of_le
      (by decide : (0 : Q') < Q'.mkPos 6 25 (by decide))
      (Q'.ge_of_eqv anchorEffectiveRatio_eqv_six_twentyfive)
  exact Q'.mul_pos hratio hratio

theorem anchorDoubledTimeRate_nonnegative :
    (0 : Q') ≤ anchorDoubledTimeRate :=
  Q'.le_of_lt anchorDoubledTimeRate_pos

theorem anchorDoubledTimeRate_lt_one :
    anchorDoubledTimeRate < (1 : Q') := by
  have heq : anchorDoubledTimeRate ≈
      Q'.mkPos 6 25 (by decide) * Q'.mkPos 6 25 (by decide) := by
    unfold anchorDoubledTimeRate
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        anchorEffectiveRatio_eqv_six_twentyfive)
      (Q'.mul_eqv_congr_left _ _ _
        anchorEffectiveRatio_eqv_six_twentyfive)
  exact Q'.lt_of_le_of_lt (Q'.le_of_eqv heq) (by decide)

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

private theorem doubledPower_eqv_ratePower (shift : Nat) :
    anchorEffectiveRatio ^ (shift + shift) ≈
      anchorDoubledTimeRate ^ shift := by
  refine Q'.eqv_trans _
    (anchorEffectiveRatio ^ shift * anchorEffectiveRatio ^ shift) _
    (Q'.pow_add_eqv anchorEffectiveRatio shift shift) ?_
  exact Q'.eqv_symm (pow_mul_self_local anchorEffectiveRatio shift)

theorem anchorTemporalTail_eqv_geometric (shift : Nat) :
    anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2 ≈
      (anchorEffectiveRatio ^ 6 * Q'.ofNat 2) *
        anchorDoubledTimeRate ^ shift := by
  have hexponent : shift + shift + 6 = 6 + (shift + shift) := by omega
  rw [hexponent]
  refine Q'.eqv_trans _
    ((anchorEffectiveRatio ^ 6 *
        anchorEffectiveRatio ^ (shift + shift)) * Q'.ofNat 2) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.pow_add_eqv anchorEffectiveRatio 6 (shift + shift))
  refine Q'.eqv_trans _
    ((anchorEffectiveRatio ^ 6 * anchorDoubledTimeRate ^ shift) *
      Q'.ofNat 2) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (doubledPower_eqv_ratePower shift))
  ring_qeqv

def strictObservableRawPrefactor
    (rootCount : Nat)
    (leftStates rightStates : List (List Bool))
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  (coefficientL1 leftStates leftCoefficient *
      coefficientL1 rightStates rightCoefficient) *
    (Q'.ofNat rootCount *
      (anchorEffectiveRatio ^ 6 * Q'.ofNat 2))

/-- Add one to make the clustering prefactor strictly positive even for the
zero observable. -/
def strictObservablePositivePrefactor
    (rootCount : Nat)
    (leftStates rightStates : List (List Bool))
    (leftCoefficient rightCoefficient : List Bool → Q') : Q' :=
  (1 : Q') + strictObservableRawPrefactor rootCount
    leftStates rightStates leftCoefficient rightCoefficient

private theorem coefficientL1_nonnegative_any
    (states : List (List Bool)) (coefficient : List Bool → Q') :
    (0 : Q') ≤ coefficientL1 states coefficient := by
  unfold coefficientL1
  exact listQSum_nonnegative_on _ states
    (fun state hstate => Q'.abs_nonneg (coefficient state))

theorem strictObservableRawPrefactor_nonnegative
    (rootCount : Nat)
    (leftStates rightStates : List (List Bool))
    (leftCoefficient rightCoefficient : List Bool → Q') :
    (0 : Q') ≤ strictObservableRawPrefactor rootCount
      leftStates rightStates leftCoefficient rightCoefficient := by
  unfold strictObservableRawPrefactor
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (coefficientL1_nonnegative_any leftStates leftCoefficient)
      (coefficientL1_nonnegative_any rightStates rightCoefficient))
    (Q'.mul_nonneg _ _
      (YMGap.Constructive.ExpNeg.ofNat_nonneg' rootCount)
      (Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorEffectiveRatio
          anchorEffectiveRatio_nonnegative 6)
        (YMGap.Constructive.ExpNeg.ofNat_nonneg' 2)))

theorem strictObservablePositivePrefactor_pos
    (rootCount : Nat)
    (leftStates rightStates : List (List Bool))
    (leftCoefficient rightCoefficient : List Bool → Q') :
    (0 : Q') < strictObservablePositivePrefactor rootCount
      leftStates rightStates leftCoefficient rightCoefficient := by
  have hone : (0 : Q') < (1 : Q') := by decide
  exact Q'.pos_of_lt_of_le hone
    (Q'.add_le_self_of_nonneg (1 : Q') _
      (strictObservableRawPrefactor_nonnegative rootCount
        leftStates rightStates leftCoefficient rightCoefficient))

theorem strictDoubledTimeObservableCovariance_abs_le_geometric
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (leftCoefficient rightCoefficient : List Bool → Q') :
    Q'.abs
        (anchorTwoBlockObservableCovariance
          (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
          (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
          leftCoefficient rightCoefficient) ≤
      strictObservablePositivePrefactor roots.length
          (strictJointFingerprintSpace roots.length)
          (strictJointFingerprintSpace roots.length)
          leftCoefficient rightCoefficient *
        anchorDoubledTimeRate ^ shift := by
  have hraw := strictDoubledTimeObservableCovariance_abs_le_l1
    hadmissible hroots leftCoefficient rightCoefficient
  let leftL1 := coefficientL1
    (strictJointFingerprintSpace roots.length) leftCoefficient
  let rightL1 := coefficientL1
    (strictJointFingerprintSpace roots.length) rightCoefficient
  let rootCount := Q'.ofNat roots.length
  let rawPrefactor := strictObservableRawPrefactor roots.length
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    leftCoefficient rightCoefficient
  let positivePrefactor := strictObservablePositivePrefactor roots.length
    (strictJointFingerprintSpace roots.length)
    (strictJointFingerprintSpace roots.length)
    leftCoefficient rightCoefficient
  let ratePower := anchorDoubledTimeRate ^ shift
  have hfactor :
      (leftL1 * rightL1) *
          strictDoubledTimeNormalizedCovarianceEpsilon roots.length shift ≈
        rawPrefactor * ratePower := by
    unfold strictDoubledTimeNormalizedCovarianceEpsilon
      rawPrefactor strictObservableRawPrefactor
      leftL1 rightL1 ratePower
    refine Q'.eqv_trans _
      (coefficientL1
          (strictJointFingerprintSpace roots.length) leftCoefficient *
        coefficientL1
          (strictJointFingerprintSpace roots.length) rightCoefficient *
        (Q'.ofNat roots.length *
          ((anchorEffectiveRatio ^ 6 * Q'.ofNat 2) *
            anchorDoubledTimeRate ^ shift))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _
          (anchorTemporalTail_eqv_geometric shift))
    · ring_qeqv
  have htoRaw :
      Q'.abs
          (anchorTwoBlockObservableCovariance
            (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
            (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
            leftCoefficient rightCoefficient) ≤
        rawPrefactor * ratePower :=
    Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hfactor)
  have hprefactor : rawPrefactor ≤ positivePrefactor := by
    unfold positivePrefactor strictObservablePositivePrefactor
    refine Q'.le_trans' _ (rawPrefactor + (1 : Q')) _
      (Q'.add_le_self_of_nonneg rawPrefactor 1 Q'.zero_le_one) ?_
    exact Q'.le_of_eqv (Q'.add_comm_eqv rawPrefactor 1)
  refine Q'.le_trans' _ _ _ htoRaw ?_
  exact Q'.mul_le_mul_of_nonneg_right _ _ ratePower
    hprefactor
    (Q'.pow_nonneg anchorDoubledTimeRate
      anchorDoubledTimeRate_nonnegative shift)

#print axioms anchorDoubledTimeRate_pos
#print axioms anchorDoubledTimeRate_lt_one
#print axioms anchorTemporalTail_eqv_geometric
#print axioms strictObservablePositivePrefactor_pos
#print axioms strictDoubledTimeObservableCovariance_abs_le_geometric

end YMGap.Continuum.Z4StrictJointObservableGeometricClustering
