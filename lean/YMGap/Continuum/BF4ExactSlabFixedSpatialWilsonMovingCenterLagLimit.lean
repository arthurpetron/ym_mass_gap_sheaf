/-
# Fixed-source joint approximation after finite OWN-center cancellation

The original centered endpoint pairs retain their moving finite odd-window
mean. Its contribution to a lag difference is paid BEFORE using the two
fixed-source joint limits. Each raw pair is the original chronological
two-loop expression, with its own lag-dependent partition. The independent
cutoff, exterior-time and representative thresholds are displayed explicitly.

Nome, width, loop and both lags stay fixed. There is no coupling-, width-
or spacing-uniform estimate, no passage of a moving polynomial through a
fixed-test limit, and no new limit object.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
  (originalWindowScalar originalWindowScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialCap)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] baseLinks originalWindowScalar originalJointLimit
  middleRatio rawPair centeredPair mixRate

private theorem pair_within {width : Nat} (loop : SourceLoop width) (L : Nat) :
    Within L (.mul (.loop 0 loop 1) (.loop L loop 1)) :=
  ⟨Nat.zero_le L, Nat.le_refl L⟩

/-- The literal original two-loop observable is the raw finite pair at the
SAME heat stage and chronological partition. -/
theorem raw_original_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (loop : SourceLoop width) (stage n L : Nat) :
    rawPair hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _) n L
        (sourceCharacter width loop.edges 1) ≈
      originalWindowScalar hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1)) stage n n := by
  simpa only [rawPair, sourcePolynomial, Nat.zero_mul, liftBoundary] using
    Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L
      (.mul (.loop 0 loop 1) (.loop L loop 1)) (pair_within loop L) stage n n)

private theorem difference_upper (x y X Y e : Q')
    (hx : x ≤ X+e) (hy : Y ≤ y+e) : x + -y ≤ X + -Y + (e+e) :=
  Q'.le_trans' _ _ _ (Q'.add_le_add hx (Q'.neg_le_neg_add hy))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.add (.neg (.var 1)) (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.var 2)))
      (by decide) (fun
        | 0 => X
        | 1 => Y
        | _ => e)))

private theorem commute_error (x e d : Q') : (x+e)+d ≈ (x+d)+e :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.var 2))
    (.add (.add (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun
      | 0 => x
      | 1 => e
      | _ => d)

/-- The two original fixed-source joint moduli and the already-paid moving
center give both orders of approximation. The same p is used in both
EXISTING CReal representatives. No finite mean limit is assumed. -/
theorem centered_lag_joint_approx {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (loop : SourceLoop width) (L J : Nat)
    (epsilon : Q') (he : (0 : Q') < epsilon) (stage n p : Nat)
    (hk : max
      (jointCutoffThreshold hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1)) epsilon)
      (jointCutoffThreshold hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1)) epsilon) ≤ stage)
    (ht : max
      (jointTimeThreshold hw0 hw1 (.mul (.loop 0 loop 1) (.loop L loop 1)) epsilon)
      (jointTimeThreshold hw0 hw1 (.mul (.loop 0 loop 1) (.loop J loop 1)) epsilon) ≤ n)
    (hp : max
      (jointModulus hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1)) epsilon)
      (jointModulus hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1)) epsilon) ≤ p) :
    let f := sourceCharacter width loop.edges 1
    let K := headCutoff w+stage
    let hK : headCutoff w ≤ K := Nat.le_add_right _ _
    let c := middleRatio hw0 hw1 K width hK (n+1) n f
    let C := polynomialCap f
    let error := mixRate hw0 hw1 width^n*((C+C)*(C+C))
    let limitDifference :=
      (originalJointLimit hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1))
        (pair_within loop L)).approx p +
      -((originalJointLimit hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1))
        (pair_within loop J)).approx p)
    centeredPair hw0 hw1 K width hK n L f c +
        -(centeredPair hw0 hw1 K width hK n J f c) ≤
      limitDifference + error + (epsilon+epsilon) ∧
    limitDifference ≤
      centeredPair hw0 hw1 K width hK n L f c +
        -(centeredPair hw0 hw1 K width hK n J f c) + error + (epsilon+epsilon) := by
  dsimp only
  let f := sourceCharacter width loop.edges 1
  let K := headCutoff w+stage
  have hK : headCutoff w ≤ K := Nat.le_add_right _ _
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  let error := mixRate hw0 hw1 width^n*
    ((polynomialCap f+polynomialCap f)*(polynomialCap f+polynomialCap f))
  let rawDifference := rawPair hw0 hw1 K width hK n L f +
    -(rawPair hw0 hw1 K width hK n J f)
  let centeredDifference := centeredPair hw0 hw1 K width hK n L f c +
    -(centeredPair hw0 hw1 K width hK n J f c)
  let limitDifference :=
    (originalJointLimit hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1))
      (pair_within loop L)).approx p +
    -((originalJointLimit hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1))
      (pair_within loop J)).approx p)
  have hL := originalJoint_approx hw0 hw1 L
    (.mul (.loop 0 loop 1) (.loop L loop 1)) (pair_within loop L) epsilon he stage n p
    (Nat.le_trans (Nat.le_max_left _ _) hk)
    (Nat.le_trans (Nat.le_max_left _ _) ht)
    (Nat.le_trans (Nat.le_max_left _ _) hp)
  have hJ := originalJoint_approx hw0 hw1 J
    (.mul (.loop 0 loop 1) (.loop J loop 1)) (pair_within loop J) epsilon he stage n p
    (Nat.le_trans (Nat.le_max_right _ _) hk)
    (Nat.le_trans (Nat.le_max_right _ _) ht)
    (Nat.le_trans (Nat.le_max_right _ _) hp)
  have hLp := raw_original_pin hw0 hw1 width loop stage n L
  have hJp := raw_original_pin hw0 hw1 width loop stage n J
  have hrawUpper : rawDifference ≤ limitDifference+(epsilon+epsilon) :=
    difference_upper _ _ _ _ epsilon
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hLp) hL.1)
      (Q'.le_trans' _ _ _ hJ.2
        (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hJp)))
  have hrawLower : limitDifference ≤ rawDifference+(epsilon+epsilon) :=
    difference_upper _ _ _ _ epsilon
      (Q'.le_trans' _ _ _ hL.2
        (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hLp)))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hJp) hJ.1)
  have hcenter := polynomial_own_centered_lag_difference_bounds hw0 hw1 K width hK
    n L J f (sourceCharacter_supported width loop.edges 1)
  have hupper : centeredDifference ≤ limitDifference+error+(epsilon+epsilon) :=
    Q'.le_trans' _ _ _ hcenter.1
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ error hrawUpper)
        (Q'.le_of_eqv (commute_error limitDifference (epsilon+epsilon) error)))
  have hlower : limitDifference ≤ centeredDifference+error+(epsilon+epsilon) :=
    Q'.le_trans' _ _ _ hrawLower
      (Q'.add_le_add_right _ _ (epsilon+epsilon) hcenter.2)
  exact ⟨hupper, hlower⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit.raw_original_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit.centered_lag_joint_approx
