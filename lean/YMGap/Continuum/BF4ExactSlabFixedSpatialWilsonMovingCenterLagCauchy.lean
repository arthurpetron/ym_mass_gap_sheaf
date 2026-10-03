/-
# The actual moving-center lag stream converges to existing raw limits

The Type-valued QCauchy data constructs a modulus for the diagonal of the
original OWN-centered lag difference. Each term keeps its own finite mean
middleRatio(k+1,k,f). Exact finite cancellation pays that mean before the
two fixed-source Wilson limits are used. The target is their EXISTING
constructive-real difference, not a new limit construction.

Nome, width, loop and both lags are fixed. Relative signed slope bounds,
changing-family uniformity and the completed dyadic response join are not
provided by this finite-to-limit result.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Constructive.CRealComplete

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
  (polynomialCap polynomialCap_nonnegative)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] originalWindowScalar originalJointLimit
  middleRatio rawPair centeredPair mixRate

private def tolerance (epsilon : Q') : Q' := HalfPow.half*(HalfPow.half*epsilon)

private theorem tolerance_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < tolerance epsilon :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)

private theorem four_tolerances (epsilon : Q') :
    (tolerance epsilon+tolerance epsilon)+(tolerance epsilon+tolerance epsilon) ≈ epsilon :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (ExpNeg.two_halves (HalfPow.half*epsilon))
    (ExpNeg.two_halves (HalfPow.half*epsilon))) (ExpNeg.two_halves epsilon)

private def meanErrorCap {width : Nat} (loop : SourceLoop width) : Q' :=
  let C := polynomialCap (sourceCharacter width loop.edges 1)
  (C+C)*(C+C)

private theorem meanErrorCap_nonnegative {width : Nat} (loop : SourceLoop width) :
    (0 : Q') ≤ meanErrorCap loop := by
  let C := polynomialCap (sourceCharacter width loop.edges 1)
  have hC : (0 : Q') ≤ C+C := Q'.zero_le_add _ _
    (polynomialCap_nonnegative _) (polynomialCap_nonnegative _)
  exact Q'.mul_nonneg _ _ hC hC

private theorem pair_within {width : Nat} (loop : SourceLoop width) (L : Nat) :
    Within L (.mul (.loop 0 loop 1) (.loop L loop 1)) :=
  ⟨Nat.zero_le L, Nat.le_refl L⟩

/-- Literal original lag difference, using the SAME actual finite OWN mean
in both endpoint copies and both lags. -/
def ownCenteredLagDifference {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (loop : SourceLoop width) (L J stage n : Nat) : Q' :=
  let f := sourceCharacter width loop.edges 1
  let K := headCutoff w+stage
  let hK : headCutoff w ≤ K := Nat.le_add_right _ _
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  centeredPair hw0 hw1 K width hK n L f c +
    -(centeredPair hw0 hw1 K width hK n J f c)

private def diagonalModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (L J : Nat) (epsilon : Q') : Nat :=
  max (max
    (jointModulus hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1)) (tolerance epsilon))
    (jointModulus hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1)) (tolerance epsilon)))
    (geometricCutoff (mixRate hw0 hw1 width) (meanErrorCap loop) (tolerance epsilon))

private theorem difference_upper (x y X Y d : Q')
    (hx : x ≤ X+d) (hy : Y ≤ y+d) : x + -y ≤ X + -Y + (d+d) :=
  Q'.le_trans' _ _ _ (Q'.add_le_add hx (Q'.neg_le_neg_add hy))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.add (.neg (.var 1)) (.var 2)))
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.var 2)))
      (by decide) (fun
        | 0 => X
        | 1 => Y
        | _ => d)))

private theorem four_step (epsilon x y u v : Q')
    (hx : x ≤ u+tolerance epsilon)
    (hu : u ≤ v+(tolerance epsilon+tolerance epsilon))
    (hv : v ≤ y+tolerance epsilon) : x ≤ y+epsilon := by
  let d := tolerance epsilon
  have h := Q'.le_trans' _ _ _ hx
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ d hu)
      (Q'.add_le_add_right _ _ d (Q'.add_le_add_right _ _ (d+d) hv)))
  have he : ((y+d)+(d+d))+d ≈ y+((d+d)+(d+d)) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 1))) (.var 1))
      (.add (.var 0) (.add (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1))))
      (by decide) (fun | 0 => y | _ => d)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he
    (Q'.add_eqv_congr_left y _ _ (four_tolerances epsilon))))

private theorem diagonal_raw_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (loop : SourceLoop width) (L J : Nat)
    (epsilon : Q') (he : (0 : Q') < epsilon) (k : Nat)
    (hk : diagonalModulus hw0 hw1 loop L J epsilon ≤ k) :
    let raw := originalWindowScalar hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1)) k k k +
      -(originalWindowScalar hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1)) k k k)
    ownCenteredLagDifference hw0 hw1 width loop L J k k ≤ raw+tolerance epsilon ∧
      raw ≤ ownCenteredLagDifference hw0 hw1 width loop L J k k+tolerance epsilon := by
  have h := polynomial_own_centered_lag_difference_bounds hw0 hw1 (headCutoff w+k) width
    (Nat.le_add_right _ _) k L J (sourceCharacter width loop.edges 1)
    (sourceCharacter_supported width loop.edges 1)
  have hg := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) (meanErrorCap_nonnegative loop)
    (tolerance_positive he) k (Nat.le_trans (Nat.le_max_right _ _) hk)
  have hp := Q'.add_eqv_congr' (raw_original_pin hw0 hw1 width loop k k L)
    (Q'.neg_eqv_congr _ _ (raw_original_pin hw0 hw1 width loop k k J))
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.add_le_add (Q'.le_of_eqv hp) hg),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hp)
      (Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_left _ _ _ hg))⟩

/-- Explicit Type-valued Cauchy data. Its M is the maximum of BOTH original
joint moduli at epsilon/4 and the actual mean-error geometric cutoff. -/
def ownCenteredLagDifferenceCauchy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (loop : SourceLoop width) (L J : Nat) :
    QCauchy (fun k => ownCenteredLagDifference hw0 hw1 width loop L J k k) where
  M := diagonalModulus hw0 hw1 loop L J
  bound := by
    intro epsilon he i j hi hj
    let d := tolerance epsilon
    have hd := tolerance_positive he
    have hL := (originalJointCauchy hw0 hw1 L
      (.mul (.loop 0 loop 1) (.loop L loop 1)) (pair_within loop L)).bound
      d hd i j
      (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hi)
      (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hj)
    have hJ := (originalJointCauchy hw0 hw1 J
      (.mul (.loop 0 loop 1) (.loop J loop 1)) (pair_within loop J)).bound
      d hd i j
      (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hi)
      (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hj)
    have hrawUpper := difference_upper _ _ _ _ d hL.1 hJ.2
    have hrawLower := difference_upper _ _ _ _ d hL.2 hJ.1
    have hci := diagonal_raw_bounds hw0 hw1 loop L J epsilon he i hi
    have hcj := diagonal_raw_bounds hw0 hw1 loop L J epsilon he j hj
    exact ⟨four_step epsilon _ _ _ _ hci.1 hrawUpper hcj.2,
      four_step epsilon _ _ _ _ hcj.1 hrawLower hci.2⟩

private theorem three_step (epsilon : Q') (he : (0 : Q') < epsilon) (x y e : Q')
    (h : x ≤ y+e+(tolerance epsilon+tolerance epsilon))
    (he_small : e ≤ tolerance epsilon) : x ≤ y+epsilon := by
  let d := tolerance epsilon
  have hthree : x ≤ (y+d)+(d+d) := Q'.le_trans' _ _ _ h
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_left y _ _ he_small))
  have hfour := Q'.le_trans' _ _ _ hthree
    (Q'.add_le_self_of_nonneg ((y+d)+(d+d)) d (Q'.le_of_lt (tolerance_positive he)))
  have hregroup : ((y+d)+(d+d))+d ≈ y+((d+d)+(d+d)) :=
    poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 1))) (.var 1))
      (.add (.var 0) (.add (.add (.var 1) (.var 1)) (.add (.var 1) (.var 1))))
      (by decide) (fun | 0 => y | _ => d)
  exact Q'.le_trans' _ _ _ hfour (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hregroup
    (Q'.add_eqv_congr_left y _ _ (four_tolerances epsilon))))

/-- The rational-embedded ACTUAL moving-center diagonal converges to the
already constructed difference of fixed-source raw two-point limits. -/
theorem ownCenteredLagDifference_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (loop : SourceLoop width) (L J : Nat) :
    ConvergesTo (fun k => ofQ' (ownCenteredLagDifference hw0 hw1 width loop L J k k))
      (CReal.sub
        (originalJointLimit hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1)) (pair_within loop L))
        (originalJointLimit hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1)) (pair_within loop J))) := by
  intro epsilon he
  let d := tolerance epsilon
  let M := diagonalModulus hw0 hw1 loop L J epsilon
  let P := max
    (jointModulus hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1)) d)
    (jointModulus hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1)) d)
  refine ⟨M, fun k hk => ⟨P, fun p hp => ?_⟩⟩
  have hLP : jointModulus hw0 hw1 L (.mul (.loop 0 loop 1) (.loop L loop 1)) d ≤ k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk
  have hJP : jointModulus hw0 hw1 J (.mul (.loop 0 loop 1) (.loop J loop 1)) d ≤ k :=
    Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk
  have h := centered_lag_joint_approx hw0 hw1 width loop L J d (tolerance_positive he) k k p
    (Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_right _ _) hLP,
      Nat.le_trans (Nat.le_max_right _ _) hJP⟩)
    (Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left _ _) hLP,
      Nat.le_trans (Nat.le_max_left _ _) hJP⟩) hp
  have hg := geometric_bound (mixRate_nonnegative hw0 hw1 width)
    (mixRate_lt_one hw0 hw1 width) (meanErrorCap_nonnegative loop)
    (tolerance_positive he) k (Nat.le_trans (Nat.le_max_right _ _) hk)
  change ownCenteredLagDifference hw0 hw1 width loop L J k k ≤
      (CReal.sub _ _).approx p+epsilon ∧
    (CReal.sub _ _).approx p ≤ ownCenteredLagDifference hw0 hw1 width loop L J k k+epsilon
  rw [CReal.sub_approx]
  exact ⟨three_step epsilon he _ _ _ h.1 hg, three_step epsilon he _ _ _ h.2 hg⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy.ownCenteredLagDifference
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy.ownCenteredLagDifferenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMovingCenterLagCauchy.ownCenteredLagDifference_converges
