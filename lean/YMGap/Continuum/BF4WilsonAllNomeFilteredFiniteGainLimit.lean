/-
# Explicit original finite-gain approximation to the SAME completed gain

The cutoff, exterior-time and CReal representative thresholds are computed
from the existing centered-transfer and COMPLETE filtered-source joint
moduli, plus the original 48 mixRate^n boundary error. The finite mean is
still its own moving odd mean. No source convergence, favorable gain,
reserve or changing-family uniformity is supplied as a new hypothesis.
Nome and spatial width are fixed throughout this finite-to-limit join.
-/

import YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation
import YMGap.Continuum.BF4WilsonAllNomeFilteredGainLimit
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression filteredExpression_within filteredIncrement)
open YMGap.Continuum.BF4WilsonAllNomeFilteredGainLimit (gainLimit)
open YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
  (mixRate mixRate_nonnegative mixRate_lt_one)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] originalWindowScalar finiteScalar transferLimit originalJointLimit

/-- One quarter of the requested error, computed without a positive input. -/
def gainTolerance (epsilon : Q') : Q' := HalfPow.half*(HalfPow.half*epsilon)

theorem gainTolerance_positive {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < gainTolerance epsilon := Q'.mul_pos (by decide) (Q'.mul_pos (by decide) he)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (loop : SourceLoop width)

local notation "loopExpr" => WindowExpression.loop 0 loop 1
local notation "loopWithin" => Nat.le_refl (0 : Nat)
local notation "filteredExpr" => filteredExpression loopExpr
local notation "filteredWithin" => filteredExpression_within loopWithin

/-- Independent original heat-cutoff threshold. -/
def gainCutoffThreshold (epsilon : Q') : Nat :=
  max (cutoffThreshold hw0 hw1 loopExpr loopWithin (gainTolerance epsilon))
    (jointCutoffThreshold hw0 hw1 2 filteredExpr (gainTolerance epsilon))

/-- Independent original exterior-time threshold, including the actual
endpoint-mismatch and mixed-cross boundary-forgetting onset. -/
def gainTimeThreshold (epsilon : Q') : Nat :=
  max (max (timeThreshold hw0 hw1 loopExpr loopWithin (gainTolerance epsilon))
    (jointTimeThreshold hw0 hw1 filteredExpr (gainTolerance epsilon)))
    (geometricCutoff (mixRate hw0 hw1 width) 48 (gainTolerance epsilon))

/-- Representative threshold for the two EXISTING constructive limits. -/
def gainRepresentativeThreshold (epsilon : Q') : Nat :=
  max ((transferCauchy hw0 hw1 loopExpr loopWithin).M (gainTolerance epsilon))
    (jointModulus hw0 hw1 2 filteredExpr (gainTolerance epsilon))

private theorem weighted_upper (b x y e : Q') (hb0 : (0 : Q') ≤ b) (hb1 : b ≤ 1)
    (he : (0 : Q') ≤ e) (h : x ≤ y+e) : b*x ≤ b*y+e := by
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ b h hb0
  have herr : b*e ≤ e := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ e hb1 he) (Q'.le_of_eqv (Q'.one_mul_eqv e))
  exact Q'.le_trans' _ _ _ hm (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
    (Q'.add_le_add_left (b*y) _ _ herr))

private theorem linear_upper (j J f F b e : Q') (hb0 : (0 : Q') ≤ b) (hb1 : b ≤ 1)
    (he : (0 : Q') ≤ e) (hj : j ≤ J+e) (hf : F ≤ f+e) :
    b*j-HalfPow.half*f ≤ b*J-HalfPow.half*F+(e+e) := by
  have hJ := weighted_upper b j J e hb0 hb1 he hj
  have hF := weighted_upper HalfPow.half (-f) (-F) e HalfPow.half_nonneg (by decide) he
    (Q'.neg_le_neg_add hf)
  have hn : -(HalfPow.half*f) ≤ -(HalfPow.half*F)+e := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_neg_eqv _ _))
    (Q'.le_trans' _ _ _ hF (Q'.le_of_eqv
      (Q'.add_eqv_congr_right _ _ _ (Q'.mul_neg_eqv _ _))))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add hJ hn)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 2)))
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 2))) (by decide)
      (fun | 0 => b*J | 1 => -(HalfPow.half*F) | _ => e)))

private theorem three_tolerance_small {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (gainTolerance epsilon+gainTolerance epsilon)+gainTolerance epsilon ≤ epsilon := by
  let d := gainTolerance epsilon
  have hfour : ((d+d)+d)+d ≈ epsilon := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.var 0) (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.mul (.var 0) (.var 1))))
        (.mul (.var 0) (.mul (.var 0) (.var 1)))) (.mul (.var 0) (.mul (.var 0) (.var 1))))
      (.mul (.mul (.mul (.const 4) (.var 0)) (.var 0)) (.var 1))
      (by decide) (fun | 0 => HalfPow.half | _ => epsilon))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : ((4 : Q')*HalfPow.half)*HalfPow.half ≈ 1)) (Q'.one_mul_eqv epsilon))
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg ((d+d)+d) d
    (Q'.le_of_lt (gainTolerance_positive he))) (Q'.le_of_eqv hfour)

/-- The displayed thresholds construct BOTH-order approximation of the
actual finite normalized gain. The target is the already pinned SAME
completed gain, not a new limit datum. -/
theorem normalizedFiniteGain_approx (epsilon : Q') (he : (0 : Q') < epsilon)
    (a : Q') (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) (stage n p : Nat)
    (hk : gainCutoffThreshold hw0 hw1 width loop epsilon ≤ stage)
    (ht : gainTimeThreshold hw0 hw1 width loop epsilon ≤ n)
    (hp : gainRepresentativeThreshold hw0 hw1 width loop epsilon ≤ p) :
    normalizedFiniteGain hw0 hw1 width stage n loop a ≤
        (gainLimit hw0 hw1 loopExpr loopWithin a).approx p+epsilon ∧
      (gainLimit hw0 hw1 loopExpr loopWithin a).approx p ≤
        normalizedFiniteGain hw0 hw1 width stage n loop a+epsilon := by
  let d := gainTolerance epsilon
  have hd := gainTolerance_positive he
  have hC := transferLimit_approx hw0 hw1 loopExpr loopWithin d hd stage n p
    (Nat.le_trans (Nat.le_max_left _ _) hk)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) ht)
    (Nat.le_trans (Nat.le_max_left _ _) hp)
  have hF := originalJoint_approx hw0 hw1 2 filteredExpr filteredWithin d hd stage n p
    (Nat.le_trans (Nat.le_max_right _ _) hk)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) ht)
    (Nat.le_trans (Nat.le_max_right _ _) hp)
  have hgeo : mixRate hw0 hw1 width^n*48 ≤ d := geometric_bound
    (mixRate_nonnegative hw0 hw1 width) (mixRate_lt_one hw0 hw1 width) (by decide) hd n
    (Nat.le_trans (Nat.le_max_right _ _) ht)
  have hfinite := normalizedFiniteGain_bracket hw0 hw1 width stage n loop a ha0 ha1
  have hb0 : (0 : Q') ≤ 1-a := Q'.sub_nonneg_of_le ha1
  have hb1 : 1-a ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left (1 : Q') _ _ (Q'.neg_le_neg ha0))
    (Q'.le_of_eqv (by decide : (1 : Q') + -(0 : Q') ≈ 1))
  let finiteBase := (1-a)*finiteScalar hw0 hw1 loopExpr stage n -
    HalfPow.half*originalWindowScalar hw0 hw1 2 filteredExpr stage n n
  let limitBase := (gainLimit hw0 hw1 loopExpr loopWithin a).approx p
  have hupper : finiteBase ≤ limitBase+(d+d) := linear_upper _ _ _ _ (1-a) d hb0 hb1
    (Q'.le_of_lt hd) hC.1 hF.2
  have hlower : limitBase ≤ finiteBase+(d+d) := linear_upper _ _ _ _ (1-a) d hb0 hb1
    (Q'.le_of_lt hd) hC.2 hF.1
  have h1 : normalizedFiniteGain hw0 hw1 width stage n loop a ≤ limitBase+((d+d)+d) :=
    Q'.le_trans' _ _ _ hfinite.1 (Q'.le_trans' _ _ _ (Q'.add_le_add hupper hgeo)
      (Q'.le_of_eqv (Q'.add_assoc_eqv _ _ _)))
  have h2 : limitBase ≤ normalizedFiniteGain hw0 hw1 width stage n loop a+((d+d)+d) :=
    Q'.le_trans' _ _ _ hlower (Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ (d+d) hfinite.2)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (d+d)
        (Q'.add_le_add_left _ _ _ hgeo))
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.var 1)) (.var 2))
          (.add (.var 0) (.add (.var 2) (.var 1))) (by decide) (fun
            | 0 => normalizedFiniteGain hw0 hw1 width stage n loop a | 1 => d | _ => d+d)))))
  exact ⟨Q'.le_trans' _ _ _ h1 (Q'.add_le_add_left _ _ _ (three_tolerance_small he)),
    Q'.le_trans' _ _ _ h2 (Q'.add_le_add_left _ _ _ (three_tolerance_small he))⟩

end YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit

#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit.gainTolerance
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit.gainTolerance_positive
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit.gainCutoffThreshold
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit.gainTimeThreshold
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit.gainRepresentativeThreshold
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainLimit.normalizedFiniteGain_approx
