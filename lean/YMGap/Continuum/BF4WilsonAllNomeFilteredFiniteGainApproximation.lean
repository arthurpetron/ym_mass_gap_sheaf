/-
# The actual finite commutator gain reaches the existing original scalars

The cutoff is the original head-plus-stage cutoff. The moving center is
the SAME finite odd mean, and all mixed quantities use the SAME EVEN
partition. The literal radius-two source and existing matched centered
transfer scalar approximate the normalized actual commutator gain with
both-order error 48 mixRate^n, for 0<=a<=1.

This is a fixed-nome/width finite comparison. It asserts neither a favorable
gain nor a reserve, uniform changing-family control, or continuum survival.
No centered eigenpin or replacement carrier is introduced.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
import YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit

namespace YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression sourcePolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredNoiseDrift
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredOwnYoung (ownMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredCommutatorGain
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate mixRate_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeFilteredIncrement (filteredExpression)
open YMGap.Continuum.BF4WilsonAllNomeCenteredTransferBondLimit (finiteScalar)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] sourceCharacter originalWindowScalar finiteScalar
  YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonMeanRadial.mean
  sourcePolynomial filteredExpression numerator evenPartition noise driftSquare
  centeredTransferCross endpointMismatch commutatorGain

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width stage n : Nat) (loop : SourceLoop width)

local notation "K" => headCutoff w+stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "f" => sourceCharacter width loop.edges 1
local notation "c" => ownMean hw0 hw1 K width hK n loop
local notation "E" => evenPartition w K width n
local notation "hE" => evenPartition_positive hw0 hw1 K width hK n
local notation "z" => Q'.recipPos E hE
local notation "Ffinite" => originalWindowScalar hw0 hw1 2
  (filteredExpression (WindowExpression.loop 0 loop 1)) stage n n
local notation "Cfinite" => finiteScalar hw0 hw1 (WindowExpression.loop 0 loop 1) stage n

/-- Divide the existing actual signed gain by its original even partition. -/
def normalizedFiniteGain (a : Q') : Q' := commutatorGain w K width n f c a*z
def normalizedFiniteCross : Q' := centeredTransferCross w K width n f c*z
def normalizedFiniteMismatch : Q' := endpointMismatch w K width n f c*z

private theorem solve_gain (F D J G a : Q')
    (h : F ≈ D+2*(1-a)*J-2*G) :
    G ≈ (1-a)*J-HalfPow.half*F+HalfPow.half*D := by
  have htwo : 2*G ≈ D+2*(1-a)*J-F := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.mul (.const 2) (.var 3))
      (.add (.add (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
        (.neg (.add (.add (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
          (.neg (.mul (.const 2) (.var 3))))))
      (by decide) (fun | 0 => D | 1 => 1-a | 2 => J | _ => G))
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.eqv_symm h)))
  have hhalf : HalfPow.half*(2*G) ≈ G := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : HalfPow.half*2 ≈ (1 : Q'))) (Q'.one_mul_eqv _))
  have hfactor : (HalfPow.half*2)*((1-a)*J) ≈ (1-a)*J :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
      (by decide : HalfPow.half*2 ≈ (1 : Q'))) (Q'.one_mul_eqv _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hhalf)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ htwo)
      (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
        (.mul (.var 4) (.add (.add (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2))) (.neg (.var 3))))
        (.add (.add (.mul (.mul (.var 4) (.const 2)) (.mul (.var 1) (.var 2)))
          (.neg (.mul (.var 4) (.var 3)))) (.mul (.var 4) (.var 0)))
        (by decide) (fun | 0 => D | 1 => 1-a | 2 => J | 3 => F | _ => HalfPow.half))
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' hfactor (Q'.eqv_refl _)) (Q'.eqv_refl _))))

/-- Exact finite gain, with the COMPLETE original radius-two source retained. -/
theorem normalizedFiniteGain_identity (a : Q') :
    normalizedFiniteGain hw0 hw1 width stage n loop a ≈
      (1-a)*normalizedFiniteCross hw0 hw1 width stage n loop - HalfPow.half*Ffinite +
        HalfPow.half*normalizedFiniteMismatch hw0 hw1 width stage n loop := by
  have hsource : Ffinite ≈ numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1)))*z :=
    Q'.eqv_trans _ _ _ (filtered_loop_originalWindowScalar hw0 hw1 width stage n loop 1)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (filtered_loop_numerator w K width n loop 1)))
  have hraw : numerator w K width n (sourcePolynomial (filteredExpression (.loop 0 loop 1))) ≈
      endpointMismatch w K width n f c + 2*(1-a)*centeredTransferCross w K width n f c -
        2*commutatorGain w K width n f c a :=
    filtered_loop_commutator_identity w K width n loop c a
  have hnorm : Ffinite ≈ normalizedFiniteMismatch hw0 hw1 width stage n loop +
      2*(1-a)*normalizedFiniteCross hw0 hw1 width stage n loop -
        2*normalizedFiniteGain hw0 hw1 width stage n loop a :=
    Q'.eqv_trans _ _ _ hsource (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hraw)
      (poly_identity_of_normal_eq
        (.mul (.add (.add (.var 0) (.mul (.mul (.const 2) (.var 1)) (.var 2)))
          (.neg (.mul (.const 2) (.var 3)))) (.var 4))
        (.add (.add (.mul (.var 0) (.var 4))
          (.mul (.mul (.const 2) (.var 1)) (.mul (.var 2) (.var 4))))
          (.neg (.mul (.const 2) (.mul (.var 3) (.var 4))))) (by decide) (fun
            | 0 => endpointMismatch w K width n f c | 1 => 1-a
            | 2 => centeredTransferCross w K width n f c
            | 3 => commutatorGain w K width n f c a | _ => z)))
  exact solve_gain _ _ _ _ a hnorm

private theorem normalize_bound (x Z e : Q') (hz : (0 : Q') < Z)
    (h : x ≤ e*Z) : x*Q'.recipPos Z hz ≤ e :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h
    (Q'.le_of_lt (Q'.recipPos_pos Z hz)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv Z hz))
        (Q'.mul_one_eqv e))))

/-- Both signs of the actual normalized endpoint mismatch have the same
computed error, with no finite odd/even partition identification. -/
theorem normalizedFiniteMismatch_bounds :
    normalizedFiniteMismatch hw0 hw1 width stage n loop ≤ mixRate hw0 hw1 width^n*32 ∧
      -normalizedFiniteMismatch hw0 hw1 width stage n loop ≤ mixRate hw0 hw1 width^n*32 := by
  have h := endpointMismatch_bound hw0 hw1 K width hK n loop
  have hp := normalize_bound _ E _ hE (Q'.le_trans' _ _ _ (Q'.le_abs_self _) h)
  have hn := normalize_bound _ E _ hE (Q'.le_trans' _ _ _ (Q'.neg_le_abs _) h)
  exact ⟨hp, Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_mul_eqv _ _)) hn⟩

private theorem perturb (J C F D b e : Q') (hb0 : (0 : Q') ≤ b) (hb1 : b ≤ 1)
    (he : (0 : Q') ≤ e) (hj : J ≤ C+e) (hd : D ≤ e) :
    b*J-HalfPow.half*F+HalfPow.half*D ≤ b*C-HalfPow.half*F+(e+HalfPow.half*e) := by
  have hjb := Q'.mul_le_mul_of_nonneg_left _ _ b hj hb0
  have hdb := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hd HalfPow.half_nonneg
  have hbe : b*e ≤ e := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ e hb1 he) (Q'.le_of_eqv (Q'.one_mul_eqv e))
  have h : b*J-HalfPow.half*F+HalfPow.half*D ≤
      b*(C+e)-HalfPow.half*F+HalfPow.half*e := Q'.le_trans' _ _ _
    (Q'.add_le_add_left (b*J-HalfPow.half*F) _ _ hdb)
    (Q'.add_le_add_right _ _ (HalfPow.half*e)
      (Q'.add_le_add_right _ _ (-(HalfPow.half*F)) hjb))
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.add (.var 1) (.var 3))) (.neg (.var 2))) (.var 4))
      (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 2)))
        (.add (.mul (.var 0) (.var 3)) (.var 4))) (by decide) (fun
          | 0 => b | 1 => C | 2 => HalfPow.half*F | 3 => e | _ => HalfPow.half*e)))
    (Q'.add_le_add_left (b*C-HalfPow.half*F) _ _
      (Q'.add_le_add_right _ _ (HalfPow.half*e) hbe)))

private theorem error_pin (r : Q') : r*32+HalfPow.half*(r*32) ≈ r*48 :=
  Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.const 32)) (.mul (.var 1) (.mul (.var 0) (.const 32))))
    (.mul (.var 0) (.add (.const 32) (.mul (.var 1) (.const 32))))
    (by decide) (fun | 0 => r | _ => HalfPow.half))
    (Q'.mul_eqv_congr_left _ _ _ (by decide : (32 : Q')+HalfPow.half*32 ≈ 48))

/-- The constructed finite gain approximates the EXISTING original finite
scalars in both orders. No gain comparison or convergence is supplied as a
new hypothesis. The nome and width remain fixed. -/
theorem normalizedFiniteGain_bracket (a : Q') (ha0 : (0 : Q') ≤ a) (ha1 : a ≤ 1) :
    normalizedFiniteGain hw0 hw1 width stage n loop a ≤ (1-a)*Cfinite-HalfPow.half*Ffinite+
      mixRate hw0 hw1 width^n*48 ∧
    (1-a)*Cfinite-HalfPow.half*Ffinite ≤ normalizedFiniteGain hw0 hw1 width stage n loop a+
      mixRate hw0 hw1 width^n*48 := by
  let J := normalizedFiniteCross hw0 hw1 width stage n loop
  let D := normalizedFiniteMismatch hw0 hw1 width stage n loop
  let G := normalizedFiniteGain hw0 hw1 width stage n loop a
  let e := mixRate hw0 hw1 width^n*32
  have hJ : J ≤ Cfinite+e ∧ Cfinite ≤ J+e := by
    simpa only [normalizedFiniteCross, finiteScalar, sourcePolynomial, Nat.zero_mul] using
      centeredTransferCross_commonTail hw0 hw1 K width hK n loop
  have hD := normalizedFiniteMismatch_bounds hw0 hw1 width stage n loop
  have hb0 : (0 : Q') ≤ 1-a := Q'.sub_nonneg_of_le ha1
  have hb1 : 1-a ≤ (1 : Q') := by
    have h := Q'.add_le_add_left (1 : Q') _ _ (Q'.neg_le_neg ha0)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.const 1) (.neg (.const 0))) (.const 1) (by decide) (fun _ => a)))
  have he : (0 : Q') ≤ e := Q'.mul_nonneg _ _
    (Q'.pow_nonneg _ (mixRate_nonnegative hw0 hw1 width) n) (by decide)
  have hg := normalizedFiniteGain_identity hw0 hw1 width stage n loop a
  have ht := error_pin (mixRate hw0 hw1 width^n)
  have hup := perturb J Cfinite Ffinite D (1-a) e hb0 hb1 he hJ.1 hD.1
  have hrev := perturb Cfinite J Ffinite (-D) (1-a) e hb0 hb1 he hJ.2 hD.2
  have hrev' := Q'.add_le_add_right _ _ (HalfPow.half*D) hrev
  have hleft : ((1-a)*Cfinite-HalfPow.half*Ffinite+HalfPow.half*(-D))+HalfPow.half*D ≈
      (1-a)*Cfinite-HalfPow.half*Ffinite := poly_identity_of_normal_eq
    (.add (.add (.var 0) (.mul (.var 1) (.neg (.var 2)))) (.mul (.var 1) (.var 2)))
    (.var 0) (by decide) (fun | 0 => (1-a)*Cfinite-HalfPow.half*Ffinite | 1 => HalfPow.half | _ => D)
  have hright : ((1-a)*J-HalfPow.half*Ffinite+(e+HalfPow.half*e))+HalfPow.half*D ≈
      G+mixRate hw0 hw1 width^n*48 := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.var 1)) (by decide) (fun
        | 0 => (1-a)*J-HalfPow.half*Ffinite | 1 => e+HalfPow.half*e | _ => HalfPow.half*D))
    (Q'.add_eqv_congr' (Q'.eqv_symm hg) ht)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hg)
      (Q'.le_trans' _ _ _ hup (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ ht))),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hrev' (Q'.le_of_eqv hright))⟩

end YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation

#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation.normalizedFiniteGain
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation.normalizedFiniteCross
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation.normalizedFiniteMismatch
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation.normalizedFiniteGain_identity
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation.normalizedFiniteMismatch_bounds
#print axioms YMGap.Continuum.BF4WilsonAllNomeFilteredFiniteGainApproximation.normalizedFiniteGain_bracket
