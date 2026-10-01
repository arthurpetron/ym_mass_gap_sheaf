/-
# Squared local error of the original scaled physical Cayley map

The linked graph identity gives a fourth-order squared error on the SAME
completed Wilson bond carrier.  The represented second core supplies actual
linked points and bounds their second output by its explicit original Cauchy
preimage.  This is a local consistency estimate, not a time-product limit,
physical-time calibration, Hamiltonian mass estimate, or continuum statement.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCore
import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BoundedTransferCalculus
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (Completion completedInner)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedSub completedNeg completedSmul completedZero)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedAdd_comm completedAdd_zero completedNeg_add)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_smul_left completedInner_smul_right)
open YMGap.Continuum.BF4WilsonAllNomeDistance
  (completedDist completedDist_triangle)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion inner)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg realScale imagScale linked_error_cayley_sum)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "BR" => bondCompletedInner hw0 hw1
local notation "I" => inner hw0 hw1
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1

private theorem rc_exchange (a b c d : RC) :
    RCadd (RCadd a b) (RCadd c d) = RCadd (RCadd a c) (RCadd b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro aa bb
  refine Quotient.inductionOn₂ c d ?_
  intro cc dd
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (by decide)
      (fun | 0 => aa.approx n | 1 => bb.approx n
           | 2 => cc.approx n | _ => dd.approx n)))

def fourCopies (a : RC) : RC := RCadd (RCadd a a) (RCadd a a)

theorem fourCopies_mono {a b : RC} (h : RCle a b) :
    RCle (fourCopies a) (fourCopies b) :=
  RCadd_le_add (RCadd_le_add h h) (RCadd_le_add h h)

theorem fourCopies_eq_scale_four (a : RC) : fourCopies a = RCscale 4 a := by
  refine Quotient.inductionOn a ?_
  intro aa
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0)) (.add (.var 0) (.var 0)))
      (.mul (.const 4) (.var 0)) (by decide)
      (fun _ => aa.approx n)))

private theorem completed_neg_zero :
    completedNeg hw0 hw1 (completedZero hw0 hw1 width) =
      completedZero hw0 hw1 width := by
  have h := completedNeg_add hw0 hw1 (completedZero hw0 hw1 width)
  rw [completedAdd_zero] at h
  exact h

private theorem completed_sub_zero (x : V) :
    completedSub hw0 hw1 x (completedZero hw0 hw1 width) = x := by
  change completedAdd hw0 hw1 x
    (completedNeg hw0 hw1 (completedZero hw0 hw1 width)) = x
  rw [completed_neg_zero hw0 hw1, completedAdd_zero]

private theorem completed_sub_add_right (x y : V) :
    completedSub hw0 hw1 (completedAdd hw0 hw1 x y) y = x := by
  change completedAdd hw0 hw1 (completedAdd hw0 hw1 x y)
    (completedNeg hw0 hw1 y) = x
  rw [completedAdd_assoc, completedAdd_comm hw0 hw1 y (completedNeg hw0 hw1 y),
    completedNeg_add, completedAdd_zero]

/-- The existing squared-distance triangle, on the original all-nome Wilson
completion, gives a sqrt-free two-term norm ceiling. -/
theorem completed_norm_add_le (x y : V) :
    RCle (B (completedAdd hw0 hw1 x y) (completedAdd hw0 hw1 x y))
      (RCadd (RCadd (B x x) (B x x)) (RCadd (B y y) (B y y))) := by
  have h := completedDist_triangle hw0 hw1
    (completedAdd hw0 hw1 x y) y (completedZero hw0 hw1 width)
  unfold completedDist at h
  rw [completed_sub_zero hw0 hw1, completed_sub_add_right hw0 hw1,
    completed_sub_zero hw0 hw1] at h
  exact h

private theorem completed_norm_smul (c : Q') (x : V) :
    B (completedSmul hw0 hw1 c x) (completedSmul hw0 hw1 c x) =
      RCscale (c*c) (B x x) := by
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]

private theorem completed_norm_neg (x : V) :
    B (completedNeg hw0 hw1 x) (completedNeg hw0 hw1 x) = B x x := by
  change B (completedSmul hw0 hw1 (-1) x)
    (completedSmul hw0 hw1 (-1) x) = B x x
  rw [completed_norm_smul]
  have hc : ((-1 : Q')*(-1)).eqv 1 :=
    poly_identity_of_normal_eq
      (.mul (.const (-1)) (.const (-1))) (.const 1) (by decide) (fun _ => (0 : Q'))
  rw [scale_congr hc, RCscale_one]

/-- The original real physical bond carrier inherits the same norm-add
ceiling; no thermodynamic carrier is substituted. -/
theorem bond_norm_add_le (x y : RH) :
    RCle (BR (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y)
      (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y))
      (RCadd (RCadd (BR x x) (BR x x)) (RCadd (BR y y) (BR y y))) := by
  rw [bondValue_inner, bondValue_add, bondValue_inner, bondValue_inner]
  exact completed_norm_add_le hw0 hw1 _ _

private theorem bond_norm_smul (c : Q') (x : RH) :
    BR (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x)
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x) =
      RCscale (c*c) (BR x x) := by
  rw [bondValue_inner, bondValue_smul, bondValue_inner]
  exact completed_norm_smul hw0 hw1 c _

private theorem bond_norm_neg (x : RH) :
    BR (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x)
      (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x) = BR x x := by
  rw [bondValue_inner, bondValue_negate, bondValue_inner]
  exact completed_norm_neg hw0 hw1 _

/-- Squared norm on the actual complex physical bond carrier. -/
def normSq (x : H) : RC := (I x x).1

private theorem normSq_components (x : H) :
    normSq hw0 hw1 x = RCadd (BR x.1 x.1) (BR x.2 x.2) := rfl

private theorem normSq_realScale (c : Q') (x : H) :
    normSq hw0 hw1 (realScale hw0 hw1 c x) =
      RCscale (c*c) (normSq hw0 hw1 x) := by
  rw [normSq_components, normSq_components]
  change RCadd
    (BR (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x.1)
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x.1))
    (BR (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x.2)
      (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 c x.2)) = _
  rw [bond_norm_smul, bond_norm_smul, RCscale_RCadd]

private theorem normSq_cneg (x : H) :
    normSq hw0 hw1 (cneg hw0 hw1 x) = normSq hw0 hw1 x := by
  rw [normSq_components, normSq_components]
  change RCadd
    (BR (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x.1)
      (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x.1))
    (BR (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x.2)
      (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x.2)) = _
  rw [bond_norm_neg, bond_norm_neg]

/-- Sqrt-free complex norm triangle, obtained coordinatewise on the SAME
Wilson bond completion. -/
theorem normSq_add_le (x y : H) :
    RCle (normSq hw0 hw1 (A x y))
      (RCadd (RCadd (normSq hw0 hw1 x) (normSq hw0 hw1 x))
        (RCadd (normSq hw0 hw1 y) (normSq hw0 hw1 y))) := by
  have h₁ := bond_norm_add_le hw0 hw1 x.1 y.1
  have h₂ := bond_norm_add_le hw0 hw1 x.2 y.2
  have h := RCadd_le_add h₁ h₂
  change RCle (normSq hw0 hw1 (A x y))
    (RCadd
      (RCadd (RCadd (BR x.1 x.1) (BR x.1 x.1))
        (RCadd (BR y.1 y.1) (BR y.1 y.1)))
      (RCadd (RCadd (BR x.2 x.2) (BR x.2 x.2))
        (RCadd (BR y.2 y.2) (BR y.2 y.2)))) at h
  rw [rc_exchange
    (RCadd (BR x.1 x.1) (BR x.1 x.1))
    (RCadd (BR y.1 y.1) (BR y.1 y.1))
    (RCadd (BR x.2 x.2) (BR x.2 x.2))
    (RCadd (BR y.2 y.2) (BR y.2 y.2))] at h
  rw [rc_exchange (BR x.1 x.1) (BR x.1 x.1)
    (BR x.2 x.2) (BR x.2 x.2),
    rc_exchange (BR y.1 y.1) (BR y.1 y.1)
      (BR y.2 y.2) (BR y.2 y.2)] at h
  exact h

/-- Unitarity and the original squared-distance triangle give the exact
four-copy ceiling for a Cayley orbit sum. -/
theorem cayley_sum_norm_le (t : Q') (ht : (0 : Q') < t) (z : H) :
    RCle (normSq hw0 hw1 (A z (C t ht z)))
      (fourCopies (normSq hw0 hw1 z)) := by
  have h := normSq_add_le hw0 hw1 z (C t ht z)
  have hn : normSq hw0 hw1 (C t ht z) = normSq hw0 hw1 z :=
    congrArg Prod.fst
      (BF4WilsonAllNomeComplexBondOSScaledCayley.pairing_preserved
        hw0 hw1 t ht z z)
  rw [hn] at h
  exact h

/-- Actual linked graph local consistency is fourth order in squared norm.
The real rate is written as a computable rational scalar, without roots. -/
theorem linked_error_norm_le (t : Q') (ht : (0 : Q') < t)
    (d e : Domain hw0 hw1 (width := width))
    (hlink : Out d = In e) :
    RCle
      (normSq hw0 hw1
        (A (A (C t ht (In d)) (cneg hw0 hw1 (In d)))
          (imagScale hw0 hw1 t (A (Out d) (Out d)))))
      (RCscale ((t*t)*(t*t))
        (fourCopies (normSq hw0 hw1 (Out e)))) := by
  rw [linked_error_cayley_sum hw0 hw1 t ht d e hlink,
    normSq_cneg, normSq_realScale]
  exact RCscale_mono (Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))
    (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht)))
    (cayley_sum_norm_le hw0 hw1 t ht (Out e))

/-- The same local ceiling with the explicit fourth-order rational factor. -/
theorem linked_error_norm_le_four (t : Q') (ht : (0 : Q') < t)
    (d e : Domain hw0 hw1 (width := width))
    (hlink : Out d = In e) :
    RCle
      (normSq hw0 hw1
        (A (A (C t ht (In d)) (cneg hw0 hw1 (In d)))
          (imagScale hw0 hw1 t (A (Out d) (Out d)))))
      (RCscale ((4 : Q')*((t*t)*(t*t))) (normSq hw0 hw1 (Out e))) := by
  have h := linked_error_norm_le hw0 hw1 t ht d e hlink
  rw [fourCopies_eq_scale_four, RCscale_RCscale,
    scale_congr (Q'.mul_comm_eqv ((t*t)*(t*t)) 4)] at h
  exact h

/-- Explicit original preimage norm of the two represented Cauchy rows. -/
def preimageNorm
    (Y : (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy ×
      (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy) : RC :=
  let D := BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)
  let Class := Quotient.mk D.completionSetoid
  RCadd (B (Class Y.1) (Class Y.1)) (B (Class Y.2) (Class Y.2))

/-- The represented second core gives an actual bound on the SAME carrier.
The right side is the explicit original preimage norm, not a norm of the
twice-time-smoothed physical input. -/
theorem secondCore_error_norm_le (t : Q') (ht : (0 : Q') < t)
    (Y : (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy ×
      (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy) :
    RCle
      (normSq hw0 hw1
        (A (A (C t ht (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y)))
          (cneg hw0 hw1
            (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))))
          (imagScale hw0 hw1 t
            (A (Out (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))
              (Out (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))))))
      (RCscale ((t*t)*(t*t))
        (fourCopies (preimageNorm hw0 hw1 Y))) := by
  let d := BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y
  let e := BF4WilsonAllNomeComplexBondOSSecondCore.second hw0 hw1 Y
  have hlink : Out d = In e :=
    BF4WilsonAllNomeComplexBondOSSecondCore.first_output_eq_second_input hw0 hw1 Y
  have hbase := linked_error_norm_le hw0 hw1 t ht d e hlink
  have hsource := BF4WilsonAllNomeComplexBondOSSecondCore.second_output_norm_le
    hw0 hw1 Y
  have hfour : RCle (fourCopies (normSq hw0 hw1 (Out e)))
      (fourCopies (preimageNorm hw0 hw1 Y)) :=
    fourCopies_mono (by exact hsource)
  exact RCle_trans hbase
    (RCscale_mono (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))
      (Q'.mul_nonneg _ _ (Q'.le_of_lt ht) (Q'.le_of_lt ht))) hfour)

/-- Explicit represented-core fourth-order ceiling, with no source-free
extension to arbitrary derivative-domain outputs. -/
theorem secondCore_error_norm_le_four (t : Q') (ht : (0 : Q') < t)
    (Y : (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy ×
      (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)).Cauchy) :
    RCle
      (normSq hw0 hw1
        (A (A (C t ht (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y)))
          (cneg hw0 hw1
            (In (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))))
          (imagScale hw0 hw1 t
            (A (Out (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))
              (Out (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))))))
      (RCscale ((4 : Q')*((t*t)*(t*t))) (preimageNorm hw0 hw1 Y)) := by
  have h := secondCore_error_norm_le hw0 hw1 t ht Y
  rw [fourCopies_eq_scale_four, RCscale_RCscale,
    scale_congr (Q'.mul_comm_eqv ((t*t)*(t*t)) 4)] at h
  exact h

#print axioms completed_norm_add_le
#print axioms bond_norm_add_le
#print axioms fourCopies
#print axioms fourCopies_mono
#print axioms fourCopies_eq_scale_four
#print axioms normSq
#print axioms normSq_add_le
#print axioms cayley_sum_norm_le
#print axioms linked_error_norm_le
#print axioms linked_error_norm_le_four
#print axioms preimageNorm
#print axioms secondCore_error_norm_le
#print axioms secondCore_error_norm_le_four

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
