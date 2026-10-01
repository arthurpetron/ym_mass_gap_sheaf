/-
# First graph differences for the ORIGINAL physical Cayley family

This module works on the same completed complex Wilson-bond carrier and its
constructed derivative graph.  Its estimates are local rational-parameter
statements on graph points, not a doubled-step refinement theorem, physical-time
calibration, group, or continuum limit.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul completedZero)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedAdd_comm completedZero_add completedAdd_zero
    completedNeg_add completedSmul_add)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_smul_left completedInner_smul_right)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (imagScale negativeImagScale cneg plus_input_imag minus_input_imag
    cayley_graph imagScale_smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyErrorBound
  (normSq normSq_add_le cayley_sum_norm_le fourCopies fourCopies_eq_scale_four)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Neg" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1

private theorem completed_norm_smul (c : Q')
    (x : BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width) :
    BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
        (completedSmul hw0 hw1 c x) (completedSmul hw0 hw1 c x) =
      RCscale (c*c)
        (BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x) := by
  rw [completedInner_smul_left,completedInner_smul_right,RCscale_RCscale]

private theorem completed_norm_neg
    (x : BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width) :
    BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
        (completedNeg hw0 hw1 x) (completedNeg hw0 hw1 x) =
      BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1 x x := by
  change BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
      (completedSmul hw0 hw1 (-1) x) (completedSmul hw0 hw1 (-1) x) = _
  rw [completed_norm_smul]
  have hc : Q'.eqv ((-1 : Q')*(-1)) 1 := by decide
  rw [scale_congr hc,RCscale_one]

private theorem real_norm_smul (c : Q') (x : RH) :
    bondCompletedInner hw0 hw1 (Scale c x) (Scale c x) =
      RCscale (c*c) (bondCompletedInner hw0 hw1 x x) := by
  rw [BF4WilsonAllNomeBondOSTime.bondValue_inner,bondValue_smul,
    BF4WilsonAllNomeBondOSTime.bondValue_inner]
  exact completed_norm_smul hw0 hw1 c _

private theorem real_norm_neg (x : RH) :
    bondCompletedInner hw0 hw1 (Neg x) (Neg x) =
      bondCompletedInner hw0 hw1 x x := by
  rw [BF4WilsonAllNomeBondOSTime.bondValue_inner,bondValue_negate,
    BF4WilsonAllNomeBondOSTime.bondValue_inner]
  exact completed_norm_neg hw0 hw1 _

private theorem rc_add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro aa bb
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (aa.approx n) (bb.approx n)))

/-- Norm preservation under the actual physical componentwise additive
inverse, needed by finite Cayley-product telescoping. -/
theorem normSq_neg (x : H) :
    normSq hw0 hw1 (cneg hw0 hw1 x) = normSq hw0 hw1 x := by
  change RCadd (bondCompletedInner hw0 hw1 (Neg x.1) (Neg x.1))
      (bondCompletedInner hw0 hw1 (Neg x.2) (Neg x.2)) =
    RCadd (bondCompletedInner hw0 hw1 x.1 x.1)
      (bondCompletedInner hw0 hw1 x.2 x.2)
  rw [real_norm_neg,real_norm_neg]

/-- The rational imaginary rotation has exactly its expected squared norm
on the SAME complex physical quotient. -/
theorem normSq_imagScale (t : Q') (x : H) :
    normSq hw0 hw1 (imagScale hw0 hw1 t x) =
      RCscale (t*t) (normSq hw0 hw1 x) := by
  change RCadd
    (bondCompletedInner hw0 hw1 (Neg (Scale t x.2)) (Neg (Scale t x.2)))
    (bondCompletedInner hw0 hw1 (Scale t x.1) (Scale t x.1)) = _
  rw [real_norm_neg,real_norm_smul,real_norm_smul]
  rw [← RCscale_RCadd]
  exact congrArg (RCscale (t*t))
    (rc_add_comm (bondCompletedInner hw0 hw1 x.2 x.2)
      (bondCompletedInner hw0 hw1 x.1 x.1))

private def zero : H :=
  (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width),
   BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width))

private theorem real_add_assoc (x y z : RH) :
    Add (Add x y) z = Add x (Add y z) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_add]
  exact completedAdd_assoc hw0 hw1 _ _ _

private theorem real_add_comm (x y : RH) : Add x y = Add y x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_add]
  exact completedAdd_comm hw0 hw1 _ _

private theorem real_add_zero (x : RH) :
    Add x (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1) = x := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_add,BF4WilsonAllNomeBondOSLinear.bondValue_zero]
  exact completedAdd_zero hw0 hw1 _

private theorem real_neg_add (x : RH) :
    Add (Neg x) x = BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_add,bondValue_negate,
    BF4WilsonAllNomeBondOSLinear.bondValue_zero]
  exact completedNeg_add hw0 hw1 _

private theorem real_scale_add (t : Q') (x y : RH) :
    Scale t (Add x y) = Add (Scale t x) (Scale t y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 t _ _

private theorem real_neg_additive (x y : RH) :
    Neg (Add x y) = Add (Neg x) (Neg y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_add,bondValue_negate]
  exact completedSmul_add hw0 hw1 (-1) _ _

/-- The original physical complex addition is associative; exported for
finite Cayley-product difference normalization. -/
theorem add_assoc (x y z : H) : A (A x y) z = A x (A y z) :=
  Prod.ext (real_add_assoc hw0 hw1 x.1 y.1 z.1)
    (real_add_assoc hw0 hw1 x.2 y.2 z.2)

/-- Commutativity on the same physical quotient, with no representative
selection. -/
theorem add_comm (x y : H) : A x y = A y x :=
  Prod.ext (real_add_comm hw0 hw1 x.1 y.1)
    (real_add_comm hw0 hw1 x.2 y.2)

theorem add_zero (x : H) : A x (zero hw0 hw1) = x :=
  Prod.ext (real_add_zero hw0 hw1 x.1) (real_add_zero hw0 hw1 x.2)

theorem zero_add (x : H) : A (zero hw0 hw1) x = x := by
  rw [add_comm,add_zero]

theorem neg_add (x : H) : A (cneg hw0 hw1 x) x = zero hw0 hw1 :=
  Prod.ext (real_neg_add hw0 hw1 x.1) (real_neg_add hw0 hw1 x.2)

theorem add_neg (x : H) : A x (cneg hw0 hw1 x) = zero hw0 hw1 := by
  rw [add_comm,neg_add]

/-- Cancellation in the actual completed physical carrier. -/
theorem add_left_cancel (a b c : H) (h : A a b = A a c) : b = c := by
  have hh := congrArg (fun v => A (cneg hw0 hw1 a) v) h
  dsimp only at hh
  rw [← add_assoc,← add_assoc,neg_add,zero_add,zero_add] at hh
  exact hh

theorem add_right_cancel (a b c : H) (h : A a c = A b c) : a = b := by
  apply add_left_cancel hw0 hw1 c
  calc
    A c a = A a c := add_comm hw0 hw1 c a
    _ = A b c := h
    _ = A c b := add_comm hw0 hw1 b c

private theorem imag_add (t : Q') (x y : H) :
    imagScale hw0 hw1 t (A x y) =
      A (imagScale hw0 hw1 t x) (imagScale hw0 hw1 t y) := by
  apply Prod.ext
  · exact (congrArg Neg (real_scale_add hw0 hw1 t x.2 y.2)).trans
      (real_neg_additive hw0 hw1 (Scale t x.2) (Scale t y.2))
  · exact real_scale_add hw0 hw1 t x.1 y.1

private theorem imag_negative_cancel (t : Q') (x : H) :
    A (imagScale hw0 hw1 t x) (negativeImagScale hw0 hw1 t x) =
      zero hw0 hw1 := by
  apply Prod.ext
  · exact real_neg_add hw0 hw1 (Scale t x.2)
  · change Add (Scale t x.1) (Neg (Scale t x.1)) =
      BF4WilsonAllNomeBondOSLinear.zero hw0 hw1
    rw [real_add_comm]
    exact real_neg_add hw0 hw1 (Scale t x.1)

private theorem cayley_imag (s t : Q') (ht : (0 : Q') < t) (x : H) :
    C t ht (imagScale hw0 hw1 s x) =
      imagScale hw0 hw1 s (C t ht x) := by
  rw [imagScale_smul,imagScale_smul]
  exact BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_smul hw0 hw1 t ht
    (ofQ' 0) (ofQ' s)
    (BF4WilsonAllNomeCompletedRealScalar.rationalCauchy 0)
    (BF4WilsonAllNomeCompletedRealScalar.rationalCauchy s) x

private theorem first_rearrange (t : Q') (b c y z : H)
    (h : A b (imagScale hw0 hw1 t c) =
      A y (negativeImagScale hw0 hw1 t z)) :
    A y (cneg hw0 hw1 b) = imagScale hw0 hw1 t (A z c) := by
  let p := imagScale hw0 hw1 t z
  let q := imagScale hw0 hw1 t c
  have hp : imagScale hw0 hw1 t (A z c) = A p q :=
    imag_add hw0 hw1 t z c
  rw [hp]
  apply add_right_cancel hw0 hw1 _ _ b
  calc
    A (A y (cneg hw0 hw1 b)) b = y := by
      rw [add_assoc,neg_add,add_zero]
    _ = A p (A y (negativeImagScale hw0 hw1 t z)) := by
      have hh : A p (A y (negativeImagScale hw0 hw1 t z)) = y := calc
        A p (A y (negativeImagScale hw0 hw1 t z)) =
            A y (A p (negativeImagScale hw0 hw1 t z)) := by
          rw [← add_assoc hw0 hw1 p y _,add_comm hw0 hw1 p y,add_assoc]
        _ = y := by rw [imag_negative_cancel,add_zero]
      exact hh.symm
    _ = A p (A b q) := by rw [h]
    _ = A (A p q) b := by
      calc
        A p (A b q) = A p (A q b) := by rw [add_comm hw0 hw1 b q]
        _ = A (A p q) b := (add_assoc hw0 hw1 _ _ _).symm

/-- First-order exact graph difference.  This is a true domain statement:
no unbounded action is applied to an arbitrary completed vector. -/
theorem cayley_domain_difference (t : Q') (ht : (0 : Q') < t) (d : D) :
    A (In d) (cneg hw0 hw1 (C t ht (In d))) =
      imagScale hw0 hw1 t
        (A (Out d) (C t ht (Out d))) := by
  have h : A (C t ht (In d))
      (imagScale hw0 hw1 t (C t ht (Out d))) =
        A (In d) (negativeImagScale hw0 hw1 t (Out d)) := by
    calc
      A (C t ht (In d)) (imagScale hw0 hw1 t (C t ht (Out d))) =
          A (C t ht (In d)) (C t ht (imagScale hw0 hw1 t (Out d))) := by
            rw [cayley_imag]
      _ = C t ht (A (In d) (imagScale hw0 hw1 t (Out d))) :=
        (BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add
          hw0 hw1 t ht _ _).symm
      _ = C t ht (BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.plus
          hw0 hw1 t d) := by rw [plus_input_imag]
      _ = BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.minus hw0 hw1 t d :=
        cayley_graph hw0 hw1 t ht d
      _ = A (In d) (negativeImagScale hw0 hw1 t (Out d)) :=
        minus_input_imag hw0 hw1 t d
  exact first_rearrange hw0 hw1 t _ _ _ _ h

/-- The first graph difference has a source-independent norm ceiling on
the ACTUAL graph output.  This is the ingredient that avoids an `A³` point. -/
theorem cayley_domain_difference_norm_le (t : Q') (ht : (0 : Q') < t)
    (d : D) :
    RCle
      (normSq hw0 hw1
        (A (In d) (cneg hw0 hw1 (C t ht (In d)))))
      (RCscale (t*t) (fourCopies (normSq hw0 hw1 (Out d)))) := by
  rw [cayley_domain_difference, normSq_imagScale]
  exact RCscale_mono (Q'.mul_nonneg _ _
    (Q'.le_of_lt ht) (Q'.le_of_lt ht))
    (cayley_sum_norm_le hw0 hw1 t ht (Out d))

theorem cayley_domain_difference_norm_le_four (t : Q')
    (ht : (0 : Q') < t) (d : D) :
    RCle
      (normSq hw0 hw1
        (A (In d) (cneg hw0 hw1 (C t ht (In d)))))
      (RCscale ((4 : Q')*(t*t)) (normSq hw0 hw1 (Out d))) := by
  have h := cayley_domain_difference_norm_le hw0 hw1 t ht d
  rw [fourCopies_eq_scale_four,RCscale_RCscale,
    scale_congr (Q'.mul_comm_eqv (t*t) 4)] at h
  exact h

#print axioms add_assoc
#print axioms add_comm
#print axioms add_left_cancel
#print axioms add_right_cancel
#print axioms cayley_domain_difference
#print axioms normSq_neg
#print axioms normSq_imagScale
#print axioms cayley_domain_difference_norm_le
#print axioms cayley_domain_difference_norm_le_four

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
