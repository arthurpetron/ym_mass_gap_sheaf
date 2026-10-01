/-
# Exact mixed-parameter defect on the original physical Cayley graph

Two positive rational Cayley steps are compared with their summed step on
the SAME original complex Wilson-bond completion. A subsequent norm estimate
uses a supplied linked second graph point. This file proves only
an exact finite identity, not a product limit or a time-composition law.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_add completedAdd_smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
  (graphMap graphMap_input graphMap_output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
  (diff graphError)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "N" => cneg hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "RA" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "RN" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "RS" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "Z" =>
  (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width),
   BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width))

private theorem add_assoc (x y z : H) : A (A x y) z = A x (A y z) :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_assoc hw0 hw1 x y z

private theorem add_comm (x y : H) : A x y = A y x :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_comm hw0 hw1 x y

private theorem add_zero (x : H) : A x Z = x :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_zero hw0 hw1 x

private theorem add_neg (x : H) :
    A x (N x) = Z :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_neg hw0 hw1 x

private theorem neg_add (x : H) :
    A (N x) x = Z :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.neg_add hw0 hw1 x

private theorem add_exchange (a b c d : H) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  calc
    A (A a b) (A c d) = A a (A b (A c d)) := add_assoc hw0 hw1 _ _ _
    _ = A a (A c (A b d)) := by
      rw [← add_assoc hw0 hw1 b c d, add_comm hw0 hw1 b c, add_assoc]
    _ = A (A a c) (A b d) := (add_assoc hw0 hw1 _ _ _).symm

private theorem add_move_last (a b c d : H) :
    A (A a b) (A c d) = A (A a d) (A b c) := by
  calc
    A (A a b) (A c d) = A (A a b) (A d c) := by rw [add_comm hw0 hw1 c d]
    _ = A (A a d) (A b c) := add_exchange hw0 hw1 a b d c

private theorem neg_additive (x y : H) : N (A x y) = A (N x) (N y) := by
  apply BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_right_cancel hw0 hw1
    _ _ (A x y)
  calc
    A (N (A x y)) (A x y) =
        Z :=
      neg_add hw0 hw1 _
    _ = A Z Z :=
      (BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.zero_add hw0 hw1 _).symm
    _ = A (A (N x) x) (A (N y) y) := by rw [neg_add,neg_add]
    _ = A (A (N x) (N y)) (A x y) := (add_exchange hw0 hw1 _ _ _ _).symm

private theorem neg_neg (x : H) : N (N x) = x := by
  apply BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_right_cancel hw0 hw1
    _ _ (N x)
  calc
    A (N (N x)) (N x) =
        Z := neg_add hw0 hw1 _
    _ = A x (N x) := (add_neg hw0 hw1 x).symm

private theorem diff_trans (a b c : H) :
    A (diff hw0 hw1 a b) (diff hw0 hw1 b c) = diff hw0 hw1 a c := by
  unfold diff
  calc
    A (A a (N b)) (A b (N c)) = A (A a (N c)) (A (N b) b) :=
      add_move_last hw0 hw1 _ _ _ _
    _ = A (A a (N c)) Z :=
      congrArg (A (A a (N c))) (neg_add hw0 hw1 b)
    _ = A a (N c) := add_zero hw0 hw1 _

private theorem neg_diff (a b : H) :
    N (diff hw0 hw1 a b) = diff hw0 hw1 b a := by
  unfold diff
  rw [neg_additive,neg_neg,add_comm]

private theorem mixed_error_algebra (p q r v U V W : H) :
    diff hw0 hw1 p v =
      A (A (A (A (diff hw0 hw1 p q) W)
        (A (diff hw0 hw1 q r) U))
        (N (A (diff hw0 hw1 v r) (A U V))))
        (A V (N W)) := by
  have h₁ : A (A (diff hw0 hw1 p q) W) (A (diff hw0 hw1 q r) U) =
      A (diff hw0 hw1 p r) (A W U) := by
    calc
      A (A (diff hw0 hw1 p q) W) (A (diff hw0 hw1 q r) U) =
          A (A (diff hw0 hw1 p q) (diff hw0 hw1 q r)) (A W U) :=
        add_exchange hw0 hw1 _ _ _ _
      _ = A (diff hw0 hw1 p r) (A W U) := by rw [diff_trans]
  have h₂ : A (diff hw0 hw1 p r) (N (diff hw0 hw1 v r)) =
      diff hw0 hw1 p v := by rw [neg_diff,diff_trans]
  have h₃ : A (A W U) (N (A U V)) = A W (N V) := by
    rw [neg_additive]
    calc
      A (A W U) (A (N U) (N V)) = A (A (A W U) (N U)) (N V) :=
        (add_assoc hw0 hw1 _ _ _).symm
      _ = A W (N V) := by
        rw [add_assoc hw0 hw1 W U (N U),add_neg,add_zero]
  have h₄ : A (A W (N V)) (A V (N W)) =
      Z := by
    calc
      A (A W (N V)) (A V (N W)) = A (A W (N W)) (A (N V) V) :=
        add_move_last hw0 hw1 _ _ _ _
      _ = A Z Z := by
        rw [add_neg,neg_add]
      _ = Z :=
        BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.zero_add hw0 hw1 _
  apply Eq.symm
  calc
    A (A (A (A (diff hw0 hw1 p q) W) (A (diff hw0 hw1 q r) U))
        (N (A (diff hw0 hw1 v r) (A U V)))) (A V (N W)) =
        A (A (A (diff hw0 hw1 p r) (A W U))
          (A (N (diff hw0 hw1 v r)) (N (A U V)))) (A V (N W)) := by
      rw [h₁,neg_additive]
    _ = A (A (A (diff hw0 hw1 p r) (N (diff hw0 hw1 v r)))
          (A (A W U) (N (A U V)))) (A V (N W)) :=
      congrArg (fun q : H => A q (A V (N W)))
        (add_exchange hw0 hw1 (diff hw0 hw1 p r) (A W U)
          (N (diff hw0 hw1 v r)) (N (A U V)))
    _ = A (A (diff hw0 hw1 p v) (A W (N V))) (A V (N W)) := by rw [h₂,h₃]
    _ = A (diff hw0 hw1 p v) (A (A W (N V)) (A V (N W))) :=
      add_assoc hw0 hw1 _ _ _
    _ = diff hw0 hw1 p v := by rw [h₄,add_zero]

private theorem real_neg_additive (x y : RH) : RN (RA x y) = RA (RN x) (RN y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_negate,bondValue_add]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem real_scale_add_parameter (a b : Q') (x : RH) :
    RS (a+b) x = RA (RS a x) (RS b x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact (completedAdd_smul hw0 hw1 a b _).symm

private theorem real_scale_add (a : Q') (x y : RH) :
    RS a (RA x y) = RA (RS a x) (RS a y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 a _ _

private theorem real_scale_neg (a : Q') (x : RH) : RS a (RN x) = RN (RS a x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change completedSmul hw0 hw1 a (completedSmul hw0 hw1 (-1) (bondValue hw0 hw1 x)) =
    completedSmul hw0 hw1 (-1) (completedSmul hw0 hw1 a (bondValue hw0 hw1 x))
  rw [YMGap.Continuum.BF4WilsonAllNomeLinearLaws.completedSmul_mul,
    YMGap.Continuum.BF4WilsonAllNomeLinearLaws.completedSmul_mul]
  exact YMGap.Continuum.BF4WilsonAllNomeLinearLaws.completedSmul_congr hw0 hw1
    (Q'.mul_comm_eqv a (-1)) _

/-- Actual rational addition for the imaginary graph rotation. -/
theorem imagScale_add_parameter (a b : Q') (x : H) :
    imagScale hw0 hw1 (a+b) x =
      A (imagScale hw0 hw1 a x) (imagScale hw0 hw1 b x) := by
  apply Prod.ext
  · exact (congrArg (RN) (real_scale_add_parameter hw0 hw1 a b x.2)).trans
      (real_neg_additive hw0 hw1 (RS a x.2) (RS b x.2))
  · exact real_scale_add_parameter hw0 hw1 a b x.1

private theorem imag_add (a : Q') (x y : H) :
    imagScale hw0 hw1 a (A x y) =
      A (imagScale hw0 hw1 a x) (imagScale hw0 hw1 a y) := by
  apply Prod.ext
  · exact (congrArg (RN) (real_scale_add hw0 hw1 a x.2 y.2)).trans
      (real_neg_additive hw0 hw1 (RS a x.2) (RS a y.2))
  · exact real_scale_add hw0 hw1 a x.1 y.1

private theorem imag_neg (a : Q') (x : H) :
    imagScale hw0 hw1 a (N x) = N (imagScale hw0 hw1 a x) := by
  apply Prod.ext
  · change RN (RS a (RN x.2)) = RN (RN (RS a x.2))
    rw [real_scale_neg]
  · exact real_scale_neg hw0 hw1 a x.1

private theorem imag_double_diff (a : Q') (x y : H) :
    imagScale hw0 hw1 a (A (diff hw0 hw1 x y) (diff hw0 hw1 x y)) =
      diff hw0 hw1 (imagScale hw0 hw1 a (A x x))
        (imagScale hw0 hw1 a (A y y)) := by
  let u := imagScale hw0 hw1 a x
  let v := imagScale hw0 hw1 a y
  calc
    imagScale hw0 hw1 a (A (diff hw0 hw1 x y) (diff hw0 hw1 x y)) =
        A (A u (N v)) (A u (N v)) := by
      unfold diff
      simp only [imag_add,imag_neg]
      rfl
    _ = A (A u u) (A (N v) (N v)) := add_exchange hw0 hw1 _ _ _ _
    _ = diff hw0 hw1 (imagScale hw0 hw1 a (A x x))
        (imagScale hw0 hw1 a (A y y)) := by
      rw [imag_add,imag_add]
      unfold diff
      rw [neg_additive]

/-- The mixed one-step defect on the SAME original graph. A subsequent bound
uses a supplied linked second point; this algebraic identity needs only d. -/
theorem mixed_error_identity (a b : Q') (ha : (0 : Q') < a) (hb : (0 : Q') < b)
    (hc : (0 : Q') < a+b) (d : D) :
    diff hw0 hw1 (C b hb (C a ha (In d))) (C (a+b) hc (In d)) =
      A (A (A (graphError hw0 hw1 b hb (graphMap hw0 hw1 a ha d))
          (graphError hw0 hw1 a ha d))
          (N (graphError hw0 hw1 (a+b) hc d)))
        (imagScale hw0 hw1 b
          (A (diff hw0 hw1 (Out d) (C a ha (Out d)))
             (diff hw0 hw1 (Out d) (C a ha (Out d))))) := by
  let x := In d
  let y := Out d
  let p := C b hb (C a ha x)
  let q := C a ha x
  let v := C (a+b) hc x
  let U := imagScale hw0 hw1 a (A y y)
  let V := imagScale hw0 hw1 b (A y y)
  let W := imagScale hw0 hw1 b (A (C a ha y) (C a ha y))
  have h₁ : graphError hw0 hw1 b hb (graphMap hw0 hw1 a ha d) =
      A (diff hw0 hw1 p q) W := by
    unfold graphError p q W x y
    rw [graphMap_input,graphMap_output]
  have h₀ : graphError hw0 hw1 a ha d = A (diff hw0 hw1 q x) U := by
    rfl
  have h₂ : graphError hw0 hw1 (a+b) hc d =
      A (diff hw0 hw1 v x) (A U V) := by
    unfold graphError v U V x y
    rw [imagScale_add_parameter]
  have hcorrection :
      imagScale hw0 hw1 b
        (A (diff hw0 hw1 y (C a ha y)) (diff hw0 hw1 y (C a ha y))) =
      A V (N W) := by
    rw [imag_double_diff]
    unfold V W
    rfl
  rw [h₁,h₀,h₂,hcorrection]
  exact mixed_error_algebra hw0 hw1 p q x v U V W

#print axioms imagScale_add_parameter
#print axioms mixed_error_identity

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyMixedIdentity
