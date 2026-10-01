/-
# Exact two-step error of the ORIGINAL physical Cayley map

The four-error identity is finite additive algebra on the constructed
complex Wilson bond carrier.  Every source term uses the SAME derivative
graph and the actual graph-preserving Cayley witness.  No product limit,
time calibration, or continuum assertion occurs here.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_add completedSmul_congr completedAdd_smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
  (cneg imagScale)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyCommutation
  (graphMap graphMap_input graphMap_output)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "A" => BF4WilsonAllNomeComplexBondOSTime.add hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "N" => cneg hw0 hw1
local notation "S" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "RA" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Z" =>
  (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width),
   BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width))

/-- Difference on the SAME complex physical quotient. -/
def diff (x y : H) : H := A x (N y)

/-- The original one-step graph error, with the complete factor-two
imaginary phase explicitly present. -/
def graphError (t : Q') (_ht : (0 : Q') < t) (d : D) : H :=
  A (diff hw0 hw1 (C t _ht (In d)) (In d))
    (imagScale hw0 hw1 t (A (Out d) (Out d)))

private theorem add_assoc (x y z : H) : A (A x y) z = A x (A y z) :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_assoc hw0 hw1 x y z

private theorem add_comm (x y : H) : A x y = A y x :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_comm hw0 hw1 x y

private theorem add_zero (x : H) : A x Z = x :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_zero hw0 hw1 x

private theorem zero_add (x : H) : A Z x = x :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.zero_add hw0 hw1 x

private theorem neg_add (x : H) : A (N x) x = Z :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.neg_add hw0 hw1 x

private theorem add_neg (x : H) : A x (N x) = Z :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_neg hw0 hw1 x

private theorem add_right_cancel (a b c : H) (h : A a c = A b c) : a = b :=
  BF4WilsonAllNomeComplexBondOSScaledCayleyRefinement.add_right_cancel
    hw0 hw1 a b c h

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
    A (A a b) (A c d) = A (A a b) (A d c) := by
      rw [add_comm hw0 hw1 c d]
    _ = A (A a d) (A b c) := add_exchange hw0 hw1 a b d c

private theorem neg_additive (x y : H) : N (A x y) = A (N x) (N y) := by
  apply add_right_cancel hw0 hw1 _ _ (A x y)
  calc
    A (N (A x y)) (A x y) = Z := neg_add hw0 hw1 _
    _ = A Z Z := (zero_add hw0 hw1 Z).symm
    _ = A (A (N x) x) (A (N y) y) := by
      rw [neg_add,neg_add]
    _ = A (A (N x) (N y)) (A x y) :=
      (add_exchange hw0 hw1 _ _ _ _).symm

private theorem neg_neg (x : H) : N (N x) = x := by
  apply add_right_cancel hw0 hw1 _ _ (N x)
  calc
    A (N (N x)) (N x) = Z := neg_add hw0 hw1 _
    _ = A x (N x) := (add_neg hw0 hw1 x).symm

private theorem diff_trans (a b c : H) :
    A (diff hw0 hw1 a b) (diff hw0 hw1 b c) =
      diff hw0 hw1 a c := by
  unfold diff
  calc
    A (A a (N b)) (A b (N c)) = A (A a (N c)) (A (N b) b) :=
      add_move_last hw0 hw1 _ _ _ _
    _ = A (A a (N c)) Z := by rw [neg_add]
    _ = A a (N c) := add_zero hw0 hw1 _

private theorem neg_diff (a b : H) :
    N (diff hw0 hw1 a b) = diff hw0 hw1 b a := by
  unfold diff
  rw [neg_additive,neg_neg,add_comm]

private theorem twice_cancel (x y : H) :
    A (A x y) (N y) = x := by
  rw [add_assoc,add_neg,add_zero]

/-- Pure finite additive cancellation; the ambient variable names correspond
to two Cayley steps, one doubled step, and two imaginary graph rotations. -/
private theorem four_error_algebra (a b c d u v : H) :
    diff hw0 hw1 a d =
      A (A (A
          (A (diff hw0 hw1 a b) (A v v))
          (A (diff hw0 hw1 b c) (A u u)))
          (N (A (diff hw0 hw1 d c) (A (A u u) (A u u)))))
        (A (A u u) (N (A v v))) := by
  let U := A u u
  let V := A v v
  have h₁ : A (A (diff hw0 hw1 a b) V)
      (A (diff hw0 hw1 b c) U) =
      A (diff hw0 hw1 a c) (A V U) := by
    calc
      A (A (diff hw0 hw1 a b) V)
          (A (diff hw0 hw1 b c) U) =
        A (A (diff hw0 hw1 a b) (diff hw0 hw1 b c)) (A V U) :=
          add_exchange hw0 hw1 _ _ _ _
      _ = A (diff hw0 hw1 a c) (A V U) := by rw [diff_trans]
  have h₂ : A (diff hw0 hw1 a c) (N (diff hw0 hw1 d c)) =
      diff hw0 hw1 a d := by
    rw [neg_diff,diff_trans]
  have h₃ : A (A V U) (N (A U U)) = A V (N U) := by
    rw [neg_additive]
    calc
      A (A V U) (A (N U) (N U)) =
          A (A (A V U) (N U)) (N U) :=
            (add_assoc hw0 hw1 _ _ _).symm
      _ = A V (N U) := by rw [twice_cancel]
  have h₄ : A (A V (N U)) (A U (N V)) = Z := by
    calc
      A (A V (N U)) (A U (N V)) =
          A (A V (N V)) (A (N U) U) := add_move_last hw0 hw1 _ _ _ _
      _ = A Z Z := by rw [add_neg,neg_add]
      _ = Z := zero_add hw0 hw1 Z
  apply Eq.symm
  calc
    A (A (A (A (diff hw0 hw1 a b) V)
          (A (diff hw0 hw1 b c) U))
          (N (A (diff hw0 hw1 d c) (A U U))))
        (A U (N V)) =
      A (A (A (diff hw0 hw1 a c) (A V U))
        (A (N (diff hw0 hw1 d c)) (N (A U U))))
        (A U (N V)) := by rw [h₁,neg_additive]
    _ = A (A (A (diff hw0 hw1 a c) (N (diff hw0 hw1 d c)))
        (A (A V U) (N (A U U))))
        (A U (N V)) :=
      congrArg (fun q : H => A q (A U (N V)))
        (add_exchange hw0 hw1 (diff hw0 hw1 a c) (A V U)
          (N (diff hw0 hw1 d c)) (N (A U U)))
    _ = A (A (diff hw0 hw1 a d) (A V (N U)))
        (A U (N V)) := by rw [h₂,h₃]
    _ = A (diff hw0 hw1 a d)
        (A (A V (N U)) (A U (N V))) := add_assoc hw0 hw1 _ _ _
    _ = diff hw0 hw1 a d := by rw [h₄,add_zero]

private theorem real_scale_add (h : Q') (x y : RH) :
    S h (RA x y) = RA (S h x) (S h y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact completedSmul_add hw0 hw1 h _ _

private theorem real_neg_additive (x y : RH) :
    BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 (RA x y) =
      RA (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x)
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_negate,bondValue_add]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem real_scale_neg (h : Q') (x : RH) :
    S h (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x) =
      BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 (S h x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change completedSmul hw0 hw1 h
      (completedSmul hw0 hw1 (-1) (bondValue hw0 hw1 x)) =
    completedSmul hw0 hw1 (-1)
      (completedSmul hw0 hw1 h (bondValue hw0 hw1 x))
  rw [YMGap.Continuum.BF4WilsonAllNomeLinearLaws.completedSmul_mul,
    YMGap.Continuum.BF4WilsonAllNomeLinearLaws.completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv h (-1)) _

private theorem real_neg_neg (x : RH) :
    BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x) = x :=
  congrArg Prod.fst
    (neg_neg hw0 hw1
      (x,BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width)))

private theorem real_scale_double (h : Q') (x : RH) :
    S ((2 : Q')*h) x = RA (S h x) (S h x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  have hc : Q'.eqv ((2 : Q')*h) (h+h) :=
    poly_identity_of_normal_eq
      (.mul (.const 2) (.var 0)) (.add (.var 0) (.var 0))
      (by decide) (fun _ => h)
  calc
    completedSmul hw0 hw1 ((2 : Q')*h) (bondValue hw0 hw1 x) =
        completedSmul hw0 hw1 (h+h) (bondValue hw0 hw1 x) :=
          completedSmul_congr hw0 hw1 hc _
    _ = completedAdd hw0 hw1
        (completedSmul hw0 hw1 h (bondValue hw0 hw1 x))
        (completedSmul hw0 hw1 h (bondValue hw0 hw1 x)) :=
          (completedAdd_smul hw0 hw1 h h _).symm

private theorem imag_add (h : Q') (x y : H) :
    imagScale hw0 hw1 h (A x y) =
      A (imagScale hw0 hw1 h x) (imagScale hw0 hw1 h y) := by
  apply Prod.ext
  · exact (congrArg (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1)
      (real_scale_add hw0 hw1 h x.2 y.2)).trans
      (real_neg_additive hw0 hw1 (S h x.2) (S h y.2))
  · exact real_scale_add hw0 hw1 h x.1 y.1

private theorem imag_neg (h : Q') (x : H) :
    imagScale hw0 hw1 h (N x) = N (imagScale hw0 hw1 h x) := by
  apply Prod.ext
  · change BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
        (S h (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 x.2)) =
      BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
        (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1 (S h x.2))
    rw [real_scale_neg]
  · exact real_scale_neg hw0 hw1 h x.1

/-- The rational doubled parameter agrees with two actual imaginary
rotations, using a checked scalar polynomial identity. -/
theorem imag_double (h : Q') (x : H) :
    imagScale hw0 hw1 ((2 : Q')*h) x =
      A (imagScale hw0 hw1 h x) (imagScale hw0 hw1 h x) := by
  apply Prod.ext
  · exact (congrArg (BF4WilsonAllNomeBondOSLinear.negate hw0 hw1)
      (real_scale_double hw0 hw1 h x.2)).trans
      (real_neg_additive hw0 hw1 (S h x.2) (S h x.2))
  · exact real_scale_double hw0 hw1 h x.1

/-- The promised EXACT doubled-step four-error decomposition.  No linked
second graph point is needed for this algebraic identity; the norm consumer
will provide it to bound the original second output. -/
theorem doubled_error_identity (h : Q') (hh : (0 : Q') < h)
    (h2 : (0 : Q') < ((2 : Q')*h)) (d : D) :
    diff hw0 hw1 (C h hh (C h hh (In d))) (C ((2 : Q')*h) h2 (In d)) =
      A (A (A
          (graphError hw0 hw1 h hh (graphMap hw0 hw1 h hh d))
          (graphError hw0 hw1 h hh d))
          (N (graphError hw0 hw1 ((2 : Q')*h) h2 d)))
        (imagScale hw0 hw1 ((2 : Q')*h)
          (diff hw0 hw1 (Out d) (C h hh (Out d)))) := by
  let x := In d
  let y := Out d
  let a := C h hh (C h hh x)
  let b := C h hh x
  let c := x
  let z := C ((2 : Q')*h) h2 x
  let u := imagScale hw0 hw1 h y
  let v := imagScale hw0 hw1 h (C h hh y)
  have h₁ : graphError hw0 hw1 h hh (graphMap hw0 hw1 h hh d) =
      A (diff hw0 hw1 a b) (A v v) := by
    unfold graphError a b v y x
    rw [graphMap_input,graphMap_output,imag_add]
  have h₀ : graphError hw0 hw1 h hh d =
      A (diff hw0 hw1 b c) (A u u) := by
    unfold graphError b c u y x
    rw [imag_add]
  have h₂ : graphError hw0 hw1 ((2 : Q')*h) h2 d =
      A (diff hw0 hw1 z c) (A (A u u) (A u u)) := by
    unfold graphError z c u y x
    rw [imag_add,imag_double]
  have hc : imagScale hw0 hw1 ((2 : Q')*h)
      (diff hw0 hw1 (Out d) (C h hh (Out d))) =
      A (A u u) (N (A v v)) := by
    unfold diff u v y
    rw [imag_add,imag_neg,imag_double,imag_double]
  rw [h₁,h₀,h₂,hc]
  exact four_error_algebra hw0 hw1 a b c z u v

#print axioms diff
#print axioms graphError
#print axioms imag_double
#print axioms doubled_error_identity

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyDoubledIdentity
