/-
# Linked-graph consistency of the actual scaled physical Cayley map

The argument uses two linked points of the ORIGINAL complex physical
derivative graph.  The parameter is rational; its complex scalar action
retains both explicit rational Cauchy witnesses.  There is no assertion that
an arbitrary graph output belongs to the derivative domain, and no
identification with physical time or a logarithm.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayley
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_negate bondValue_sub bondValue_smul bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
  (rationalCauchy completedRealSmul_ofQ')
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul completedZero)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedAdd_assoc completedAdd_comm completedZero_add completedAdd_zero
    completedNeg_add completedSmul_one completedSmul_zero completedSmul_mul
    completedSmul_add completedAdd_smul completedSmul_congr)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
  (add smul)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts
  (plus minus plusDomain)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
  (t : Q') (ht : (0 : Q') < t)

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "Add" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "Neg" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "Scale" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "A" => add hw0 hw1
local notation "In" => input hw0 hw1
local notation "Out" => output hw0 hw1
local notation "C" => BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1 t ht
local notation "P" => plus hw0 hw1 t
local notation "M" => minus hw0 hw1 t

/-- Multiplication by the rational imaginary scalar `i*t` on the SAME
completed physical carrier, written componentwise to expose the graph law. -/
def imagScale (x : H) : H := (Neg (Scale t x.2), Scale t x.1)

/-- Multiplication by `-i*t`, retaining the opposite graph shift. -/
def negativeImagScale (x : H) : H := (Scale t x.2, Neg (Scale t x.1))

/-- The imaginary rotation is the already-defined complex scalar operation,
with both rational Cauchy witnesses supplied rather than inferred. -/
theorem imagScale_smul (x : H) :
    imagScale hw0 hw1 t x =
      smul hw0 hw1 (ofQ' 0) (ofQ' t)
        (rationalCauchy 0) (rationalCauchy t) x := by
  apply Prod.ext
  · apply bondValue_injective hw0 hw1
    simp only [imagScale, BF4WilsonAllNomeComplexBondOSTime.smul,
      bondValue_negate, bondValue_smul, bondValue_sub, bondValue_realSmul]
    simp only [completedRealSmul_ofQ', completedSmul_zero]
    change completedNeg hw0 hw1
      (completedSmul hw0 hw1 t (bondValue hw0 hw1 x.2)) =
        completedAdd hw0 hw1 (completedZero hw0 hw1 width)
          (completedNeg hw0 hw1
            (completedSmul hw0 hw1 t (bondValue hw0 hw1 x.2)))
    exact (completedZero_add hw0 hw1 _).symm
  · apply bondValue_injective hw0 hw1
    simp only [imagScale, BF4WilsonAllNomeComplexBondOSTime.smul,
      bondValue_add, bondValue_smul, bondValue_realSmul]
    simp only [completedRealSmul_ofQ', completedSmul_zero]
    exact (completedAdd_zero hw0 hw1 _).symm

/-- The displayed plus shift is literally input plus the rational imaginary
rotation of output.  No extra graph point or domain invariance is used. -/
theorem plus_input_imag (d : D) :
    P d = A (In d) (imagScale hw0 hw1 t (Out d)) := by
  rfl

theorem minus_input_imag (d : D) :
    M d = A (In d) (negativeImagScale hw0 hw1 t (Out d)) := by
  rfl

/-- Cayley action on each *actual* graph shift; surjectivity of the plus
shift has already been constructed on this same carrier. -/
theorem cayley_graph (d : D) : C (P d) = M d := by
  exact congrArg (M) (BF4WilsonAllNomeComplexBondOSScaledCayley.plus_left
    hw0 hw1 t ht d)

/-- The componentwise additive inverse on the existing physical pair. -/
def cneg (x : H) : H := (Neg x.1, Neg x.2)

/-- Rational real scaling of both original completed bond components. -/
def realScale (c : Q') (x : H) : H := (Scale c x.1, Scale c x.2)

private def czero : H :=
  (BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width),
   BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width))

private theorem real_add_assoc (x y z : RH) : Add (Add x y) z = Add x (Add y z) := by
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
  rw [bondValue_add, BF4WilsonAllNomeBondOSLinear.bondValue_zero]
  exact completedAdd_zero hw0 hw1 _

private theorem real_neg_add (x : RH) :
    Add (Neg x) x = BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 := by
  apply bondValue_injective hw0 hw1
  rw [bondValue_add,bondValue_negate,BF4WilsonAllNomeBondOSLinear.bondValue_zero]
  exact completedNeg_add hw0 hw1 _

private theorem real_scale_add (c : Q') (x y : RH) :
    Scale c (Add x y) = Add (Scale c x) (Scale c y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_add,bondValue_smul]
  exact completedSmul_add hw0 hw1 c _ _

private theorem real_neg_additive (x y : RH) : Neg (Add x y) = Add (Neg x) (Neg y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_add,bondValue_negate]
  exact completedSmul_add hw0 hw1 (-1) _ _

private theorem real_scale_neg (c : Q') (x : RH) : Scale c (Neg x) = Neg (Scale c x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change completedSmul hw0 hw1 c
      (completedSmul hw0 hw1 (-1) (bondValue hw0 hw1 x)) =
    completedSmul hw0 hw1 (-1)
      (completedSmul hw0 hw1 c (bondValue hw0 hw1 x))
  rw [completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv c (-1)) _

private theorem real_scale_mul (a b : Q') (x : RH) :
    Scale a (Scale b x) = Scale (a*b) x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul]
  exact completedSmul_mul hw0 hw1 a b _

private theorem complex_add_assoc (x y z : H) : A (A x y) z = A x (A y z) :=
  Prod.ext (real_add_assoc hw0 hw1 x.1 y.1 z.1)
    (real_add_assoc hw0 hw1 x.2 y.2 z.2)

private theorem complex_add_comm (x y : H) : A x y = A y x :=
  Prod.ext (real_add_comm hw0 hw1 x.1 y.1)
    (real_add_comm hw0 hw1 x.2 y.2)

private theorem complex_add_zero (x : H) : A x (czero hw0 hw1) = x :=
  Prod.ext (real_add_zero hw0 hw1 x.1) (real_add_zero hw0 hw1 x.2)

private theorem complex_zero_add (x : H) : A (czero hw0 hw1) x = x := by
  rw [complex_add_comm,complex_add_zero]

private theorem complex_neg_add (x : H) : A (cneg hw0 hw1 x) x = czero hw0 hw1 :=
  Prod.ext (real_neg_add hw0 hw1 x.1) (real_neg_add hw0 hw1 x.2)

private theorem complex_add_neg (x : H) : A x (cneg hw0 hw1 x) = czero hw0 hw1 := by
  rw [complex_add_comm,complex_neg_add]

private theorem complex_cancel_right (x y z : H) (h : A x z = A y z) : x = y := by
  have hh := congrArg (fun v => A v (cneg hw0 hw1 z)) h
  change A (A x z) (cneg hw0 hw1 z) =
    A (A y z) (cneg hw0 hw1 z) at hh
  rw [complex_add_assoc,complex_add_assoc,complex_add_neg,
    complex_add_zero,complex_add_zero] at hh
  exact hh

private theorem complex_four_exchange (a b c d : H) :
    A (A a b) (A c d) = A (A a c) (A b d) := by
  calc
    A (A a b) (A c d) = A a (A b (A c d)) := complex_add_assoc hw0 hw1 _ _ _
    _ = A a (A c (A b d)) := by
      rw [← complex_add_assoc hw0 hw1 b c d,
        complex_add_comm hw0 hw1 b c,complex_add_assoc]
    _ = A (A a c) (A b d) := (complex_add_assoc hw0 hw1 _ _ _).symm

private theorem complex_move_last (a b c d : H) :
    A (A (A a b) c) d = A (A a d) (A b c) := by
  calc
    A (A (A a b) c) d = A (A a b) (A c d) := complex_add_assoc hw0 hw1 _ _ _
    _ = A (A a b) (A d c) := by rw [complex_add_comm hw0 hw1 c d]
    _ = A (A a d) (A b c) := complex_four_exchange hw0 hw1 a b d c

private theorem imagScale_add (x y : H) :
    imagScale hw0 hw1 t (A x y) =
      A (imagScale hw0 hw1 t x) (imagScale hw0 hw1 t y) := by
  apply Prod.ext
  · exact (congrArg Neg (real_scale_add hw0 hw1 t x.2 y.2)).trans
      (real_neg_additive hw0 hw1 (Scale t x.2) (Scale t y.2))
  · exact real_scale_add hw0 hw1 t x.1 y.1

private theorem imagScale_neg (x : H) :
    imagScale hw0 hw1 t (cneg hw0 hw1 x) =
      cneg hw0 hw1 (imagScale hw0 hw1 t x) := by
  apply Prod.ext
  · change Neg (Scale t (Neg x.2)) = Neg (Neg (Scale t x.2))
    rw [real_scale_neg]
  · exact real_scale_neg hw0 hw1 t x.1

private theorem imagScale_cayley (x : H) :
    C (imagScale hw0 hw1 t x) = imagScale hw0 hw1 t (C x) := by
  rw [imagScale_smul,imagScale_smul]
  exact BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_smul hw0 hw1 t ht
    (ofQ' 0) (ofQ' t) (rationalCauchy 0) (rationalCauchy t) x

private theorem imagScale_square (x : H) :
    imagScale hw0 hw1 t (imagScale hw0 hw1 t x) =
      cneg hw0 hw1 (realScale hw0 hw1 (t*t) x) := by
  apply Prod.ext
  · exact congrArg Neg (real_scale_mul hw0 hw1 t t x.1)
  · exact (real_scale_neg hw0 hw1 t (Scale t x.2)).trans
      (congrArg Neg (real_scale_mul hw0 hw1 t t x.2))

private theorem imag_negative_cancel (x : H) :
    A (imagScale hw0 hw1 t x) (negativeImagScale hw0 hw1 t x) =
      czero hw0 hw1 := by
  apply Prod.ext
  · exact real_neg_add hw0 hw1 (Scale t x.2)
  · change Add (Scale t x.1) (Neg (Scale t x.1)) =
      BF4WilsonAllNomeBondOSLinear.zero hw0 hw1
    rw [real_add_comm]
    exact real_neg_add hw0 hw1 (Scale t x.1)

private theorem negative_imag_cancel (x : H) :
    A (negativeImagScale hw0 hw1 t x) (imagScale hw0 hw1 t x) =
      czero hw0 hw1 := by
  rw [complex_add_comm,imag_negative_cancel]

private theorem first_rearrangement (a b x y : H)
    (h : A a (imagScale hw0 hw1 t b) =
      A x (negativeImagScale hw0 hw1 t y)) :
    A (A a (cneg hw0 hw1 x))
        (imagScale hw0 hw1 t (A y y)) =
      imagScale hw0 hw1 t (A y (cneg hw0 hw1 b)) := by
  let p := imagScale hw0 hw1 t y
  let q := imagScale hw0 hw1 t b
  have hp : imagScale hw0 hw1 t (A y y) = A p p :=
    imagScale_add hw0 hw1 t y y
  have hq : imagScale hw0 hw1 t (A y (cneg hw0 hw1 b)) =
      A p (cneg hw0 hw1 q) := by
    rw [imagScale_add,imagScale_neg]
  rw [hp,hq]
  apply complex_cancel_right hw0 hw1 _ _ q
  calc
    A (A (A a (cneg hw0 hw1 x)) (A p p)) q =
        A (A a q) (A (cneg hw0 hw1 x) (A p p)) :=
      complex_move_last hw0 hw1 _ _ _ _
    _ = A (A x (negativeImagScale hw0 hw1 t y))
          (A (cneg hw0 hw1 x) (A p p)) := by rw [h]
    _ = A (A x (cneg hw0 hw1 x))
          (A (negativeImagScale hw0 hw1 t y) (A p p)) :=
      complex_four_exchange hw0 hw1 _ _ _ _
    _ = A (negativeImagScale hw0 hw1 t y) (A p p) := by
      rw [complex_add_neg,complex_zero_add]
    _ = A (A (negativeImagScale hw0 hw1 t y) p) p :=
      (complex_add_assoc hw0 hw1 _ _ _).symm
    _ = p := by rw [negative_imag_cancel,complex_zero_add]
    _ = A (A p (cneg hw0 hw1 q)) q := by
      rw [complex_add_assoc,complex_neg_add,complex_add_zero]

private theorem second_rearrangement (b c y z : H)
    (h : A b (imagScale hw0 hw1 t c) =
      A y (negativeImagScale hw0 hw1 t z)) :
    A y (cneg hw0 hw1 b) = imagScale hw0 hw1 t (A z c) := by
  let p := imagScale hw0 hw1 t z
  let q := imagScale hw0 hw1 t c
  have hp : imagScale hw0 hw1 t (A z c) = A p q :=
    imagScale_add hw0 hw1 t z c
  rw [hp]
  apply complex_cancel_right hw0 hw1 _ _ b
  calc
    A (A y (cneg hw0 hw1 b)) b = y := by
      rw [complex_add_assoc,complex_neg_add,complex_add_zero]
    _ = A p (A y (negativeImagScale hw0 hw1 t z)) := by
      have hh : A p (A y (negativeImagScale hw0 hw1 t z)) = y := calc
        A p (A y (negativeImagScale hw0 hw1 t z)) =
            A y (A p (negativeImagScale hw0 hw1 t z)) := by
          rw [← complex_add_assoc,complex_add_comm hw0 hw1 p y,
            complex_add_assoc]
        _ = y := by rw [imag_negative_cancel,complex_add_zero]
      exact hh.symm
    _ = A p (A b q) := by rw [h]
    _ = A (A p q) b := by
      calc
        A p (A b q) = A p (A q b) := by rw [complex_add_comm hw0 hw1 b q]
        _ = A (A p q) b := (complex_add_assoc hw0 hw1 _ _ _).symm

/-- The exact linked graph calculation stops at the complete Cayley sum;
the latter is identified with the constructed plus-shift input below. -/
theorem linked_error_cayley_sum (d e : D) (hlink : Out d = In e) :
    A (A (C (In d)) (cneg hw0 hw1 (In d)))
        (imagScale hw0 hw1 t (A (Out d) (Out d))) =
      cneg hw0 hw1
        (realScale hw0 hw1 (t*t) (A (Out e) (C (Out e)))) := by
  let x := In d
  let y := Out d
  let z := Out e
  have hd : A (C x) (imagScale hw0 hw1 t (C y)) =
      A x (negativeImagScale hw0 hw1 t y) := by
    calc
      A (C x) (imagScale hw0 hw1 t (C y)) =
          A (C x) (C (imagScale hw0 hw1 t y)) := by
            rw [imagScale_cayley]
      _ = C (A x (imagScale hw0 hw1 t y)) :=
        (BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add hw0 hw1 t ht _ _).symm
      _ = C (P d) := by rw [plus_input_imag]
      _ = M d := cayley_graph hw0 hw1 t ht d
      _ = A x (negativeImagScale hw0 hw1 t y) := minus_input_imag hw0 hw1 t d
  have he : A (C y) (imagScale hw0 hw1 t (C z)) =
      A y (negativeImagScale hw0 hw1 t z) := by
    calc
      A (C y) (imagScale hw0 hw1 t (C z)) =
          A (C y) (C (imagScale hw0 hw1 t z)) := by
            rw [imagScale_cayley]
      _ = C (A y (imagScale hw0 hw1 t z)) :=
        (BF4WilsonAllNomeComplexBondOSScaledCayley.cayley_add hw0 hw1 t ht _ _).symm
      _ = C (P e) := by
        change C (A (Out d) (imagScale hw0 hw1 t (Out e))) = C (P e)
        rw [hlink,plus_input_imag]
      _ = M e := cayley_graph hw0 hw1 t ht e
      _ = A y (negativeImagScale hw0 hw1 t z) := by
        change M e = A (Out d) (negativeImagScale hw0 hw1 t (Out e))
        rw [hlink,minus_input_imag]
  calc
    A (A (C x) (cneg hw0 hw1 x))
        (imagScale hw0 hw1 t (A y y)) =
        imagScale hw0 hw1 t (A y (cneg hw0 hw1 (C y))) :=
          first_rearrangement hw0 hw1 t (C x) (C y) x y hd
    _ = imagScale hw0 hw1 t
          (imagScale hw0 hw1 t (A z (C z))) := by
            rw [second_rearrangement hw0 hw1 t (C y) (C z) y z he]
    _ = cneg hw0 hw1 (realScale hw0 hw1 (t*t) (A z (C z))) :=
      imagScale_square hw0 hw1 t _

private theorem real_four_exchange (a b c d : RH) :
    Add (Add a b) (Add c d) = Add (Add a c) (Add b d) := by
  calc
    Add (Add a b) (Add c d) = Add a (Add b (Add c d)) :=
      real_add_assoc hw0 hw1 _ _ _
    _ = Add a (Add c (Add b d)) := by
      rw [← real_add_assoc hw0 hw1 b c d,
        real_add_comm hw0 hw1 b c,real_add_assoc]
    _ = Add (Add a c) (Add b d) := (real_add_assoc hw0 hw1 _ _ _).symm

private theorem real_sub_add_pair (a b : RH) :
    Add (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 a b) (Add a b) =
      Add a a := by
  change Add (Add a (Neg b)) (Add a b) = Add a a
  rw [real_four_exchange hw0 hw1 a (Neg b) a b,
    real_neg_add,real_add_zero]

private theorem real_add_sub_pair (a b : RH) :
    Add (Add a b) (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 a b) =
      Add a a := by
  rw [real_add_comm,real_sub_add_pair]

/-- This is the constructive plus/minus averaging identity on the SAME
actual graph preimage.  In particular, `z+C_t z=2*J_t z`. -/
theorem cayley_average_input (z : H) :
    A z (C z) =
      A (In (plusDomain hw0 hw1 t ht z))
        (In (plusDomain hw0 hw1 t ht z)) := by
  let v := plusDomain hw0 hw1 t ht z
  have hv : P v = z :=
    BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts.plus_right hw0 hw1 t ht z
  calc
    A z (C z) = A (P v) (M v) := by rw [hv]; rfl
    _ = A (In v) (In v) := by
      apply Prod.ext
      · exact real_sub_add_pair hw0 hw1 _ _
      · exact real_add_sub_pair hw0 hw1 _ _

/-- The requested local consistency formula retains the constructed
plus-shift input; its exact coefficient is two copies of `-t²`, without
choosing a graph representative or invoking arbitrary-domain invariance. -/
theorem linked_error_average (d e : D) (hlink : Out d = In e) :
    A (A (C (In d)) (cneg hw0 hw1 (In d)))
        (imagScale hw0 hw1 t (A (Out d) (Out d))) =
      cneg hw0 hw1
        (realScale hw0 hw1 (t*t)
          (A (In (plusDomain hw0 hw1 t ht (Out e)))
            (In (plusDomain hw0 hw1 t ht (Out e))))) := by
  rw [linked_error_cayley_sum hw0 hw1 t ht d e hlink,
    cayley_average_input hw0 hw1 t ht (Out e)]

private theorem real_scale_double (c : Q') (x : RH) :
    Scale c (Add x x) = Scale (c+c) x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_add]
  exact (completedSmul_add hw0 hw1 c _ _).trans
    (completedAdd_smul hw0 hw1 c c _)

private theorem real_scale_congr {a b : Q'} (hab : a.eqv b) (x : RH) :
    Scale a x = Scale b x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul]
  exact completedSmul_congr hw0 hw1 hab _

private theorem two_square_coeff :
    ((t*t)+(t*t)).eqv ((2 : Q')*(t*t)) :=
  poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
    (.mul (.const 2) (.mul (.var 0) (.var 0))) (by decide) (fun _ => t)

private theorem realScale_double (c : Q') (x : H) :
    realScale hw0 hw1 c (A x x) = realScale hw0 hw1 (c+c) x :=
  Prod.ext (real_scale_double hw0 hw1 c x.1)
    (real_scale_double hw0 hw1 c x.2)

private theorem realScale_congr {a b : Q'} (hab : a.eqv b) (x : H) :
    realScale hw0 hw1 a x = realScale hw0 hw1 b x :=
  Prod.ext (real_scale_congr hw0 hw1 hab x.1)
    (real_scale_congr hw0 hw1 hab x.2)

/-- The exact linked second-domain phase, with coefficient `-2*t²`.
The phase acts on the original completed input of the constructed
plus-shift inverse; no physical-time interpretation is made. -/
theorem cayley_linked_error (d e : D) (hlink : Out d = In e) :
    A (A (C (In d)) (cneg hw0 hw1 (In d)))
        (imagScale hw0 hw1 t (A (Out d) (Out d))) =
      cneg hw0 hw1
        (realScale hw0 hw1 ((2 : Q')*(t*t))
          (In (plusDomain hw0 hw1 t ht (Out e)))) := by
  let v := In (plusDomain hw0 hw1 t ht (Out e))
  calc
    A (A (C (In d)) (cneg hw0 hw1 (In d)))
        (imagScale hw0 hw1 t (A (Out d) (Out d))) =
      cneg hw0 hw1 (realScale hw0 hw1 (t*t) (A v v)) :=
        linked_error_average hw0 hw1 t ht d e hlink
    _ = cneg hw0 hw1 (realScale hw0 hw1 ((t*t)+(t*t)) v) :=
      congrArg (cneg hw0 hw1) (realScale_double hw0 hw1 (t*t) v)
    _ = cneg hw0 hw1 (realScale hw0 hw1 ((2 : Q')*(t*t)) v) :=
      congrArg (cneg hw0 hw1) (realScale_congr hw0 hw1 (two_square_coeff t) v)

#print axioms imagScale
#print axioms negativeImagScale
#print axioms imagScale_smul
#print axioms plus_input_imag
#print axioms minus_input_imag
#print axioms cayley_graph
#print axioms cneg
#print axioms realScale
#print axioms linked_error_cayley_sum
#print axioms cayley_average_input
#print axioms linked_error_average
#print axioms cayley_linked_error

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConsistency
