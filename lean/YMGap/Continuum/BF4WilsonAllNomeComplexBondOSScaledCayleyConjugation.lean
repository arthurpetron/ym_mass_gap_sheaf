/-
# Conjugation of the actual physical bond Cayley map

Complex conjugation negates the imaginary ORIGINAL completed bond component.
The witnessed derivative graph is real, so its conjugate exchanges the two
constructed imaginary shifts.  Consequently the finite Cayley inverse is
conjugate to the finite Cayley map on the SAME physical carrier.  This is
not a physical-time reversal, a continuum operation, or a group law.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyRows
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayley
import YMGap.Continuum.BF4WilsonAllNomeBondOSAdjoint
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphLinear

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConjugation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedNeg completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
  (completedSmul_mul completedSmul_congr completedSmul_one completedSmul_add)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion toSectorRep fromSectorRep fromSectorRep_limit bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_add bondValue_sub bondValue_negate bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (Domain input output)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance distance_value)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledImaginaryShifts
  (plus minus plusDomain minusDomain plus_right minus_right)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "RD" => Domain hw0 hw1 (width := width)
local notation "D" => BF4WilsonAllNomeComplexBondOSDerivative.Domain hw0 hw1 (width := width)
local notation "V" => bondValue hw0 hw1
local notation "N" => BF4WilsonAllNomeBondOSLinear.negate hw0 hw1
local notation "A" => BF4WilsonAllNomeBondOSLinear.add hw0 hw1
local notation "S" => BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
local notation "T" => BF4WilsonAllNomeBondOSLinear.smul hw0 hw1
local notation "RI" => input hw0 hw1
local notation "RO" => output hw0 hw1

attribute [local irreducible] toSectorRep fromSectorRep

/-- The actual complex-conjugate completed Wilson bond class. -/
def conjugate (x : H) : H := (x.1,N x.2)

local notation "K" => conjugate hw0 hw1

private theorem real_neg_neg (x : RH) : N (N x) = x := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_negate]
  change completedSmul hw0 hw1 (-1)
    (completedSmul hw0 hw1 (-1) (V x)) = V x
  rw [completedSmul_mul,
    completedSmul_congr hw0 hw1
      (by decide : Q'.eqv ((-1 : Q') * (-1)) 1),completedSmul_one]

theorem conjugate_involutive (x : H) : K (K x) = x := by
  apply Prod.ext
  · rfl
  · exact real_neg_neg hw0 hw1 x.2

/-- The original physical squared distance is conjugation invariant. -/
theorem conjugate_distance (x y : H) :
    distance hw0 hw1 (K x) (K y) = distance hw0 hw1 x y := by
  simp only [distance_value]
  change
    RCadd (BF4WilsonAllNomeDistance.completedDist hw0 hw1 (V x.1) (V y.1))
      (BF4WilsonAllNomeDistance.completedDist hw0 hw1 (V (N x.2)) (V (N y.2))) =
    RCadd (BF4WilsonAllNomeDistance.completedDist hw0 hw1 (V x.1) (V y.1))
      (BF4WilsonAllNomeDistance.completedDist hw0 hw1 (V x.2) (V y.2))
  congr 1
  rw [bondValue_negate,bondValue_negate]
  change BF4WilsonAllNomeDistance.completedDist hw0 hw1
      (completedSmul hw0 hw1 (-1) (V x.2))
      (completedSmul hw0 hw1 (-1) (V y.2)) =
    BF4WilsonAllNomeDistance.completedDist hw0 hw1 (V x.2) (V y.2)
  rw [BF4WilsonAllNomeDerivativeGraphLinear.completedDist_smul,
    YMGap.Continuum.RCSignedPairBudget.scale_congr
      (by decide : Q'.eqv ((-1 : Q') * (-1)) 1),RCscale_one]

/-- Constructive supplied-Rows conjugation; only its imaginary sector row is
negated, retaining an original time-range witness. -/
def conjugateRows (X : Rows hw0 hw1 (width := width)) :
    Rows hw0 hw1 (width := width) :=
  (X.1,fromSectorRep hw0 hw1
    (BF4WilsonAllNomeTimeSector.negate hw0 hw1 (toSectorRep hw0 hw1 X.2)))

theorem conjugateRows_pin (X : Rows hw0 hw1 (width := width)) :
    ofRows hw0 hw1 (conjugateRows hw0 hw1 X) = K (ofRows hw0 hw1 X) := by
  let Q := BF4WilsonAllNomeTimeSector.negate hw0 hw1 (toSectorRep hw0 hw1 X.2)
  have hsecond :
      (Quotient.mk (BF4WilsonAllNomeBondOSCompletion.rowSetoid hw0 hw1)
        (fromSectorRep hw0 hw1 Q) : RH) =
      N (Quotient.mk (BF4WilsonAllNomeBondOSCompletion.rowSetoid hw0 hw1) X.2) := by
    apply bondValue_injective hw0 hw1
    have hleft := fromSectorRep_limit hw0 hw1 Q
    have hright := bondValue_negate hw0 hw1
      (Quotient.mk (BF4WilsonAllNomeBondOSCompletion.rowSetoid hw0 hw1) X.2)
    exact hleft.trans hright.symm
  simpa only [conjugateRows,ofRows,conjugate] using
    congrArg
      (fun z : RH =>
        (Quotient.mk (BF4WilsonAllNomeBondOSCompletion.rowSetoid hw0 hw1) X.1,z))
      hsecond

private theorem real_neg_add (x y : RH) : N (A x y) = A (N x) (N y) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_negate,bondValue_add]
  change completedSmul hw0 hw1 (-1) (completedAdd hw0 hw1 (V x) (V y)) =
    completedAdd hw0 hw1
      (completedSmul hw0 hw1 (-1) (V x))
      (completedSmul hw0 hw1 (-1) (V y))
  exact completedSmul_add hw0 hw1 (-1) (V x) (V y)

private theorem real_neg_sub (x y : RH) : N (S x y) = A (N x) y := by
  change N (A x (N y)) = A (N x) y
  rw [real_neg_add,real_neg_neg]

private theorem real_smul_neg (t : Q') (x : RH) : T t (N x) = N (T t x) := by
  apply bondValue_injective hw0 hw1
  simp only [bondValue_smul,bondValue_negate]
  change completedSmul hw0 hw1 t (completedSmul hw0 hw1 (-1) (V x)) =
    completedSmul hw0 hw1 (-1) (completedSmul hw0 hw1 t (V x))
  rw [completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv t (-1)) (V x)

/-- Negation of a real graph point is reconstructed by the already proved
physical adjoint-domain theorem; no domain representative is selected. -/
private theorem real_neg_adjoint (d : RD) :
    BF4WilsonAllNomeBondOSAdjoint.AdjointPair hw0 hw1 (N (RI d)) (N (RO d)) := by
  intro e
  rw [bondValue_inner,bondValue_inner,bondValue_negate,bondValue_negate]
  change BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
      (completedSmul hw0 hw1 (-1) (V (RI d))) (V (RO e)) =
    BF4WilsonAllNomeCompletedInner.completedInner hw0 hw1
      (completedSmul hw0 hw1 (-1) (V (RO d))) (V (RI e))
  rw [
    BF4WilsonAllNomeBilinearTime.completedInner_smul_left,
    BF4WilsonAllNomeBilinearTime.completedInner_smul_left]
  have h := BF4WilsonAllNomeBondOSAdjoint.domain_adjoint hw0 hw1 d e
  rw [bondValue_inner,bondValue_inner] at h
  exact congrArg (RCscale (-1))
    h

def realNegDomain (d : RD) : RD :=
  BF4WilsonAllNomeBondOSAdjoint.adjointDomain hw0 hw1 (N (RI d)) (N (RO d))

theorem realNegDomain_input (d : RD) :
    RI (realNegDomain hw0 hw1 d) = N (RI d) :=
  BF4WilsonAllNomeBondOSAdjoint.adjointDomain_input hw0 hw1 _ _
    (real_neg_adjoint hw0 hw1 d)

theorem realNegDomain_output (d : RD) :
    RO (realNegDomain hw0 hw1 d) = N (RO d) :=
  BF4WilsonAllNomeBondOSAdjoint.adjointDomain_output hw0 hw1 _ _
    (real_neg_adjoint hw0 hw1 d)

def conjugateDomain (d : D) : D := (d.1,realNegDomain hw0 hw1 d.2)

theorem conjugateDomain_input (d : D) :
    BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
      (conjugateDomain hw0 hw1 d) =
      K (BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1 d) :=
  Prod.ext rfl (realNegDomain_input hw0 hw1 d.2)

theorem conjugateDomain_output (d : D) :
    BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1
      (conjugateDomain hw0 hw1 d) =
      K (BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1 d) :=
  Prod.ext rfl (realNegDomain_output hw0 hw1 d.2)

private theorem conjugate_plus (t : Q') (d : D) :
    K (plus hw0 hw1 t d) =
      minus hw0 hw1 t (conjugateDomain hw0 hw1 d) := by
  apply Prod.ext
  · dsimp only [conjugate,plus,minus,conjugateDomain]
    rw [realNegDomain_output]
    change S (RI d.1) (T t (RO d.2)) =
      A (RI d.1) (T t (N (RO d.2)))
    rw [real_smul_neg]
    rfl
  · dsimp only [conjugate,plus,minus,conjugateDomain]
    rw [realNegDomain_input]
    change N (A (RI d.2) (T t (RO d.1))) =
      S (N (RI d.2)) (T t (RO d.1))
    exact real_neg_add hw0 hw1 _ _

private theorem conjugate_minus (t : Q') (d : D) :
    K (minus hw0 hw1 t d) =
      plus hw0 hw1 t (conjugateDomain hw0 hw1 d) := by
  apply Prod.ext
  · dsimp only [conjugate,plus,minus,conjugateDomain]
    rw [realNegDomain_output]
    change A (RI d.1) (T t (RO d.2)) =
      S (RI d.1) (T t (N (RO d.2)))
    rw [real_smul_neg]
    change A (RI d.1) (T t (RO d.2)) =
      A (RI d.1) (N (N (T t (RO d.2))))
    rw [real_neg_neg]
  · dsimp only [conjugate,plus,minus,conjugateDomain]
    rw [realNegDomain_input]
    change N (S (RI d.2) (T t (RO d.1))) =
      A (N (RI d.2)) (T t (RO d.1))
    exact real_neg_sub hw0 hw1 _ _

/-- The finite Cayley inverse is the conjugate of the finite Cayley map
for the SAME witnessed physical derivative and rational parameter. -/
theorem conjugate_cayley_conjugate (t : Q') (ht : (0 : Q') < t) (x : H) :
    K (BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1 t ht (K x)) =
      BF4WilsonAllNomeComplexBondOSScaledCayley.inverse hw0 hw1 t ht x := by
  let d := plusDomain hw0 hw1 t ht (K x)
  have hplus : plus hw0 hw1 t d = K x := plus_right hw0 hw1 t ht (K x)
  have hminus : minus hw0 hw1 t (conjugateDomain hw0 hw1 d) = x := by
    rw [← conjugate_plus hw0 hw1 t d,hplus,conjugate_involutive]
  have hd : minusDomain hw0 hw1 t ht x = conjugateDomain hw0 hw1 d := by
    calc
      minusDomain hw0 hw1 t ht x =
          minusDomain hw0 hw1 t ht
            (minus hw0 hw1 t (conjugateDomain hw0 hw1 d)) :=
        congrArg (minusDomain hw0 hw1 t ht) hminus.symm
      _ = conjugateDomain hw0 hw1 d :=
        BF4WilsonAllNomeComplexBondOSScaledCayley.minus_left hw0 hw1 t ht _
  calc
    K (BF4WilsonAllNomeComplexBondOSScaledCayley.cayley hw0 hw1 t ht (K x)) =
        K (minus hw0 hw1 t d) := rfl
    _ = plus hw0 hw1 t (conjugateDomain hw0 hw1 d) := conjugate_minus hw0 hw1 t d
    _ = BF4WilsonAllNomeComplexBondOSScaledCayley.inverse hw0 hw1 t ht x := by
      rw [← hd]
      rfl

#print axioms conjugate
#print axioms conjugate_involutive
#print axioms conjugate_distance
#print axioms conjugateRows
#print axioms conjugateRows_pin
#print axioms conjugateDomain
#print axioms conjugateDomain_input
#print axioms conjugateDomain_output
#print axioms conjugate_cayley_conjugate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyConjugation
