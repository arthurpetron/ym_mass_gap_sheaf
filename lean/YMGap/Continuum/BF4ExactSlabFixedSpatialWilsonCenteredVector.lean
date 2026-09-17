/-
# Actual centered Wilson vectors and their connected pairings

Subtract rational approximations of the original unit coefficient. The
exact coefficient-square distance gives a Type-level Cauchy modulus. The
resulting vector belongs to the already constructed Wilson completion.
Its unit pairing is zero and its mixed pairing is the connected original
form. No completed real scalar action or selected quotient representative
is needed. This does not construct time, a strict bound or continuum QFT.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenterAlgebra
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
  (centerTolerance centerTolerance_positive coefficient_square_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "D" => seminorm hw0 hw1 hsmall hd hs hb
local notation "P" => intrinsicForm hw0 hw1 hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 hsmall hd hs hb
local notation "data" => pairingData hw0 hw1 hsmall hd hs hb

def mean (x : IntrinsicExpression base) : CReal := P x (unit base)

def meanCauchy (x : IntrinsicExpression base) :
    QCauchy (mean hw0 hw1 hsmall hd hs hb x).approx :=
  intrinsicFormCauchy hw0 hw1 hsmall hd hs hb x (unit base)

/-- The original scalar modulus, clipped at one for the squared distance. -/
def centeredRate (x : IntrinsicExpression base) (epsilon : Q') : Nat :=
  (meanCauchy hw0 hw1 hsmall hd hs hb x).M (centerTolerance epsilon)

def centeredStream (x : IntrinsicExpression base) : (D).Cauchy where
  seq n := centerApprox x ((mean hw0 hw1 hsmall hd hs hb x).approx n)
  modulus := centeredRate hw0 hw1 hsmall hd hs hb x
  isCauchy := by
    intro epsilon he m n hm hn
    have h := (meanCauchy hw0 hw1 hsmall hd hs hb x).bound
      (centerTolerance epsilon) (centerTolerance_positive he) m n hm hn
    exact leEv_trans
      (leEv_of_equiv (centerApprox_distance hw0 hw1 hsmall hd hs hb x _ _))
      (leEv_of_le (ofQ'_le_ofQ' (coefficient_square_bound he h)))

/-- An explicit representative of a vector of the SAME existing completion. -/
def centeredVector (x : IntrinsicExpression base) : Completion hw0 hw1 hsmall hd hs hb :=
  Quotient.mk (D).completionSetoid (centeredStream hw0 hw1 hsmall hd hs hb x)

theorem centeredStream_seq (x : IntrinsicExpression base) (n : Nat) :
    (centeredStream hw0 hw1 hsmall hd hs hb x).seq n =
      centerApprox x ((mean hw0 hw1 hsmall hd hs hb x).approx n) := rfl

theorem centeredStream_modulus (x : IntrinsicExpression base) :
    (centeredStream hw0 hw1 hsmall hd hs hb x).modulus =
      centeredRate hw0 hw1 hsmall hd hs hb x := rfl

theorem mean_approximations_converge (x : IntrinsicExpression base) :
    ConvergesTo (fun n => ofQ' ((mean hw0 hw1 hsmall hd hs hb x).approx n))
      (mean hw0 hw1 hsmall hd hs hb x) := by
  intro epsilon he
  let c := meanCauchy hw0 hw1 hsmall hd hs hb x
  exact ⟨c.M epsilon, fun n hn => ⟨c.M epsilon, fun k hk => c.bound epsilon he n k hn hk⟩⟩

local notation "C" => centeredStream hw0 hw1 hsmall hd hs hb
local notation "v" => centeredVector hw0 hw1 hsmall hd hs hb

attribute [local irreducible] intrinsicForm

theorem centered_unit_representative (x : IntrinsicExpression base) :
    Equiv (representativeInner hw0 hw1 hsmall hd hs hb (C x) ((D).constant (unit base)))
      czero := by
  have hc : ConvergesTo
      (fun k => sub (mean hw0 hw1 hsmall hd hs hb x)
        (ofQ' ((mean hw0 hw1 hsmall hd hs hb x).approx k)))
      (sub (mean hw0 hw1 hsmall hd hs hb x) (mean hw0 hw1 hsmall hd hs hb x)) :=
    TrigAddCReal.convergesTo_add (convergesTo_const _)
      (TrigAddCReal.convergesTo_neg (mean_approximations_converge hw0 hw1 hsmall hd hs hb x))
  exact (Equiv_of_limit_of_equal
    (fun k => centerApprox_unit hw0 hw1 hsmall hd hs hb x
      ((mean hw0 hw1 hsmall hd hs hb x).approx k))
    (CRealSeminormPairingCompletion.pairSequence_converges data (C x) ((D).constant (unit base)))
    hc).trans (sub_self_eqv_zero _)

theorem centeredVector_orthogonal (x : IntrinsicExpression base) :
    B (v x) (embed hw0 hw1 hsmall hd hs hb (unit base)) = RCzero :=
  Quotient.sound (centered_unit_representative hw0 hw1 hsmall hd hs hb x)

/-- The connected scalar of the original intrinsic reflected form. -/
def centeredMoment (x y : IntrinsicExpression base) : CReal :=
  sub (P x y) (mul (P x (unit base)) (P y (unit base)))

/-- Independent mean approximations are passed through the actual mixed limit. -/
theorem centered_pair_representative (x y : IntrinsicExpression base) :
    Equiv (representativeInner hw0 hw1 hsmall hd hs hb (C x) (C y))
      (centeredMoment hw0 hw1 hsmall hd hs hb x y) := by
  let mu := mean hw0 hw1 hsmall hd hs hb x
  let nu := mean hw0 hw1 hsmall hd hs hb y
  let A := P x y
  let E := P (unit base) y
  let S (k : Nat) :=
    sub (sub A (mul (ofQ' (mu.approx k)) E))
      (sub (mul (ofQ' (nu.approx k)) mu)
        (mul (ofQ' (mu.approx k)) (ofQ' (nu.approx k))))
  have hmu := mean_approximations_converge hw0 hw1 hsmall hd hs hb x
  have hnu := mean_approximations_converge hw0 hw1 hsmall hd hs hb y
  have hc : ConvergesTo S
      (sub (sub A (mul mu E)) (sub (mul nu mu) (mul mu nu))) :=
    TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (convergesTo_const A)
        (TrigAddCReal.convergesTo_neg
          (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
            hmu (convergesTo_const E))))
      (TrigAddCReal.convergesTo_neg
        (TrigAddCReal.convergesTo_add
          (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
            hnu (convergesTo_const mu))
          (TrigAddCReal.convergesTo_neg
            (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
              hmu hnu))))
  have h := Equiv_of_limit_of_equal
    (aSeq := CRealSeminormPairingCompletion.pairSequence data (C x) (C y))
    (bSeq := S)
    (fun k => (centerApprox_pairing hw0 hw1 hsmall hd hs hb x y
      (mu.approx k) (nu.approx k)).trans
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)))
    (CRealSeminormPairingCompletion.pairSequence_converges data (C x) (C y)) hc
  have hcancel : Equiv (sub (mul nu mu) (mul mu nu)) czero :=
    (Equiv_add (CRealAlg.cmul_comm nu mu) (Equiv.refl _)).trans (sub_self_eqv_zero _)
  have hclean : Equiv (sub (sub A (mul mu E)) (sub (mul nu mu) (mul mu nu)))
      (sub A (mul mu E)) :=
    (Equiv_add (Equiv.refl _) (neg_congr hcancel)).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-(0 : Q')) 0))
        (QPoly.q_add_zero_eqv _)))
  exact h.trans (hclean.trans (Equiv_add (Equiv.refl _) (neg_congr
    (TrigSignedAdd.mul_congr_right (intrinsicForm_symm hw0 hw1 hsmall hd hs hb (unit base) y)))))

theorem centeredVector_pairing (x y : IntrinsicExpression base) :
    B (v x) (v y) = Quotient.mk crealSetoid (centeredMoment hw0 hw1 hsmall hd hs hb x y) :=
  Quotient.sound (centered_pair_representative hw0 hw1 hsmall hd hs hb x y)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.mean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.meanCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centeredRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centeredStream
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centeredVector
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centeredStream_seq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centeredStream_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.mean_approximations_converge
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centered_unit_representative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centeredVector_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centeredMoment
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centered_pair_representative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredVector.centeredVector_pairing
