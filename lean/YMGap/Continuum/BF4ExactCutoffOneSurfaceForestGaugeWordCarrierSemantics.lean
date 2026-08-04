/-
# Haar-carrier algebra for BF4 forest-gauge words

This module connects coefficientwise rational-polynomial equality to the
arbitrary-insertion Haar carrier used by the surface proof.  It also lifts
that equality componentwise to polynomial quaternions.  The purpose is to
perform Hamilton-word reassociation and cancellation structurally, without
canonical expansion of a selected surface.

## Axiom gate

Finite list induction and the existing constructive coefficient quotient
only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
import YMGap.Continuum.SU2QuaternionRatPolyDifferential

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar

local infix:50 " ≈ " => Q'.eqv

/-! ## Coefficient equality inside the Haar carrier -/

private theorem quaternionHaar_eq_ratWeightedSum
    (blocks : Nat) : ∀ polynomial : RatPoly,
    quaternionHaar blocks polynomial ≈
      ratWeightedSum (quaternionHaarMono blocks) polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest =>
      Q'.add_eqv_congr'
        (Q'.eqv_refl
          (term.2 * quaternionHaarMono blocks term.1))
        (quaternionHaar_eq_ratWeightedSum blocks rest)

/-- Coefficientwise equality is stronger than exact Haar equality after an
arbitrary polynomial insertion. -/
theorem RatPolyCoeffEqv.haarCarrier
    {blocks : Nat} {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) :
    HaarCarrierEqv blocks left right := by
  intro insertion
  exact Q'.eqv_trans _
    (ratWeightedSum (quaternionHaarMono blocks)
      (polyMul insertion left)) _
    (quaternionHaar_eq_ratWeightedSum blocks _)
    (Q'.eqv_trans _
      (ratWeightedSum (quaternionHaarMono blocks)
        (polyMul insertion right)) _
      ((RatPolyCoeffEqv.mul_left insertion h)
        (quaternionHaarMono blocks))
      (Q'.eqv_symm (quaternionHaar_eq_ratWeightedSum blocks _)))

/-- A Haar-carrier relation can be multiplied on the right.  Commutativity
is used only in the real coefficient-polynomial quotient; the Hamilton word
itself remains noncommutative. -/
theorem HaarCarrierEqv.mul_right
    {blocks : Nat} (factor : RatPoly)
    {left right : RatPoly} (h : HaarCarrierEqv blocks left right) :
    HaarCarrierEqv blocks
      (polyMul left factor) (polyMul right factor) := by
  exact HaarCarrierEqv.trans
    (RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.mul_comm left factor))
    (HaarCarrierEqv.trans
      (HaarCarrierEqv.mul_left factor h)
      (RatPolyCoeffEqv.haarCarrier
        (RatPolyCoeffEqv.mul_comm factor right)))

theorem HaarCarrierEqv.mul
    {blocks : Nat}
    {left left' right right' : RatPoly}
    (hleft : HaarCarrierEqv blocks left left')
    (hright : HaarCarrierEqv blocks right right') :
    HaarCarrierEqv blocks
      (polyMul left right) (polyMul left' right') :=
  HaarCarrierEqv.trans
    (HaarCarrierEqv.mul_right right hleft)
    (HaarCarrierEqv.mul_left left' hright)

inductive HaarCarrierListEqv (blocks : Nat) :
    List RatPoly → List RatPoly → Prop
  | nil : HaarCarrierListEqv blocks [] []
  | cons {left right : RatPoly} {leftRest rightRest : List RatPoly} :
      HaarCarrierEqv blocks left right →
      HaarCarrierListEqv blocks leftRest rightRest →
      HaarCarrierListEqv blocks
        (left :: leftRest) (right :: rightRest)

theorem factorProduct_carrier_of_listEqv
    {blocks : Nat} {left right : List RatPoly}
    (hpairs : HaarCarrierListEqv blocks left right) :
    HaarCarrierEqv blocks
      (factorProduct left) (factorProduct right) := by
  induction hpairs with
  | nil => exact HaarCarrierEqv.refl _ polyOne
  | cons hfactor _ induction =>
      exact HaarCarrierEqv.mul hfactor induction

/-! ## Componentwise polynomial-quaternion equality -/

private theorem ratWeightedSum_polyNeg
    (weight : List Nat → Q') : ∀ polynomial : RatPoly,
    ratWeightedSum weight (polyNeg polynomial) ≈
      -(ratWeightedSum weight polynomial)
  | [] => by
      change (0 : Q') ≈ -0
      decide
  | term :: rest => by
      change
        (-term.2) * weight term.1 +
              ratWeightedSum weight (polyNeg rest) ≈
          -(term.2 * weight term.1 + ratWeightedSum weight rest)
      refine Q'.eqv_trans _
        (-(term.2 * weight term.1) +
          -(ratWeightedSum weight rest)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.neg_mul_eqv term.2 (weight term.1))
          (ratWeightedSum_polyNeg weight rest)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv_split
            (term.2 * weight term.1)
            (ratWeightedSum weight rest))

theorem RatPolyCoeffEqv.neg
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv (polyNeg left) (polyNeg right) := by
  intro weight
  exact Q'.eqv_trans _ (-(ratWeightedSum weight left)) _
    (ratWeightedSum_polyNeg weight left)
    (Q'.eqv_trans _ (-(ratWeightedSum weight right)) _
      (Q'.neg_eqv_congr _ _ (h weight))
      (Q'.eqv_symm (ratWeightedSum_polyNeg weight right)))

structure PolyQuaternionCoeffEqv
    (left right : PolyQuaternion) : Prop where
  scalar : RatPolyCoeffEqv left.scalar right.scalar
  iPart : RatPolyCoeffEqv left.iPart right.iPart
  jPart : RatPolyCoeffEqv left.jPart right.jPart
  kPart : RatPolyCoeffEqv left.kPart right.kPart

theorem PolyQuaternionCoeffEqv.refl (quaternion : PolyQuaternion) :
    PolyQuaternionCoeffEqv quaternion quaternion :=
  ⟨RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _,
    RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _⟩

theorem PolyQuaternionCoeffEqv.symm
    {left right : PolyQuaternion}
    (h : PolyQuaternionCoeffEqv left right) :
    PolyQuaternionCoeffEqv right left :=
  ⟨h.scalar.symm, h.iPart.symm, h.jPart.symm, h.kPart.symm⟩

theorem PolyQuaternionCoeffEqv.trans
    {first middle last : PolyQuaternion}
    (hfirst : PolyQuaternionCoeffEqv first middle)
    (hlast : PolyQuaternionCoeffEqv middle last) :
    PolyQuaternionCoeffEqv first last :=
  ⟨hfirst.scalar.trans hlast.scalar,
    hfirst.iPart.trans hlast.iPart,
    hfirst.jPart.trans hlast.jPart,
    hfirst.kPart.trans hlast.kPart⟩

theorem PolyQuaternionCoeffEqv.conj
    {left right : PolyQuaternion}
  (h : PolyQuaternionCoeffEqv left right) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.conj left) (PolyQuaternion.conj right) :=
  ⟨h.scalar, RatPolyCoeffEqv.neg h.iPart,
    RatPolyCoeffEqv.neg h.jPart, RatPolyCoeffEqv.neg h.kPart⟩

theorem PolyQuaternionCoeffEqv.mul
    {left left' right right' : PolyQuaternion}
    (hleft : PolyQuaternionCoeffEqv left left')
    (hright : PolyQuaternionCoeffEqv right right') :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul left right)
      (PolyQuaternion.mul left' right') := by
  constructor
  · exact RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.mul hleft.scalar hright.scalar)
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.mul hleft.iPart hright.iPart)
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.mul hleft.jPart hright.jPart)
          (RatPolyCoeffEqv.mul hleft.kPart hright.kPart))))
  · exact RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.mul hleft.scalar hright.iPart)
      (RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.mul hleft.iPart hright.scalar)
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.mul hleft.jPart hright.kPart)
          (RatPolyCoeffEqv.neg
            (RatPolyCoeffEqv.mul hleft.kPart hright.jPart))))
  · exact RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.mul hleft.scalar hright.jPart)
      (RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.mul hleft.jPart hright.scalar)
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.mul hleft.kPart hright.iPart)
          (RatPolyCoeffEqv.neg
            (RatPolyCoeffEqv.mul hleft.iPart hright.kPart))))
  · exact RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.mul hleft.scalar hright.kPart)
      (RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.mul hleft.kPart hright.scalar)
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.mul hleft.iPart hright.jPart)
          (RatPolyCoeffEqv.neg
            (RatPolyCoeffEqv.mul hleft.jPart hright.iPart))))

theorem characterPolynomial_coeffEqv
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) : ∀ spin,
    RatPolyCoeffEqv
      (characterPolynomial left spin)
      (characterPolynomial right spin)
  | 0 => RatPolyCoeffEqv.refl polyOne
  | 1 => h.smul 2
  | spin + 2 =>
      RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.mul (h.smul 2)
          (characterPolynomial_coeffEqv h (spin + 1)))
        ((characterPolynomial_coeffEqv h spin).smul (-1))

/-! ## Reflective identities under polynomial substitution -/

private theorem monoMul_right_nil_local : ∀ monomial : List Nat,
    monoMul monomial [] = monomial
  | [] => rfl
  | _ :: _ => by simp only [monoMul]

theorem RatPolyCoeffEqv.mul_one (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polynomial polyOne) polynomial := by
  intro weight
  induction polynomial with
  | nil => exact Q'.eqv_refl 0
  | cons term rest induction =>
      change
        (term.2 * 1) * weight (monoMul term.1 []) +
              ratWeightedSum weight (polyMul rest polyOne) ≈
          term.2 * weight term.1 + ratWeightedSum weight rest
      rw [monoMul_right_nil_local]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv term.2))
        induction

theorem RatPolyCoeffEqv.one_mul (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polyOne polynomial) polynomial :=
  RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_comm polyOne polynomial)
    (RatPolyCoeffEqv.mul_one polynomial)

theorem RatPolyCoeffEqv.mul_four_swap
    (a b c d : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul a b) (polyMul c d))
      (polyMul (polyMul a c) (polyMul b d)) := by
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_assoc a b (polyMul c d)) ?_
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_left a
      (RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.mul_assoc b c d))) ?_
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_left a
      (RatPolyCoeffEqv.mul_right
        (RatPolyCoeffEqv.mul_comm b c) d)) ?_
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_left a
      (RatPolyCoeffEqv.mul_assoc c b d)) ?_
  exact RatPolyCoeffEqv.symm
    (RatPolyCoeffEqv.mul_assoc a c (polyMul b d))

def coeffPolyPow (polynomial : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | exponent + 1 =>
      polyMul (coeffPolyPow polynomial exponent) polynomial

theorem coeffPolyPow_congr
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) : ∀ exponent,
    RatPolyCoeffEqv
      (coeffPolyPow left exponent) (coeffPolyPow right exponent)
  | 0 => RatPolyCoeffEqv.refl polyOne
  | exponent + 1 =>
      RatPolyCoeffEqv.mul (coeffPolyPow_congr h exponent) h

theorem coeffPolyPow_add (polynomial : RatPoly) : ∀ first second,
    RatPolyCoeffEqv
      (coeffPolyPow polynomial (first + second))
      (polyMul (coeffPolyPow polynomial first)
        (coeffPolyPow polynomial second))
  | first, 0 => by
      simpa using RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.mul_one (coeffPolyPow polynomial first))
  | first, second + 1 => by
      rw [Nat.add_succ]
      change RatPolyCoeffEqv
        (polyMul (coeffPolyPow polynomial (first + second)) polynomial)
        (polyMul (coeffPolyPow polynomial first)
          (polyMul (coeffPolyPow polynomial second) polynomial))
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul
          (coeffPolyPow_add polynomial first second)
          (RatPolyCoeffEqv.refl polynomial))
        (RatPolyCoeffEqv.mul_assoc
          (coeffPolyPow polynomial first)
          (coeffPolyPow polynomial second) polynomial)

def coeffEvalMonoFrom
    (environment : Nat → RatPoly) : Nat → List Nat → RatPoly
  | _, [] => polyOne
  | index, exponent :: rest =>
      polyMul (coeffPolyPow (environment index) exponent)
        (coeffEvalMonoFrom environment (index + 1) rest)

def coeffEvalMono
    (environment : Nat → RatPoly) (monomial : List Nat) : RatPoly :=
  coeffEvalMonoFrom environment 0 monomial

private theorem coeffEvalMonoFrom_monoMul
    (environment : Nat → RatPoly) :
    ∀ (index : Nat) (left right : List Nat),
    RatPolyCoeffEqv
      (coeffEvalMonoFrom environment index (monoMul left right))
      (polyMul
        (coeffEvalMonoFrom environment index left)
        (coeffEvalMonoFrom environment index right))
  | _, [], right =>
      RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.one_mul
          (coeffEvalMonoFrom environment _ right))
  | _, left, [] => by
      rw [monoMul_right_nil_local]
      exact RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.mul_one
          (coeffEvalMonoFrom environment _ left))
  | index, leftExponent :: leftRest,
      rightExponent :: rightRest => by
      change RatPolyCoeffEqv
        (polyMul
          (coeffPolyPow (environment index)
            (leftExponent + rightExponent))
          (coeffEvalMonoFrom environment (index + 1)
            (monoMul leftRest rightRest)))
        (polyMul
          (polyMul (coeffPolyPow (environment index) leftExponent)
            (coeffEvalMonoFrom environment (index + 1) leftRest))
          (polyMul (coeffPolyPow (environment index) rightExponent)
            (coeffEvalMonoFrom environment (index + 1) rightRest)))
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul
          (coeffPolyPow_add (environment index)
            leftExponent rightExponent)
          (coeffEvalMonoFrom_monoMul environment (index + 1)
            leftRest rightRest))
        (RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.mul_four_swap
            (coeffPolyPow (environment index) leftExponent)
            (coeffEvalMonoFrom environment (index + 1) leftRest)
            (coeffPolyPow (environment index) rightExponent)
            (coeffEvalMonoFrom environment (index + 1) rightRest)))

theorem coeffEvalMono_monoMul
    (environment : Nat → RatPoly) (left right : List Nat) :
    RatPolyCoeffEqv
      (coeffEvalMono environment (monoMul left right))
      (polyMul (coeffEvalMono environment left)
        (coeffEvalMono environment right)) :=
  coeffEvalMonoFrom_monoMul environment 0 left right

def coeffRawTerm
    (environment : Nat → RatPoly) (term : List Nat × Int) : RatPoly :=
  polySmul (Q'.ofInt term.2)
    (coeffEvalMono environment term.1)

def coeffEvalRaw
    (environment : Nat → RatPoly) : RawPoly → RatPoly
  | [] => polyZero
  | term :: rest =>
      polyAdd (coeffRawTerm environment term)
        (coeffEvalRaw environment rest)

theorem coeffEvalRaw_append
    (environment : Nat → RatPoly) : ∀ left right,
    RatPolyCoeffEqv
      (coeffEvalRaw environment (left ++ right))
      (polyAdd (coeffEvalRaw environment left)
        (coeffEvalRaw environment right))
  | [], right => RatPolyCoeffEqv.symm
      (RatPolyCoeffEqv.zero_add (coeffEvalRaw environment right))
  | term :: rest, right => by
      change RatPolyCoeffEqv
        (polyAdd (coeffRawTerm environment term)
          (coeffEvalRaw environment (rest ++ right)))
        (polyAdd
          (polyAdd (coeffRawTerm environment term)
            (coeffEvalRaw environment rest))
          (coeffEvalRaw environment right))
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.refl _)
          (coeffEvalRaw_append environment rest right))
        (RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.add_assoc
            (coeffRawTerm environment term)
            (coeffEvalRaw environment rest)
            (coeffEvalRaw environment right)))

private theorem ofInt_neg_eqv_local (coefficient : Int) :
    Q'.ofInt (-coefficient) ≈ -(Q'.ofInt coefficient) := by
  show (-coefficient) * (1 : Int) =
    (-coefficient) * (1 : Int)
  rfl

private theorem ofInt_mul_eqv_local (first second : Int) :
    Q'.ofInt (first * second) ≈
      Q'.ofInt first * Q'.ofInt second := by
  show (first * second) * (1 * 1) =
    (first * second) * 1
  omega

private theorem ofInt_add_eqv_local (first second : Int) :
    Q'.ofInt (first + second) ≈
      Q'.ofInt first + Q'.ofInt second := by
  show (first + second) * (1 * 1) =
    (first * 1 + second * 1) * 1
  omega

private theorem polyNeg_polySmul_coeff
    (coefficient : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (polyNeg (polySmul coefficient polynomial))
      (polySmul (-coefficient) polynomial) := by
  intro weight
  refine Q'.eqv_trans _
    (-(ratWeightedSum weight
      (polySmul coefficient polynomial))) _
    (ratWeightedSum_polyNeg weight _)
    (Q'.eqv_trans _
      (-(coefficient * ratWeightedSum weight polynomial)) _
      (Q'.neg_eqv_congr _ _
        (ratWeightedSum_smul weight coefficient polynomial))
      (Q'.eqv_trans _
        ((-coefficient) * ratWeightedSum weight polynomial) _
        (Q'.eqv_symm
          (Q'.neg_mul_eqv coefficient
            (ratWeightedSum weight polynomial)))
        (Q'.eqv_symm
          (ratWeightedSum_smul weight (-coefficient) polynomial))))

private theorem coeffRawTerm_neg
    (environment : Nat → RatPoly)
    (monomial : List Nat) (coefficient : Int) :
    RatPolyCoeffEqv
      (coeffRawTerm environment (monomial, -coefficient))
      (polyNeg (coeffRawTerm environment (monomial, coefficient))) := by
  unfold coeffRawTerm
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.smul_coefficient
      (ofInt_neg_eqv_local coefficient)
      (coeffEvalMono environment monomial))
    (RatPolyCoeffEqv.symm
      (polyNeg_polySmul_coeff (Q'.ofInt coefficient)
        (coeffEvalMono environment monomial)))

theorem coeffEvalRaw_rawNeg
    (environment : Nat → RatPoly) : ∀ polynomial,
    RatPolyCoeffEqv
      (coeffEvalRaw environment (rawNeg polynomial))
      (polyNeg (coeffEvalRaw environment polynomial))
  | [] => RatPolyCoeffEqv.refl polyZero
  | (monomial, coefficient) :: rest => by
      simp only [rawNeg, List.map_cons, coeffEvalRaw, polyNeg,
        polyAdd, List.map_append]
      exact RatPolyCoeffEqv.add
        (coeffRawTerm_neg environment monomial coefficient)
        (coeffEvalRaw_rawNeg environment rest)

private theorem coeffRawTerm_mul
    (environment : Nat → RatPoly)
    (left right : List Nat × Int) :
    RatPolyCoeffEqv
      (polyMul (coeffRawTerm environment left)
        (coeffRawTerm environment right))
      (coeffRawTerm environment
        (monoMul left.1 right.1, left.2 * right.2)) := by
  unfold coeffRawTerm
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.polyMul_smul_left
      (Q'.ofInt left.2) (coeffEvalMono environment left.1)
      (polySmul (Q'.ofInt right.2)
        (coeffEvalMono environment right.1))) ?_
  refine RatPolyCoeffEqv.trans
    ((RatPolyCoeffEqv.polyMul_smul_right
      (Q'.ofInt right.2)
      (coeffEvalMono environment left.1)
      (coeffEvalMono environment right.1)).smul
        (Q'.ofInt left.2)) ?_
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.smul_assoc
      (Q'.ofInt left.2) (Q'.ofInt right.2)
      (polyMul (coeffEvalMono environment left.1)
        (coeffEvalMono environment right.1))) ?_
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_symm (ofInt_mul_eqv_local left.2 right.2))
      (polyMul (coeffEvalMono environment left.1)
        (coeffEvalMono environment right.1))) ?_
  exact (coeffEvalMono_monoMul environment left.1 right.1).symm.smul
    (Q'.ofInt (left.2 * right.2))

theorem coeffEvalRaw_scaleTerm
    (environment : Nat → RatPoly)
    (monomial : List Nat) (coefficient : Int) : ∀ polynomial,
    RatPolyCoeffEqv
      (coeffEvalRaw environment
        (scaleTerm monomial coefficient polynomial))
      (polyMul (coeffRawTerm environment (monomial, coefficient))
        (coeffEvalRaw environment polynomial))
  | [] => RatPolyCoeffEqv.symm
      (RatPolyCoeffEqv.mul_zero_right
        (coeffRawTerm environment (monomial, coefficient)))
  | term :: rest => by
      change RatPolyCoeffEqv
        (polyAdd
          (coeffRawTerm environment
            (monoMul monomial term.1, coefficient * term.2))
          (coeffEvalRaw environment
            (scaleTerm monomial coefficient rest)))
        (polyMul (coeffRawTerm environment (monomial, coefficient))
          (polyAdd (coeffRawTerm environment term)
            (coeffEvalRaw environment rest)))
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.symm
            (coeffRawTerm_mul environment
              (monomial, coefficient) term))
          (coeffEvalRaw_scaleTerm environment monomial coefficient rest))
        (RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.mul_add_right
            (coeffRawTerm environment (monomial, coefficient))
            (coeffRawTerm environment term)
            (coeffEvalRaw environment rest)))

theorem coeffEvalRaw_rawMul
    (environment : Nat → RatPoly) : ∀ left right,
    RatPolyCoeffEqv
      (coeffEvalRaw environment (rawMul left right))
      (polyMul (coeffEvalRaw environment left)
        (coeffEvalRaw environment right))
  | [], right => RatPolyCoeffEqv.symm
      (RatPolyCoeffEqv.mul_zero_left
        (coeffEvalRaw environment right))
  | term :: rest, right => by
      change RatPolyCoeffEqv
        (coeffEvalRaw environment
          (scaleTerm term.1 term.2 right ++ rawMul rest right))
        (polyMul
          (polyAdd (coeffRawTerm environment term)
            (coeffEvalRaw environment rest))
          (coeffEvalRaw environment right))
      exact RatPolyCoeffEqv.trans
        (coeffEvalRaw_append environment _ _)
        (RatPolyCoeffEqv.trans
          (RatPolyCoeffEqv.add
            (coeffEvalRaw_scaleTerm environment term.1 term.2 right)
            (coeffEvalRaw_rawMul environment rest right))
          (RatPolyCoeffEqv.symm
            (by
              rw [polyMul_add_left_exact]
              exact RatPolyCoeffEqv.refl _)))

theorem coeffEvalRaw_rawPow
    (environment : Nat → RatPoly) (polynomial : RawPoly) : ∀ power,
    RatPolyCoeffEqv
      (coeffEvalRaw environment (rawPow polynomial power))
      (coeffPolyPow (coeffEvalRaw environment polynomial) power)
  | 0 => by
      change RatPolyCoeffEqv
        (polyAdd
          (polySmul (Q'.ofInt 1) polyOne) polyZero) polyOne
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.smul_coefficient
            (Q'.eqv_refl 1) polyOne)
          (RatPolyCoeffEqv.refl polyZero))
        (RatPolyCoeffEqv.add_zero polyOne)
  | power + 1 =>
      RatPolyCoeffEqv.trans
        (coeffEvalRaw_rawMul environment
          (rawPow polynomial power) polynomial)
        (RatPolyCoeffEqv.mul
          (coeffEvalRaw_rawPow environment polynomial power)
          (RatPolyCoeffEqv.refl _))

theorem RatPolyCoeffEqv.one_smul (polynomial : RatPoly) :
    RatPolyCoeffEqv (polySmul 1 polynomial) polynomial := by
  intro weight
  exact Q'.eqv_trans _ (1 * ratWeightedSum weight polynomial) _
    (ratWeightedSum_smul weight 1 polynomial)
    (Q'.one_mul_eqv _)

private theorem coeffEvalMonoFrom_varMono
    (environment : Nat → RatPoly) : ∀ index variableIndex,
    RatPolyCoeffEqv
      (coeffEvalMonoFrom environment index (varMono variableIndex))
      (environment (index + variableIndex))
  | index, 0 => by
      change RatPolyCoeffEqv
        (polyMul
          (polyMul polyOne (environment index)) polyOne)
        (environment (index + 0))
      rw [Nat.add_zero]
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul_right
          (RatPolyCoeffEqv.one_mul (environment index)) polyOne)
        (RatPolyCoeffEqv.mul_one (environment index))
  | index, variableIndex + 1 => by
      change RatPolyCoeffEqv
        (polyMul polyOne
          (coeffEvalMonoFrom environment (index + 1)
            (varMono variableIndex)))
        (environment (index + (variableIndex + 1)))
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.one_mul _)
        (by
          have h := coeffEvalMonoFrom_varMono environment
            (index + 1) variableIndex
          have hindex : index + 1 + variableIndex =
              index + (variableIndex + 1) := by omega
          rw [hindex] at h
          exact h)

theorem coeffEvalMono_varMono
    (environment : Nat → RatPoly) (variableIndex : Nat) :
    RatPolyCoeffEqv
      (coeffEvalMono environment (varMono variableIndex))
      (environment variableIndex) := by
  simpa [coeffEvalMono] using
    (coeffEvalMonoFrom_varMono environment 0 variableIndex)

def coeffEvalExpr
    (environment : Nat → RatPoly) : PolyExpr → RatPoly
  | .const coefficient =>
      polySmul (Q'.ofInt coefficient) polyOne
  | .var index => environment index
  | .add left right =>
      polyAdd (coeffEvalExpr environment left)
        (coeffEvalExpr environment right)
  | .mul left right =>
      polyMul (coeffEvalExpr environment left)
        (coeffEvalExpr environment right)
  | .neg value => polyNeg (coeffEvalExpr environment value)
  | .pow value power =>
      coeffPolyPow (coeffEvalExpr environment value) power

theorem coeffEvalExpr_rawNormalize
    (environment : Nat → RatPoly) : ∀ expression,
    RatPolyCoeffEqv
      (coeffEvalExpr environment expression)
      (coeffEvalRaw environment (rawNormalize expression))
  | .const coefficient => by
      change RatPolyCoeffEqv
        (polySmul (Q'.ofInt coefficient) polyOne)
        (polyAdd (polySmul (Q'.ofInt coefficient) polyOne) polyZero)
      exact RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.add_zero _)
  | .var index => by
      change RatPolyCoeffEqv
        (environment index)
        (polyAdd
          (polySmul (Q'.ofInt 1)
            (coeffEvalMono environment (varMono index))) polyZero)
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.symm
          (coeffEvalMono_varMono environment index))
        (RatPolyCoeffEqv.trans
          (RatPolyCoeffEqv.symm
            (RatPolyCoeffEqv.one_smul
              (coeffEvalMono environment (varMono index))))
          (RatPolyCoeffEqv.symm
            (RatPolyCoeffEqv.add_zero _)))
  | .add left right =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add
          (coeffEvalExpr_rawNormalize environment left)
          (coeffEvalExpr_rawNormalize environment right))
        (RatPolyCoeffEqv.symm
          (coeffEvalRaw_append environment
            (rawNormalize left) (rawNormalize right)))
  | .mul left right =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul
          (coeffEvalExpr_rawNormalize environment left)
          (coeffEvalExpr_rawNormalize environment right))
        (RatPolyCoeffEqv.symm
          (coeffEvalRaw_rawMul environment
            (rawNormalize left) (rawNormalize right)))
  | .neg value =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.neg
          (coeffEvalExpr_rawNormalize environment value))
        (RatPolyCoeffEqv.symm
          (coeffEvalRaw_rawNeg environment (rawNormalize value)))
  | .pow value power =>
      RatPolyCoeffEqv.trans
        (coeffPolyPow_congr
          (coeffEvalExpr_rawNormalize environment value) power)
        (RatPolyCoeffEqv.symm
          (coeffEvalRaw_rawPow environment
            (rawNormalize value) power))

private theorem coeffRawTerm_zero
    (environment : Nat → RatPoly) (monomial : List Nat) :
    RatPolyCoeffEqv
      (coeffRawTerm environment (monomial, 0)) polyZero := by
  unfold coeffRawTerm
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_refl 0) (coeffEvalMono environment monomial))
    (RatPolyCoeffEqv.zero_smul _)

private theorem coeffRawTerm_add
    (environment : Nat → RatPoly)
    (monomial : List Nat) (first second : Int) :
    RatPolyCoeffEqv
      (polyAdd
        (coeffRawTerm environment (monomial, first))
        (coeffRawTerm environment (monomial, second)))
      (coeffRawTerm environment (monomial, first + second)) := by
  unfold coeffRawTerm
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add_smul_same
      (Q'.ofInt first) (Q'.ofInt second)
      (coeffEvalMono environment monomial))
    (RatPolyCoeffEqv.smul_coefficient
      (Q'.eqv_symm (ofInt_add_eqv_local first second))
      (coeffEvalMono environment monomial))

private theorem add_swap_nested
    (first second rest : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd second (polyAdd first rest))
      (polyAdd first (polyAdd second rest)) := by
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.symm
      (RatPolyCoeffEqv.add_assoc second first rest))
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.add_comm second first)
        (RatPolyCoeffEqv.refl rest))
      (RatPolyCoeffEqv.add_assoc first second rest))

theorem coeffEvalRaw_insertTerm
    (environment : Nat → RatPoly)
    (monomial : List Nat) (coefficient : Int) : ∀ polynomial,
    RatPolyCoeffEqv
      (coeffEvalRaw environment
        (insertTerm monomial coefficient polynomial))
      (polyAdd (coeffRawTerm environment (monomial, coefficient))
        (coeffEvalRaw environment polynomial))
  | [] => by
      by_cases hzero : coefficient = 0
      · subst coefficient
        simp only [insertTerm, if_true, coeffEvalRaw]
        exact RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.trans
            (RatPolyCoeffEqv.add
              (coeffRawTerm_zero environment monomial)
              (RatPolyCoeffEqv.refl polyZero))
            (RatPolyCoeffEqv.zero_add polyZero))
      · simp only [insertTerm, hzero, if_false, coeffEvalRaw]
        exact RatPolyCoeffEqv.refl _
  | (otherMonomial, otherCoefficient) :: rest => by
      by_cases hzero : coefficient = 0
      · subst coefficient
        simp only [insertTerm, if_true]
        exact RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.trans
            (RatPolyCoeffEqv.add
              (coeffRawTerm_zero environment monomial)
              (RatPolyCoeffEqv.refl _))
            (RatPolyCoeffEqv.zero_add _))
      · rw [show insertTerm monomial coefficient
            ((otherMonomial, otherCoefficient) :: rest) =
          match monoCmp monomial otherMonomial with
          | .lt => (monomial, coefficient) ::
              (otherMonomial, otherCoefficient) :: rest
          | .eq => if coefficient + otherCoefficient = 0
              then rest
              else (monomial, coefficient + otherCoefficient) :: rest
          | .gt => (otherMonomial, otherCoefficient) ::
              insertTerm monomial coefficient rest by
            change
              (if coefficient = 0 then
                (otherMonomial, otherCoefficient) :: rest
              else
                match monoCmp monomial otherMonomial with
                | .lt => (monomial, coefficient) ::
                    (otherMonomial, otherCoefficient) :: rest
                | .eq => if coefficient + otherCoefficient = 0
                    then rest
                    else (monomial, coefficient + otherCoefficient) :: rest
                | .gt => (otherMonomial, otherCoefficient) ::
                    insertTerm monomial coefficient rest) = _
            rw [if_neg hzero]]
        cases hcmp : monoCmp monomial otherMonomial with
        | lt => exact RatPolyCoeffEqv.refl _
        | eq =>
            have hmonomial : monomial = otherMonomial := monoCmp_eq hcmp
            subst otherMonomial
            by_cases hcombined : coefficient + otherCoefficient = 0
            · simp only [hcombined, if_true]
              exact RatPolyCoeffEqv.symm
                (RatPolyCoeffEqv.trans
                  (RatPolyCoeffEqv.symm
                    (RatPolyCoeffEqv.add_assoc
                      (coeffRawTerm environment (monomial, coefficient))
                      (coeffRawTerm environment (monomial, otherCoefficient))
                      (coeffEvalRaw environment rest)))
                  (RatPolyCoeffEqv.trans
                    (RatPolyCoeffEqv.add
                      (RatPolyCoeffEqv.trans
                        (coeffRawTerm_add environment monomial
                          coefficient otherCoefficient)
                        (by
                          rw [hcombined]
                          exact coeffRawTerm_zero environment monomial))
                      (RatPolyCoeffEqv.refl _))
                    (RatPolyCoeffEqv.zero_add _)))
            · simp only [hcombined, if_false, coeffEvalRaw]
              exact RatPolyCoeffEqv.symm
                (RatPolyCoeffEqv.trans
                  (RatPolyCoeffEqv.symm
                    (RatPolyCoeffEqv.add_assoc
                      (coeffRawTerm environment (monomial, coefficient))
                      (coeffRawTerm environment (monomial, otherCoefficient))
                      (coeffEvalRaw environment rest)))
                  (RatPolyCoeffEqv.add
                    (coeffRawTerm_add environment monomial
                      coefficient otherCoefficient)
                    (RatPolyCoeffEqv.refl _)))
        | gt =>
            change RatPolyCoeffEqv
              (polyAdd
                (coeffRawTerm environment
                  (otherMonomial, otherCoefficient))
                (coeffEvalRaw environment
                  (insertTerm monomial coefficient rest)))
              (polyAdd (coeffRawTerm environment (monomial, coefficient))
                (polyAdd
                  (coeffRawTerm environment
                    (otherMonomial, otherCoefficient))
                  (coeffEvalRaw environment rest)))
            exact RatPolyCoeffEqv.trans
              (RatPolyCoeffEqv.add
                (RatPolyCoeffEqv.refl _)
                (coeffEvalRaw_insertTerm environment
                  monomial coefficient rest))
              (add_swap_nested
                (coeffRawTerm environment (monomial, coefficient))
                (coeffRawTerm environment
                  (otherMonomial, otherCoefficient))
                (coeffEvalRaw environment rest))

theorem coeffEvalRaw_canon
    (environment : Nat → RatPoly) : ∀ polynomial,
    RatPolyCoeffEqv
      (coeffEvalRaw environment (canon polynomial))
      (coeffEvalRaw environment polynomial)
  | [] => RatPolyCoeffEqv.refl polyZero
  | term :: rest =>
      RatPolyCoeffEqv.trans
        (coeffEvalRaw_insertTerm environment term.1 term.2 (canon rest))
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.refl _)
          (coeffEvalRaw_canon environment rest))

/-- Any identity accepted by the repository's reflective integer polynomial
normalizer remains coefficientwise valid after substituting arbitrary finite
rational polynomials for its variables. -/
theorem coeffEvalExpr_eqv_of_normalize_eq
    (left right : PolyExpr)
    (h : normalize left = normalize right)
    (environment : Nat → RatPoly) :
    RatPolyCoeffEqv
      (coeffEvalExpr environment left)
      (coeffEvalExpr environment right) := by
  exact RatPolyCoeffEqv.trans
    (coeffEvalExpr_rawNormalize environment left)
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.symm
        (coeffEvalRaw_canon environment (rawNormalize left)))
      (by
        change RatPolyCoeffEqv
          (coeffEvalRaw environment (normalize left))
          (coeffEvalExpr environment right)
        rw [h]
        exact RatPolyCoeffEqv.trans
          (coeffEvalRaw_canon environment (rawNormalize right))
          (RatPolyCoeffEqv.symm
            (coeffEvalExpr_rawNormalize environment right))))

structure PolyQuaternionExpr where
  scalar : PolyExpr
  iPart : PolyExpr
  jPart : PolyExpr
  kPart : PolyExpr

namespace PolyQuaternionExpr

def one : PolyQuaternionExpr :=
  ⟨.const 1, .const 0, .const 0, .const 0⟩

def coordinate (offset : Nat) : PolyQuaternionExpr :=
  ⟨.var offset, .var (offset + 1), .var (offset + 2), .var (offset + 3)⟩

def conj (q : PolyQuaternionExpr) : PolyQuaternionExpr :=
  ⟨q.scalar, .neg q.iPart, .neg q.jPart, .neg q.kPart⟩

def mul (q r : PolyQuaternionExpr) : PolyQuaternionExpr where
  scalar :=
    .add (.mul q.scalar r.scalar)
      (.neg
        (.add (.mul q.iPart r.iPart)
          (.add (.mul q.jPart r.jPart)
            (.mul q.kPart r.kPart))))
  iPart :=
    .add (.mul q.scalar r.iPart)
      (.add (.mul q.iPart r.scalar)
        (.add (.mul q.jPart r.kPart)
          (.neg (.mul q.kPart r.jPart))))
  jPart :=
    .add (.mul q.scalar r.jPart)
      (.add (.mul q.jPart r.scalar)
        (.add (.mul q.kPart r.iPart)
          (.neg (.mul q.iPart r.kPart))))
  kPart :=
    .add (.mul q.scalar r.kPart)
      (.add (.mul q.kPart r.scalar)
        (.add (.mul q.iPart r.jPart)
          (.neg (.mul q.jPart r.iPart))))

def norm (q : PolyQuaternionExpr) : PolyExpr :=
  .add (.mul q.scalar q.scalar)
    (.add (.mul q.iPart q.iPart)
      (.add (.mul q.jPart q.jPart)
        (.mul q.kPart q.kPart)))

def scalarQuaternion (scalar : PolyExpr) : PolyQuaternionExpr :=
  ⟨scalar, .const 0, .const 0, .const 0⟩

end PolyQuaternionExpr

def polyQuaternionNorm (q : PolyQuaternion) : RatPoly :=
  polyAdd (polyMul q.scalar q.scalar)
    (polyAdd (polyMul q.iPart q.iPart)
      (polyAdd (polyMul q.jPart q.jPart)
        (polyMul q.kPart q.kPart)))

def scalarPolyQuaternion (scalar : RatPoly) : PolyQuaternion :=
  ⟨scalar, polyZero, polyZero, polyZero⟩

private theorem monoMul_varMono_self : ∀ coordinate : Nat,
    monoMul (varMono coordinate) (varMono coordinate) =
      coordinateSquareMono coordinate
  | 0 => rfl
  | coordinate + 1 => by
      change
        monoMul (0 :: varMono coordinate) (0 :: varMono coordinate) =
          0 :: coordinateSquareMono coordinate
      simp only [monoMul, Nat.zero_add]
      rw [monoMul_varMono_self coordinate]

/-- The formal Hamilton norm of a coordinate quaternion is coefficientwise
the four-coordinate radius polynomial consumed by the constructive Haar
sphere ideal.  Coefficientwise equality is the appropriate statement because
`Q'` deliberately retains unreduced rational representatives. -/
theorem polyQuaternionNorm_coordinateVariable (block : Nat) :
    RatPolyCoeffEqv
      (polyQuaternionNorm (PolyQuaternion.coordinateVariable block))
      (quaternionRadiusPolynomial block) := by
  change
    RatPolyCoeffEqv
      [ (monoMul (varMono (4 * block)) (varMono (4 * block)), 1 * 1),
        (monoMul (varMono (4 * block + 1)) (varMono (4 * block + 1)), 1 * 1),
        (monoMul (varMono (4 * block + 2)) (varMono (4 * block + 2)), 1 * 1),
        (monoMul (varMono (4 * block + 3)) (varMono (4 * block + 3)), 1 * 1) ]
      [ (coordinateSquareMono (4 * block), 1),
        (coordinateSquareMono (4 * block + 1), 1),
        (coordinateSquareMono (4 * block + 2), 1),
        (coordinateSquareMono (4 * block + 3), 1) ]
  rw [monoMul_varMono_self, monoMul_varMono_self,
    monoMul_varMono_self, monoMul_varMono_self]
  intro weight
  exact Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv 1))
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv 1))
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv 1))
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv 1))
          (Q'.eqv_refl 0))))

theorem PolyQuaternionCoeffEqv.scalarQuaternion
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) :
    PolyQuaternionCoeffEqv
      (scalarPolyQuaternion left) (scalarPolyQuaternion right) :=
  ⟨h, RatPolyCoeffEqv.refl polyZero,
    RatPolyCoeffEqv.refl polyZero, RatPolyCoeffEqv.refl polyZero⟩

private theorem RatPolyCoeffEqv.add_three_zero
    {first second third : RatPoly}
    (hfirst : RatPolyCoeffEqv first polyZero)
    (hsecond : RatPolyCoeffEqv second polyZero)
    (hthird : RatPolyCoeffEqv third polyZero) :
    RatPolyCoeffEqv
      (polyAdd first (polyAdd second third)) polyZero :=
  RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add hfirst
      (RatPolyCoeffEqv.add hsecond hthird))
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.zero_add (polyAdd polyZero polyZero))
      (RatPolyCoeffEqv.zero_add polyZero))

/-- Right multiplication by a scalar quaternion scales the scalar component,
coefficientwise.  The zero vector components are discharged constructively. -/
theorem PolyQuaternionCoeffEqv.mul_scalar_scalar
    (q : PolyQuaternion) (scalar : RatPoly) :
    RatPolyCoeffEqv
      (PolyQuaternion.mul q (scalarPolyQuaternion scalar)).scalar
      (polyMul q.scalar scalar) := by
  have hzero : RatPolyCoeffEqv
      (polyAdd (polyMul q.iPart polyZero)
        (polyAdd (polyMul q.jPart polyZero)
          (polyMul q.kPart polyZero))) polyZero :=
    RatPolyCoeffEqv.add_three_zero
      (RatPolyCoeffEqv.mul_zero_right q.iPart)
      (RatPolyCoeffEqv.mul_zero_right q.jPart)
      (RatPolyCoeffEqv.mul_zero_right q.kPart)
  have hneg : RatPolyCoeffEqv
      (polyNeg
        (polyAdd (polyMul q.iPart polyZero)
          (polyAdd (polyMul q.jPart polyZero)
            (polyMul q.kPart polyZero)))) polyZero := by
    simpa [polyNeg, polyZero] using RatPolyCoeffEqv.neg hzero
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.refl (polyMul q.scalar scalar)) hneg)
    (RatPolyCoeffEqv.add_zero (polyMul q.scalar scalar))

private def threeQuaternionEnvironment
    (first second third : PolyQuaternion) : Nat → RatPoly
  | 0 => first.scalar
  | 1 => first.iPart
  | 2 => first.jPart
  | 3 => first.kPart
  | 4 => second.scalar
  | 5 => second.iPart
  | 6 => second.jPart
  | 7 => second.kPart
  | 8 => third.scalar
  | 9 => third.iPart
  | 10 => third.jPart
  | 11 => third.kPart
  | _ => polyZero

private def twoQuaternionEnvironment
    (first second : PolyQuaternion) : Nat → RatPoly :=
  threeQuaternionEnvironment first second PolyQuaternion.one

private def exprAssocLeft : PolyQuaternionExpr :=
  PolyQuaternionExpr.mul
    (PolyQuaternionExpr.mul
      (PolyQuaternionExpr.coordinate 0)
      (PolyQuaternionExpr.coordinate 4))
    (PolyQuaternionExpr.coordinate 8)

private def exprAssocRight : PolyQuaternionExpr :=
  PolyQuaternionExpr.mul
    (PolyQuaternionExpr.coordinate 0)
    (PolyQuaternionExpr.mul
      (PolyQuaternionExpr.coordinate 4)
      (PolyQuaternionExpr.coordinate 8))

private theorem exprAssoc_normal :
    normalize exprAssocLeft.scalar = normalize exprAssocRight.scalar ∧
      normalize exprAssocLeft.iPart = normalize exprAssocRight.iPart ∧
      normalize exprAssocLeft.jPart = normalize exprAssocRight.jPart ∧
      normalize exprAssocLeft.kPart = normalize exprAssocRight.kPart := by
  set_option maxRecDepth 100000 in
  decide

theorem PolyQuaternionCoeffEqv.mul_assoc
    (first second third : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul (PolyQuaternion.mul first second) third)
      (PolyQuaternion.mul first (PolyQuaternion.mul second third)) := by
  let environment := threeQuaternionEnvironment first second third
  constructor
  · simpa [environment, exprAssocLeft, exprAssocRight,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, threeQuaternionEnvironment, PolyQuaternion.mul] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprAssocLeft.scalar exprAssocRight.scalar
        exprAssoc_normal.1 environment)
  · simpa [environment, exprAssocLeft, exprAssocRight,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, threeQuaternionEnvironment, PolyQuaternion.mul] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprAssocLeft.iPart exprAssocRight.iPart
        exprAssoc_normal.2.1 environment)
  · simpa [environment, exprAssocLeft, exprAssocRight,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, threeQuaternionEnvironment, PolyQuaternion.mul] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprAssocLeft.jPart exprAssocRight.jPart
        exprAssoc_normal.2.2.1 environment)
  · simpa [environment, exprAssocLeft, exprAssocRight,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.coordinate,
      coeffEvalExpr, threeQuaternionEnvironment, PolyQuaternion.mul] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprAssocLeft.kPart exprAssocRight.kPart
        exprAssoc_normal.2.2.2 environment)

private def exprConjProduct : PolyQuaternionExpr :=
  PolyQuaternionExpr.mul
    (PolyQuaternionExpr.coordinate 0)
    (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))

private def exprConjProductTarget : PolyQuaternionExpr :=
  PolyQuaternionExpr.scalarQuaternion
    (PolyQuaternionExpr.norm (PolyQuaternionExpr.coordinate 0))

private theorem exprConjProduct_normal :
    normalize exprConjProduct.scalar =
        normalize exprConjProductTarget.scalar ∧
      normalize exprConjProduct.iPart =
        normalize exprConjProductTarget.iPart ∧
      normalize exprConjProduct.jPart =
        normalize exprConjProductTarget.jPart ∧
      normalize exprConjProduct.kPart =
        normalize exprConjProductTarget.kPart := by
  set_option maxRecDepth 100000 in
  decide

theorem PolyQuaternionCoeffEqv.mul_conj
    (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul q (PolyQuaternion.conj q))
      (scalarPolyQuaternion (polyQuaternionNorm q)) := by
  let environment := twoQuaternionEnvironment q q
  constructor
  · simpa [environment, exprConjProduct, exprConjProductTarget,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.scalarQuaternion,
      PolyQuaternionExpr.norm, coeffEvalExpr, twoQuaternionEnvironment,
      threeQuaternionEnvironment, PolyQuaternion.mul, PolyQuaternion.conj,
      scalarPolyQuaternion, polyQuaternionNorm] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjProduct.scalar exprConjProductTarget.scalar
        exprConjProduct_normal.1 environment)
  · refine RatPolyCoeffEqv.trans ?_
      (RatPolyCoeffEqv.zero_smul polyOne)
    simpa [environment, exprConjProduct, exprConjProductTarget,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.scalarQuaternion,
      PolyQuaternionExpr.norm, coeffEvalExpr, twoQuaternionEnvironment,
      threeQuaternionEnvironment, PolyQuaternion.mul, PolyQuaternion.conj,
      scalarPolyQuaternion, polyQuaternionNorm] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjProduct.iPart exprConjProductTarget.iPart
        exprConjProduct_normal.2.1 environment)
  · refine RatPolyCoeffEqv.trans ?_
      (RatPolyCoeffEqv.zero_smul polyOne)
    simpa [environment, exprConjProduct, exprConjProductTarget,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.scalarQuaternion,
      PolyQuaternionExpr.norm, coeffEvalExpr, twoQuaternionEnvironment,
      threeQuaternionEnvironment, PolyQuaternion.mul, PolyQuaternion.conj,
      scalarPolyQuaternion, polyQuaternionNorm] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjProduct.jPart exprConjProductTarget.jPart
        exprConjProduct_normal.2.2.1 environment)
  · refine RatPolyCoeffEqv.trans ?_
      (RatPolyCoeffEqv.zero_smul polyOne)
    simpa [environment, exprConjProduct, exprConjProductTarget,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.scalarQuaternion,
      PolyQuaternionExpr.norm, coeffEvalExpr, twoQuaternionEnvironment,
      threeQuaternionEnvironment, PolyQuaternion.mul, PolyQuaternion.conj,
      scalarPolyQuaternion, polyQuaternionNorm] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjProduct.kPart exprConjProductTarget.kPart
        exprConjProduct_normal.2.2.2 environment)

private def exprConjMulProduct : PolyQuaternionExpr :=
  PolyQuaternionExpr.mul
    (PolyQuaternionExpr.conj (PolyQuaternionExpr.coordinate 0))
    (PolyQuaternionExpr.coordinate 0)

private theorem exprConjMulProduct_normal :
    normalize exprConjMulProduct.scalar =
        normalize exprConjProductTarget.scalar ∧
      normalize exprConjMulProduct.iPart =
        normalize exprConjProductTarget.iPart ∧
      normalize exprConjMulProduct.jPart =
        normalize exprConjProductTarget.jPart ∧
      normalize exprConjMulProduct.kPart =
        normalize exprConjProductTarget.kPart := by
  set_option maxRecDepth 100000 in
  decide

theorem PolyQuaternionCoeffEqv.conj_mul
    (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul (PolyQuaternion.conj q) q)
      (scalarPolyQuaternion (polyQuaternionNorm q)) := by
  let environment := twoQuaternionEnvironment q q
  constructor
  · simpa [environment, exprConjMulProduct, exprConjProductTarget,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.scalarQuaternion,
      PolyQuaternionExpr.norm, coeffEvalExpr, twoQuaternionEnvironment,
      threeQuaternionEnvironment, PolyQuaternion.mul, PolyQuaternion.conj,
      scalarPolyQuaternion, polyQuaternionNorm] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjMulProduct.scalar exprConjProductTarget.scalar
        exprConjMulProduct_normal.1 environment)
  · refine RatPolyCoeffEqv.trans ?_
      (RatPolyCoeffEqv.zero_smul polyOne)
    simpa [environment, exprConjMulProduct, exprConjProductTarget,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.scalarQuaternion,
      PolyQuaternionExpr.norm, coeffEvalExpr, twoQuaternionEnvironment,
      threeQuaternionEnvironment, PolyQuaternion.mul, PolyQuaternion.conj,
      scalarPolyQuaternion, polyQuaternionNorm] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjMulProduct.iPart exprConjProductTarget.iPart
        exprConjMulProduct_normal.2.1 environment)
  · refine RatPolyCoeffEqv.trans ?_
      (RatPolyCoeffEqv.zero_smul polyOne)
    simpa [environment, exprConjMulProduct, exprConjProductTarget,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.scalarQuaternion,
      PolyQuaternionExpr.norm, coeffEvalExpr, twoQuaternionEnvironment,
      threeQuaternionEnvironment, PolyQuaternion.mul, PolyQuaternion.conj,
      scalarPolyQuaternion, polyQuaternionNorm] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjMulProduct.jPart exprConjProductTarget.jPart
        exprConjMulProduct_normal.2.2.1 environment)
  · refine RatPolyCoeffEqv.trans ?_
      (RatPolyCoeffEqv.zero_smul polyOne)
    simpa [environment, exprConjMulProduct, exprConjProductTarget,
      PolyQuaternionExpr.mul, PolyQuaternionExpr.conj,
      PolyQuaternionExpr.coordinate, PolyQuaternionExpr.scalarQuaternion,
      PolyQuaternionExpr.norm, coeffEvalExpr, twoQuaternionEnvironment,
      threeQuaternionEnvironment, PolyQuaternion.mul, PolyQuaternion.conj,
      scalarPolyQuaternion, polyQuaternionNorm] using
      (coeffEvalExpr_eqv_of_normalize_eq
        exprConjMulProduct.kPart exprConjProductTarget.kPart
        exprConjMulProduct_normal.2.2.2 environment)

/-- Either orientation followed by the opposite orientation is the scalar
radius polynomial of that quaternion block. -/
theorem orientedCoordinateQuaternion_mul_opposite
    (block : Nat) (reverse : Bool) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul
        (orientedCoordinateQuaternion block reverse)
        (orientedCoordinateQuaternion block (!reverse)))
      (scalarPolyQuaternion (quaternionRadiusPolynomial block)) := by
  cases reverse with
  | false =>
      exact PolyQuaternionCoeffEqv.trans
        (by simpa [orientedCoordinateQuaternion] using
          (PolyQuaternionCoeffEqv.mul_conj
            (PolyQuaternion.coordinateVariable block)))
        (PolyQuaternionCoeffEqv.scalarQuaternion
          (polyQuaternionNorm_coordinateVariable block))
  | true =>
      exact PolyQuaternionCoeffEqv.trans
        (by simpa [orientedCoordinateQuaternion] using
          (PolyQuaternionCoeffEqv.conj_mul
            (PolyQuaternion.coordinateVariable block)))
        (PolyQuaternionCoeffEqv.scalarQuaternion
          (polyQuaternionNorm_coordinateVariable block))

private theorem exprScalarCyclic_normal :
    normalize
        (PolyQuaternionExpr.mul
          (PolyQuaternionExpr.coordinate 0)
          (PolyQuaternionExpr.coordinate 4)).scalar =
      normalize
        (PolyQuaternionExpr.mul
          (PolyQuaternionExpr.coordinate 4)
          (PolyQuaternionExpr.coordinate 0)).scalar := by
  set_option maxRecDepth 100000 in
  decide

theorem polyQuaternion_mul_scalar_cyclic
    (left right : PolyQuaternion) :
    RatPolyCoeffEqv
      (PolyQuaternion.mul left right).scalar
      (PolyQuaternion.mul right left).scalar := by
  let environment := twoQuaternionEnvironment left right
  simpa [environment, PolyQuaternionExpr.mul,
    PolyQuaternionExpr.coordinate, coeffEvalExpr,
    twoQuaternionEnvironment, threeQuaternionEnvironment,
    PolyQuaternion.mul] using
    (coeffEvalExpr_eqv_of_normalize_eq
      (PolyQuaternionExpr.mul
        (PolyQuaternionExpr.coordinate 0)
        (PolyQuaternionExpr.coordinate 4)).scalar
      (PolyQuaternionExpr.mul
        (PolyQuaternionExpr.coordinate 4)
        (PolyQuaternionExpr.coordinate 0)).scalar
      exprScalarCyclic_normal environment)

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.haarCarrier
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.HaarCarrierEqv.mul_right
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.factorProduct_carrier_of_listEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.PolyQuaternionCoeffEqv.mul
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.characterPolynomial_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.PolyQuaternionCoeffEqv.mul_assoc
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.orientedCoordinateQuaternion_mul_opposite
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.polyQuaternion_mul_scalar_cyclic
