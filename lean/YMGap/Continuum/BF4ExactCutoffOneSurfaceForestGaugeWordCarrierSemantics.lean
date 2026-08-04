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
open YMGap.Continuum.BF4ExactCutoffOneHaarFiveEvaluation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactSlabSelectedFaceCanonicalWord
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarTranslation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionSpinTwoConditionalHaar
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter

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

private theorem RatPolyCoeffEqv.neg_zero_of
    {polynomial : RatPoly}
    (h : RatPolyCoeffEqv polynomial polyZero) :
    RatPolyCoeffEqv (polyNeg polynomial) polyZero := by
  simpa [polyNeg, polyZero] using RatPolyCoeffEqv.neg h

private theorem RatPolyCoeffEqv.add_four_middle
    {first middle third fourth target : RatPoly}
    (hfirst : RatPolyCoeffEqv first polyZero)
    (hmiddle : RatPolyCoeffEqv middle target)
    (hthird : RatPolyCoeffEqv third polyZero)
    (hfourth : RatPolyCoeffEqv fourth polyZero) :
    RatPolyCoeffEqv
      (polyAdd first (polyAdd middle (polyAdd third fourth))) target :=
  RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add hfirst
      (RatPolyCoeffEqv.add hmiddle
        (RatPolyCoeffEqv.add hthird hfourth)))
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.zero_add
        (polyAdd target (polyAdd polyZero polyZero)))
      (RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add
          (RatPolyCoeffEqv.refl target)
          (RatPolyCoeffEqv.zero_add polyZero))
        (RatPolyCoeffEqv.add_zero target)))

/-- Multiplication by a scalar quaternion scales all four components. -/
theorem PolyQuaternionCoeffEqv.mul_scalar
    (q : PolyQuaternion) (scalar : RatPoly) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul q (scalarPolyQuaternion scalar))
      ⟨polyMul q.scalar scalar, polyMul q.iPart scalar,
        polyMul q.jPart scalar, polyMul q.kPart scalar⟩ := by
  constructor
  · exact PolyQuaternionCoeffEqv.mul_scalar_scalar q scalar
  · exact RatPolyCoeffEqv.add_four_middle
      (RatPolyCoeffEqv.mul_zero_right q.scalar)
      (RatPolyCoeffEqv.refl (polyMul q.iPart scalar))
      (RatPolyCoeffEqv.mul_zero_right q.jPart)
      (RatPolyCoeffEqv.neg_zero_of
        (RatPolyCoeffEqv.mul_zero_right q.kPart))
  · exact RatPolyCoeffEqv.add_four_middle
      (RatPolyCoeffEqv.mul_zero_right q.scalar)
      (RatPolyCoeffEqv.refl (polyMul q.jPart scalar))
      (RatPolyCoeffEqv.mul_zero_right q.kPart)
      (RatPolyCoeffEqv.neg_zero_of
        (RatPolyCoeffEqv.mul_zero_right q.iPart))
  · exact RatPolyCoeffEqv.add_four_middle
      (RatPolyCoeffEqv.mul_zero_right q.scalar)
      (RatPolyCoeffEqv.refl (polyMul q.kPart scalar))
      (RatPolyCoeffEqv.mul_zero_right q.iPart)
      (RatPolyCoeffEqv.neg_zero_of
        (RatPolyCoeffEqv.mul_zero_right q.jPart))

theorem PolyQuaternionCoeffEqv.mul_one (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul q PolyQuaternion.one) q := by
  exact PolyQuaternionCoeffEqv.trans
    (by simpa [PolyQuaternion.one, scalarPolyQuaternion] using
      (PolyQuaternionCoeffEqv.mul_scalar q polyOne))
    ⟨RatPolyCoeffEqv.mul_one q.scalar,
      RatPolyCoeffEqv.mul_one q.iPart,
      RatPolyCoeffEqv.mul_one q.jPart,
      RatPolyCoeffEqv.mul_one q.kPart⟩

theorem PolyQuaternionCoeffEqv.one_mul (q : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (PolyQuaternion.mul PolyQuaternion.one q) q := by
  constructor
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using RatPolyCoeffEqv.one_mul q.scalar
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using RatPolyCoeffEqv.one_mul q.iPart
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using RatPolyCoeffEqv.one_mul q.jPart
  · simpa [PolyQuaternion.mul, PolyQuaternion.one, polyZero,
      polyAdd, polyMul, polyNeg] using RatPolyCoeffEqv.one_mul q.kPart

theorem HaarCarrierEqv.add
    {blocks : Nat} {left left' right right' : RatPoly}
    (hleft : HaarCarrierEqv blocks left left')
    (hright : HaarCarrierEqv blocks right right') :
    HaarCarrierEqv blocks
      (polyAdd left right) (polyAdd left' right') := by
  change QuaternionHaarCarrierEqv blocks
    (polyAdd left right) (polyAdd left' right')
  exact QuaternionHaarCarrierEqv.add hleft hright

theorem HaarCarrierEqv.smul
    {blocks : Nat} (scale : Q') {left right : RatPoly}
    (h : HaarCarrierEqv blocks left right) :
    HaarCarrierEqv blocks
      (polySmul scale left) (polySmul scale right) := by
  change QuaternionHaarCarrierEqv blocks
    (polySmul scale left) (polySmul scale right)
  exact QuaternionHaarCarrierEqv.smul scale h

private theorem RatPolyCoeffEqv.neg_eq_negOne_smul :
    ∀ polynomial : RatPoly,
    RatPolyCoeffEqv
      (polyNeg polynomial) (polySmul (-1) polynomial)
  | [] => RatPolyCoeffEqv.refl polyZero
  | term :: rest => by
      intro weight
      change
        (-term.2) * weight term.1 +
              ratWeightedSum weight (polyNeg rest) ≈
          ((-1) * term.2) * weight term.1 +
            ratWeightedSum weight (polySmul (-1) rest)
      have hcoefficient : (-term.2) ≈ (-1) * term.2 := by
        exact Q'.eqv_symm
          (Q'.eqv_trans _ (-(1 * term.2)) _
            (Q'.neg_mul_eqv 1 term.2)
            (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv term.2)))
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ hcoefficient)
        (RatPolyCoeffEqv.neg_eq_negOne_smul rest weight)

theorem HaarCarrierEqv.neg
    {blocks : Nat} {left right : RatPoly}
    (h : HaarCarrierEqv blocks left right) :
    HaarCarrierEqv blocks (polyNeg left) (polyNeg right) :=
  HaarCarrierEqv.trans
    (RatPolyCoeffEqv.haarCarrier
      (RatPolyCoeffEqv.neg_eq_negOne_smul left))
    (HaarCarrierEqv.trans
      (HaarCarrierEqv.smul (-1) h)
      (HaarCarrierEqv.symm
        (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.neg_eq_negOne_smul right))))

/-- Componentwise arbitrary-insertion Haar equivalence for polynomial
quaternions.  Unlike coefficient equality, this relation can erase unit
radius factors and still survives every later Hamilton multiplication. -/
structure PolyQuaternionHaarCarrierEqv
    (blocks : Nat) (left right : PolyQuaternion) : Prop where
  scalar : HaarCarrierEqv blocks left.scalar right.scalar
  iPart : HaarCarrierEqv blocks left.iPart right.iPart
  jPart : HaarCarrierEqv blocks left.jPart right.jPart
  kPart : HaarCarrierEqv blocks left.kPart right.kPart

theorem PolyQuaternionHaarCarrierEqv.of_coeff
    {blocks : Nat} {left right : PolyQuaternion}
    (h : PolyQuaternionCoeffEqv left right) :
    PolyQuaternionHaarCarrierEqv blocks left right :=
  ⟨RatPolyCoeffEqv.haarCarrier h.scalar,
    RatPolyCoeffEqv.haarCarrier h.iPart,
    RatPolyCoeffEqv.haarCarrier h.jPart,
    RatPolyCoeffEqv.haarCarrier h.kPart⟩

theorem PolyQuaternionHaarCarrierEqv.refl
    (blocks : Nat) (q : PolyQuaternion) :
    PolyQuaternionHaarCarrierEqv blocks q q :=
  ⟨HaarCarrierEqv.refl blocks q.scalar,
    HaarCarrierEqv.refl blocks q.iPart,
    HaarCarrierEqv.refl blocks q.jPart,
    HaarCarrierEqv.refl blocks q.kPart⟩

theorem PolyQuaternionHaarCarrierEqv.trans
    {blocks : Nat} {first middle last : PolyQuaternion}
    (hfirst : PolyQuaternionHaarCarrierEqv blocks first middle)
    (hlast : PolyQuaternionHaarCarrierEqv blocks middle last) :
    PolyQuaternionHaarCarrierEqv blocks first last :=
  ⟨HaarCarrierEqv.trans hfirst.scalar hlast.scalar,
    HaarCarrierEqv.trans hfirst.iPart hlast.iPart,
    HaarCarrierEqv.trans hfirst.jPart hlast.jPart,
    HaarCarrierEqv.trans hfirst.kPart hlast.kPart⟩

theorem PolyQuaternionHaarCarrierEqv.mul
    {blocks : Nat} {left left' right right' : PolyQuaternion}
    (hleft : PolyQuaternionHaarCarrierEqv blocks left left')
    (hright : PolyQuaternionHaarCarrierEqv blocks right right') :
    PolyQuaternionHaarCarrierEqv blocks
      (PolyQuaternion.mul left right)
      (PolyQuaternion.mul left' right') := by
  constructor
  · exact HaarCarrierEqv.add
      (HaarCarrierEqv.mul hleft.scalar hright.scalar)
      (HaarCarrierEqv.neg (HaarCarrierEqv.add
        (HaarCarrierEqv.mul hleft.iPart hright.iPart)
        (HaarCarrierEqv.add
          (HaarCarrierEqv.mul hleft.jPart hright.jPart)
          (HaarCarrierEqv.mul hleft.kPart hright.kPart))))
  · exact HaarCarrierEqv.add
      (HaarCarrierEqv.mul hleft.scalar hright.iPart)
      (HaarCarrierEqv.add
        (HaarCarrierEqv.mul hleft.iPart hright.scalar)
        (HaarCarrierEqv.add
          (HaarCarrierEqv.mul hleft.jPart hright.kPart)
          (HaarCarrierEqv.neg
            (HaarCarrierEqv.mul hleft.kPart hright.jPart))))
  · exact HaarCarrierEqv.add
      (HaarCarrierEqv.mul hleft.scalar hright.jPart)
      (HaarCarrierEqv.add
        (HaarCarrierEqv.mul hleft.jPart hright.scalar)
        (HaarCarrierEqv.add
          (HaarCarrierEqv.mul hleft.kPart hright.iPart)
          (HaarCarrierEqv.neg
            (HaarCarrierEqv.mul hleft.iPart hright.kPart))))
  · exact HaarCarrierEqv.add
      (HaarCarrierEqv.mul hleft.scalar hright.kPart)
      (HaarCarrierEqv.add
        (HaarCarrierEqv.mul hleft.kPart hright.scalar)
        (HaarCarrierEqv.add
          (HaarCarrierEqv.mul hleft.iPart hright.jPart)
          (HaarCarrierEqv.neg
            (HaarCarrierEqv.mul hleft.jPart hright.iPart))))

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

/-- A right-associated oriented word product, used only as the structural
normal form for reasoning about cyclic boundaries. -/
def orientedSurfaceWordProduct : List OrientedSurfaceEdge → PolyQuaternion
  | [] => PolyQuaternion.one
  | entry :: rest =>
      PolyQuaternion.mul
        (orientedCoordinateQuaternion entry.1 entry.2)
        (orientedSurfaceWordProduct rest)

private theorem orientedSurfaceWordFold_coeffEqv
    (initial : PolyQuaternion) : ∀ word : List OrientedSurfaceEdge,
    PolyQuaternionCoeffEqv
      (word.foldl
        (fun total entry => PolyQuaternion.mul total
          (orientedCoordinateQuaternion entry.1 entry.2)) initial)
      (PolyQuaternion.mul initial (orientedSurfaceWordProduct word))
  | [] => PolyQuaternionCoeffEqv.symm
      (PolyQuaternionCoeffEqv.mul_one initial)
  | entry :: rest => by
      exact PolyQuaternionCoeffEqv.trans
        (orientedSurfaceWordFold_coeffEqv
          (PolyQuaternion.mul initial
            (orientedCoordinateQuaternion entry.1 entry.2)) rest)
        (PolyQuaternionCoeffEqv.mul_assoc initial
          (orientedCoordinateQuaternion entry.1 entry.2)
          (orientedSurfaceWordProduct rest))

theorem compactOrientedQuaternionWord_coeffEqv_product
    (word : List OrientedSurfaceEdge) :
    PolyQuaternionCoeffEqv
      (compactOrientedQuaternionWord word)
      (orientedSurfaceWordProduct word) :=
  PolyQuaternionCoeffEqv.trans
    (orientedSurfaceWordFold_coeffEqv PolyQuaternion.one word)
    (PolyQuaternionCoeffEqv.one_mul (orientedSurfaceWordProduct word))

theorem orientedSurfaceWordProduct_append
    (left right : List OrientedSurfaceEdge) :
    PolyQuaternionCoeffEqv
      (orientedSurfaceWordProduct (left ++ right))
      (PolyQuaternion.mul
        (orientedSurfaceWordProduct left)
        (orientedSurfaceWordProduct right)) := by
  induction left with
  | nil =>
      exact PolyQuaternionCoeffEqv.symm
        (PolyQuaternionCoeffEqv.one_mul
          (orientedSurfaceWordProduct right))
  | cons entry rest induction =>
      exact PolyQuaternionCoeffEqv.trans
        (PolyQuaternionCoeffEqv.mul
          (PolyQuaternionCoeffEqv.refl
            (orientedCoordinateQuaternion entry.1 entry.2)) induction)
        (PolyQuaternionCoeffEqv.symm
          (PolyQuaternionCoeffEqv.mul_assoc
            (orientedCoordinateQuaternion entry.1 entry.2)
            (orientedSurfaceWordProduct rest)
            (orientedSurfaceWordProduct right)))

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

/-- An oriented edge followed by its inverse is the quaternion unit in the
componentwise Haar carrier, provided its block is integrated. -/
theorem PolyQuaternionHaarCarrierEqv.oriented_pair_one
    {blocks block : Nat} (hblock : block < blocks) (reverse : Bool) :
    PolyQuaternionHaarCarrierEqv blocks
      (PolyQuaternion.mul
        (orientedCoordinateQuaternion block reverse)
        (orientedCoordinateQuaternion block (!reverse)))
      PolyQuaternion.one :=
  PolyQuaternionHaarCarrierEqv.trans
    (PolyQuaternionHaarCarrierEqv.of_coeff
      (orientedCoordinateQuaternion_mul_opposite block reverse))
    ⟨quaternionRadiusPolynomial_carrier_one hblock,
      HaarCarrierEqv.refl blocks polyZero,
      HaarCarrierEqv.refl blocks polyZero,
      HaarCarrierEqv.refl blocks polyZero⟩

/-- Componentwise carrier equivalence of word holonomies survives appending
the same oriented suffix. -/
theorem compactOrientedQuaternionWord_append_congr
    {blocks : Nat} {left right : List (Nat × Bool)}
    (h : PolyQuaternionHaarCarrierEqv blocks
      (compactOrientedQuaternionWord left)
      (compactOrientedQuaternionWord right)) :
    ∀ suffix : List (Nat × Bool),
    PolyQuaternionHaarCarrierEqv blocks
      (compactOrientedQuaternionWord (left ++ suffix))
      (compactOrientedQuaternionWord (right ++ suffix))
  | [] => by simpa using h
  | entry :: rest => by
      have hentry := PolyQuaternionHaarCarrierEqv.mul h
        (PolyQuaternionHaarCarrierEqv.refl blocks
          (orientedCoordinateQuaternion entry.1 entry.2))
      have hprefix : PolyQuaternionHaarCarrierEqv blocks
          (compactOrientedQuaternionWord (left ++ [entry]))
          (compactOrientedQuaternionWord (right ++ [entry])) := by
        simpa [compactOrientedQuaternionWord, List.foldl_append] using hentry
      simpa [List.append_assoc] using
        (compactOrientedQuaternionWord_append_congr hprefix rest)

/-- One adjacent inverse pair at the end of a word can be erased in the
componentwise Haar carrier. -/
theorem compactOrientedQuaternionWord_append_inverse_pair
    {blocks : Nat} (word : List (Nat × Bool))
    (entry : Nat × Bool) (hblock : entry.1 < blocks) :
    PolyQuaternionHaarCarrierEqv blocks
      (compactOrientedQuaternionWord
        (word ++ [entry, (entry.1, !entry.2)]))
      (compactOrientedQuaternionWord word) := by
  let wordValue := compactOrientedQuaternionWord word
  let oriented := orientedCoordinateQuaternion entry.1 entry.2
  let inverse := orientedCoordinateQuaternion entry.1 (!entry.2)
  have hassoc : PolyQuaternionHaarCarrierEqv blocks
      (PolyQuaternion.mul (PolyQuaternion.mul wordValue oriented) inverse)
      (PolyQuaternion.mul wordValue (PolyQuaternion.mul oriented inverse)) :=
    PolyQuaternionHaarCarrierEqv.of_coeff
      (PolyQuaternionCoeffEqv.mul_assoc wordValue oriented inverse)
  have hcancel : PolyQuaternionHaarCarrierEqv blocks
      (PolyQuaternion.mul wordValue (PolyQuaternion.mul oriented inverse))
      (PolyQuaternion.mul wordValue PolyQuaternion.one) :=
    PolyQuaternionHaarCarrierEqv.mul
      (PolyQuaternionHaarCarrierEqv.refl blocks wordValue)
      (PolyQuaternionHaarCarrierEqv.oriented_pair_one hblock entry.2)
  have hone : PolyQuaternionHaarCarrierEqv blocks
      (PolyQuaternion.mul wordValue PolyQuaternion.one) wordValue :=
    PolyQuaternionHaarCarrierEqv.of_coeff
      (PolyQuaternionCoeffEqv.mul_one wordValue)
  simpa [wordValue, oriented, inverse, compactOrientedQuaternionWord,
    List.foldl_append] using
    (PolyQuaternionHaarCarrierEqv.trans hassoc
      (PolyQuaternionHaarCarrierEqv.trans hcancel hone))

private theorem bool_eq_not_of_ne {left right : Bool}
    (h : left ≠ right) : right = !left := by
  cases left <;> cases right <;> simp_all

private theorem mem_freeSurfaceReduceStep
    {stack : List OrientedSurfaceEdge} {entry item : OrientedSurfaceEdge}
    (hitem : item ∈ freeSurfaceReduceStep stack entry) :
    item = entry ∨ item ∈ stack := by
  cases stack with
  | nil => simpa [freeSurfaceReduceStep] using hitem
  | cons head rest =>
      by_cases hcancel : head.1 = entry.1 ∧ head.2 ≠ entry.2
      · right
        exact List.mem_cons_of_mem head
          (by simpa [freeSurfaceReduceStep, hcancel] using hitem)
      · simpa [freeSurfaceReduceStep, hcancel] using hitem

/-- One executable stack step preserves the word holonomy in the
componentwise Haar carrier. -/
theorem freeSurfaceReduceStep_carrier
    {blocks : Nat} (stack : List OrientedSurfaceEdge)
    (entry : OrientedSurfaceEdge)
    (hstack : ∀ item, item ∈ stack → item.1 < blocks) :
    PolyQuaternionHaarCarrierEqv blocks
      (compactOrientedQuaternionWord (stack.reverse ++ [entry]))
      (compactOrientedQuaternionWord
        (freeSurfaceReduceStep stack entry).reverse) := by
  cases stack with
  | nil =>
      exact PolyQuaternionHaarCarrierEqv.refl blocks _
  | cons head rest =>
      by_cases hcancel : head.1 = entry.1 ∧ head.2 ≠ entry.2
      · have hinverse : entry = (head.1, !head.2) := by
          apply Prod.ext
          · exact hcancel.1.symm
          · exact bool_eq_not_of_ne hcancel.2
        have hpair := compactOrientedQuaternionWord_append_inverse_pair
          (blocks := blocks) rest.reverse head
          (hstack head List.mem_cons_self)
        have hsource :
            (head :: rest).reverse ++ [entry] =
              rest.reverse ++ [head, (head.1, !head.2)] := by
          simp [hinverse, List.append_assoc]
        have htarget :
            (freeSurfaceReduceStep (head :: rest) entry).reverse =
              rest.reverse := by
          simp [freeSurfaceReduceStep, hcancel]
        rw [hsource, htarget]
        exact hpair
      · have hsame :
            (head :: rest).reverse ++ [entry] =
              (freeSurfaceReduceStep (head :: rest) entry).reverse := by
          simp [freeSurfaceReduceStep, hcancel, List.append_assoc]
        rw [hsame]
        exact PolyQuaternionHaarCarrierEqv.refl blocks _

/-- The fold-level invariant of the executable free reducer.  The source is
the unreduced stack word followed by the remaining input; the target is the
final reversed stack. -/
theorem freeSurfaceReduceFold_carrier
    {blocks : Nat} : ∀ (word stack : List OrientedSurfaceEdge),
    (∀ item, item ∈ stack → item.1 < blocks) →
    (∀ item, item ∈ word → item.1 < blocks) →
    PolyQuaternionHaarCarrierEqv blocks
      (compactOrientedQuaternionWord (stack.reverse ++ word))
      (compactOrientedQuaternionWord
        (word.foldl freeSurfaceReduceStep stack).reverse)
  | [], stack, _, _ => by
      simpa using PolyQuaternionHaarCarrierEqv.refl blocks
        (compactOrientedQuaternionWord stack.reverse)
  | entry :: rest, stack, hstack, hword => by
      let nextStack := freeSurfaceReduceStep stack entry
      have hentry : entry.1 < blocks :=
        hword entry List.mem_cons_self
      have hrest : ∀ item, item ∈ rest → item.1 < blocks := by
        intro item hitem
        exact hword item (List.mem_cons_of_mem entry hitem)
      have hnext : ∀ item, item ∈ nextStack → item.1 < blocks := by
        intro item hitem
        rcases mem_freeSurfaceReduceStep hitem with rfl | hold
        · exact hentry
        · exact hstack item hold
      have hstep := freeSurfaceReduceStep_carrier
        (blocks := blocks) stack entry hstack
      have hsuffix :=
        compactOrientedQuaternionWord_append_congr hstep rest
      have hrecursive := freeSurfaceReduceFold_carrier
        (blocks := blocks) rest nextStack hnext hrest
      exact PolyQuaternionHaarCarrierEqv.trans
        (by simpa [nextStack, List.append_assoc] using hsuffix)
        hrecursive

/-- Free reduction of any block-bounded oriented word preserves its complete
polynomial quaternion in the arbitrary-insertion Haar carrier. -/
theorem freeSurfaceReduce_carrier
    {blocks : Nat} (word : List OrientedSurfaceEdge)
    (hword : ∀ item, item ∈ word → item.1 < blocks) :
    PolyQuaternionHaarCarrierEqv blocks
      (compactOrientedQuaternionWord word)
      (compactOrientedQuaternionWord (freeSurfaceReduce word)) := by
  simpa [freeSurfaceReduce] using
    (freeSurfaceReduceFold_carrier
      (blocks := blocks) word []
      (fun _ hitem => by simp at hitem) hword)

/-- Consequently the spin-one face factor is unchanged by the executable
free reducer, with arbitrary surrounding face factors retained. -/
theorem compactFundamentalWordFactor_freeSurfaceReduce_carrier
    {blocks : Nat} (word : List OrientedSurfaceEdge)
    (hword : ∀ item, item ∈ word → item.1 < blocks) :
    HaarCarrierEqv blocks
      (compactFundamentalWordFactor word)
      (compactFundamentalWordFactor (freeSurfaceReduce word)) := by
  simpa [compactFundamentalWordFactor, characterPolynomial] using
    (HaarCarrierEqv.smul 2
      (freeSurfaceReduce_carrier
        (blocks := blocks) word hword).scalar)

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

/-- A scalar radius quaternion can be erased on the left of any quaternion
at the level of scalar Haar carriers.  Cyclic scalarity moves it to the right,
where the already-proved scalar multiplication formula exposes the radius
factor consumed by the sphere ideal. -/
theorem scalarRadiusQuaternion_mul_scalar_carrier
    {blocks block : Nat} (hblock : block < blocks)
    (q : PolyQuaternion) :
    HaarCarrierEqv blocks
      (PolyQuaternion.mul
        (scalarPolyQuaternion (quaternionRadiusPolynomial block)) q).scalar
      q.scalar :=
  HaarCarrierEqv.trans
    (RatPolyCoeffEqv.haarCarrier
      (polyQuaternion_mul_scalar_cyclic
        (scalarPolyQuaternion (quaternionRadiusPolynomial block)) q))
    (HaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier
        (PolyQuaternionCoeffEqv.mul_scalar_scalar q
          (quaternionRadiusPolynomial block)))
      (HaarCarrierEqv.trans
        (HaarCarrierEqv.mul_left q.scalar
          (quaternionRadiusPolynomial_carrier_one hblock))
        (RatPolyCoeffEqv.haarCarrier
          (RatPolyCoeffEqv.mul_one q.scalar))))

/-- Removing inverse-oriented first and last letters preserves the traced
fundamental face factor.  This is the structural soundness theorem for one
successful `cancelSurfaceCyclicBoundary` step. -/
theorem compactFundamentalWordFactor_cyclic_boundary_carrier
    {blocks : Nat} (first : OrientedSurfaceEdge)
    (middle : List OrientedSurfaceEdge) (hblock : first.1 < blocks) :
    HaarCarrierEqv blocks
      (compactFundamentalWordFactor
        (first :: (middle ++ [(first.1, !first.2)])))
      (compactFundamentalWordFactor middle) := by
  let firstValue := orientedCoordinateQuaternion first.1 first.2
  let lastValue := orientedCoordinateQuaternion first.1 (!first.2)
  let middleValue := orientedSurfaceWordProduct middle
  have hrest : PolyQuaternionCoeffEqv
      (orientedSurfaceWordProduct
        (middle ++ [(first.1, !first.2)]))
      (PolyQuaternion.mul middleValue lastValue) :=
    PolyQuaternionCoeffEqv.trans
      (orientedSurfaceWordProduct_append middle
        [(first.1, !first.2)])
      (PolyQuaternionCoeffEqv.mul
        (PolyQuaternionCoeffEqv.refl middleValue)
        (by simpa [lastValue, orientedSurfaceWordProduct] using
          (PolyQuaternionCoeffEqv.mul_one lastValue)))
  have hword : PolyQuaternionCoeffEqv
      (compactOrientedQuaternionWord
        (first :: (middle ++ [(first.1, !first.2)])))
      (PolyQuaternion.mul
        (PolyQuaternion.mul firstValue middleValue) lastValue) :=
    PolyQuaternionCoeffEqv.trans
      (compactOrientedQuaternionWord_coeffEqv_product _)
      (PolyQuaternionCoeffEqv.trans
        (PolyQuaternionCoeffEqv.mul
          (PolyQuaternionCoeffEqv.refl firstValue) hrest)
        (PolyQuaternionCoeffEqv.symm
          (PolyQuaternionCoeffEqv.mul_assoc
            firstValue middleValue lastValue)))
  have hrotate : RatPolyCoeffEqv
      (PolyQuaternion.mul
        (PolyQuaternion.mul firstValue middleValue) lastValue).scalar
      (PolyQuaternion.mul
        (PolyQuaternion.mul lastValue firstValue) middleValue).scalar :=
    RatPolyCoeffEqv.trans
      (polyQuaternion_mul_scalar_cyclic
        (PolyQuaternion.mul firstValue middleValue) lastValue)
      (PolyQuaternionCoeffEqv.symm
        (PolyQuaternionCoeffEqv.mul_assoc
          lastValue firstValue middleValue)).scalar
  have hpair : PolyQuaternionCoeffEqv
      (PolyQuaternion.mul lastValue firstValue)
      (scalarPolyQuaternion
        (quaternionRadiusPolynomial first.1)) := by
    simpa [firstValue, lastValue] using
      (orientedCoordinateQuaternion_mul_opposite first.1 (!first.2))
  have hpairMiddle : PolyQuaternionCoeffEqv
      (PolyQuaternion.mul
        (PolyQuaternion.mul lastValue firstValue) middleValue)
      (PolyQuaternion.mul
        (scalarPolyQuaternion (quaternionRadiusPolynomial first.1))
        middleValue) :=
    PolyQuaternionCoeffEqv.mul hpair
      (PolyQuaternionCoeffEqv.refl middleValue)
  have hscalar : HaarCarrierEqv blocks
      (compactOrientedQuaternionWord
        (first :: (middle ++ [(first.1, !first.2)]))).scalar
      middleValue.scalar :=
    HaarCarrierEqv.trans
      (RatPolyCoeffEqv.haarCarrier hword.scalar)
      (HaarCarrierEqv.trans
        (RatPolyCoeffEqv.haarCarrier hrotate)
        (HaarCarrierEqv.trans
          (RatPolyCoeffEqv.haarCarrier hpairMiddle.scalar)
          (scalarRadiusQuaternion_mul_scalar_carrier
            hblock middleValue)))
  have hmiddle : HaarCarrierEqv blocks middleValue.scalar
      (compactOrientedQuaternionWord middle).scalar :=
    HaarCarrierEqv.symm
      (RatPolyCoeffEqv.haarCarrier
        (compactOrientedQuaternionWord_coeffEqv_product middle).scalar)
  simpa [compactFundamentalWordFactor, characterPolynomial] using
    (HaarCarrierEqv.smul 2
      (HaarCarrierEqv.trans hscalar hmiddle))

private theorem cancelSurfaceCyclicBoundary_mem
    {word inner : List OrientedSurfaceEdge}
    (hcancel : cancelSurfaceCyclicBoundary word = some inner) :
    ∀ item, item ∈ inner → item ∈ word := by
  intro item hitem
  cases word with
  | nil => simp [cancelSurfaceCyclicBoundary] at hcancel
  | cons first rest =>
      cases rest with
      | nil =>
          simp [cancelSurfaceCyclicBoundary] at hcancel
      | cons second tail =>
          generalize hreverse : (second :: tail).reverse = reversed
          cases reversed with
          | nil => simp at hreverse
          | cons last reverseMiddle =>
              by_cases hends : first.1 = last.1 ∧ first.2 ≠ last.2
              · simp [cancelSurfaceCyclicBoundary, hreverse, hends] at hcancel
                have hinner : inner = reverseMiddle.reverse := hcancel.symm
                have hrest : second :: tail =
                    reverseMiddle.reverse ++ [last] := by
                  have := congrArg List.reverse hreverse
                  simpa using this
                rw [hinner] at hitem
                apply List.mem_cons_of_mem first
                rw [hrest]
                exact List.mem_append_left [last] hitem
              · simp [cancelSurfaceCyclicBoundary, hreverse, hends] at hcancel

/-- A successful executable cyclic-boundary cancellation preserves the
fundamental face factor in the arbitrary-insertion Haar carrier. -/
theorem cancelSurfaceCyclicBoundary_carrier
    {blocks : Nat} {word inner : List OrientedSurfaceEdge}
    (hcancel : cancelSurfaceCyclicBoundary word = some inner)
    (hword : ∀ item, item ∈ word → item.1 < blocks) :
    HaarCarrierEqv blocks
      (compactFundamentalWordFactor word)
      (compactFundamentalWordFactor inner) := by
  cases word with
  | nil => simp [cancelSurfaceCyclicBoundary] at hcancel
  | cons first rest =>
      cases rest with
      | nil =>
          simp [cancelSurfaceCyclicBoundary] at hcancel
      | cons second tail =>
          generalize hreverse : (second :: tail).reverse = reversed
          cases reversed with
          | nil => simp at hreverse
          | cons last reverseMiddle =>
              by_cases hends : first.1 = last.1 ∧ first.2 ≠ last.2
              · simp [cancelSurfaceCyclicBoundary, hreverse, hends] at hcancel
                have hinner : inner = reverseMiddle.reverse := hcancel.symm
                have hrest : second :: tail =
                    reverseMiddle.reverse ++ [last] := by
                  have := congrArg List.reverse hreverse
                  simpa using this
                have hlast : last = (first.1, !first.2) := by
                  apply Prod.ext
                  · exact hends.1.symm
                  · exact bool_eq_not_of_ne hends.2
                rw [hinner, hrest, hlast]
                exact compactFundamentalWordFactor_cyclic_boundary_carrier
                  first reverseMiddle.reverse
                  (hword first List.mem_cons_self)
              · simp [cancelSurfaceCyclicBoundary, hreverse, hends] at hcancel

private theorem freeSurfaceReduceFold_mem
    {word stack : List OrientedSurfaceEdge} {item : OrientedSurfaceEdge}
    (hitem : item ∈ word.foldl freeSurfaceReduceStep stack) :
    item ∈ stack ∨ item ∈ word := by
  induction word generalizing stack with
  | nil => exact Or.inl hitem
  | cons entry rest induction =>
      rcases induction hitem with hnext | hrest
      · rcases mem_freeSurfaceReduceStep hnext with rfl | hstack
        · exact Or.inr List.mem_cons_self
        · exact Or.inl hstack
      · exact Or.inr (List.mem_cons_of_mem entry hrest)

private theorem freeSurfaceReduce_mem
    {word : List OrientedSurfaceEdge} {item : OrientedSurfaceEdge}
    (hitem : item ∈ freeSurfaceReduce word) : item ∈ word := by
  have hfold : item ∈ word.foldl freeSurfaceReduceStep [] := by
    simpa [freeSurfaceReduce] using hitem
  rcases freeSurfaceReduceFold_mem hfold with hnil | hword
  · simp at hnil
  · exact hword

/-- Fuel-bounded cyclic reduction preserves the traced fundamental factor. -/
theorem cyclicFreeSurfaceReduceAux_carrier
    {blocks : Nat} : ∀ (fuel : Nat) (word : List OrientedSurfaceEdge),
    (∀ item, item ∈ word → item.1 < blocks) →
    HaarCarrierEqv blocks
      (compactFundamentalWordFactor word)
      (compactFundamentalWordFactor
        (cyclicFreeSurfaceReduceAux fuel word))
  | 0, word, _ => HaarCarrierEqv.refl blocks _
  | fuel + 1, word, hword => by
      cases hcancel : cancelSurfaceCyclicBoundary word with
      | none =>
          simpa [cyclicFreeSurfaceReduceAux, hcancel] using
            HaarCarrierEqv.refl blocks
              (compactFundamentalWordFactor word)
      | some inner =>
          have hinner : ∀ item, item ∈ inner → item.1 < blocks := by
            intro item hitem
            exact hword item
              (cancelSurfaceCyclicBoundary_mem hcancel item hitem)
          simpa [cyclicFreeSurfaceReduceAux, hcancel] using
            (HaarCarrierEqv.trans
              (cancelSurfaceCyclicBoundary_carrier hcancel hword)
              (cyclicFreeSurfaceReduceAux_carrier fuel inner hinner))

/-- Full free-plus-cyclic reduction preserves one fundamental face factor. -/
theorem compactFundamentalWordFactor_cyclicFreeSurfaceReduce_carrier
    {blocks : Nat} (word : List OrientedSurfaceEdge)
    (hword : ∀ item, item ∈ word → item.1 < blocks) :
    HaarCarrierEqv blocks
      (compactFundamentalWordFactor word)
      (compactFundamentalWordFactor (cyclicFreeSurfaceReduce word)) := by
  let reduced := freeSurfaceReduce word
  have hreduced : ∀ item, item ∈ reduced → item.1 < blocks := by
    intro item hitem
    exact hword item (freeSurfaceReduce_mem hitem)
  exact HaarCarrierEqv.trans
    (compactFundamentalWordFactor_freeSurfaceReduce_carrier word hword)
    (by simpa [cyclicFreeSurfaceReduce, reduced] using
      (cyclicFreeSurfaceReduceAux_carrier
        reduced.length reduced hreduced))

/-! ## Structural algebra of translated-head substitution -/

private theorem translatedHead_drop_monoMul :
    ∀ (count : Nat) (left right : List Nat),
      (monoMul left right).drop count =
        monoMul (left.drop count) (right.drop count)
  | 0, left, right => by simp
  | count + 1, [], right => by simp [monoMul]
  | count + 1, left, [] => by
      rw [monoMul_right_nil_local, List.drop_nil,
        monoMul_right_nil_local]
  | count + 1, _ :: left, _ :: right => by
      simp only [monoMul, List.drop_succ_cons]
      exact translatedHead_drop_monoMul count left right

private theorem fourZeroHead_monoMul (left right : List Nat) :
    monoMul ([0, 0, 0, 0] ++ left) ([0, 0, 0, 0] ++ right) =
      [0, 0, 0, 0] ++ monoMul left right := by
  rfl

private theorem headTailLiftTerm_mul
    (left right : RatTerm) :
    headTailLiftTerm
        (monoMul left.1 right.1, left.2 * right.2) =
      polyMul (headTailLiftTerm left) (headTailLiftTerm right) := by
  change
    [([0, 0, 0, 0] ++ (monoMul left.1 right.1).drop 4,
        left.2 * right.2)] =
      [
        (monoMul ([0, 0, 0, 0] ++ left.1.drop 4)
            ([0, 0, 0, 0] ++ right.1.drop 4),
          left.2 * right.2)]
  rw [translatedHead_drop_monoMul,
    fourZeroHead_monoMul]

private theorem ratPolyPow_eq_coeffPolyPow
    (polynomial : RatPoly) : ∀ exponent,
    ratPolyPow polynomial exponent = coeffPolyPow polynomial exponent
  | 0 => rfl
  | exponent + 1 => by
      change
        polyMul (ratPolyPow polynomial exponent) polynomial =
          polyMul (coeffPolyPow polynomial exponent) polynomial
      rw [ratPolyPow_eq_coeffPolyPow polynomial exponent]

private def eightPolynomialEnvironment
    (p0 p1 p2 p3 p4 p5 p6 p7 : RatPoly) : Nat → RatPoly
  | 0 => p0
  | 1 => p1
  | 2 => p2
  | 3 => p3
  | 4 => p4
  | 5 => p5
  | 6 => p6
  | 7 => p7
  | _ => polyZero

private def pairedEightProductExpr : PolyExpr :=
  .mul (.mul (.var 0) (.var 1))
    (.mul (.mul (.var 2) (.var 3))
      (.mul (.mul (.var 4) (.var 5))
        (.mul (.var 6) (.var 7))))

private def separatedEightProductExpr : PolyExpr :=
  .mul
    (.mul (.var 0)
      (.mul (.var 2) (.mul (.var 4) (.var 6))))
    (.mul (.var 1)
      (.mul (.var 3) (.mul (.var 5) (.var 7))))

private theorem pairedEightProductExpr_normal :
    normalize pairedEightProductExpr =
      normalize separatedEightProductExpr := by
  decide

private theorem pairedEightProduct_coeffEqv
    (p0 p1 p2 p3 p4 p5 p6 p7 : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul p0 p1)
        (polyMul (polyMul p2 p3)
          (polyMul (polyMul p4 p5) (polyMul p6 p7))))
      (polyMul
        (polyMul p0 (polyMul p2 (polyMul p4 p6)))
        (polyMul p1 (polyMul p3 (polyMul p5 p7)))) := by
  let environment :=
    eightPolynomialEnvironment p0 p1 p2 p3 p4 p5 p6 p7
  simpa [environment, eightPolynomialEnvironment,
    pairedEightProductExpr, separatedEightProductExpr,
    coeffEvalExpr] using
    (coeffEvalExpr_eqv_of_normalize_eq
      pairedEightProductExpr separatedEightProductExpr
      pairedEightProductExpr_normal environment)

theorem translatedHeadMonomial_add
    (translated : PolyQuaternion)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    RatPolyCoeffEqv
      (translatedHeadMonomial translated
        (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3))
      (polyMul
        (translatedHeadMonomial translated a0 a1 a2 a3)
        (translatedHeadMonomial translated b0 b1 b2 b3)) := by
  simp only [translatedHeadMonomial, ratPolyPow_eq_coeffPolyPow]
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul
      (coeffPolyPow_add translated.scalar a0 b0)
      (RatPolyCoeffEqv.mul
        (coeffPolyPow_add translated.iPart a1 b1)
        (RatPolyCoeffEqv.mul
          (coeffPolyPow_add translated.jPart a2 b2)
          (coeffPolyPow_add translated.kPart a3 b3))))
    (pairedEightProduct_coeffEqv
      (coeffPolyPow translated.scalar a0)
      (coeffPolyPow translated.scalar b0)
      (coeffPolyPow translated.iPart a1)
      (coeffPolyPow translated.iPart b1)
      (coeffPolyPow translated.jPart a2)
      (coeffPolyPow translated.jPart b2)
      (coeffPolyPow translated.kPart a3)
      (coeffPolyPow translated.kPart b3))

theorem translatedHeadTerm_mul
    (translated : PolyQuaternion) (left right : RatTerm) :
    RatPolyCoeffEqv
      (translatedHeadTerm translated
        (monoMul left.1 right.1, left.2 * right.2))
      (polyMul (translatedHeadTerm translated left)
        (translatedHeadTerm translated right)) := by
  simp only [translatedHeadTerm, exponentAt_monoMul]
  rw [headTailLiftTerm_mul]
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul
      (translatedHeadMonomial_add translated
        (exponentAt left.1 0) (exponentAt left.1 1)
        (exponentAt left.1 2) (exponentAt left.1 3)
        (exponentAt right.1 0) (exponentAt right.1 1)
        (exponentAt right.1 2) (exponentAt right.1 3))
      (RatPolyCoeffEqv.refl _))
    (RatPolyCoeffEqv.mul_four_swap
      (translatedHeadMonomial translated
        (exponentAt left.1 0) (exponentAt left.1 1)
        (exponentAt left.1 2) (exponentAt left.1 3))
      (translatedHeadMonomial translated
        (exponentAt right.1 0) (exponentAt right.1 1)
        (exponentAt right.1 2) (exponentAt right.1 3))
      (headTailLiftTerm left) (headTailLiftTerm right))

theorem translatedHeadPolynomial_add
    (translated : PolyQuaternion) : ∀ left right : RatPoly,
    translatedHeadPolynomial translated (polyAdd left right) =
      polyAdd (translatedHeadPolynomial translated left)
        (translatedHeadPolynomial translated right)
  | [], right => rfl
  | term :: rest, right => by
      rw [show polyAdd (term :: rest) right =
          term :: polyAdd rest right by rfl]
      rw [show translatedHeadPolynomial translated
          (term :: polyAdd rest right) =
          polyAdd (translatedHeadTerm translated term)
            (translatedHeadPolynomial translated (polyAdd rest right)) by
          rfl]
      rw [show translatedHeadPolynomial translated (term :: rest) =
          polyAdd (translatedHeadTerm translated term)
            (translatedHeadPolynomial translated rest) by rfl]
      rw [translatedHeadPolynomial_add translated rest right]
      change
        translatedHeadTerm translated term ++
              (translatedHeadPolynomial translated rest ++
                translatedHeadPolynomial translated right) =
          (translatedHeadTerm translated term ++
              translatedHeadPolynomial translated rest) ++
            translatedHeadPolynomial translated right
      exact (List.append_assoc
        (translatedHeadTerm translated term)
        (translatedHeadPolynomial translated rest)
        (translatedHeadPolynomial translated right)).symm

private theorem translatedHeadPolynomial_mul_single
    (translated : PolyQuaternion) (left : RatTerm) : ∀ right : RatPoly,
    RatPolyCoeffEqv
      (translatedHeadPolynomial translated (polyMul [left] right))
      (polyMul (translatedHeadTerm translated left)
        (translatedHeadPolynomial translated right))
  | [] => by
      change RatPolyCoeffEqv polyZero
        (polyMul (translatedHeadTerm translated left) polyZero)
      exact RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.mul_zero_right _)
  | right :: rest => by
      rw [polyMul_single_cons_right_exact,
        translatedHeadPolynomial_add]
      rw [show translatedHeadPolynomial translated
          (polyMul [left] [right]) =
          translatedHeadTerm translated
            (monoMul left.1 right.1, left.2 * right.2) by
          simp [polyMul, polyAdd, polyZero,
            translatedHeadPolynomial]]
      rw [show translatedHeadPolynomial translated (right :: rest) =
          polyAdd (translatedHeadTerm translated right)
            (translatedHeadPolynomial translated rest) by rfl]
      change RatPolyCoeffEqv
        (polyAdd
          (translatedHeadTerm translated
            (monoMul left.1 right.1, left.2 * right.2))
          (translatedHeadPolynomial translated (polyMul [left] rest)))
        (polyMul (translatedHeadTerm translated left)
          (polyAdd (translatedHeadTerm translated right)
            (translatedHeadPolynomial translated rest)))
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add
          (translatedHeadTerm_mul translated left right)
          (translatedHeadPolynomial_mul_single translated left rest))
        (RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.mul_add_right
            (translatedHeadTerm translated left)
            (translatedHeadTerm translated right)
            (translatedHeadPolynomial translated rest)))

/-- Translated-head substitution is multiplicative in the constructive
coefficient quotient.  The proof works termwise and never expands or
canonicalizes a complete surface polynomial. -/
theorem translatedHeadPolynomial_mul
    (translated : PolyQuaternion) : ∀ left right : RatPoly,
    RatPolyCoeffEqv
      (translatedHeadPolynomial translated (polyMul left right))
      (polyMul (translatedHeadPolynomial translated left)
        (translatedHeadPolynomial translated right))
  | [], right => RatPolyCoeffEqv.refl polyZero
  | term :: rest, right => by
      rw [polyMul_cons_left_exact,
        translatedHeadPolynomial_add]
      rw [show translatedHeadPolynomial translated (term :: rest) =
          polyAdd (translatedHeadTerm translated term)
            (translatedHeadPolynomial translated rest) by rfl]
      rw [polyMul_add_left_exact]
      exact RatPolyCoeffEqv.add
        (translatedHeadPolynomial_mul_single translated term right)
        (translatedHeadPolynomial_mul translated rest right)

private theorem translatedHeadTerm_smul
    (translated : PolyQuaternion) (scale : Q') (term : RatTerm) :
    RatPolyCoeffEqv
      (translatedHeadTerm translated (term.1, scale * term.2))
      (polySmul scale (translatedHeadTerm translated term)) := by
  change RatPolyCoeffEqv
    (polyMul
      (translatedHeadMonomial translated
        (exponentAt term.1 0) (exponentAt term.1 1)
        (exponentAt term.1 2) (exponentAt term.1 3))
      (polySmul scale (headTailLiftTerm term)))
    (polySmul scale
      (polyMul
        (translatedHeadMonomial translated
          (exponentAt term.1 0) (exponentAt term.1 1)
          (exponentAt term.1 2) (exponentAt term.1 3))
        (headTailLiftTerm term)))
  let monomial := translatedHeadMonomial translated
    (exponentAt term.1 0) (exponentAt term.1 1)
    (exponentAt term.1 2) (exponentAt term.1 3)
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_comm monomial
      (polySmul scale (headTailLiftTerm term)))
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.polyMul_smul_left scale
        (headTailLiftTerm term) monomial)
      (RatPolyCoeffEqv.smul scale
        (RatPolyCoeffEqv.mul_comm
          (headTailLiftTerm term) monomial)))

theorem translatedHeadPolynomial_smul
    (translated : PolyQuaternion) (scale : Q') : ∀ polynomial : RatPoly,
    RatPolyCoeffEqv
      (translatedHeadPolynomial translated (polySmul scale polynomial))
      (polySmul scale
        (translatedHeadPolynomial translated polynomial))
  | [] => RatPolyCoeffEqv.refl polyZero
  | term :: rest => by
      rw [show polySmul scale (term :: rest) =
          (term.1, scale * term.2) :: polySmul scale rest by rfl]
      rw [show translatedHeadPolynomial translated
          ((term.1, scale * term.2) :: polySmul scale rest) =
          polyAdd
            (translatedHeadTerm translated (term.1, scale * term.2))
            (translatedHeadPolynomial translated
              (polySmul scale rest)) by rfl]
      rw [show translatedHeadPolynomial translated (term :: rest) =
          polyAdd (translatedHeadTerm translated term)
            (translatedHeadPolynomial translated rest) by rfl]
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add
          (translatedHeadTerm_smul translated scale term)
          (translatedHeadPolynomial_smul translated scale rest))
        (RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.smul_add scale
            (translatedHeadTerm translated term)
            (translatedHeadPolynomial translated rest)))

private theorem RatPolyCoeffEqv.single_coefficient
    (monomial : List Nat) {left right : Q'}
    (hcoefficient : left ≈ right) :
    RatPolyCoeffEqv [(monomial, left)] [(monomial, right)] := by
  intro weight
  change left * weight monomial + 0 ≈
    right * weight monomial + 0
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hcoefficient)

private theorem translatedHeadTerm_coefficient_smul
    (translated : PolyQuaternion) (term : RatTerm) :
    RatPolyCoeffEqv
      (translatedHeadTerm translated term)
      (polySmul term.2
        (translatedHeadTerm translated (term.1, 1))) := by
  let monomial := translatedHeadMonomial translated
    (exponentAt term.1 0) (exponentAt term.1 1)
    (exponentAt term.1 2) (exponentAt term.1 3)
  have htail : RatPolyCoeffEqv
      (headTailLiftTerm term)
      (headTailLiftTerm (term.1, term.2 * 1)) := by
    apply RatPolyCoeffEqv.single_coefficient
    exact Q'.eqv_symm (Q'.mul_one_eqv term.2)
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul
      (RatPolyCoeffEqv.refl monomial) htail)
    (translatedHeadTerm_smul translated term.2 (term.1, 1))

private theorem ratWeightedSum_translatedHeadPolynomial
    (translated : PolyQuaternion) (weight : List Nat → Q') :
    ∀ polynomial : RatPoly,
    ratWeightedSum weight
        (translatedHeadPolynomial translated polynomial) ≈
      ratWeightedSum
        (fun monomial => ratWeightedSum weight
          (translatedHeadTerm translated (monomial, 1)))
        polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      let transformed : List Nat → Q' := fun monomial =>
        ratWeightedSum weight
          (translatedHeadTerm translated (monomial, 1))
      refine Q'.eqv_trans _
        (ratWeightedSum weight (translatedHeadTerm translated term) +
          ratWeightedSum weight
            (translatedHeadPolynomial translated rest)) _
        (ratWeightedSum_add weight
          (translatedHeadTerm translated term)
          (translatedHeadPolynomial translated rest)) ?_
      exact Q'.add_eqv_congr'
        (Q'.eqv_trans _
          (ratWeightedSum weight
            (polySmul term.2
              (translatedHeadTerm translated (term.1, 1)))) _
          ((translatedHeadTerm_coefficient_smul translated term) weight)
          (ratWeightedSum_smul weight term.2
            (translatedHeadTerm translated (term.1, 1))))
        (ratWeightedSum_translatedHeadPolynomial
          translated weight rest)

/-- Translated-head substitution descends to the constructive coefficient
quotient, so its algebra laws compose through a translation chain. -/
theorem translatedHeadPolynomial_coeffEqv
    (translated : PolyQuaternion) {left right : RatPoly}
    (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (translatedHeadPolynomial translated left)
      (translatedHeadPolynomial translated right) := by
  intro weight
  let transformed : List Nat → Q' := fun monomial =>
    ratWeightedSum weight
      (translatedHeadTerm translated (monomial, 1))
  exact Q'.eqv_trans _ (ratWeightedSum transformed left) _
    (ratWeightedSum_translatedHeadPolynomial translated weight left)
    (Q'.eqv_trans _ (ratWeightedSum transformed right) _
      (heqv transformed)
      (Q'.eqv_symm
        (ratWeightedSum_translatedHeadPolynomial
          translated weight right)))

open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

private theorem ratWeightedSum_reindexQuaternionPolynomial
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    (weight : List Nat → Q') : ∀ polynomial : RatPoly,
    ratWeightedSum weight
        (reindexQuaternionPolynomial permutation polynomial) ≈
      ratWeightedSum
        (fun monomial => weight
          (reindexQuaternionExponents permutation monomial))
        polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        term.2 * weight
              (reindexQuaternionExponents permutation term.1) +
            ratWeightedSum weight
              (reindexQuaternionPolynomial permutation rest) ≈
          term.2 * weight
              (reindexQuaternionExponents permutation term.1) +
            ratWeightedSum
              (fun monomial => weight
                (reindexQuaternionExponents permutation monomial)) rest
      exact Q'.add_eqv_congr_left _ _ _
        (ratWeightedSum_reindexQuaternionPolynomial
          permutation weight rest)

theorem RatPolyCoeffEqv.reindex
    {blocks : Nat} (permutation : QuaternionBlockInvolution blocks)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (reindexQuaternionPolynomial permutation left)
      (reindexQuaternionPolynomial permutation right) := by
  intro weight
  let transformed : List Nat → Q' := fun monomial =>
    weight (reindexQuaternionExponents permutation monomial)
  exact Q'.eqv_trans _ (ratWeightedSum transformed left) _
    (ratWeightedSum_reindexQuaternionPolynomial
      permutation weight left)
    (Q'.eqv_trans _ (ratWeightedSum transformed right) _
      (heqv transformed)
      (Q'.eqv_symm
        (ratWeightedSum_reindexQuaternionPolynomial
          permutation weight right)))

open YMGap.Continuum.SU2QuaternionSelectedHaarTranslation

private theorem exposeTranslationPairPolynomial_coeffEqv
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (exposeTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier left)
      (exposeTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier right) := by
  exact RatPolyCoeffEqv.reindex
    (translationPairTailPermutation blocks selected multiplier
      hblocks hselected hmultiplier)
    (RatPolyCoeffEqv.reindex
      (translationPairHeadPermutation blocks selected hselected) heqv)

private theorem restoreTranslationPairPolynomial_coeffEqv
    (blocks selected multiplier : Nat)
    (hblocks : 1 < blocks)
    (hselected : selected < blocks) (hmultiplier : multiplier < blocks)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (restoreTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier left)
      (restoreTranslationPairPolynomial blocks selected multiplier
        hblocks hselected hmultiplier right) := by
  exact RatPolyCoeffEqv.reindex
    (translationPairHeadPermutation blocks selected hselected)
    (RatPolyCoeffEqv.reindex
      (translationPairTailPermutation blocks selected multiplier
        hblocks hselected hmultiplier) heqv)

theorem selectedLeftTranslatedPolynomial_coeffEqv
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct left)
      (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct right) := by
  apply restoreTranslationPairPolynomial_coeffEqv
  apply translatedHeadPolynomial_coeffEqv
  exact exposeTranslationPairPolynomial_coeffEqv
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier heqv

theorem selectedRightTranslatedPolynomial_coeffEqv
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct left)
      (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct right) := by
  apply restoreTranslationPairPolynomial_coeffEqv
  apply translatedHeadPolynomial_coeffEqv
  exact exposeTranslationPairPolynomial_coeffEqv
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier heqv

theorem selectedLeftTranslatedPolynomial_mul
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (left right : RatPoly) :
    RatPolyCoeffEqv
      (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct (polyMul left right))
      (polyMul
        (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct left)
        (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct right)) := by
  have htranslated := translatedHeadPolynomial_mul
    leftTranslatedHeadQuaternion
    (exposeTranslationPairPolynomial (tailBlocks + 1)
      selected multiplier (by omega) hselected hmultiplier left)
    (exposeTranslationPairPolynomial (tailBlocks + 1)
      selected multiplier (by omega) hselected hmultiplier right)
  have hrestored := restoreTranslationPairPolynomial_coeffEqv
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier htranslated
  simpa [selectedLeftTranslatedPolynomial,
    exposeTranslationPairPolynomial,
    restoreTranslationPairPolynomial,
    reindexQuaternionPolynomial_mul] using hrestored

theorem selectedRightTranslatedPolynomial_mul
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (left right : RatPoly) :
    RatPolyCoeffEqv
      (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct (polyMul left right))
      (polyMul
        (selectedRightTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct left)
        (selectedRightTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct right)) := by
  have htranslated := translatedHeadPolynomial_mul
    rightTranslatedHeadQuaternion
    (exposeTranslationPairPolynomial (tailBlocks + 1)
      selected multiplier (by omega) hselected hmultiplier left)
    (exposeTranslationPairPolynomial (tailBlocks + 1)
      selected multiplier (by omega) hselected hmultiplier right)
  have hrestored := restoreTranslationPairPolynomial_coeffEqv
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier htranslated
  simpa [selectedRightTranslatedPolynomial,
    exposeTranslationPairPolynomial,
    restoreTranslationPairPolynomial,
    reindexQuaternionPolynomial_mul] using hrestored

/-! ### Coordinate-sign substitution in the coefficient quotient -/

private theorem decide_exponentParity_add_local
    (left right : Nat) :
    decide ((left + right) % 2 = 1) =
      xor (decide (left % 2 = 1))
        (decide (right % 2 = 1)) := by
  have hleft : left % 2 = 0 ∨ left % 2 = 1 := by omega
  have hright : right % 2 = 0 ∨ right % 2 = 1 := by omega
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright <;>
    rw [Nat.add_mod, hleft, hright] <;> decide

private theorem selectedExponentParity_monoMul_local
    (coordinates : Nat) (selected : Nat → Bool)
    (left right : List Nat) :
    selectedExponentParity coordinates selected (monoMul left right) =
      xor
        (selectedExponentParity coordinates selected left)
        (selectedExponentParity coordinates selected right) := by
  unfold selectedExponentParity
  have hfold : ∀ (entries : List Nat) (leftParity rightParity : Bool),
      entries.foldl
          (fun parity coordinate =>
            if selected coordinate then
              xor parity
                (decide
                  (exponentAt (monoMul left right) coordinate % 2 = 1))
            else parity)
          (xor leftParity rightParity) =
        xor
          (entries.foldl
            (fun parity coordinate =>
              if selected coordinate then
                xor parity
                  (decide (exponentAt left coordinate % 2 = 1))
              else parity)
            leftParity)
          (entries.foldl
            (fun parity coordinate =>
              if selected coordinate then
                xor parity
                  (decide (exponentAt right coordinate % 2 = 1))
              else parity)
            rightParity) := by
    intro entries leftParity rightParity
    induction entries generalizing leftParity rightParity with
    | nil => rfl
    | cons coordinate rest induction =>
        simp only [List.foldl_cons]
        by_cases hselected : selected coordinate = true
        · rw [if_pos hselected, if_pos hselected, if_pos hselected,
            YMGap.Continuum.SU2QuaternionRatPolyDifferential.exponentAt_monoMul,
            decide_exponentParity_add_local]
          have hxor : ∀ leftBit rightBit : Bool,
              xor (xor leftParity rightParity)
                  (xor leftBit rightBit) =
                xor (xor leftParity leftBit)
                  (xor rightParity rightBit) := by
            intro leftBit rightBit
            cases leftParity <;> cases rightParity <;>
              cases leftBit <;> cases rightBit <;> rfl
          rw [hxor]
          exact induction _ _
        · rw [if_neg hselected, if_neg hselected, if_neg hselected]
          exact induction _ _
  simpa only [Bool.false_xor] using
    hfold (List.range coordinates) false false

set_option linter.unusedSimpArgs false in
private theorem signSelectedTerm_mul_coeffEqv
    (coordinates : Nat) (selected : Nat → Bool)
    (left right : RatTerm) :
    RatPolyCoeffEqv
      [signSelectedTerm coordinates selected
        (monoMul left.1 right.1, left.2 * right.2)]
      [(monoMul
          (signSelectedTerm coordinates selected left).1
          (signSelectedTerm coordinates selected right).1,
        (signSelectedTerm coordinates selected left).2 *
          (signSelectedTerm coordinates selected right).2)] := by
  apply RatPolyCoeffEqv.single_coefficient
  unfold signSelectedTerm
  rw [selectedExponentParity_monoMul_local]
  generalize hleft :
    selectedExponentParity coordinates selected left.1 = leftParity
  generalize hright :
    selectedExponentParity coordinates selected right.1 = rightParity
  cases leftParity <;> cases rightParity
  · simp only [hleft, hright, Bool.false_xor, if_false, Prod.snd]
    exact Q'.eqv_refl _
  · simp only [hleft, hright, Bool.false_xor, if_false, if_true,
      Prod.snd]
    exact Q'.eqv_symm (Q'.mul_neg_eqv left.2 right.2)
  · simp only [hleft, hright, Bool.true_xor, Bool.not_false,
      if_false, if_true, Prod.snd]
    exact Q'.eqv_symm (Q'.neg_mul_eqv left.2 right.2)
  · simp only [hleft, hright, Bool.true_xor, Bool.not_true,
      if_false, if_true, Prod.snd]
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (-(left.2 * (-right.2))) _
        (Q'.neg_mul_eqv left.2 (-right.2))
        (Q'.eqv_trans _ (-(-(left.2 * right.2))) _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_neg_eqv left.2 right.2))
          (Q'.neg_neg_eqv (left.2 * right.2))))

private theorem signSelectedPolynomial_mulRow_coeffEqv
    (coordinates : Nat) (selected : Nat → Bool)
    (source : RatTerm) : ∀ right : RatPoly,
    RatPolyCoeffEqv
      (signSelectedPolynomial coordinates selected
        (right.map fun target =>
          (monoMul source.1 target.1, source.2 * target.2)))
      ((signSelectedPolynomial coordinates selected right).map
        fun target =>
          (monoMul
              (signSelectedTerm coordinates selected source).1
              target.1,
            (signSelectedTerm coordinates selected source).2 *
              target.2))
  | [] => RatPolyCoeffEqv.refl polyZero
  | target :: rest => by
      simpa [signSelectedPolynomial, polyAdd] using
        (RatPolyCoeffEqv.add
          (signSelectedTerm_mul_coeffEqv
            coordinates selected source target)
          (signSelectedPolynomial_mulRow_coeffEqv
            coordinates selected source rest))

theorem signSelectedPolynomial_mul_coeffEqv
    (coordinates : Nat) (selected : Nat → Bool) :
    ∀ left right : RatPoly,
    RatPolyCoeffEqv
      (signSelectedPolynomial coordinates selected
        (polyMul left right))
      (polyMul
        (signSelectedPolynomial coordinates selected left)
        (signSelectedPolynomial coordinates selected right))
  | [], right => RatPolyCoeffEqv.refl polyZero
  | source :: rest, right => by
      simpa only [polyMul, List.flatMap_cons,
        signSelectedPolynomial, List.map_append, List.map_cons] using
        (RatPolyCoeffEqv.add
          (signSelectedPolynomial_mulRow_coeffEqv
            coordinates selected source right)
          (signSelectedPolynomial_mul_coeffEqv
            coordinates selected rest right))

private theorem ratWeightedSum_signSelectedPolynomial
    (coordinates : Nat) (selected : Nat → Bool)
    (weight : List Nat → Q') : ∀ polynomial : RatPoly,
    ratWeightedSum weight
        (signSelectedPolynomial coordinates selected polynomial) ≈
      ratWeightedSum
        (fun monomial =>
          if selectedExponentParity coordinates selected monomial
          then -(weight monomial) else weight monomial)
        polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (if selectedExponentParity coordinates selected term.1
          then -term.2 else term.2) * weight term.1 +
            ratWeightedSum weight
              (signSelectedPolynomial coordinates selected rest) ≈
          term.2 *
              (if selectedExponentParity coordinates selected term.1
                then -(weight term.1) else weight term.1) +
            ratWeightedSum
              (fun monomial =>
                if selectedExponentParity coordinates selected monomial
                then -(weight monomial) else weight monomial) rest
      apply Q'.add_eqv_congr'
      · generalize hparity :
          selectedExponentParity coordinates selected term.1 = parity
        cases parity
        · exact Q'.eqv_refl _
        · exact Q'.eqv_trans _ (-(term.2 * weight term.1)) _
            (Q'.neg_mul_eqv term.2 (weight term.1))
            (Q'.eqv_symm (Q'.mul_neg_eqv term.2 (weight term.1)))
      · exact ratWeightedSum_signSelectedPolynomial
          coordinates selected weight rest

theorem signSelectedPolynomial_coeffEqv
    (coordinates : Nat) (selected : Nat → Bool)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (signSelectedPolynomial coordinates selected left)
      (signSelectedPolynomial coordinates selected right) := by
  intro weight
  let transformed : List Nat → Q' := fun monomial =>
    if selectedExponentParity coordinates selected monomial
    then -(weight monomial) else weight monomial
  exact Q'.eqv_trans _ (ratWeightedSum transformed left) _
    (ratWeightedSum_signSelectedPolynomial
      coordinates selected weight left)
    (Q'.eqv_trans _ (ratWeightedSum transformed right) _
      (heqv transformed)
      (Q'.eqv_symm
        (ratWeightedSum_signSelectedPolynomial
          coordinates selected weight right)))

theorem signSelectedPolynomial_smul_coeffEqv
    (coordinates : Nat) (selected : Nat → Bool)
    (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (signSelectedPolynomial coordinates selected
        (polySmul scale polynomial))
      (polySmul scale
        (signSelectedPolynomial coordinates selected polynomial)) := by
  intro weight
  let transformed : List Nat → Q' := fun monomial =>
    if selectedExponentParity coordinates selected monomial
    then -(weight monomial) else weight monomial
  exact Q'.eqv_trans _
    (ratWeightedSum transformed (polySmul scale polynomial)) _
    (ratWeightedSum_signSelectedPolynomial
      coordinates selected weight (polySmul scale polynomial))
    (Q'.eqv_trans _
      (scale * ratWeightedSum transformed polynomial) _
      (ratWeightedSum_smul transformed scale polynomial)
      (Q'.eqv_trans _
        (scale * ratWeightedSum weight
          (signSelectedPolynomial coordinates selected polynomial)) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm
            (ratWeightedSum_signSelectedPolynomial
              coordinates selected weight polynomial)))
        (Q'.eqv_symm
          (ratWeightedSum_smul weight scale
            (signSelectedPolynomial coordinates selected polynomial)))))

theorem conjugateQuaternionBlockPolynomial_coeffEqv
    (blocks block : Nat) {left right : RatPoly}
    (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (conjugateQuaternionBlockPolynomial blocks block left)
      (conjugateQuaternionBlockPolynomial blocks block right) := by
  simpa [conjugateQuaternionBlockPolynomial] using
    (signSelectedPolynomial_coeffEqv (4 * blocks)
      (quaternionConjugateCoordinateSelector block) heqv)

theorem conjugateQuaternionBlockPolynomial_mul
    (blocks block : Nat) (left right : RatPoly) :
    RatPolyCoeffEqv
      (conjugateQuaternionBlockPolynomial blocks block
        (polyMul left right))
      (polyMul
        (conjugateQuaternionBlockPolynomial blocks block left)
        (conjugateQuaternionBlockPolynomial blocks block right)) := by
  simpa [conjugateQuaternionBlockPolynomial] using
    (signSelectedPolynomial_mul_coeffEqv (4 * blocks)
      (quaternionConjugateCoordinateSelector block) left right)

theorem conjugateQuaternionBlockPolynomial_smul
    (blocks block : Nat) (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (conjugateQuaternionBlockPolynomial blocks block
        (polySmul scale polynomial))
      (polySmul scale
        (conjugateQuaternionBlockPolynomial blocks block polynomial)) := by
  simpa [conjugateQuaternionBlockPolynomial] using
    (signSelectedPolynomial_smul_coeffEqv (4 * blocks)
      (quaternionConjugateCoordinateSelector block) scale polynomial)

theorem selectedLeftInverseTranslatedPolynomial_coeffEqv
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (selectedLeftInverseTranslatedPolynomial tailBlocks
        selected multiplier hblocks hselected hmultiplier hdistinct left)
      (selectedLeftInverseTranslatedPolynomial tailBlocks
        selected multiplier hblocks hselected hmultiplier hdistinct right) := by
  apply conjugateQuaternionBlockPolynomial_coeffEqv
  apply selectedLeftTranslatedPolynomial_coeffEqv
  exact conjugateQuaternionBlockPolynomial_coeffEqv
    (tailBlocks + 1) multiplier heqv

theorem selectedRightInverseTranslatedPolynomial_coeffEqv
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (selectedRightInverseTranslatedPolynomial tailBlocks
        selected multiplier hblocks hselected hmultiplier hdistinct left)
      (selectedRightInverseTranslatedPolynomial tailBlocks
        selected multiplier hblocks hselected hmultiplier hdistinct right) := by
  apply conjugateQuaternionBlockPolynomial_coeffEqv
  apply selectedRightTranslatedPolynomial_coeffEqv
  exact conjugateQuaternionBlockPolynomial_coeffEqv
    (tailBlocks + 1) multiplier heqv

theorem selectedLeftInverseTranslatedPolynomial_mul
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (left right : RatPoly) :
    RatPolyCoeffEqv
      (selectedLeftInverseTranslatedPolynomial tailBlocks
        selected multiplier hblocks hselected hmultiplier hdistinct
        (polyMul left right))
      (polyMul
        (selectedLeftInverseTranslatedPolynomial tailBlocks
          selected multiplier hblocks hselected hmultiplier hdistinct left)
        (selectedLeftInverseTranslatedPolynomial tailBlocks
          selected multiplier hblocks hselected hmultiplier hdistinct
          right)) := by
  let conjugate := conjugateQuaternionBlockPolynomial
    (tailBlocks + 1) multiplier
  let translate := selectedLeftTranslatedPolynomial tailBlocks
    selected multiplier hblocks hselected hmultiplier hdistinct
  exact RatPolyCoeffEqv.trans
    (conjugateQuaternionBlockPolynomial_coeffEqv
      (tailBlocks + 1) multiplier
      (selectedLeftTranslatedPolynomial_coeffEqv
        tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct
        (conjugateQuaternionBlockPolynomial_mul
          (tailBlocks + 1) multiplier left right)))
    (RatPolyCoeffEqv.trans
      (conjugateQuaternionBlockPolynomial_coeffEqv
        (tailBlocks + 1) multiplier
        (selectedLeftTranslatedPolynomial_mul
          tailBlocks selected multiplier hblocks hselected hmultiplier
          hdistinct (conjugate left) (conjugate right)))
      (conjugateQuaternionBlockPolynomial_mul
        (tailBlocks + 1) multiplier
        (translate (conjugate left)) (translate (conjugate right))))

theorem selectedRightInverseTranslatedPolynomial_mul
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (left right : RatPoly) :
    RatPolyCoeffEqv
      (selectedRightInverseTranslatedPolynomial tailBlocks
        selected multiplier hblocks hselected hmultiplier hdistinct
        (polyMul left right))
      (polyMul
        (selectedRightInverseTranslatedPolynomial tailBlocks
          selected multiplier hblocks hselected hmultiplier hdistinct left)
        (selectedRightInverseTranslatedPolynomial tailBlocks
          selected multiplier hblocks hselected hmultiplier hdistinct
          right)) := by
  let conjugate := conjugateQuaternionBlockPolynomial
    (tailBlocks + 1) multiplier
  let translate := selectedRightTranslatedPolynomial tailBlocks
    selected multiplier hblocks hselected hmultiplier hdistinct
  exact RatPolyCoeffEqv.trans
    (conjugateQuaternionBlockPolynomial_coeffEqv
      (tailBlocks + 1) multiplier
      (selectedRightTranslatedPolynomial_coeffEqv
        tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct
        (conjugateQuaternionBlockPolynomial_mul
          (tailBlocks + 1) multiplier left right)))
    (RatPolyCoeffEqv.trans
      (conjugateQuaternionBlockPolynomial_coeffEqv
        (tailBlocks + 1) multiplier
        (selectedRightTranslatedPolynomial_mul
          tailBlocks selected multiplier hblocks hselected hmultiplier
          hdistinct (conjugate left) (conjugate right)))
      (conjugateQuaternionBlockPolynomial_mul
        (tailBlocks + 1) multiplier
        (translate (conjugate left)) (translate (conjugate right))))

theorem selectedLeftTranslatedPolynomial_smul
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct
        (polySmul scale polynomial))
      (polySmul scale
        (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct polynomial)) := by
  have htranslated := translatedHeadPolynomial_smul
    leftTranslatedHeadQuaternion scale
    (exposeTranslationPairPolynomial (tailBlocks + 1)
      selected multiplier (by omega) hselected hmultiplier polynomial)
  have hrestored := restoreTranslationPairPolynomial_coeffEqv
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier htranslated
  simpa [selectedLeftTranslatedPolynomial,
    exposeTranslationPairPolynomial,
    restoreTranslationPairPolynomial,
    reindexQuaternionPolynomial_smul] using hrestored

theorem selectedRightTranslatedPolynomial_smul
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct
        (polySmul scale polynomial))
      (polySmul scale
        (selectedRightTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct polynomial)) := by
  have htranslated := translatedHeadPolynomial_smul
    rightTranslatedHeadQuaternion scale
    (exposeTranslationPairPolynomial (tailBlocks + 1)
      selected multiplier (by omega) hselected hmultiplier polynomial)
  have hrestored := restoreTranslationPairPolynomial_coeffEqv
    (tailBlocks + 1) selected multiplier (by omega)
    hselected hmultiplier htranslated
  simpa [selectedRightTranslatedPolynomial,
    exposeTranslationPairPolynomial,
    restoreTranslationPairPolynomial,
    reindexQuaternionPolynomial_smul] using hrestored

theorem selectedLeftInverseTranslatedPolynomial_smul
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (selectedLeftInverseTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct
        (polySmul scale polynomial))
      (polySmul scale
        (selectedLeftInverseTranslatedPolynomial tailBlocks selected
          multiplier hblocks hselected hmultiplier hdistinct polynomial)) := by
  exact RatPolyCoeffEqv.trans
    (conjugateQuaternionBlockPolynomial_coeffEqv
      (tailBlocks + 1) multiplier
      (selectedLeftTranslatedPolynomial_coeffEqv
        tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct
        (conjugateQuaternionBlockPolynomial_smul
          (tailBlocks + 1) multiplier scale polynomial)))
    (RatPolyCoeffEqv.trans
      (conjugateQuaternionBlockPolynomial_coeffEqv
        (tailBlocks + 1) multiplier
        (selectedLeftTranslatedPolynomial_smul tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct scale
          (conjugateQuaternionBlockPolynomial
            (tailBlocks + 1) multiplier polynomial)))
      (conjugateQuaternionBlockPolynomial_smul
        (tailBlocks + 1) multiplier scale
        (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct
          (conjugateQuaternionBlockPolynomial
            (tailBlocks + 1) multiplier polynomial))))

theorem selectedRightInverseTranslatedPolynomial_smul
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (selectedRightInverseTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct
        (polySmul scale polynomial))
      (polySmul scale
        (selectedRightInverseTranslatedPolynomial tailBlocks selected
          multiplier hblocks hselected hmultiplier hdistinct polynomial)) := by
  exact RatPolyCoeffEqv.trans
    (conjugateQuaternionBlockPolynomial_coeffEqv
      (tailBlocks + 1) multiplier
      (selectedRightTranslatedPolynomial_coeffEqv
        tailBlocks selected multiplier hblocks hselected hmultiplier
        hdistinct
        (conjugateQuaternionBlockPolynomial_smul
          (tailBlocks + 1) multiplier scale polynomial)))
    (RatPolyCoeffEqv.trans
      (conjugateQuaternionBlockPolynomial_coeffEqv
        (tailBlocks + 1) multiplier
        (selectedRightTranslatedPolynomial_smul tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct scale
          (conjugateQuaternionBlockPolynomial
            (tailBlocks + 1) multiplier polynomial)))
      (conjugateQuaternionBlockPolynomial_smul
        (tailBlocks + 1) multiplier scale
        (selectedRightTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct
          (conjugateQuaternionBlockPolynomial
            (tailBlocks + 1) multiplier polynomial))))

theorem selectedLeftTranslatedPolynomial_add
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (left right : RatPoly) :
    selectedLeftTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct (polyAdd left right) =
      polyAdd
        (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct left)
        (selectedLeftTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct right) := by
  simp [selectedLeftTranslatedPolynomial,
    exposeTranslationPairPolynomial,
    restoreTranslationPairPolynomial,
    reindexQuaternionPolynomial_add,
    translatedHeadPolynomial_add]

theorem selectedRightTranslatedPolynomial_add
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (left right : RatPoly) :
    selectedRightTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct (polyAdd left right) =
      polyAdd
        (selectedRightTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct left)
        (selectedRightTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct right) := by
  simp [selectedRightTranslatedPolynomial,
    exposeTranslationPairPolynomial,
    restoreTranslationPairPolynomial,
    reindexQuaternionPolynomial_add,
    translatedHeadPolynomial_add]

theorem selectedLeftInverseTranslatedPolynomial_add
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (left right : RatPoly) :
    selectedLeftInverseTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct (polyAdd left right) =
      polyAdd
        (selectedLeftInverseTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct left)
        (selectedLeftInverseTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct right) := by
  simp [selectedLeftInverseTranslatedPolynomial,
    selectedLeftTranslatedPolynomial_add,
    signSelectedPolynomial_add,
    conjugateQuaternionBlockPolynomial]

theorem selectedRightInverseTranslatedPolynomial_add
    (tailBlocks selected multiplier : Nat)
    (hblocks : 0 < tailBlocks)
    (hselected : selected < tailBlocks + 1)
    (hmultiplier : multiplier < tailBlocks + 1)
    (hdistinct : selected ≠ multiplier)
    (left right : RatPoly) :
    selectedRightInverseTranslatedPolynomial tailBlocks selected multiplier
        hblocks hselected hmultiplier hdistinct (polyAdd left right) =
      polyAdd
        (selectedRightInverseTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct left)
        (selectedRightInverseTranslatedPolynomial tailBlocks selected multiplier
          hblocks hselected hmultiplier hdistinct right) := by
  simp [selectedRightInverseTranslatedPolynomial,
    selectedRightTranslatedPolynomial_add,
    signSelectedPolynomial_add,
    conjugateQuaternionBlockPolynomial]

open YMGap.Continuum.SU2QuaternionSelectedHaarTranslationChain

theorem applySelectedTranslationStep_coeffEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    {left right : RatPoly} (heqv : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (applySelectedTranslationStep hblocks step left)
      (applySelectedTranslationStep hblocks step right) := by
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedLeftTranslatedPolynomial_coeffEqv tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct heqv)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedLeftInverseTranslatedPolynomial_coeffEqv tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct heqv)
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedRightTranslatedPolynomial_coeffEqv tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct heqv)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedRightInverseTranslatedPolynomial_coeffEqv tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct heqv)

theorem applySelectedTranslationStep_mul
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (left right : RatPoly) :
    RatPolyCoeffEqv
      (applySelectedTranslationStep hblocks step (polyMul left right))
      (polyMul
        (applySelectedTranslationStep hblocks step left)
        (applySelectedTranslationStep hblocks step right)) := by
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedLeftTranslatedPolynomial_mul tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct left right)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedLeftInverseTranslatedPolynomial_mul tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct left right)
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedRightTranslatedPolynomial_mul tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct left right)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedRightInverseTranslatedPolynomial_mul tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct left right)

theorem applySelectedTranslationStep_smul
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (applySelectedTranslationStep hblocks step
        (polySmul scale polynomial))
      (polySmul scale
        (applySelectedTranslationStep hblocks step polynomial)) := by
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedLeftTranslatedPolynomial_smul tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct scale polynomial)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedLeftInverseTranslatedPolynomial_smul tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct scale polynomial)
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedRightTranslatedPolynomial_smul tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct scale polynomial)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedRightInverseTranslatedPolynomial_smul tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct scale polynomial)

theorem applySelectedTranslationStep_add
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks)
    (left right : RatPoly) :
    applySelectedTranslationStep hblocks step (polyAdd left right) =
      polyAdd
        (applySelectedTranslationStep hblocks step left)
        (applySelectedTranslationStep hblocks step right) := by
  cases hside : step.side with
  | left =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedLeftTranslatedPolynomial_add tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct left right)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedLeftInverseTranslatedPolynomial_add tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct left right)
  | right =>
      cases horientation : step.multiplierOrientation with
      | direct =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedRightTranslatedPolynomial_add tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct left right)
      | inverse =>
          simpa [applySelectedTranslationStep, hside, horientation] using
            (selectedRightInverseTranslatedPolynomial_add tailBlocks
              step.selected step.multiplier hblocks step.selected_lt
              step.multiplier_lt step.distinct left right)

theorem applySelectedTranslationSteps_coeffEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks))
      {left right : RatPoly},
      RatPolyCoeffEqv left right →
      RatPolyCoeffEqv
        (applySelectedTranslationSteps hblocks steps left)
        (applySelectedTranslationSteps hblocks steps right)
  | [], _, _, heqv => heqv
  | step :: rest, _, _, heqv =>
      applySelectedTranslationSteps_coeffEqv hblocks rest
        (applySelectedTranslationStep_coeffEqv hblocks step heqv)

theorem applySelectedTranslationSteps_mul
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks))
      (left right : RatPoly),
      RatPolyCoeffEqv
        (applySelectedTranslationSteps hblocks steps (polyMul left right))
        (polyMul
          (applySelectedTranslationSteps hblocks steps left)
          (applySelectedTranslationSteps hblocks steps right))
  | [], left, right => RatPolyCoeffEqv.refl (polyMul left right)
  | step :: rest, left, right =>
      RatPolyCoeffEqv.trans
        (applySelectedTranslationSteps_coeffEqv hblocks rest
          (applySelectedTranslationStep_mul hblocks step left right))
        (applySelectedTranslationSteps_mul hblocks rest
          (applySelectedTranslationStep hblocks step left)
          (applySelectedTranslationStep hblocks step right))

theorem applySelectedTranslationSteps_smul
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks))
      (scale : Q') (polynomial : RatPoly),
      RatPolyCoeffEqv
        (applySelectedTranslationSteps hblocks steps
          (polySmul scale polynomial))
        (polySmul scale
          (applySelectedTranslationSteps hblocks steps polynomial))
  | [], scale, polynomial =>
      RatPolyCoeffEqv.refl (polySmul scale polynomial)
  | step :: rest, scale, polynomial =>
      RatPolyCoeffEqv.trans
        (applySelectedTranslationSteps_coeffEqv hblocks rest
          (applySelectedTranslationStep_smul
            hblocks step scale polynomial))
        (applySelectedTranslationSteps_smul hblocks rest scale
          (applySelectedTranslationStep hblocks step polynomial))

theorem applySelectedTranslationSteps_neg
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks))
    (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (applySelectedTranslationSteps hblocks steps (polyNeg polynomial))
      (polyNeg
        (applySelectedTranslationSteps hblocks steps polynomial)) := by
  exact RatPolyCoeffEqv.trans
    (applySelectedTranslationSteps_coeffEqv hblocks steps
      (RatPolyCoeffEqv.neg_eq_negOne_smul polynomial))
    (RatPolyCoeffEqv.trans
      (applySelectedTranslationSteps_smul hblocks steps (-1) polynomial)
      (RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.neg_eq_negOne_smul
          (applySelectedTranslationSteps hblocks steps polynomial))))

theorem applySelectedTranslationSteps_add
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks) :
    ∀ (steps : List (SelectedTranslationStep tailBlocks))
      (left right : RatPoly),
      applySelectedTranslationSteps hblocks steps (polyAdd left right) =
        polyAdd
          (applySelectedTranslationSteps hblocks steps left)
          (applySelectedTranslationSteps hblocks steps right)
  | [], left, right => rfl
  | step :: rest, left, right => by
      simp only [applySelectedTranslationSteps]
      rw [applySelectedTranslationStep_add hblocks step left right]
      exact applySelectedTranslationSteps_add hblocks rest
        (applySelectedTranslationStep hblocks step left)
        (applySelectedTranslationStep hblocks step right)

def applySelectedTranslationStepsQuaternion
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks))
    (quaternion : PolyQuaternion) : PolyQuaternion where
  scalar := applySelectedTranslationSteps hblocks steps quaternion.scalar
  iPart := applySelectedTranslationSteps hblocks steps quaternion.iPart
  jPart := applySelectedTranslationSteps hblocks steps quaternion.jPart
  kPart := applySelectedTranslationSteps hblocks steps quaternion.kPart

theorem applySelectedTranslationStepsQuaternion_coeffEqv
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks))
    {left right : PolyQuaternion}
    (heqv : PolyQuaternionCoeffEqv left right) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion hblocks steps left)
      (applySelectedTranslationStepsQuaternion hblocks steps right) :=
  ⟨applySelectedTranslationSteps_coeffEqv hblocks steps heqv.scalar,
    applySelectedTranslationSteps_coeffEqv hblocks steps heqv.iPart,
    applySelectedTranslationSteps_coeffEqv hblocks steps heqv.jPart,
    applySelectedTranslationSteps_coeffEqv hblocks steps heqv.kPart⟩

theorem applySelectedTranslationStepsQuaternion_conj
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks))
    (quaternion : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion hblocks steps
        (PolyQuaternion.conj quaternion))
      (PolyQuaternion.conj
        (applySelectedTranslationStepsQuaternion hblocks steps
          quaternion)) :=
  ⟨RatPolyCoeffEqv.refl _,
    applySelectedTranslationSteps_neg hblocks steps quaternion.iPart,
    applySelectedTranslationSteps_neg hblocks steps quaternion.jPart,
    applySelectedTranslationSteps_neg hblocks steps quaternion.kPart⟩

private theorem applySelectedTranslationSteps_threeSum
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks))
    (first second third : RatPoly) :
    RatPolyCoeffEqv
      (applySelectedTranslationSteps hblocks steps
        (polyAdd first (polyAdd second third)))
      (polyAdd
        (applySelectedTranslationSteps hblocks steps first)
        (polyAdd
          (applySelectedTranslationSteps hblocks steps second)
          (applySelectedTranslationSteps hblocks steps third))) := by
  rw [applySelectedTranslationSteps_add,
    applySelectedTranslationSteps_add]
  exact RatPolyCoeffEqv.refl _

theorem applySelectedTranslationStepsQuaternion_mul
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks))
    (left right : PolyQuaternion) :
    PolyQuaternionCoeffEqv
      (applySelectedTranslationStepsQuaternion hblocks steps
        (PolyQuaternion.mul left right))
      (PolyQuaternion.mul
        (applySelectedTranslationStepsQuaternion hblocks steps left)
        (applySelectedTranslationStepsQuaternion hblocks steps right)) := by
  constructor
  · simp only [applySelectedTranslationStepsQuaternion,
      PolyQuaternion.mul]
    rw [applySelectedTranslationSteps_add]
    apply RatPolyCoeffEqv.add
    · exact applySelectedTranslationSteps_mul hblocks steps
        left.scalar right.scalar
    · exact RatPolyCoeffEqv.trans
        (applySelectedTranslationSteps_neg hblocks steps _)
        (RatPolyCoeffEqv.neg
          (RatPolyCoeffEqv.trans
            (applySelectedTranslationSteps_threeSum hblocks steps _ _ _)
            (RatPolyCoeffEqv.add
              (applySelectedTranslationSteps_mul hblocks steps
                left.iPart right.iPart)
              (RatPolyCoeffEqv.add
                (applySelectedTranslationSteps_mul hblocks steps
                  left.jPart right.jPart)
                (applySelectedTranslationSteps_mul hblocks steps
                  left.kPart right.kPart)))))
  · simp only [applySelectedTranslationStepsQuaternion,
      PolyQuaternion.mul]
    rw [applySelectedTranslationSteps_add]
    apply RatPolyCoeffEqv.add
    · exact applySelectedTranslationSteps_mul hblocks steps
        left.scalar right.iPart
    · exact RatPolyCoeffEqv.trans
        (applySelectedTranslationSteps_threeSum hblocks steps _ _ _)
        (RatPolyCoeffEqv.add
          (applySelectedTranslationSteps_mul hblocks steps
            left.iPart right.scalar)
          (RatPolyCoeffEqv.add
            (applySelectedTranslationSteps_mul hblocks steps
              left.jPart right.kPart)
            (RatPolyCoeffEqv.trans
              (applySelectedTranslationSteps_neg hblocks steps _)
              (RatPolyCoeffEqv.neg
                (applySelectedTranslationSteps_mul hblocks steps
                  left.kPart right.jPart)))))
  · simp only [applySelectedTranslationStepsQuaternion,
      PolyQuaternion.mul]
    rw [applySelectedTranslationSteps_add]
    apply RatPolyCoeffEqv.add
    · exact applySelectedTranslationSteps_mul hblocks steps
        left.scalar right.jPart
    · exact RatPolyCoeffEqv.trans
        (applySelectedTranslationSteps_threeSum hblocks steps _ _ _)
        (RatPolyCoeffEqv.add
          (applySelectedTranslationSteps_mul hblocks steps
            left.jPart right.scalar)
          (RatPolyCoeffEqv.add
            (applySelectedTranslationSteps_mul hblocks steps
              left.kPart right.iPart)
            (RatPolyCoeffEqv.trans
              (applySelectedTranslationSteps_neg hblocks steps _)
              (RatPolyCoeffEqv.neg
                (applySelectedTranslationSteps_mul hblocks steps
                  left.iPart right.kPart)))))
  · simp only [applySelectedTranslationStepsQuaternion,
      PolyQuaternion.mul]
    rw [applySelectedTranslationSteps_add]
    apply RatPolyCoeffEqv.add
    · exact applySelectedTranslationSteps_mul hblocks steps
        left.scalar right.kPart
    · exact RatPolyCoeffEqv.trans
        (applySelectedTranslationSteps_threeSum hblocks steps _ _ _)
        (RatPolyCoeffEqv.add
          (applySelectedTranslationSteps_mul hblocks steps
            left.kPart right.scalar)
          (RatPolyCoeffEqv.add
            (applySelectedTranslationSteps_mul hblocks steps
              left.iPart right.jPart)
            (RatPolyCoeffEqv.trans
              (applySelectedTranslationSteps_neg hblocks steps _)
              (RatPolyCoeffEqv.neg
                (applySelectedTranslationSteps_mul hblocks steps
                  left.jPart right.iPart)))))

/-! ## Canonical finite coordinate certificates -/

def polyQuaternionCanonicalCoeffCheck
    (left right : PolyQuaternion) : Bool :=
  decide (RatPolyTermwiseEqv (canonRat left.scalar) (canonRat right.scalar)) &&
    (decide (RatPolyTermwiseEqv
        (canonRat left.iPart) (canonRat right.iPart)) &&
      (decide (RatPolyTermwiseEqv
          (canonRat left.jPart) (canonRat right.jPart)) &&
        decide (RatPolyTermwiseEqv
          (canonRat left.kPart) (canonRat right.kPart))))

theorem polyQuaternionCanonicalCoeffCheck_sound
    {left right : PolyQuaternion}
    (hcheck : polyQuaternionCanonicalCoeffCheck left right = true) :
    PolyQuaternionCoeffEqv left right := by
  have hsplit :
      RatPolyTermwiseEqv (canonRat left.scalar) (canonRat right.scalar) ∧
      RatPolyTermwiseEqv (canonRat left.iPart) (canonRat right.iPart) ∧
      RatPolyTermwiseEqv (canonRat left.jPart) (canonRat right.jPart) ∧
      RatPolyTermwiseEqv (canonRat left.kPart) (canonRat right.kPart) := by
    simpa [polyQuaternionCanonicalCoeffCheck] using hcheck
  exact ⟨RatPolyCoeffEqv.of_canon_termwise hsplit.1,
    RatPolyCoeffEqv.of_canon_termwise hsplit.2.1,
    RatPolyCoeffEqv.of_canon_termwise hsplit.2.2.1,
    RatPolyCoeffEqv.of_canon_termwise hsplit.2.2.2⟩

def identityQuaternionBlockInvolution
    (blocks : Nat) : QuaternionBlockInvolution blocks where
  map := fun block => block
  map_lt := fun _ hblock => hblock
  involutive := fun _ _ => rfl

theorem identityReindexQuaternionPolynomial_prefix
    (blocks : Nat) : ∀ polynomial : RatPoly,
    QuaternionPrefixPolynomialEqv blocks
      (reindexQuaternionPolynomial
        (identityQuaternionBlockInvolution blocks) polynomial)
      polynomial
  | [] => .nil
  | term :: rest => by
      apply QuaternionPrefixPolynomialEqv.cons
      · constructor
        · exact Q'.eqv_refl term.2
        · intro coordinate hcoordinate
          rw [exponentAt_reindexQuaternionExponents
            (identityQuaternionBlockInvolution blocks)
            term.1 hcoordinate]
          change exponentAt term.1
              (4 * (coordinate / 4) + coordinate % 4) =
            exponentAt term.1 coordinate
          rw [show 4 * (coordinate / 4) + coordinate % 4 = coordinate by
            omega]
      · exact identityReindexQuaternionPolynomial_prefix blocks rest

theorem identityReindexPolyQuaternion_prefix
    (blocks : Nat) (quaternion : PolyQuaternion) :
    QuaternionPrefixPolyQuaternionEqv blocks
      (reindexPolyQuaternion
        (identityQuaternionBlockInvolution blocks) quaternion)
      quaternion :=
  ⟨identityReindexQuaternionPolynomial_prefix blocks quaternion.scalar,
    identityReindexQuaternionPolynomial_prefix blocks quaternion.iPart,
    identityReindexQuaternionPolynomial_prefix blocks quaternion.jPart,
    identityReindexQuaternionPolynomial_prefix blocks quaternion.kPart⟩

def paddedSubstitutedSurfaceGaugeEntryQuaternion
    (mask : Nat) (entry : OrientedSurfaceEdge) : PolyQuaternion :=
  reindexPolyQuaternion (identityQuaternionBlockInvolution 32)
    (compactOrientedQuaternionWord
      ((substituteSurfaceGaugeEntry mask entry).map fun substituted =>
        (surfaceActiveBlock substituted.1, substituted.2)))

def surfaceForestGaugeCoordinateSemanticCheck
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (edgeId : Nat) (reverse : Bool) : Bool :=
  polyQuaternionCanonicalCoeffCheck
    (applySelectedTranslationStepsQuaternion (by decide : 0 < 31)
      (surfaceForestGaugeTranslationSteps mask hmask)
      (orientedCoordinateQuaternion (surfaceActiveBlock edgeId) reverse))
    (paddedSubstitutedSurfaceGaugeEntryQuaternion mask (edgeId, reverse))

def selectedTranslationStepForwardWord
    {tailBlocks : Nat} (step : SelectedTranslationStep tailBlocks)
    (block : Nat) : List OrientedSurfaceEdge :=
  if block = step.selected then
    let multiplierReverse := match step.multiplierOrientation with
      | .direct => false
      | .inverse => true
    match step.side with
    | .left =>
        [(step.multiplier, multiplierReverse), (step.selected, false)]
    | .right =>
        [(step.selected, false), (step.multiplier, multiplierReverse)]
  else [(block, false)]

def selectedTranslationStepCoordinateCheck
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (step : SelectedTranslationStep tailBlocks) (block : Nat) : Bool :=
  polyQuaternionCanonicalCoeffCheck
    (applySelectedTranslationStepsQuaternion hblocks
      [step] (orientedCoordinateQuaternion block false))
    (reindexPolyQuaternion
      (identityQuaternionBlockInvolution (tailBlocks + 1))
      (compactOrientedQuaternionWord
        (selectedTranslationStepForwardWord step block)))

def surfaceForestGaugeStepCoordinateCheck
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) : Bool :=
  (surfaceForestGaugeTranslationSteps mask hmask).all fun step =>
    (List.range 32).all fun block =>
      selectedTranslationStepCoordinateCheck
        (by decide : 0 < 31) step block

def binarySurfaceForestGaugeCoordinateSemanticCheck : Bool :=
  binarySurfaceMasks.attach.all fun maskEntry =>
    (List.range 32).all fun edgeId =>
      [false, true].all fun reverse =>
        surfaceForestGaugeCoordinateSemanticCheck
          maskEntry.1 maskEntry.2 edgeId reverse

theorem applySelectedTranslationSteps_factorProduct
    {tailBlocks : Nat} (hblocks : 0 < tailBlocks)
    (steps : List (SelectedTranslationStep tailBlocks)) :
    ∀ factors : List RatPoly, factors ≠ [] →
    RatPolyCoeffEqv
      (applySelectedTranslationSteps hblocks steps
        (factorProduct factors))
      (factorProduct (factors.map fun factor =>
        applySelectedTranslationSteps hblocks steps factor))
  | [], hnonempty => False.elim (hnonempty rfl)
  | [factor], _ =>
      RatPolyCoeffEqv.trans
        (applySelectedTranslationSteps_coeffEqv hblocks steps
          (RatPolyCoeffEqv.mul_one factor))
        (RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.mul_one
            (applySelectedTranslationSteps hblocks steps factor)))
  | factor :: next :: rest, _ =>
      RatPolyCoeffEqv.trans
        (applySelectedTranslationSteps_mul hblocks steps factor
          (factorProduct (next :: rest)))
        (RatPolyCoeffEqv.mul
          (RatPolyCoeffEqv.refl _)
          (applySelectedTranslationSteps_factorProduct
            hblocks steps (next :: rest) (by simp)))

/-! ## Specialization to all certified surface faces -/

def binarySubstitutedSurfaceGaugeWordBlockBoundCheck : Bool :=
  binarySurfaceMasks.all fun mask =>
    (surfaceSelectedCompactFaceIds mask).all fun faceId =>
      (substituteSurfaceGaugeWord mask
        (hypercubeFaceWords.getD faceId [])).all fun entry =>
          decide (entry.1 < 32)

theorem binarySubstitutedSurfaceGaugeWordBlockBoundCheck_true :
    binarySubstitutedSurfaceGaugeWordBlockBoundCheck = true := by
  decide

theorem substitutedSurfaceGaugeWord_block_lt
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (faceId : Nat) (hface : faceId ∈ surfaceSelectedCompactFaceIds mask)
    (entry : OrientedSurfaceEdge)
    (hentry : entry ∈ substituteSurfaceGaugeWord mask
      (hypercubeFaceWords.getD faceId [])) : entry.1 < 32 := by
  have hmaskRow := List.all_eq_true.mp
    binarySubstitutedSurfaceGaugeWordBlockBoundCheck_true mask hmask
  have hfaceRow := List.all_eq_true.mp hmaskRow faceId hface
  exact of_decide_eq_true (List.all_eq_true.mp hfaceRow entry hentry)

/-- For every selected face of every certified surface, the fully substituted
word factor is Haar-carrier equivalent to the checked unrenumbered physical
chord factor. -/
theorem substitutedSurfaceGaugeFaceFactor_carrier
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (faceId : Nat) (hface : faceId ∈ surfaceSelectedCompactFaceIds mask) :
    HaarCarrierEqv 32
      (compactFundamentalWordFactor
        (substituteSurfaceGaugeWord mask
          (hypercubeFaceWords.getD faceId [])))
      (compactFundamentalWordFactor
        (surfaceForestGaugePhysicalWord mask
          (hypercubeFaceWords.getD faceId []))) := by
  have hsemantic := surfaceForestGaugeFaceWordSemanticCheck_of_mem
    mask hmask faceId hface
  have heq :
      cyclicFreeSurfaceReduce
          (substituteSurfaceGaugeWord mask
            (hypercubeFaceWords.getD faceId [])) =
        surfaceForestGaugePhysicalWord mask
          (hypercubeFaceWords.getD faceId []) := by
    simpa [surfaceForestGaugeFaceWordSemanticCheck] using hsemantic
  have hcarrier :=
    compactFundamentalWordFactor_cyclicFreeSurfaceReduce_carrier
      (blocks := 32)
      (substituteSurfaceGaugeWord mask
        (hypercubeFaceWords.getD faceId []))
      (substitutedSurfaceGaugeWord_block_lt mask hmask faceId hface)
  rw [heq] at hcarrier
  exact hcarrier

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.haarCarrier
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.HaarCarrierEqv.mul_right
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.factorProduct_carrier_of_listEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.PolyQuaternionCoeffEqv.mul
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.characterPolynomial_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.PolyQuaternionCoeffEqv.mul_assoc
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.orientedCoordinateQuaternion_mul_opposite
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.polyQuaternion_mul_scalar_cyclic
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.translatedHeadPolynomial_mul
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.translatedHeadPolynomial_smul
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.translatedHeadPolynomial_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.signSelectedPolynomial_mul_coeffEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.applySelectedTranslationSteps_factorProduct
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.applySelectedTranslationSteps_add
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.applySelectedTranslationStepsQuaternion_mul
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.polyQuaternionCanonicalCoeffCheck_sound
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.compactFundamentalWordFactor_cyclicFreeSurfaceReduce_carrier
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.substitutedSurfaceGaugeFaceFactor_carrier
