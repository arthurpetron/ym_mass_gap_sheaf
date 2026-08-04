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

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.haarCarrier
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.HaarCarrierEqv.mul_right
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.factorProduct_carrier_of_listEqv
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.PolyQuaternionCoeffEqv.mul
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.characterPolynomial_coeffEqv
