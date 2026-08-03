/-
# Constructive checker for quaternion-prefix polynomial equality

Block reindexing pads exponent vectors to the complete quaternion carrier.
This module turns the existing term-order-preserving prefix relation into a
small executable certificate.  It is intended for exact finite geometric
identifications, not for semantic polynomial normalization.
-/

import YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

namespace YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck

set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private def sparseExponentCodeAux : Nat → List Nat → List Nat
  | _, [] => []
  | coordinate, exponent :: rest =>
      if exponent = 0 then
        sparseExponentCodeAux (coordinate + 1) rest
      else
        coordinate :: exponent ::
          sparseExponentCodeAux (coordinate + 1) rest

/-- Delete zero coordinates while retaining every nonzero coordinate together
with its exponent. -/
def sparseExponentCode (monomial : List Nat) : List Nat :=
  sparseExponentCodeAux 0 monomial

private def sparseExponentAt : List Nat → Nat → Nat
  | coordinate :: exponent :: rest, target =>
      if coordinate = target then exponent
      else sparseExponentAt rest target
  | _, _ => 0

private theorem sparseExponentAt_codeAux :
    ∀ (monomial : List Nat) (offset target : Nat),
      sparseExponentAt
          (sparseExponentCodeAux offset monomial) target =
        if target < offset then 0
        else exponentAt monomial (target - offset)
  | [], offset, target => by
      simp [sparseExponentCodeAux, sparseExponentAt, exponentAt]
  | exponent :: rest, offset, target => by
      unfold sparseExponentCodeAux
      by_cases hexponent : exponent = 0
      · rw [if_pos hexponent,
          sparseExponentAt_codeAux rest (offset + 1) target]
        by_cases hlt : target < offset
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt]
          by_cases heq : target = offset
          · subst target
            rw [if_pos (by omega)]
            simp [exponentAt, hexponent]
          · rw [if_neg (by omega)]
            have hshift :
                target - offset =
                  (target - (offset + 1)) + 1 := by
              omega
            rw [hshift]
            simp [exponentAt]
      · rw [if_neg hexponent]
        unfold sparseExponentAt
        by_cases heq : offset = target
        · subst target
          rw [if_pos rfl, if_neg (by omega)]
          simp [exponentAt]
        · rw [if_neg heq,
            sparseExponentAt_codeAux rest (offset + 1) target]
          by_cases hlt : target < offset
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
            have hshift :
                target - offset =
                  (target - (offset + 1)) + 1 := by
              omega
            rw [hshift]
            simp [exponentAt]

theorem sparseExponentAt_code
    (monomial : List Nat) (target : Nat) :
    sparseExponentAt (sparseExponentCode monomial) target =
      exponentAt monomial target := by
  unfold sparseExponentCode
  rw [sparseExponentAt_codeAux]
  simp

/-- Executable equality test for one coefficient and the first `4*blocks`
exponents of a polynomial term. -/
def quaternionPrefixTermCheck
    (_blocks : Nat) (left right : RatTerm) : Bool :=
  decide (left.2 ≈ right.2) &&
    decide (sparseExponentCode left.1 = sparseExponentCode right.1)

theorem quaternionPrefixTermCheck_sound
    {blocks : Nat} {left right : RatTerm}
    (hcheck : quaternionPrefixTermCheck blocks left right = true) :
    QuaternionPrefixTermEqv blocks left right := by
  unfold quaternionPrefixTermCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  constructor
  · exact of_decide_eq_true hcheck.1
  · intro coordinate hcoordinate
    have hcode := of_decide_eq_true hcheck.2
    rw [← sparseExponentAt_code left.1 coordinate,
      hcode, sparseExponentAt_code]

/-- Term-order-preserving executable prefix check for two finite rational
polynomials. -/
def quaternionPrefixPolynomialCheck
    (blocks : Nat) : RatPoly → RatPoly → Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      quaternionPrefixTermCheck blocks left right &&
        quaternionPrefixPolynomialCheck blocks leftRest rightRest
  | _, _ => false

theorem quaternionPrefixPolynomialCheck_sound
    (blocks : Nat) : ∀ {left right : RatPoly},
    quaternionPrefixPolynomialCheck blocks left right = true →
      QuaternionPrefixPolynomialEqv blocks left right
  | [], [], _ => .nil
  | [], _ :: _, hcheck => by contradiction
  | _ :: _, [], hcheck => by contradiction
  | left :: leftRest, right :: rightRest, hcheck => by
      change
        (quaternionPrefixTermCheck blocks left right &&
          quaternionPrefixPolynomialCheck blocks leftRest rightRest) = true
        at hcheck
      rw [Bool.and_eq_true] at hcheck
      exact .cons
        (quaternionPrefixTermCheck_sound hcheck.1)
        (quaternionPrefixPolynomialCheck_sound blocks hcheck.2)

end YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck

#print axioms YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck.quaternionPrefixTermCheck_sound
#print axioms YMGap.Continuum.SU2QuaternionPrefixPolynomialCheck.quaternionPrefixPolynomialCheck_sound
