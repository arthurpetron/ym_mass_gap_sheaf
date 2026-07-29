/-
# All complement moments for the compact BF4 action

The normalized compact complement

  D = 133/4 - A

is positive in the completely-positive polynomial order established in
`BF4CompactActionCPOrder`.  This file turns that order statement into an
all-moment theorem without a degree or spin cutoff.

For order `n`, let `h = floor (n/2)` and form the literal carrier

  D^h D^h                  when n is even,
  (D^h D^h) D              when n is odd.

The even carrier is a Haar square.  The odd carrier is the same square
multiplied by `D`, so it is nonnegative by CP order.  A separate pointwise
evaluation theorem proves that the carrier really evaluates to `D^n`; it is
not merely a positivity surrogate.
-/

import YMGap.Continuum.BF4CompactActionCPOrder

namespace YMGap.Continuum.BF4CompactActionMomentPositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarPolynomialPositivity
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A multiplication-closed finite polynomial power carrier -/

/-- Literal right-recursive polynomial power.  It never canonicalizes or
truncates the carrier. -/
def polynomialPower (polynomial : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | exponent + 1 =>
      polyMul (polynomialPower polynomial exponent) polynomial

/-- The literal power evaluates to the corresponding rational power. -/
theorem eval_polynomialPower
    (rho : Nat → Q') (polynomial : RatPoly) :
    ∀ exponent : Nat,
      evalRatPoly rho (polynomialPower polynomial exponent) ≈
        qpow (evalRatPoly rho polynomial) exponent
  | 0 => evalRatPoly_one rho
  | exponent + 1 => by
      refine Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho
          (polynomialPower polynomial exponent)
          polynomial) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (eval_polynomialPower rho polynomial exponent)

/-- Powers preserve a declared quaternion-coordinate prefix. -/
theorem polynomialPower_supported
    {blocks : Nat} {polynomial : RatPoly}
    (hsupport :
      SupportedQuaternionBlocks blocks polynomial) :
    ∀ exponent : Nat,
      SupportedQuaternionBlocks blocks
        (polynomialPower polynomial exponent)
  | 0 => by
      intro term hterm
      simp [polynomialPower, polyOne] at hterm
      obtain rfl := hterm
      simp
  | exponent + 1 =>
      supported_polyMul
        (polynomialPower_supported hsupport exponent)
        hsupport

/-! ## 2. The exact parity carrier for every complement moment -/

/-- The normalized BF4 complement uses only the forty retained coordinates. -/
theorem compactActionComplementPolynomial_supported :
    SupportedQuaternionBlocks 10
      compactActionComplementPolynomial := by
  apply supported_of_bool 10
  decide

/-- The half-power used to expose an arbitrary moment as a square or a
square times the complement. -/
def compactActionComplementHalfPower
    (exponent : Nat) : RatPoly :=
  polynomialPower compactActionComplementPolynomial
    (exponent / 2)

/-- A literal polynomial representative of the `exponent`-th complement
power, arranged so positivity is manifest from parity. -/
def compactActionComplementMomentPolynomial
    (exponent : Nat) : RatPoly :=
  let half :=
    compactActionComplementHalfPower exponent
  if exponent % 2 = 0 then
    polyMul half half
  else
    polyMul (polyMul half half)
      compactActionComplementPolynomial

/-- Every parity-arranged moment remains in the exact forty-coordinate
carrier. -/
theorem compactActionComplementMomentPolynomial_supported
    (exponent : Nat) :
    SupportedQuaternionBlocks 10
      (compactActionComplementMomentPolynomial exponent) := by
  let half :=
    compactActionComplementHalfPower exponent
  have hhalf :
      SupportedQuaternionBlocks 10 half := by
    exact polynomialPower_supported
      compactActionComplementPolynomial_supported
      (exponent / 2)
  unfold compactActionComplementMomentPolynomial
  split
  · exact supported_polyMul hhalf hhalf
  · exact supported_polyMul
      (supported_polyMul hhalf hhalf)
      compactActionComplementPolynomial_supported

/-- Pointwise semantic identification: the parity-arranged carrier evaluates
to the genuine `exponent`-th power of the normalized complement. -/
theorem eval_compactActionComplementMomentPolynomial
    (rho : Nat → Q') (exponent : Nat) :
    evalRatPoly rho
        (compactActionComplementMomentPolynomial exponent) ≈
      qpow
        (evalRatPoly rho compactActionComplementPolynomial)
        exponent := by
  let base :=
    evalRatPoly rho compactActionComplementPolynomial
  let halfIndex := exponent / 2
  let halfPolynomial :=
    compactActionComplementHalfPower exponent
  have hhalf :
      evalRatPoly rho halfPolynomial ≈
        qpow base halfIndex := by
    exact eval_polynomialPower
      rho compactActionComplementPolynomial halfIndex
  unfold compactActionComplementMomentPolynomial
  by_cases heven : exponent % 2 = 0
  · rw [if_pos heven]
    have hexponent :
        halfIndex + halfIndex = exponent := by
      unfold halfIndex
      omega
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_mul rho halfPolynomial halfPolynomial) ?_
    refine Q'.eqv_trans _
      (qpow base halfIndex *
        evalRatPoly rho halfPolynomial) _
      (Q'.mul_eqv_congr_right _ _ _ hhalf) ?_
    refine Q'.eqv_trans _
      (qpow base halfIndex * qpow base halfIndex) _
      (Q'.mul_eqv_congr_left _ _ _ hhalf) ?_
    refine Q'.eqv_trans _
      (qpow base (halfIndex + halfIndex)) _
      (Q'.eqv_symm
        (qpow_add base halfIndex halfIndex)) ?_
    rw [hexponent]
    unfold base
    exact Q'.eqv_refl _
  · rw [if_neg heven]
    have hodd : exponent % 2 = 1 := by
      have hlt : exponent % 2 < 2 :=
        Nat.mod_lt exponent (by decide)
      omega
    have hexponent :
        halfIndex + halfIndex + 1 = exponent := by
      unfold halfIndex
      omega
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_mul rho
        (polyMul halfPolynomial halfPolynomial)
        compactActionComplementPolynomial) ?_
    refine Q'.eqv_trans _
      ((evalRatPoly rho halfPolynomial *
          evalRatPoly rho halfPolynomial) * base) _
      (Q'.mul_eqv_congr_right _ _ _
        (evalRatPoly_mul rho
          halfPolynomial halfPolynomial)) ?_
    refine Q'.eqv_trans _
      ((qpow base halfIndex *
          evalRatPoly rho halfPolynomial) * base) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hhalf)) ?_
    refine Q'.eqv_trans _
      ((qpow base halfIndex *
          qpow base halfIndex) * base) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hhalf)) ?_
    refine Q'.eqv_trans _
      (qpow base (halfIndex + halfIndex) * base) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (qpow_add base halfIndex halfIndex))) ?_
    have hstruct :
        qpow base (halfIndex + halfIndex) * base =
          qpow base (halfIndex + halfIndex + 1) := rfl
    rw [hstruct, hexponent]
    change qpow base exponent ≈ qpow base exponent
    exact Q'.eqv_refl _

/-! ## 3. All moment positivity -/

/-- **All normalized compact-complement moments are nonnegative.**

This is the all-label, all-degree result

  `0 <= H_10(D^n)`

with `D = 133/4 - A`, where the preceding evaluation theorem identifies the
literal parity carrier with the actual pointwise power. -/
theorem compactActionComplementMoment_nonnegative
    (exponent : Nat) :
    (0 : Q') ≤
      tenfoldHaar
        (compactActionComplementMomentPolynomial exponent) := by
  let half :=
    compactActionComplementHalfPower exponent
  have hhalf :
      SupportedQuaternionBlocks 10 half := by
    exact polynomialPower_supported
      compactActionComplementPolynomial_supported
      (exponent / 2)
  unfold compactActionComplementMomentPolynomial
  split
  · exact tenfoldHaar_square_nonnegative half hhalf
  · exact compactActionComplement_cp half hhalf

end YMGap.Continuum.BF4CompactActionMomentPositivity

#print axioms YMGap.Continuum.BF4CompactActionMomentPositivity.eval_polynomialPower
#print axioms YMGap.Continuum.BF4CompactActionMomentPositivity.polynomialPower_supported
#print axioms YMGap.Continuum.BF4CompactActionMomentPositivity.compactActionComplementPolynomial_supported
#print axioms YMGap.Continuum.BF4CompactActionMomentPositivity.compactActionComplementMomentPolynomial_supported
#print axioms YMGap.Continuum.BF4CompactActionMomentPositivity.eval_compactActionComplementMomentPolynomial
#print axioms YMGap.Continuum.BF4CompactActionMomentPositivity.compactActionComplementMoment_nonnegative
