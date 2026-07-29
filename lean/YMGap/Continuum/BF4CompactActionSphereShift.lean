/-
# Arbitrary-insertion sphere shift for the compact BF4 action

This file proves the exact normalized identity

  H_10(P D) + H_10(P A) = (133/4) H_10(P)

for every finite rational polynomial insertion `P`, where

  D = 133/4 - A

is the normalized complement from `BF4CompactActionCPOrder` and `A` is the
matching normalized action compiled from the same cleared BF4 expression.

The proof does not substitute unit-radius coordinates pointwise.  It descends
the sum of all ten quaternion radius polynomials through the exact product-Haar
sphere ideal, so the identity remains valid under an arbitrary insertion.
-/

import YMGap.Continuum.BF4CompactActionMomentPositivity

namespace YMGap.Continuum.BF4CompactActionSphereShift

set_option maxRecDepth 100000
set_option maxHeartbeats 24000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.BF4CompactActionDiagonalSOS
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Ten radius insertions collapse exactly -/

/-- Sum of the first `blocks` literal quaternion radius polynomials. -/
def quaternionRadiusPrefixSum : Nat → RatPoly
  | 0 => polyZero
  | blocks + 1 =>
      polyAdd (quaternionRadiusPrefixSum blocks)
        (quaternionRadiusPolynomial blocks)

/-- Under product Haar, every radius summand is one.  Therefore an arbitrary
polynomial insertion against the first `blocks` radii is exactly `blocks`
times its unshifted Haar value. -/
theorem quaternionHaar_mul_radiusPrefixSum_of_le
    (ambient : Nat) (polynomial : RatPoly) :
    ∀ count : Nat, count ≤ ambient →
      quaternionHaar ambient
          (polyMul polynomial
            (quaternionRadiusPrefixSum count)) ≈
        Q'.ofNat count *
          quaternionHaar ambient polynomial
  | 0, _ => by
      have hzero :
          polyMul polynomial polyZero = polyZero := by
        simp [polyMul, polyZero]
      rw [show quaternionRadiusPrefixSum 0 = polyZero by rfl,
        hzero]
      change (0 : Q') ≈
        Q'.ofNat 0 * quaternionHaar ambient polynomial
      exact Q'.eqv_symm
        (Q'.zero_mul_eqv
          (quaternionHaar ambient polynomial))
  | count + 1, hcount => by
      refine Q'.eqv_trans _
        (quaternionHaar ambient
              (polyMul polynomial
                (quaternionRadiusPrefixSum count)) +
          quaternionHaar ambient
              (polyMul polynomial
                (quaternionRadiusPolynomial count))) _
        (quaternionHaar_polyMul_add_right
          ambient polynomial
          (quaternionRadiusPrefixSum count)
          (quaternionRadiusPolynomial count)) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat count *
              quaternionHaar ambient polynomial +
          quaternionHaar ambient polynomial) _
        (QPoly.q_add_congr
          (quaternionHaar_mul_radiusPrefixSum_of_le
            ambient polynomial count (by omega))
          (quaternionHaar_mul_radius
            ambient count (by omega) polynomial)) ?_
      refine Q'.eqv_trans _
        (Q'.ofNat count *
              quaternionHaar ambient polynomial +
          1 * quaternionHaar ambient polynomial) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.eqv_refl _)
          (Q'.eqv_symm
            (Q'.one_mul_eqv
              (quaternionHaar ambient polynomial)))
      refine Q'.eqv_trans _
        ((Q'.ofNat count + 1) *
          quaternionHaar ambient polynomial) _
        (Q'.eqv_symm
          (Q'.add_mul_eqv
            (Q'.ofNat count) 1
            (quaternionHaar ambient polynomial))) ?_
      have hcast :
          Q'.ofNat (count + 1) ≈
            Q'.ofNat count + 1 := by
        exact Q'.eqv_trans _ _ _
          (Q'.ofNat_add_eqv count 1)
          (Q'.add_eqv_congr_left
            (Q'.ofNat count)
            (Q'.ofNat 1) 1 (by decide))
      exact Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm hcast)

theorem quaternionHaar_mul_radiusPrefixSum
    (blocks : Nat) (polynomial : RatPoly) :
    quaternionHaar blocks
        (polyMul polynomial
          (quaternionRadiusPrefixSum blocks)) ≈
      Q'.ofNat blocks *
        quaternionHaar blocks polynomial :=
  quaternionHaar_mul_radiusPrefixSum_of_le
    blocks polynomial blocks (Nat.le_refl blocks)

/-! ## 2. Cleared and normalized shift identities -/

/-- The expression in which the cleared complement is added back to the
cleared compact action. -/
def clearedComplementPlusActionExpr : PolyExpr :=
  .add clearedSphereComplementExpr
    clearedCompactActionExpr

/-- The same cleared expression after cancellation: `1596` times the sum of
the ten quaternion radii. -/
def clearedRadiusCeilingExpr : PolyExpr :=
  .mul (.const 1596) tenRadiusSumExpr

/-- Reflective cancellation of the action against its complement. -/
theorem clearedComplementPlusAction_normal :
    normalize clearedComplementPlusActionExpr =
      normalize clearedRadiusCeilingExpr := by
  decide

/-- The reflective forty-coordinate radius sum is the literal ten-block
radius prefix. -/
theorem tenRadiusSumPolynomial_eq :
    exprToRatPoly tenRadiusSumExpr =
      polyAdd (quaternionRadiusPrefixSum 10)
        (exprToRatPoly (.const 0)) := by
  decide

/-- The cleared radius ceiling compiles to a scalar multiple of the literal
ten-radius prefix. -/
theorem clearedRadiusCeilingPolynomial_eq :
    exprToRatPoly clearedRadiusCeilingExpr =
      polyAdd
        (polySmul (Q'.ofInt 1596)
          (quaternionRadiusPrefixSum 10))
        (exprToRatPoly (.const 0)) := by
  decide

private theorem quaternionHaar_polyMul_compiledZero_right
    (blocks : Nat) :
    ∀ polynomial : RatPoly,
      quaternionHaar blocks
          (polyMul polynomial
            (exprToRatPoly (.const 0))) ≈
        0
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (term.2 * 0) *
              quaternionHaarMono blocks
                (monoMul term.1 []) +
            quaternionHaar blocks
              (polyMul rest
                (exprToRatPoly (.const 0))) ≈
          0
      refine Q'.eqv_trans _
        (0 + 0) _ ?_ ?_
      · exact QPoly.q_add_congr
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_zero_eqv term.2))
            (Q'.zero_mul_eqv _))
          (quaternionHaar_polyMul_compiledZero_right
            blocks rest)
      · exact QPoly.q_zero_add_eqv 0

/-! ## 3. Coefficientwise transport between rational polynomial compilers -/

/-- Two literal polynomial lists have the same monomials in the same order
and equivalent rational coefficients.  Unlike semantic polynomial equality,
this relation is constructive and directly consumable by the exact Haar
functional. -/
def RatPolyTermwiseEqv : RatPoly → RatPoly → Prop
  | [], [] => True
  | left :: leftRest, right :: rightRest =>
      left.1 = right.1 ∧ left.2 ≈ right.2 ∧
        RatPolyTermwiseEqv leftRest rightRest
  | _, _ => False

instance ratPolyTermwiseEqvDecidable :
    ∀ left right : RatPoly,
      Decidable (RatPolyTermwiseEqv left right)
  | [], [] => isTrue True.intro
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | left :: leftRest, right :: rightRest =>
      match decEq left.1 right.1,
          (inferInstance :
            Decidable (left.2 ≈ right.2)),
          ratPolyTermwiseEqvDecidable leftRest rightRest with
      | isTrue hmono, isTrue hcoefficient, isTrue hrest =>
          isTrue ⟨hmono, hcoefficient, hrest⟩
      | isFalse hmono, _, _ =>
          isFalse (fun h => hmono h.1)
      | _, isFalse hcoefficient, _ =>
          isFalse (fun h => hcoefficient h.2.1)
      | _, _, isFalse hrest =>
          isFalse (fun h => hrest h.2.2)

theorem RatPolyTermwiseEqv.refl :
    ∀ polynomial : RatPoly,
      RatPolyTermwiseEqv polynomial polynomial
  | [] => True.intro
  | _ :: rest =>
      ⟨rfl, Q'.eqv_refl _, RatPolyTermwiseEqv.refl rest⟩

theorem RatPolyTermwiseEqv.append
    {left left' right right' : RatPoly}
    (hleft : RatPolyTermwiseEqv left left')
    (hright : RatPolyTermwiseEqv right right') :
    RatPolyTermwiseEqv
      (polyAdd left right) (polyAdd left' right') := by
  induction left generalizing left' with
  | nil =>
      cases left' with
      | nil => exact hright
      | cons _ _ => exact False.elim hleft
  | cons term rest induction =>
      cases left' with
      | nil => exact False.elim hleft
      | cons term' rest' =>
          exact
            ⟨hleft.1, hleft.2.1,
             induction hleft.2.2⟩

private theorem RatPolyTermwiseEqv.mulRow
    (source : RatTerm) {left right : RatPoly}
    (h : RatPolyTermwiseEqv left right) :
    RatPolyTermwiseEqv
      (left.map fun target =>
        (monoMul source.1 target.1,
          source.2 * target.2))
      (right.map fun target =>
        (monoMul source.1 target.1,
          source.2 * target.2)) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact True.intro
      | cons _ _ => exact False.elim h
  | cons target rest induction =>
      cases right with
      | nil => exact False.elim h
      | cons target' rest' =>
          have hmono :
              monoMul source.1 target.1 =
                monoMul source.1 target'.1 := by
            rw [h.1]
          exact
            ⟨hmono,
             Q'.mul_eqv_congr_left
               source.2 target.2 target'.2 h.2.1,
             induction h.2.2⟩

theorem RatPolyTermwiseEqv.polyMul_left
    (multiplier : RatPoly) {left right : RatPoly}
    (h : RatPolyTermwiseEqv left right) :
    RatPolyTermwiseEqv
      (polyMul multiplier left)
      (polyMul multiplier right) := by
  induction multiplier with
  | nil => exact True.intro
  | cons source rest induction =>
      exact RatPolyTermwiseEqv.append
        (RatPolyTermwiseEqv.mulRow source h)
        induction

/-- Exact Haar integration respects coefficientwise rational equivalence. -/
theorem quaternionHaar_termwise_eqv
    (blocks : Nat) :
    ∀ {left right : RatPoly},
      RatPolyTermwiseEqv left right →
        quaternionHaar blocks left ≈
          quaternionHaar blocks right
  | [], [], _ => Q'.eqv_refl 0
  | left :: leftRest, right :: rightRest, h => by
      have hmono : left.1 = right.1 := h.1
      change
        left.2 * quaternionHaarMono blocks left.1 +
              quaternionHaar blocks leftRest ≈
          right.2 * quaternionHaarMono blocks right.1 +
              quaternionHaar blocks rightRest
      rw [hmono]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right
          left.2 right.2
          (quaternionHaarMono blocks right.1)
          h.2.1)
        (quaternionHaar_termwise_eqv
          blocks h.2.2)

/-- Coefficientwise equivalent right factors remain equivalent after an
arbitrary left insertion and exact product-Haar integration. -/
theorem quaternionHaar_polyMul_termwise_eqv
    (blocks : Nat) (multiplier : RatPoly)
    {left right : RatPoly}
    (h : RatPolyTermwiseEqv left right) :
    quaternionHaar blocks
        (polyMul multiplier left) ≈
      quaternionHaar blocks
        (polyMul multiplier right) :=
  quaternionHaar_termwise_eqv blocks
    (RatPolyTermwiseEqv.polyMul_left multiplier h)

/-- Cleared arbitrary-insertion identity:

`H(P * clearedD) + H(P * clearedA) = 1596 * 10 * H(P)`. -/
theorem clearedCompactAction_sphere_shift
    (polynomial : RatPoly) :
    tenfoldHaar
          (polyMul polynomial
            (exprToRatPoly
              clearedSphereComplementExpr)) +
        tenfoldHaar
          (polyMul polynomial
            (exprToRatPoly
              clearedCompactActionExpr)) ≈
      (Q'.ofInt 1596 * Q'.ofNat 10) *
        tenfoldHaar polynomial := by
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul polynomial
        (exprToRatPoly
          clearedComplementPlusActionExpr))) _ ?_ ?_
  · exact Q'.eqv_symm
      (quaternionHaar_polyMul_add_right
        10 polynomial
        (exprToRatPoly
          clearedSphereComplementExpr)
        (exprToRatPoly
          clearedCompactActionExpr))
  · refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul polynomial
          (exprToRatPoly
            clearedRadiusCeilingExpr))) _
      (quaternionHaar_mul_expr_congr_of_normal_eq
        10 clearedComplementPlusActionExpr
        clearedRadiusCeilingExpr
        clearedComplementPlusAction_normal
        polynomial) ?_
    rw [clearedRadiusCeilingPolynomial_eq]
    refine Q'.eqv_trans _
      (tenfoldHaar
            (polyMul polynomial
              (polySmul (Q'.ofInt 1596)
                (quaternionRadiusPrefixSum 10))) +
        tenfoldHaar
            (polyMul polynomial
              (exprToRatPoly (.const 0)))) _
      (quaternionHaar_polyMul_add_right
        10 polynomial
        (polySmul (Q'.ofInt 1596)
          (quaternionRadiusPrefixSum 10))
        (exprToRatPoly (.const 0))) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
          (polyMul polynomial
            (polySmul (Q'.ofInt 1596)
              (quaternionRadiusPrefixSum 10))) +
        0) _
      (QPoly.q_add_congr
          (Q'.eqv_refl _)
          (quaternionHaar_polyMul_compiledZero_right
            10 polynomial)) ?_
    refine Q'.eqv_trans _
      (tenfoldHaar
        (polyMul polynomial
          (polySmul (Q'.ofInt 1596)
            (quaternionRadiusPrefixSum 10)))) _
      (QPoly.q_add_zero_eqv _) ?_
    refine Q'.eqv_trans _
      (Q'.ofInt 1596 *
        tenfoldHaar
          (polyMul polynomial
            (quaternionRadiusPrefixSum 10))) _
      (quaternionHaar_polyMul_smul_right
        10 (Q'.ofInt 1596) polynomial
        (quaternionRadiusPrefixSum 10)) ?_
    refine Q'.eqv_trans _
      (Q'.ofInt 1596 *
        (Q'.ofNat 10 *
          tenfoldHaar polynomial)) _
      (Q'.mul_eqv_congr_left _ _ _
        (quaternionHaar_mul_radiusPrefixSum
          10 polynomial)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (Q'.ofInt 1596) (Q'.ofNat 10)
        (tenfoldHaar polynomial))

/-- The normalized action companion compiled from the exact same cleared
quadratic expression as the complement. -/
def compactActionPolynomialFromCleared : RatPoly :=
  polySmul oneOver480
    (exprToRatPoly clearedCompactActionExpr)

/-- The original coupled `(K,S)` polynomial with the compiler's terminal
zero term retained.  This is only a syntactic alignment device; it does not
change any Haar integral. -/
def compactCoupledBF4ActionPolynomialWithCompilerZero : RatPoly :=
  polyAdd compactCoupledBF4ActionPolynomial
    (polySmul oneOver480
      (exprToRatPoly (.const 0)))

/-- The denominator-cleared compiler and the original `(1/96,1/8)` compiler
have identical monomials and equivalent rational coefficients. -/
theorem compactActionPolynomial_compilers_termwise :
    RatPolyTermwiseEqv
      compactActionPolynomialFromCleared
      compactCoupledBF4ActionPolynomialWithCompilerZero := by
  decide

/-- The normalized action compiled through the integer certificate is exactly
the original coupled BF4 action under arbitrary insertion and tenfold Haar.
This closes the last syntactic gap between the SOS/order layer and the
Feynman--Kac Taylor layer. -/
theorem compactActionPolynomialFromCleared_haar_eq_physical
    (polynomial : RatPoly) :
    tenfoldHaar
        (polyMul polynomial
          compactActionPolynomialFromCleared) ≈
      tenfoldHaar
        (polyMul polynomial
          compactCoupledBF4ActionPolynomial) := by
  refine Q'.eqv_trans _
    (tenfoldHaar
      (polyMul polynomial
        compactCoupledBF4ActionPolynomialWithCompilerZero)) _
    (quaternionHaar_polyMul_termwise_eqv
      10 polynomial
      compactActionPolynomial_compilers_termwise) ?_
  unfold compactCoupledBF4ActionPolynomialWithCompilerZero
  refine Q'.eqv_trans _
    (tenfoldHaar
          (polyMul polynomial
            compactCoupledBF4ActionPolynomial) +
      tenfoldHaar
          (polyMul polynomial
            (polySmul oneOver480
              (exprToRatPoly (.const 0))))) _
    (quaternionHaar_polyMul_add_right
      10 polynomial
      compactCoupledBF4ActionPolynomial
      (polySmul oneOver480
        (exprToRatPoly (.const 0)))) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar
          (polyMul polynomial
            compactCoupledBF4ActionPolynomial) +
      oneOver480 *
        tenfoldHaar
          (polyMul polynomial
            (exprToRatPoly (.const 0)))) _
    (QPoly.q_add_congr
      (Q'.eqv_refl _)
      (quaternionHaar_polyMul_smul_right
        10 oneOver480 polynomial
        (exprToRatPoly (.const 0)))) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar
          (polyMul polynomial
            compactCoupledBF4ActionPolynomial) +
      oneOver480 * 0) _
    (QPoly.q_add_congr
      (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left
        oneOver480 _ _
        (quaternionHaar_polyMul_compiledZero_right
          10 polynomial))) ?_
  refine Q'.eqv_trans _
    (tenfoldHaar
          (polyMul polynomial
            compactCoupledBF4ActionPolynomial) +
      0) _
    (QPoly.q_add_congr
      (Q'.eqv_refl _)
      (Q'.mul_zero_eqv oneOver480)) ?_
  exact QPoly.q_add_zero_eqv _

/-- Exact rational scalar calculation

`(1/480) * (1596 * 10) = 133/4`. -/
theorem normalizedCompactActionCeiling :
    oneOver480 *
        (Q'.ofInt 1596 * Q'.ofNat 10) ≈
      compactCoupledBF4ActionCeiling := by
  decide

/-- **Normalized arbitrary-insertion sphere shift.**

For every finite polynomial `P`,

`H_10(P D) + H_10(P A) = (133/4) H_10(P)`.
-/
theorem compactAction_sphere_shift
    (polynomial : RatPoly) :
    tenfoldHaar
          (polyMul polynomial
            compactActionComplementPolynomial) +
        tenfoldHaar
          (polyMul polynomial
            compactActionPolynomialFromCleared) ≈
      compactCoupledBF4ActionCeiling *
        tenfoldHaar polynomial := by
  refine Q'.eqv_trans _
    (oneOver480 *
          tenfoldHaar
            (polyMul polynomial
              (exprToRatPoly
                clearedSphereComplementExpr)) +
      oneOver480 *
          tenfoldHaar
            (polyMul polynomial
              (exprToRatPoly
                clearedCompactActionExpr))) _ ?_ ?_
  · exact QPoly.q_add_congr
      (quaternionHaar_polyMul_smul_right
        10 oneOver480 polynomial
        (exprToRatPoly
          clearedSphereComplementExpr))
      (quaternionHaar_polyMul_smul_right
        10 oneOver480 polynomial
        (exprToRatPoly
          clearedCompactActionExpr))
  · refine Q'.eqv_trans _
      (oneOver480 *
        (tenfoldHaar
            (polyMul polynomial
              (exprToRatPoly
                clearedSphereComplementExpr)) +
          tenfoldHaar
            (polyMul polynomial
              (exprToRatPoly
                clearedCompactActionExpr)))) _
      (Q'.eqv_symm
        (Q'.mul_add_eqv oneOver480 _ _)) ?_
    refine Q'.eqv_trans _
      (oneOver480 *
        ((Q'.ofInt 1596 * Q'.ofNat 10) *
          tenfoldHaar polynomial)) _
      (Q'.mul_eqv_congr_left _ _ _
        (clearedCompactAction_sphere_shift
          polynomial)) ?_
    refine Q'.eqv_trans _
      ((oneOver480 *
          (Q'.ofInt 1596 * Q'.ofNat 10)) *
        tenfoldHaar polynomial) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv oneOver480
          (Q'.ofInt 1596 * Q'.ofNat 10)
          (tenfoldHaar polynomial))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      normalizedCompactActionCeiling

/-- **Physical normalized arbitrary-insertion sphere shift.**

The action on the left is definitionally the genuine coupled `(K,S)`
polynomial used by `geometricMehlerTaylorTerm`.
-/
theorem compactPhysicalAction_sphere_shift
    (polynomial : RatPoly) :
    tenfoldHaar
          (polyMul polynomial
            compactActionComplementPolynomial) +
        tenfoldHaar
          (polyMul polynomial
            compactCoupledBF4ActionPolynomial) ≈
      compactCoupledBF4ActionCeiling *
        tenfoldHaar polynomial := by
  refine Q'.eqv_trans _
    (tenfoldHaar
          (polyMul polynomial
            compactActionComplementPolynomial) +
      tenfoldHaar
          (polyMul polynomial
            compactActionPolynomialFromCleared)) _
    (QPoly.q_add_congr
      (Q'.eqv_refl _)
      (Q'.eqv_symm
        (compactActionPolynomialFromCleared_haar_eq_physical
          polynomial))) ?_
  exact compactAction_sphere_shift polynomial

end YMGap.Continuum.BF4CompactActionSphereShift

#print axioms YMGap.Continuum.BF4CompactActionSphereShift.quaternionHaar_mul_radiusPrefixSum
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.clearedComplementPlusAction_normal
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.tenRadiusSumPolynomial_eq
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.clearedRadiusCeilingPolynomial_eq
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.clearedCompactAction_sphere_shift
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.normalizedCompactActionCeiling
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.compactAction_sphere_shift
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.compactActionPolynomial_compilers_termwise
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.compactActionPolynomialFromCleared_haar_eq_physical
#print axioms YMGap.Continuum.BF4CompactActionSphereShift.compactPhysicalAction_sphere_shift
