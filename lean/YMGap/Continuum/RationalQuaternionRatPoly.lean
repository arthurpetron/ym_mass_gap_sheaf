/-
# Rational-quaternion polynomials and the oriented plaquette word

This leaf lifts the raw Hamilton quaternion algebra to four-component
`RatPoly` data.  It is the generic polynomial layer needed before lattice
holonomies can be pulled back through concrete link-coordinate maps.

The construction contains:

* a quaternion whose four scalar-first components are raw rational
  polynomials;
* coordinate variables at an arbitrary base offset;
* scalar, unit, conjugation, and Hamilton multiplication operations;
* componentwise evaluation into `RationalQuaternion`, with exact semantic
  conjugation and multiplication laws;
* the sixteen-coordinate environment for four oriented edges; and
* the standard plaquette word `U0 * U3 * conj(U2) * conj(U1)`, together with
  its exact evaluation theorem.

All equalities of evaluated rational quaternions use the repository's honest
coordinatewise semantic equality.  No quotient or representative equality is
silently substituted for it.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.RatPolySubstitution
import YMGap.RepTheory.RationalQuaternionUnitNormGroup

namespace YMGap.Continuum.RationalQuaternionRatPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.RepTheory

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ b ha)
    (Q'.add_eqv_congr_left a' _ _ hb)

/-! ## 1. Four-component polynomial quaternions -/

/-- A raw quaternion with one finite-support rational polynomial in each
scalar-first Hamilton coordinate. -/
structure RatPolyQuaternion where
  r : RatPoly
  i : RatPoly
  j : RatPoly
  k : RatPoly

/-- The four coordinate variables beginning at `base`. -/
def variablesAt (base : Nat) : RatPolyQuaternion :=
  ⟨polyVar base, polyVar (base + 1),
    polyVar (base + 2), polyVar (base + 3)⟩

/-- Embed a scalar polynomial as a quaternion. -/
def scalar (polynomial : RatPoly) : RatPolyQuaternion :=
  ⟨polynomial, polyZero, polyZero, polyZero⟩

/-- The polynomial quaternion unit. -/
def one : RatPolyQuaternion := scalar polyOne

/-- Polynomial quaternion conjugation. -/
def conj (x : RatPolyQuaternion) : RatPolyQuaternion :=
  ⟨x.r, polyNeg x.i, polyNeg x.j, polyNeg x.k⟩

/-- A grouped four-term sum matching the parenthesization used by the raw
Hamilton multiplication definition. -/
private def groupedFourSum (a b c d : RatPoly) : RatPoly :=
  polyAdd (polyAdd a b) (polyAdd c d)

/-- Hamilton multiplication in scalar-first polynomial coordinates. -/
def mul (x y : RatPolyQuaternion) : RatPolyQuaternion :=
  ⟨groupedFourSum
      (polyMul x.r y.r) (polyNeg (polyMul x.i y.i))
      (polyNeg (polyMul x.j y.j)) (polyNeg (polyMul x.k y.k)),
    groupedFourSum
      (polyMul x.r y.i) (polyMul x.i y.r)
      (polyMul x.j y.k) (polyNeg (polyMul x.k y.j)),
    groupedFourSum
      (polyMul x.r y.j) (polyNeg (polyMul x.i y.k))
      (polyMul x.j y.r) (polyMul x.k y.i),
    groupedFourSum
      (polyMul x.r y.k) (polyMul x.i y.j)
      (polyNeg (polyMul x.j y.i)) (polyMul x.k y.r)⟩

/-! ## 2. Exact evaluation laws -/

/-- Evaluate all four polynomial coordinates in one rational environment. -/
def eval (rho : Nat → Q') (x : RatPolyQuaternion) : RationalQuaternion :=
  ⟨evalRatPoly rho x.r, evalRatPoly rho x.i,
    evalRatPoly rho x.j, evalRatPoly rho x.k⟩

theorem evalRatPoly_zero (rho : Nat → Q') :
    evalRatPoly rho polyZero ≈ 0 :=
  Q'.eqv_refl _

/-- Evaluation commutes with coefficientwise polynomial negation. -/
theorem evalRatPoly_neg (rho : Nat → Q') : ∀ polynomial : RatPoly,
    evalRatPoly rho (polyNeg polynomial) ≈
      -(evalRatPoly rho polynomial)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | term :: tail => by
      change
        (-term.2) * evalMono rho term.1 +
            evalRatPoly rho (polyNeg tail) ≈
          -(term.2 * evalMono rho term.1 + evalRatPoly rho tail)
      exact Q'.eqv_trans _ _ _
        (q_add_congr
          (Q'.neg_mul_eqv term.2 (evalMono rho term.1))
          (evalRatPoly_neg rho tail))
        (Q'.eqv_symm
          (Q'.neg_add_eqv
            (term.2 * evalMono rho term.1) (evalRatPoly rho tail)))

private theorem eval_negMul (rho : Nat → Q') (left right : RatPoly) :
    evalRatPoly rho (polyNeg (polyMul left right)) ≈
      -(evalRatPoly rho left * evalRatPoly rho right) :=
  Q'.eqv_trans _ _ _
    (evalRatPoly_neg rho (polyMul left right))
    (Q'.neg_eqv_congr _ _ (evalRatPoly_mul rho left right))

private theorem eval_groupedFourSum (rho : Nat → Q')
    (a b c d : RatPoly) :
    evalRatPoly rho (groupedFourSum a b c d) ≈
      (evalRatPoly rho a + evalRatPoly rho b) +
        (evalRatPoly rho c + evalRatPoly rho d) :=
  Q'.eqv_trans _ _ _
    (evalRatPoly_add rho (polyAdd a b) (polyAdd c d))
    (q_add_congr (evalRatPoly_add rho a b) (evalRatPoly_add rho c d))

/-- Evaluation of a scalar polynomial quaternion is the corresponding raw
scalar quaternion. -/
theorem eval_scalar (rho : Nat → Q') (polynomial : RatPoly) :
    (eval rho (scalar polynomial)).Equivalent
      (RationalQuaternion.scalar (evalRatPoly rho polynomial)) :=
  ⟨Q'.eqv_refl _, evalRatPoly_zero rho,
    evalRatPoly_zero rho, evalRatPoly_zero rho⟩

/-- Evaluation of the polynomial unit is the raw quaternion unit. -/
theorem eval_one (rho : Nat → Q') :
    (eval rho one).Equivalent RationalQuaternion.one :=
  RationalQuaternion.semanticSetoid.iseqv.trans
    (eval_scalar rho polyOne)
    (RationalQuaternion.scalar_congr (evalRatPoly_one rho))

/-- Exact evaluation of the four coordinate variables at an arbitrary base
offset. -/
theorem eval_variablesAt (rho : Nat → Q') (base : Nat) :
    (eval rho (variablesAt base)).Equivalent
      ⟨rho base, rho (base + 1), rho (base + 2), rho (base + 3)⟩ :=
  ⟨evalRatPoly_var rho base,
    evalRatPoly_var rho (base + 1),
    evalRatPoly_var rho (base + 2),
    evalRatPoly_var rho (base + 3)⟩

/-- Evaluation commutes with quaternion conjugation. -/
theorem eval_conj (rho : Nat → Q') (x : RatPolyQuaternion) :
    (eval rho (conj x)).Equivalent
      (RationalQuaternion.conj (eval rho x)) :=
  ⟨Q'.eqv_refl _, evalRatPoly_neg rho x.i,
    evalRatPoly_neg rho x.j, evalRatPoly_neg rho x.k⟩

/-- Evaluation commutes with Hamilton multiplication. -/
theorem eval_mul (rho : Nat → Q') (x y : RatPolyQuaternion) :
    (eval rho (mul x y)).Equivalent
      (RationalQuaternion.mul (eval rho x) (eval rho y)) :=
  ⟨Q'.eqv_trans _ _ _
      (eval_groupedFourSum rho
        (polyMul x.r y.r) (polyNeg (polyMul x.i y.i))
        (polyNeg (polyMul x.j y.j)) (polyNeg (polyMul x.k y.k)))
      (q_add_congr
        (q_add_congr
          (evalRatPoly_mul rho x.r y.r) (eval_negMul rho x.i y.i))
        (q_add_congr
          (eval_negMul rho x.j y.j) (eval_negMul rho x.k y.k))),
    Q'.eqv_trans _ _ _
      (eval_groupedFourSum rho
        (polyMul x.r y.i) (polyMul x.i y.r)
        (polyMul x.j y.k) (polyNeg (polyMul x.k y.j)))
      (q_add_congr
        (q_add_congr
          (evalRatPoly_mul rho x.r y.i) (evalRatPoly_mul rho x.i y.r))
        (q_add_congr
          (evalRatPoly_mul rho x.j y.k) (eval_negMul rho x.k y.j))),
    Q'.eqv_trans _ _ _
      (eval_groupedFourSum rho
        (polyMul x.r y.j) (polyNeg (polyMul x.i y.k))
        (polyMul x.j y.r) (polyMul x.k y.i))
      (q_add_congr
        (q_add_congr
          (evalRatPoly_mul rho x.r y.j) (eval_negMul rho x.i y.k))
        (q_add_congr
          (evalRatPoly_mul rho x.j y.r) (evalRatPoly_mul rho x.k y.i))),
    Q'.eqv_trans _ _ _
      (eval_groupedFourSum rho
        (polyMul x.r y.k) (polyMul x.i y.j)
        (polyNeg (polyMul x.j y.i)) (polyMul x.k y.r))
      (q_add_congr
        (q_add_congr
          (evalRatPoly_mul rho x.r y.k) (evalRatPoly_mul rho x.i y.j))
        (q_add_congr
          (eval_negMul rho x.j y.i) (evalRatPoly_mul rho x.k y.r)))⟩

/-! ## 3. The four-edge environment and plaquette holonomy -/

/-- The sixteen scalar-first coordinates of four oriented raw quaternions,
extended by zero outside the active coordinate range. -/
def fourEdgeEnvironment
    (u0 u1 u2 u3 : RationalQuaternion) : Nat → Q'
  | 0 => u0.r
  | 1 => u0.i
  | 2 => u0.j
  | 3 => u0.k
  | 4 => u1.r
  | 5 => u1.i
  | 6 => u1.j
  | 7 => u1.k
  | 8 => u2.r
  | 9 => u2.i
  | 10 => u2.j
  | 11 => u2.k
  | 12 => u3.r
  | 13 => u3.i
  | 14 => u3.j
  | 15 => u3.k
  | _ => 0

private theorem eval_fourEdge0
    (u0 u1 u2 u3 : RationalQuaternion) :
    (eval (fourEdgeEnvironment u0 u1 u2 u3) (variablesAt 0)).Equivalent
      u0 :=
  ⟨evalRatPoly_var _ 0, evalRatPoly_var _ 1,
    evalRatPoly_var _ 2, evalRatPoly_var _ 3⟩

private theorem eval_fourEdge1
    (u0 u1 u2 u3 : RationalQuaternion) :
    (eval (fourEdgeEnvironment u0 u1 u2 u3) (variablesAt 4)).Equivalent
      u1 :=
  ⟨evalRatPoly_var _ 4, evalRatPoly_var _ 5,
    evalRatPoly_var _ 6, evalRatPoly_var _ 7⟩

private theorem eval_fourEdge2
    (u0 u1 u2 u3 : RationalQuaternion) :
    (eval (fourEdgeEnvironment u0 u1 u2 u3) (variablesAt 8)).Equivalent
      u2 :=
  ⟨evalRatPoly_var _ 8, evalRatPoly_var _ 9,
    evalRatPoly_var _ 10, evalRatPoly_var _ 11⟩

private theorem eval_fourEdge3
    (u0 u1 u2 u3 : RationalQuaternion) :
    (eval (fourEdgeEnvironment u0 u1 u2 u3) (variablesAt 12)).Equivalent
      u3 :=
  ⟨evalRatPoly_var _ 12, evalRatPoly_var _ 13,
    evalRatPoly_var _ 14, evalRatPoly_var _ 15⟩

/-- The scalar-first polynomial quaternion for the standard oriented
plaquette word `U0 * U3 * conj(U2) * conj(U1)`. -/
def orientedPlaquetteHolonomyPolynomial : RatPolyQuaternion :=
  mul
    (mul
      (mul (variablesAt 0) (variablesAt 12))
      (conj (variablesAt 8)))
    (conj (variablesAt 4))

/-- Exact evaluation of the standard oriented plaquette holonomy polynomial. -/
theorem eval_orientedPlaquetteHolonomyPolynomial
    (u0 u1 u2 u3 : RationalQuaternion) :
    (eval (fourEdgeEnvironment u0 u1 u2 u3)
      orientedPlaquetteHolonomyPolynomial).Equivalent
      (RationalQuaternion.mul
        (RationalQuaternion.mul
          (RationalQuaternion.mul u0 u3)
          (RationalQuaternion.conj u2))
        (RationalQuaternion.conj u1)) := by
  let rho := fourEdgeEnvironment u0 u1 u2 u3
  have h0 : (eval rho (variablesAt 0)).Equivalent u0 :=
    eval_fourEdge0 u0 u1 u2 u3
  have h1 : (eval rho (variablesAt 4)).Equivalent u1 :=
    eval_fourEdge1 u0 u1 u2 u3
  have h2 : (eval rho (variablesAt 8)).Equivalent u2 :=
    eval_fourEdge2 u0 u1 u2 u3
  have h3 : (eval rho (variablesAt 12)).Equivalent u3 :=
    eval_fourEdge3 u0 u1 u2 u3
  have hc1 : (eval rho (conj (variablesAt 4))).Equivalent
      (RationalQuaternion.conj u1) :=
    RationalQuaternion.semanticSetoid.iseqv.trans
      (eval_conj rho (variablesAt 4))
      (RationalQuaternion.conj_congr h1)
  have hc2 : (eval rho (conj (variablesAt 8))).Equivalent
      (RationalQuaternion.conj u2) :=
    RationalQuaternion.semanticSetoid.iseqv.trans
      (eval_conj rho (variablesAt 8))
      (RationalQuaternion.conj_congr h2)
  have h03 : (eval rho (mul (variablesAt 0) (variablesAt 12))).Equivalent
      (RationalQuaternion.mul u0 u3) :=
    RationalQuaternion.semanticSetoid.iseqv.trans
      (eval_mul rho (variablesAt 0) (variablesAt 12))
      (RationalQuaternion.mul_congr h0 h3)
  have h032 :
      (eval rho
        (mul (mul (variablesAt 0) (variablesAt 12))
          (conj (variablesAt 8)))).Equivalent
        (RationalQuaternion.mul
          (RationalQuaternion.mul u0 u3)
          (RationalQuaternion.conj u2)) :=
    RationalQuaternion.semanticSetoid.iseqv.trans
      (eval_mul rho (mul (variablesAt 0) (variablesAt 12))
        (conj (variablesAt 8)))
      (RationalQuaternion.mul_congr h03 hc2)
  exact RationalQuaternion.semanticSetoid.iseqv.trans
    (eval_mul rho
      (mul (mul (variablesAt 0) (variablesAt 12))
        (conj (variablesAt 8)))
      (conj (variablesAt 4)))
    (RationalQuaternion.mul_congr h032 hc1)

#print axioms evalRatPoly_neg
#print axioms eval_conj
#print axioms eval_mul
#print axioms eval_orientedPlaquetteHolonomyPolynomial

end YMGap.Continuum.RationalQuaternionRatPoly
