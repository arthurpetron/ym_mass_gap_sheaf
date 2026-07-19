/-
# Fundamental matrix semantics for rational quaternion polynomials

`SU2QuaternionOneLinkFundamentalSchur` introduced the honest complexified
fundamental entries as pairs of real raw polynomials.  This leaf proves that
those entries really form the standard fundamental matrix representation of
the existing Hamilton quaternion algebra.

The proof is semantic and remains completely symbolic:

* a rational complex number is a pair of constructive rationals;
* a fundamental matrix is a `Bool x Bool` family of such pairs;
* its two-term matrix product is defined explicitly;
* the four matrix entries of a raw Hamilton product agree componentwise with
  that matrix product; and
* the established polynomial-quaternion `eval_mul` theorem transports the
  result to arbitrary `RatPolyQuaternion` inputs and environments.

Quaternion conjugation is likewise identified with conjugate transpose.
Since inversion on `UnitNorm` is definitionally quaternion conjugation, the
same theorem gives the inverse-orientation semantics needed by the local
Schur contraction.

No plaquette word, cube product, density polynomial, or slab enumeration is
unfolded or materialized here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur

namespace YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics

open YMGap.Constructive
open YMGap.RepTheory
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero] <;>
             ac_rfl))

/-! ## 1. Rational-complex and two-by-two matrix semantics -/

/-- Addition of rational complex values. -/
def rationalComplexAdd
    (left right : RationalComplex) : RationalComplex :=
  (left.1 + right.1, left.2 + right.2)

/-- Multiplication of rational complex values. -/
def rationalComplexMul
    (left right : RationalComplex) : RationalComplex :=
  (left.1 * right.1 + -(left.2 * right.2),
    left.1 * right.2 + left.2 * right.1)

/-- Complex conjugation of a rational complex value. -/
def rationalComplexConj (value : RationalComplex) : RationalComplex :=
  (value.1, -value.2)

/-- A fundamental two-by-two matrix, indexed constructively by `Bool`. -/
abbrev FundamentalMatrix := Bool → Bool → RationalComplex

/-- Componentwise semantic equality of fundamental matrices. -/
def FundamentalMatrixEqv
    (left right : FundamentalMatrix) : Prop :=
  ∀ row column, RationalComplexEqv (left row column) (right row column)

/-- The explicit two-term product of fundamental matrices. -/
def fundamentalMatrixMul
    (left right : FundamentalMatrix) : FundamentalMatrix :=
  fun row column =>
    rationalComplexAdd
      (rationalComplexMul (left row false) (right false column))
      (rationalComplexMul (left row true) (right true column))

/-- Conjugate transpose of a fundamental matrix. -/
def fundamentalMatrixAdjoint
    (matrix : FundamentalMatrix) : FundamentalMatrix :=
  fun row column => rationalComplexConj (matrix column row)

private theorem rationalComplexEqv_refl (value : RationalComplex) :
    RationalComplexEqv value value :=
  ⟨Q'.eqv_refl value.1, Q'.eqv_refl value.2⟩

private theorem rationalComplexEqv_symm
    {left right : RationalComplex}
    (h : RationalComplexEqv left right) :
    RationalComplexEqv right left :=
  ⟨Q'.eqv_symm h.1, Q'.eqv_symm h.2⟩

private theorem rationalComplexEqv_trans
    {first second third : RationalComplex}
    (hfirst : RationalComplexEqv first second)
    (hsecond : RationalComplexEqv second third) :
    RationalComplexEqv first third :=
  ⟨Q'.eqv_trans _ _ _ hfirst.1 hsecond.1,
    Q'.eqv_trans _ _ _ hfirst.2 hsecond.2⟩

private theorem q_add_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a + b ≈ a' + b' :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem rationalComplexAdd_congr
    {left left' right right' : RationalComplex}
    (hleft : RationalComplexEqv left left')
    (hright : RationalComplexEqv right right') :
    RationalComplexEqv
      (rationalComplexAdd left right)
      (rationalComplexAdd left' right') :=
  ⟨q_add_congr hleft.1 hright.1,
    q_add_congr hleft.2 hright.2⟩

private theorem rationalComplexMul_congr
    {left left' right right' : RationalComplex}
    (hleft : RationalComplexEqv left left')
    (hright : RationalComplexEqv right right') :
    RationalComplexEqv
      (rationalComplexMul left right)
      (rationalComplexMul left' right') :=
  ⟨q_add_congr
      (q_mul_congr hleft.1 hright.1)
      (Q'.neg_eqv_congr _ _ (q_mul_congr hleft.2 hright.2)),
    q_add_congr
      (q_mul_congr hleft.1 hright.2)
      (q_mul_congr hleft.2 hright.1)⟩

private theorem rationalComplexConj_congr
    {left right : RationalComplex}
    (h : RationalComplexEqv left right) :
    RationalComplexEqv
      (rationalComplexConj left) (rationalComplexConj right) :=
  ⟨h.1, Q'.neg_eqv_congr _ _ h.2⟩

private theorem fundamentalMatrixEqv_symm
    {left right : FundamentalMatrix}
    (h : FundamentalMatrixEqv left right) :
    FundamentalMatrixEqv right left := by
  intro row column
  exact rationalComplexEqv_symm (h row column)

private theorem fundamentalMatrixEqv_trans
    {first second third : FundamentalMatrix}
    (hfirst : FundamentalMatrixEqv first second)
    (hsecond : FundamentalMatrixEqv second third) :
    FundamentalMatrixEqv first third := by
  intro row column
  exact rationalComplexEqv_trans
    (hfirst row column) (hsecond row column)

private theorem fundamentalMatrixMul_congr
    {left left' right right' : FundamentalMatrix}
    (hleft : FundamentalMatrixEqv left left')
    (hright : FundamentalMatrixEqv right right') :
    FundamentalMatrixEqv
      (fundamentalMatrixMul left right)
      (fundamentalMatrixMul left' right') := by
  intro row column
  exact rationalComplexAdd_congr
    (rationalComplexMul_congr
      (hleft row false) (hright false column))
    (rationalComplexMul_congr
      (hleft row true) (hright true column))

private theorem fundamentalMatrixAdjoint_congr
    {left right : FundamentalMatrix}
    (h : FundamentalMatrixEqv left right) :
    FundamentalMatrixEqv
      (fundamentalMatrixAdjoint left)
      (fundamentalMatrixAdjoint right) := by
  intro row column
  exact rationalComplexConj_congr (h column row)

/-! ## 2. The standard matrix of a raw rational quaternion -/

/-- The standard complex fundamental matrix of a raw scalar-first rational
quaternion. -/
def fundamentalMatrixValue
    (quaternion : RationalQuaternion) : FundamentalMatrix
  | false, false => (quaternion.r, quaternion.i)
  | false, true => (quaternion.j, quaternion.k)
  | true, false => (-quaternion.j, quaternion.k)
  | true, true => (quaternion.r, -quaternion.i)

/-- Quaternion semantic equality is respected entrywise by the fundamental
matrix. -/
theorem fundamentalMatrixValue_congr
    {left right : RationalQuaternion}
    (h : left.Equivalent right) :
    FundamentalMatrixEqv
      (fundamentalMatrixValue left) (fundamentalMatrixValue right) := by
  intro row column
  cases row <;> cases column
  · exact ⟨h.1, h.2.1⟩
  · exact ⟨h.2.2.1, h.2.2.2⟩
  · exact ⟨Q'.neg_eqv_congr _ _ h.2.2.1, h.2.2.2⟩
  · exact ⟨h.1, Q'.neg_eqv_congr _ _ h.2.1⟩

/-- **Fundamental representation law.**  The standard complex matrix of a
Hamilton product is the two-by-two product of the standard matrices. -/
theorem fundamentalMatrixValue_mul
    (left right : RationalQuaternion) :
    FundamentalMatrixEqv
      (fundamentalMatrixValue (RationalQuaternion.mul left right))
      (fundamentalMatrixMul
        (fundamentalMatrixValue left) (fundamentalMatrixValue right)) := by
  intro row column
  cases row <;> cases column <;>
    unfold RationalComplexEqv fundamentalMatrixValue fundamentalMatrixMul
      rationalComplexAdd rationalComplexMul RationalQuaternion.mul <;>
    constructor <;> ring_qeqv

/-- Quaternion conjugation is complex conjugate transpose in the fundamental
matrix representation. -/
theorem fundamentalMatrixValue_conj
    (quaternion : RationalQuaternion) :
    FundamentalMatrixEqv
      (fundamentalMatrixValue (RationalQuaternion.conj quaternion))
      (fundamentalMatrixAdjoint (fundamentalMatrixValue quaternion)) := by
  intro row column
  cases row <;> cases column <;>
    unfold RationalComplexEqv fundamentalMatrixValue
      fundamentalMatrixAdjoint rationalComplexConj
      RationalQuaternion.conj <;>
    constructor <;> ring_qeqv

/-! ## 3. Evaluation of the polynomial fundamental matrix -/

/-- Evaluate both real components of one complex raw polynomial. -/
def evalComplexRatPoly
    (rho : Nat → Q') (value : ComplexRatPoly) : RationalComplex :=
  (evalRatPoly rho value.1, evalRatPoly rho value.2)

/-- Evaluate every fundamental entry of a polynomial quaternion. -/
def evaluatedFundamentalMatrix
    (rho : Nat → Q') (quaternion : RatPolyQuaternion) : FundamentalMatrix :=
  fun row column =>
    evalComplexRatPoly rho
      (fundamentalMatrixCoefficient quaternion row column)

private theorem evalComplexRatPoly_conj
    (rho : Nat → Q') (value : ComplexRatPoly) :
    RationalComplexEqv
      (evalComplexRatPoly rho (complexRatPolyConj value))
      (rationalComplexConj (evalComplexRatPoly rho value)) :=
  ⟨Q'.eqv_refl _, evalRatPoly_neg rho value.2⟩

/-- Evaluation of the polynomial coefficient formula agrees entrywise with
the standard matrix of the evaluated polynomial quaternion. -/
theorem evaluatedFundamentalMatrix_eq_value
    (rho : Nat → Q') (quaternion : RatPolyQuaternion) :
    FundamentalMatrixEqv
      (evaluatedFundamentalMatrix rho quaternion)
      (fundamentalMatrixValue
        (RationalQuaternionRatPoly.eval rho quaternion)) := by
  intro row column
  cases row <;> cases column
  · exact rationalComplexEqv_refl _
  · exact rationalComplexEqv_refl _
  · exact ⟨evalRatPoly_neg rho quaternion.j, Q'.eqv_refl _⟩
  · exact ⟨Q'.eqv_refl _, evalRatPoly_neg rho quaternion.i⟩

/-- **Polynomial evaluation form of the representation law.**  Evaluating
the fundamental entries of a Hamilton product gives the matrix product of
the separately evaluated fundamental entries. -/
theorem evaluatedFundamentalMatrix_mul
    (rho : Nat → Q') (left right : RatPolyQuaternion) :
    FundamentalMatrixEqv
      (evaluatedFundamentalMatrix rho
        (RationalQuaternionRatPoly.mul left right))
      (fundamentalMatrixMul
        (evaluatedFundamentalMatrix rho left)
        (evaluatedFundamentalMatrix rho right)) := by
  have hsource := evaluatedFundamentalMatrix_eq_value rho
    (RationalQuaternionRatPoly.mul left right)
  have heval := fundamentalMatrixValue_congr
    (RationalQuaternionRatPoly.eval_mul rho left right)
  have hraw := fundamentalMatrixValue_mul
    (RationalQuaternionRatPoly.eval rho left)
    (RationalQuaternionRatPoly.eval rho right)
  have hinputs := fundamentalMatrixMul_congr
    (evaluatedFundamentalMatrix_eq_value rho left)
    (evaluatedFundamentalMatrix_eq_value rho right)
  exact fundamentalMatrixEqv_trans hsource
    (fundamentalMatrixEqv_trans heval
      (fundamentalMatrixEqv_trans hraw
        (fundamentalMatrixEqv_symm hinputs)))

/-- Evaluating polynomial quaternion conjugation gives conjugate transpose of
the evaluated fundamental matrix. -/
theorem evaluatedFundamentalMatrix_conj
    (rho : Nat → Q') (quaternion : RatPolyQuaternion) :
    FundamentalMatrixEqv
      (evaluatedFundamentalMatrix rho
        (RationalQuaternionRatPoly.conj quaternion))
      (fundamentalMatrixAdjoint
        (evaluatedFundamentalMatrix rho quaternion)) := by
  have hsource := evaluatedFundamentalMatrix_eq_value rho
    (RationalQuaternionRatPoly.conj quaternion)
  have heval := fundamentalMatrixValue_congr
    (RationalQuaternionRatPoly.eval_conj rho quaternion)
  have hraw := fundamentalMatrixValue_conj
    (RationalQuaternionRatPoly.eval rho quaternion)
  have hinput := fundamentalMatrixAdjoint_congr
    (evaluatedFundamentalMatrix_eq_value rho quaternion)
  exact fundamentalMatrixEqv_trans hsource
    (fundamentalMatrixEqv_trans heval
      (fundamentalMatrixEqv_trans hraw
        (fundamentalMatrixEqv_symm hinput)))

/-! ## 4. Reverse link orientation and unit-quaternion inversion -/

/-- The reverse coefficient introduced by the one-link Schur leaf evaluates
to the matching entry of the conjugated quaternion matrix.  This discharges
the semantic interpretation that was deliberately fenced in that leaf. -/
theorem eval_reverseFundamentalCoefficient_as_conjugate
    (rho : Nat → Q') (block : Nat) (row column : Bool) :
    RationalComplexEqv
      (evalComplexRatPoly rho
        (reverseFundamentalCoefficient block row column))
      (fundamentalMatrixValue
        (RationalQuaternion.conj
          (RationalQuaternionRatPoly.eval rho
            (fundamentalLinkQuaternion block))) row column) := by
  have hconj := evalComplexRatPoly_conj rho
    (forwardFundamentalCoefficient block column row)
  have hentry := evaluatedFundamentalMatrix_eq_value rho
    (fundamentalLinkQuaternion block) column row
  have hadjoint := rationalComplexConj_congr hentry
  have hraw := fundamentalMatrixValue_conj
    (RationalQuaternionRatPoly.eval rho
      (fundamentalLinkQuaternion block)) row column
  exact rationalComplexEqv_trans
    (by simpa [reverseFundamentalCoefficient] using hconj)
    (rationalComplexEqv_trans hadjoint
      (rationalComplexEqv_symm hraw))

/-- The fundamental matrix of a rational unit-quaternion inverse is exactly
the conjugate transpose of its fundamental matrix, modulo rational semantic
equality. -/
theorem unitNormFundamentalMatrix_inv
    (quaternion : RationalQuaternion.UnitNorm) :
    FundamentalMatrixEqv
      (fundamentalMatrixValue
        (RationalQuaternion.UnitNorm.inv quaternion).val)
      (fundamentalMatrixAdjoint
        (fundamentalMatrixValue quaternion.val)) := by
  simpa [RationalQuaternion.UnitNorm.inv,
    RationalQuaternion.UnitNorm.conj] using
    (fundamentalMatrixValue_conj quaternion.val)

#print axioms fundamentalMatrixValue_mul
#print axioms fundamentalMatrixValue_conj
#print axioms evaluatedFundamentalMatrix_mul
#print axioms evaluatedFundamentalMatrix_conj
#print axioms eval_reverseFundamentalCoefficient_as_conjugate
#print axioms unitNormFundamentalMatrix_inv

end YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
