/-
# Constructive double-Haar projection of the geometric BF4 Mehler kernel

This file removes the rational-point-value mismatch left by
`BF4GeometricSpinNetworkMehler`.  The coupled kernel is an exponential and
therefore is not, in general, rational-valued.  Its finite Taylor
approximants are rational polynomials, however, and can be integrated exactly
against the ten normalized `S^3` Haar factors (five source and five target
holonomies).

The present layer constructs:

* a generic exact `n`-fold quaternion Haar moment and its tenfold
  specialization;
* a forty-coordinate polynomial for the genuine three-colour coupled BF4
  action;
* exact source/target embeddings of the geometric all-spin wavefunctions;
* the termwise and partial double-Haar Taylor coefficients.

The next section proves the coefficient-L1 domination needed to turn these
partials into a `CReal` with the already-proved factorial tail modulus.  No
pairwise orthogonality of geometric states is assumed.

## Axiom gate

Finite lists, exact `Q'` arithmetic, and kernel-reduced polynomial syntax
only.  No `Classical.*`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4GeometricSpinNetworkMehler
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.BF4GeometricHaarMehlerProjection

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.RatNat
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.BF4CanonicalClassCoordinateCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact arbitrary-product quaternion Haar moments -/

/-- Product of the first `blocks` normalized `S^3` monomial moments.
The exponent list is consumed in consecutive blocks of four. -/
def quaternionHaarPrefix : Nat → List Nat → Q'
  | 0, _ => 1
  | blocks + 1, monomial =>
      sphereMoment4
          (exponentAt monomial 0) (exponentAt monomial 1)
          (exponentAt monomial 2) (exponentAt monomial 3) *
        quaternionHaarPrefix blocks (monomial.drop 4)

/-- Exact normalized Haar moment on `SU(2)^blocks`.  Exponents beyond the
declared coordinate count force the moment to zero. -/
def quaternionHaarMono (blocks : Nat) (monomial : List Nat) : Q' :=
  if allZero (monomial.drop (4 * blocks)) then
    quaternionHaarPrefix blocks monomial
  else 0

/-- Exact normalized-Haar functional on a finite polynomial in
`4 * blocks` quaternion coordinates. -/
def quaternionHaar (blocks : Nat) : RatPoly → Q'
  | [] => 0
  | term :: rest =>
      term.2 * quaternionHaarMono blocks term.1 +
        quaternionHaar blocks rest

/-- Five source plus five target holonomies. -/
def tenfoldHaar : RatPoly → Q' := quaternionHaar 10

theorem quaternionHaarMono_one (blocks : Nat) :
    quaternionHaarMono blocks [] ≈ 1 := by
  induction blocks with
  | zero => decide
  | succ blocks ih =>
      unfold quaternionHaarMono quaternionHaarPrefix
      simp only [List.drop_nil]
      change sphereMoment4 0 0 0 0 *
          quaternionHaarPrefix blocks [] ≈ 1
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (sphereMoment4_one))
        (Q'.eqv_trans _ _ _
          (Q'.one_mul_eqv _)
          (by
            unfold quaternionHaarMono at ih
            simpa using ih))

theorem tenfoldHaar_one :
    tenfoldHaar polyOne ≈ 1 := by
  decide

/-! ### Uniform moment bounds -/

private theorem oddDoubleFactorial_le_sphereFourDenominator :
    ∀ k : Nat,
      oddDoubleFactorial k ≤ sphereFourDenominator k
  | 0 => by decide
  | k + 1 => by
      unfold oddDoubleFactorial sphereFourDenominator
      exact Nat.mul_le_mul
        (by omega)
        (oddDoubleFactorial_le_sphereFourDenominator k)

private theorem sphereFourDenominator_mul_le_add
    (a : Nat) :
    ∀ b : Nat,
      sphereFourDenominator a * sphereFourDenominator b ≤
        sphereFourDenominator (a + b)
  | 0 => by
      simp only [sphereFourDenominator, Nat.add_zero, Nat.mul_one]
      exact Nat.le_refl _
  | b + 1 => by
      have hfactor : 4 + 2 * b ≤ 4 + 2 * (a + b) := by omega
      have hinduction :=
        sphereFourDenominator_mul_le_add a b
      change
        sphereFourDenominator a *
            ((4 + 2 * b) * sphereFourDenominator b) ≤
          (4 + 2 * (a + b)) *
            sphereFourDenominator (a + b)
      calc
        sphereFourDenominator a *
              ((4 + 2 * b) * sphereFourDenominator b) =
            (4 + 2 * b) *
              (sphereFourDenominator a *
                sphereFourDenominator b) := by
                  ac_rfl
        _ ≤ (4 + 2 * (a + b)) *
              sphereFourDenominator (a + b) :=
            Nat.mul_le_mul hfactor hinduction
        _ = sphereFourDenominator (a + (b + 1)) := by
            congr 2 <;> omega

private theorem fourOddDoubleFactorials_le_denominator
    (k0 k1 k2 k3 : Nat) :
    oddDoubleFactorial k0 * oddDoubleFactorial k1 *
          oddDoubleFactorial k2 * oddDoubleFactorial k3 ≤
      sphereFourDenominator (k0 + k1 + k2 + k3) := by
  have h0 :=
    oddDoubleFactorial_le_sphereFourDenominator k0
  have h1 :=
    oddDoubleFactorial_le_sphereFourDenominator k1
  have h2 :=
    oddDoubleFactorial_le_sphereFourDenominator k2
  have h3 :=
    oddDoubleFactorial_le_sphereFourDenominator k3
  have h01 :
      sphereFourDenominator k0 * sphereFourDenominator k1 ≤
        sphereFourDenominator (k0 + k1) :=
    sphereFourDenominator_mul_le_add k0 k1
  have h012 :
      sphereFourDenominator (k0 + k1) *
          sphereFourDenominator k2 ≤
        sphereFourDenominator (k0 + k1 + k2) :=
    sphereFourDenominator_mul_le_add (k0 + k1) k2
  have h0123 :
      sphereFourDenominator (k0 + k1 + k2) *
          sphereFourDenominator k3 ≤
        sphereFourDenominator (k0 + k1 + k2 + k3) :=
    sphereFourDenominator_mul_le_add (k0 + k1 + k2) k3
  exact Nat.le_trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul h0 h1) h2) h3)
    (Nat.le_trans
      (Nat.mul_le_mul
        (Nat.le_trans
          (Nat.mul_le_mul_right
            (sphereFourDenominator k2) h01)
          h012)
        (Nat.le_refl _))
      h0123)

theorem sphereMoment4_nonnegative
    (e0 e1 e2 e3 : Nat) :
    (0 : Q') ≤ sphereMoment4 e0 e1 e2 e3 := by
  unfold sphereMoment4
  split
  · rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
    exact Int.natCast_nonneg _
  · exact Q'.le_refl' 0

theorem sphereMoment4_le_one
    (e0 e1 e2 e3 : Nat) :
    sphereMoment4 e0 e1 e2 e3 ≤ (1 : Q') := by
  unfold sphereMoment4
  split
  · show
      (Q'.mkPos
          (Int.ofNat
            (oddDoubleFactorial (e0 / 2) *
              oddDoubleFactorial (e1 / 2) *
              oddDoubleFactorial (e2 / 2) *
              oddDoubleFactorial (e3 / 2)))
          (sphereFourDenominator
            (e0 / 2 + e1 / 2 + e2 / 2 + e3 / 2))
          _).num * ((1 : Q').den : Int) ≤
        (1 : Q').num *
          ((Q'.mkPos
            (Int.ofNat
              (oddDoubleFactorial (e0 / 2) *
                oddDoubleFactorial (e1 / 2) *
                oddDoubleFactorial (e2 / 2) *
                oddDoubleFactorial (e3 / 2)))
            (sphereFourDenominator
              (e0 / 2 + e1 / 2 + e2 / 2 + e3 / 2))
            _).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]
    have honeNum : (1 : Q').num = 1 := rfl
    have honeDen : (1 : Q').den = 1 := rfl
    rw [honeNum, honeDen]
    simpa only [Int.natCast_one, Int.mul_one, Int.one_mul] using
      (Int.ofNat_le.mpr
        (fourOddDoubleFactorials_le_denominator
          (e0 / 2) (e1 / 2) (e2 / 2) (e3 / 2)))
  · decide

private theorem quaternionHaarPrefix_nonnegative :
    ∀ (blocks : Nat) (monomial : List Nat),
      (0 : Q') ≤ quaternionHaarPrefix blocks monomial
  | 0, monomial => by
      change (0 : Q') ≤ 1
      decide
  | blocks + 1, monomial =>
      Q'.mul_nonneg _ _
        (sphereMoment4_nonnegative
          (exponentAt monomial 0) (exponentAt monomial 1)
          (exponentAt monomial 2) (exponentAt monomial 3))
        (quaternionHaarPrefix_nonnegative blocks
          (monomial.drop 4))

private theorem quaternionHaarPrefix_le_one :
    ∀ (blocks : Nat) (monomial : List Nat),
      quaternionHaarPrefix blocks monomial ≤ (1 : Q')
  | 0, _ => Q'.le_refl' 1
  | blocks + 1, monomial => by
      let first :=
        sphereMoment4
          (exponentAt monomial 0) (exponentAt monomial 1)
          (exponentAt monomial 2) (exponentAt monomial 3)
      let rest :=
        quaternionHaarPrefix blocks (monomial.drop 4)
      have hfirst0 : (0 : Q') ≤ first :=
        sphereMoment4_nonnegative _ _ _ _
      have hfirst1 : first ≤ (1 : Q') :=
        sphereMoment4_le_one _ _ _ _
      have hrest0 : (0 : Q') ≤ rest :=
        quaternionHaarPrefix_nonnegative _ _
      have hrest1 : rest ≤ (1 : Q') :=
        quaternionHaarPrefix_le_one _ _
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left rest 1 first
          hrest1 hfirst0)
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.mul_one_eqv first))
          hfirst1)

theorem quaternionHaarMono_nonnegative
    (blocks : Nat) (monomial : List Nat) :
    (0 : Q') ≤ quaternionHaarMono blocks monomial := by
  unfold quaternionHaarMono
  split
  · exact quaternionHaarPrefix_nonnegative _ _
  · exact Q'.le_refl' 0

theorem quaternionHaarMono_le_one
    (blocks : Nat) (monomial : List Nat) :
    quaternionHaarMono blocks monomial ≤ (1 : Q') := by
  unfold quaternionHaarMono
  split
  · exact quaternionHaarPrefix_le_one _ _
  · decide

theorem quaternionHaarMono_abs_le_one
    (blocks : Nat) (monomial : List Nat) :
    Q'.abs (quaternionHaarMono blocks monomial) ≤ (1 : Q') := by
  rw [ExpNeg.abs_of_nonneg
    (quaternionHaarMono_nonnegative blocks monomial)]
  exact quaternionHaarMono_le_one blocks monomial

/-! ### Coefficient `L¹` domination of exact Haar integration -/

/-- Sum of absolute values of the listed rational coefficients.  Duplicate
monomials are intentionally not combined; this is the robust syntactic norm
needed for termwise majorization. -/
def polynomialCoefficientL1 : RatPoly → Q'
  | [] => 0
  | term :: rest =>
      Q'.abs term.2 + polynomialCoefficientL1 rest

theorem polynomialCoefficientL1_nonnegative :
    ∀ polynomial : RatPoly,
      (0 : Q') ≤ polynomialCoefficientL1 polynomial
  | [] => Q'.le_refl' 0
  | term :: rest =>
      Q'.zero_le_add _ _
        (Q'.abs_nonneg term.2)
        (polynomialCoefficientL1_nonnegative rest)

private theorem polynomialCoefficientL1_append :
    ∀ left right : RatPoly,
      polynomialCoefficientL1 (left ++ right) ≈
        polynomialCoefficientL1 left +
          polynomialCoefficientL1 right
  | [], right =>
      Q'.eqv_symm
        (QPoly.q_zero_add_eqv
          (polynomialCoefficientL1 right))
  | term :: rest, right => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left
          (Q'.abs term.2) _ _
          (polynomialCoefficientL1_append rest right))
        (Q'.eqv_symm
          (Q'.add_assoc_eqv
            (Q'.abs term.2)
            (polynomialCoefficientL1 rest)
            (polynomialCoefficientL1 right)))

private theorem scaledRowCoefficientL1_le
    (source : RatTerm) :
    ∀ polynomial : RatPoly,
      polynomialCoefficientL1
          (polynomial.map fun target =>
            (monoMul source.1 target.1,
              source.2 * target.2)) ≤
        Q'.abs source.2 *
          polynomialCoefficientL1 polynomial
  | [] => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_zero_eqv (Q'.abs source.2)))
  | target :: rest => by
      change
        Q'.abs (source.2 * target.2) +
            polynomialCoefficientL1
              (rest.map fun other =>
                (monoMul source.1 other.1,
                  source.2 * other.2)) ≤
          Q'.abs source.2 *
            (Q'.abs target.2 +
              polynomialCoefficientL1 rest)
      exact Q'.le_trans' _ _ _
        (ExpNeg.add_le_add2
          (ExpNeg.abs_mul_le source.2 target.2)
          (scaledRowCoefficientL1_le source rest))
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_add_eqv
              (Q'.abs source.2)
              (Q'.abs target.2)
              (polynomialCoefficientL1 rest))))

theorem polynomialCoefficientL1_mul_le :
    ∀ left right : RatPoly,
      polynomialCoefficientL1 (polyMul left right) ≤
        polynomialCoefficientL1 left *
          polynomialCoefficientL1 right
  | [], right => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.zero_mul_eqv
            (polynomialCoefficientL1 right)))
  | source :: rest, right => by
      change
        polynomialCoefficientL1
            ((right.map fun target =>
              (monoMul source.1 target.1,
                source.2 * target.2)) ++
              polyMul rest right) ≤
          (Q'.abs source.2 +
              polynomialCoefficientL1 rest) *
            polynomialCoefficientL1 right
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (polynomialCoefficientL1_append
              (right.map fun target =>
                (monoMul source.1 target.1,
                  source.2 * target.2))
              (polyMul rest right)))
          (ExpNeg.add_le_add2
            (scaledRowCoefficientL1_le source right)
            (polynomialCoefficientL1_mul_le rest right)))
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (ExpNeg.add_mul_eqv
              (Q'.abs source.2)
              (polynomialCoefficientL1 rest)
              (polynomialCoefficientL1 right))))

theorem polynomialCoefficientL1_smul_le
    (coefficient : Q') :
    ∀ polynomial : RatPoly,
      polynomialCoefficientL1
          (polySmul coefficient polynomial) ≤
        Q'.abs coefficient *
          polynomialCoefficientL1 polynomial
  | [] => by
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_zero_eqv (Q'.abs coefficient)))
  | term :: rest => by
      change
        Q'.abs (coefficient * term.2) +
            polynomialCoefficientL1
              (polySmul coefficient rest) ≤
          Q'.abs coefficient *
            (Q'.abs term.2 +
              polynomialCoefficientL1 rest)
      exact Q'.le_trans' _ _ _
        (ExpNeg.add_le_add2
          (ExpNeg.abs_mul_le coefficient term.2)
          (polynomialCoefficientL1_smul_le
            coefficient rest))
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.mul_add_eqv
              (Q'.abs coefficient)
              (Q'.abs term.2)
              (polynomialCoefficientL1 rest))))

/-- Exact product-Haar integration is a contraction for the syntactic
coefficient `L¹` norm. -/
theorem quaternionHaar_abs_le_coefficientL1
    (blocks : Nat) :
    ∀ polynomial : RatPoly,
      Q'.abs (quaternionHaar blocks polynomial) ≤
        polynomialCoefficientL1 polynomial
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      rw [ExpNeg.abs_of_nonneg (Q'.le_refl' 0)]
      exact Q'.le_refl' 0
  | term :: rest => by
      have hterm :
          Q'.abs
              (term.2 *
                quaternionHaarMono blocks term.1) ≤
            Q'.abs term.2 := by
        exact Q'.le_trans' _ _ _
          (ExpNeg.abs_mul_le term.2
            (quaternionHaarMono blocks term.1))
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_left
              (Q'.abs
                (quaternionHaarMono blocks term.1))
              1
              (Q'.abs term.2)
              (quaternionHaarMono_abs_le_one
                blocks term.1)
              (Q'.abs_nonneg term.2))
            (Q'.le_of_eqv
              (Q'.mul_one_eqv
                (Q'.abs term.2))))
      exact Q'.le_trans' _ _ _
        (ExpNeg.abs_add_le
          (term.2 * quaternionHaarMono blocks term.1)
          (quaternionHaar blocks rest))
        (ExpNeg.add_le_add2 hterm
          (quaternionHaar_abs_le_coefficientL1
            blocks rest))

/-! ## 2. A compiler from the reflective expression language -/

/-- Interpret an integer-coefficient raw polynomial as a rational polynomial. -/
def rawToRatPoly (polynomial : RawPoly) : RatPoly :=
  polynomial.map fun term => (term.1, Q'.ofInt term.2)

private theorem eval_rawToRatPoly
    (rho : Nat → Q') :
    ∀ polynomial : RawPoly,
      evalRatPoly rho (rawToRatPoly polynomial) ≈
        evalRaw rho polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      unfold rawToRatPoly List.map evalRatPoly evalRaw
      exact Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        (eval_rawToRatPoly rho rest)

/-- Compile a `PolyExpr` to the full rational polynomial carrier. -/
def exprToRatPoly (expression : PolyExpr) : RatPoly :=
  rawToRatPoly (rawNormalize expression)

theorem eval_exprToRatPoly
    (rho : Nat → Q') (expression : PolyExpr) :
    evalRatPoly rho (exprToRatPoly expression) ≈
      RingNormaliser.eval rho expression := by
  exact Q'.eqv_trans _ _ _
    (eval_rawToRatPoly rho (rawNormalize expression))
    (Q'.eqv_symm (eval_rawNormalize rho expression))

/-- Syntactic substitution of every variable in a reflective expression. -/
def substituteVariables
    (replacement : Nat → PolyExpr) : PolyExpr → PolyExpr
  | .const coefficient => .const coefficient
  | .var index => replacement index
  | .add left right =>
      .add (substituteVariables replacement left)
        (substituteVariables replacement right)
  | .mul left right =>
      .mul (substituteVariables replacement left)
        (substituteVariables replacement right)
  | .neg value => .neg (substituteVariables replacement value)
  | .pow value power =>
      .pow (substituteVariables replacement value) power

theorem eval_substituteVariables
    (rho : Nat → Q') (replacement : Nat → PolyExpr) :
    ∀ expression : PolyExpr,
      RingNormaliser.eval rho
          (substituteVariables replacement expression) ≈
        RingNormaliser.eval
          (fun index => RingNormaliser.eval rho (replacement index))
          expression
  | .const _ => Q'.eqv_refl _
  | .var _ => Q'.eqv_refl _
  | .add left right => by
      exact Q'.add_eqv_congr'
        (eval_substituteVariables rho replacement left)
        (eval_substituteVariables rho replacement right)
  | .mul left right => by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _
          (eval_substituteVariables rho replacement left))
        (Q'.mul_eqv_congr_left _ _ _
          (eval_substituteVariables rho replacement right))
  | .neg value =>
      Q'.neg_eqv_congr _ _
        (eval_substituteVariables rho replacement value)
  | .pow value power =>
      qpow_eqv_congr
        (eval_substituteVariables rho replacement value) power

/-! ## 3. The genuine coupled action as a forty-coordinate polynomial -/

private def spatialQuadraticTemplate : PolyExpr :=
  .add
    (.mul (.const 2) (.mul (.var 0) (.var 0)))
    (.add
      (.mul (.const 2) (.mul (.var 1) (.var 1)))
      (.add
        (.mul (.const 2) (.mul (.var 2) (.var 2)))
        (.add
          (.mul (.const 2) (.mul (.var 3) (.var 3)))
          (.add
            (.mul (.const 2) (.mul (.var 4) (.var 4)))
            (.add
              (.mul (.const (-2)) (.mul (.var 0) (.var 4)))
              (.add
                (.mul (.const (-2)) (.mul (.var 1) (.var 2)))
                (.add
                  (.mul (.const (-2)) (.mul (.var 1) (.var 3)))
                  (.add
                    (.mul (.const 2) (.mul (.var 1) (.var 4)))
                    (.add
                      (.mul (.const 2) (.mul (.var 2) (.var 3)))
                      (.add
                        (.mul (.const (-2)) (.mul (.var 2) (.var 4)))
                        (.mul (.const (-2))
                          (.mul (.var 3) (.var 4)))))))))))))

private def kineticQuadraticTemplate : PolyExpr :=
  let x0 := .var 0; let x1 := .var 1; let x2 := .var 2
  let x3 := .var 3; let x4 := .var 4
  .add (.mul (.const 10) (.mul x0 x0))
    (.add (.mul (.const 10) (.mul x1 x1))
      (.add (.mul (.const 10) (.mul x2 x2))
        (.add (.mul (.const 10) (.mul x3 x3))
          (.add (.mul (.const 10) (.mul x4 x4))
            (.add (.mul (.const 2) (.mul x0 x1))
              (.add (.mul (.const (-4)) (.mul x0 x2))
                (.add (.mul (.const (-2)) (.mul x0 x3))
                  (.add (.mul (.const (-8)) (.mul x0 x4))
                    (.add (.mul (.const (-10)) (.mul x1 x2))
                      (.add (.mul (.const (-8)) (.mul x1 x3))
                        (.add (.mul (.const 10) (.mul x1 x4))
                          (.add (.mul (.const 10) (.mul x2 x3))
                            (.add (.mul (.const (-8)) (.mul x2 x4))
                              (.mul (.const (-10))
                                (.mul x3 x4)))))))))))))))

/-- Imaginary coordinate `color` of source holonomy `holonomy`. -/
def sourceImaginaryVariable (color : Fin 3) (holonomy : Nat) : PolyExpr :=
  .var (4 * holonomy + color.val + 1)

/-- Imaginary coordinate `color` of target holonomy `holonomy`. -/
def targetImaginaryVariable (color : Fin 3) (holonomy : Nat) : PolyExpr :=
  .var (20 + 4 * holonomy + color.val + 1)

def sourceReplacement (color : Fin 3) (index : Nat) : PolyExpr :=
  sourceImaginaryVariable color index

def targetReplacement (color : Fin 3) (index : Nat) : PolyExpr :=
  targetImaginaryVariable color index

def differenceReplacement (color : Fin 3) (index : Nat) : PolyExpr :=
  .add (sourceReplacement color index)
    (.neg (targetReplacement color index))

def sourceSpatialPolynomial (color : Fin 3) : RatPoly :=
  exprToRatPoly
    (substituteVariables (sourceReplacement color)
      spatialQuadraticTemplate)

def targetSpatialPolynomial (color : Fin 3) : RatPoly :=
  exprToRatPoly
    (substituteVariables (targetReplacement color)
      spatialQuadraticTemplate)

def differenceKineticPolynomial (color : Fin 3) : RatPoly :=
  exprToRatPoly
    (substituteVariables (differenceReplacement color)
      kineticQuadraticTemplate)

def colorCoupledActionPolynomial (color : Fin 3) : RatPoly :=
  polyAdd
    (polySmul oneOver96 (differenceKineticPolynomial color))
    (polyAdd
      (polySmul oneOver8 (sourceSpatialPolynomial color))
      (polySmul oneOver8 (targetSpatialPolynomial color)))

def compactCoupledBF4ActionPolynomial : RatPoly :=
  lieColorIndices.foldr
    (fun color total =>
      polyAdd (colorCoupledActionPolynomial color) total)
    polyZero

/-- Extract the source Lie-algebra coordinates from a forty-coordinate
source/target quaternion environment. -/
def sourceLieEnvironment (rho : Nat → Q') :
    BF4LieConfiguration :=
  fun color holonomy =>
    rho (4 * holonomy.val + color.val + 1)

/-- Extract the target Lie-algebra coordinates from a forty-coordinate
source/target quaternion environment. -/
def targetLieEnvironment (rho : Nat → Q') :
    BF4LieConfiguration :=
  fun color holonomy =>
    rho (20 + 4 * holonomy.val + color.val + 1)

private theorem source_substitution_value
    (rho : Nat → Q') (color : Fin 3) :
    RingNormaliser.eval rho
        (substituteVariables (sourceReplacement color)
          spatialQuadraticTemplate) ≈
      spatialQuadratic (sourceLieEnvironment rho color) := by
  refine Q'.eqv_trans _ _ _
    (eval_substituteVariables rho (sourceReplacement color)
      spatialQuadraticTemplate) ?_
  unfold spatialQuadratic vectorEnvironment sourceLieEnvironment
  simp only [spatialQuadraticTemplate, RingNormaliser.eval,
    sourceReplacement, sourceImaginaryVariable]
  exact Q'.eqv_refl _

private theorem target_substitution_value
    (rho : Nat → Q') (color : Fin 3) :
    RingNormaliser.eval rho
        (substituteVariables (targetReplacement color)
          spatialQuadraticTemplate) ≈
      spatialQuadratic (targetLieEnvironment rho color) := by
  refine Q'.eqv_trans _ _ _
    (eval_substituteVariables rho (targetReplacement color)
      spatialQuadraticTemplate) ?_
  unfold spatialQuadratic vectorEnvironment targetLieEnvironment
  simp only [spatialQuadraticTemplate, RingNormaliser.eval,
    targetReplacement, targetImaginaryVariable]
  exact Q'.eqv_refl _

private theorem difference_substitution_value
    (rho : Nat → Q') (color : Fin 3) :
    RingNormaliser.eval rho
        (substituteVariables (differenceReplacement color)
          kineticQuadraticTemplate) ≈
      kineticQuadratic24
        (vectorSub
          (sourceLieEnvironment rho color)
          (targetLieEnvironment rho color)) := by
  refine Q'.eqv_trans _ _ _
    (eval_substituteVariables rho (differenceReplacement color)
      kineticQuadraticTemplate) ?_
  unfold kineticQuadratic24 vectorEnvironment vectorSub
    sourceLieEnvironment targetLieEnvironment
  simp only [kineticQuadraticTemplate, RingNormaliser.eval,
    differenceReplacement, sourceReplacement, targetReplacement,
    sourceImaginaryVariable, targetImaginaryVariable]
  exact Q'.eqv_refl _

private theorem eval_colorCoupledActionPolynomial
    (rho : Nat → Q') (color : Fin 3) :
    evalRatPoly rho (colorCoupledActionPolynomial color) ≈
      coupledBF4Action
        (sourceLieEnvironment rho color)
        (targetLieEnvironment rho color) := by
  unfold colorCoupledActionPolynomial coupledBF4Action
  refine Q'.eqv_trans _ _ _
    (evalRatPoly_add rho _ _) ?_
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _
      (evalRatPoly_smul rho oneOver96
        (differenceKineticPolynomial color))
      (Q'.mul_eqv_congr_left oneOver96 _ _
        (Q'.eqv_trans _ _ _
          (eval_exprToRatPoly rho _)
          (difference_substitution_value rho color))))
    (Q'.eqv_trans _ _ _
      (evalRatPoly_add rho _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _
          (evalRatPoly_smul rho oneOver8
            (sourceSpatialPolynomial color))
          (Q'.mul_eqv_congr_left oneOver8 _ _
            (Q'.eqv_trans _ _ _
              (eval_exprToRatPoly rho _)
              (source_substitution_value rho color))))
        (Q'.eqv_trans _ _ _
          (evalRatPoly_smul rho oneOver8
            (targetSpatialPolynomial color))
          (Q'.mul_eqv_congr_left oneOver8 _ _
            (Q'.eqv_trans _ _ _
              (eval_exprToRatPoly rho _)
              (target_substitution_value rho color))))))

/-- The forty-coordinate polynomial evaluates to the exact three-colour
coupled BF4 action used by the Feynman--Kac/Mehler kernel. -/
theorem eval_compactCoupledBF4ActionPolynomial
    (rho : Nat → Q') :
    evalRatPoly rho compactCoupledBF4ActionPolynomial ≈
      coupledBF4LieAction
        (sourceLieEnvironment rho)
        (targetLieEnvironment rho) := by
  have fold_semantics :
      ∀ colors : List (Fin 3),
        evalRatPoly rho
            (colors.foldr
              (fun color total =>
                polyAdd (colorCoupledActionPolynomial color) total)
              polyZero) ≈
          colors.foldr
            (fun color total =>
              coupledBF4Action
                  (sourceLieEnvironment rho color)
                  (targetLieEnvironment rho color) +
                total)
            0 := by
    intro colors
    induction colors with
    | nil => exact Q'.eqv_refl 0
    | cons color rest ih =>
        exact Q'.eqv_trans _ _ _
          (evalRatPoly_add rho _ _)
          (Q'.add_eqv_congr'
            (eval_colorCoupledActionPolynomial rho color) ih)
  exact fold_semantics lieColorIndices

/-! ## 4. Source/target geometric wavefunctions and Taylor coefficients -/

/-- Shift every monomial by `offset` leading zero exponents. -/
def shiftPolynomial (offset : Nat) (polynomial : RatPoly) : RatPoly :=
  polynomial.map fun term =>
    (List.replicate offset 0 ++ term.1, term.2)

def sourceGeometricWavefunction
    (state :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    RatPoly :=
  geometricBF4WavefunctionOfState state

def targetGeometricWavefunction
    (state :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    RatPoly :=
  shiftPolynomial 20 (geometricBF4WavefunctionOfState state)

/-- Recurrence for the polynomial Taylor term `(-A)^k/k!`. -/
def negativeExponentialPolynomialTerm (action : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | k + 1 =>
      polySmul (-Q'.invSucc k)
        (polyMul (negativeExponentialPolynomialTerm action k) action)

theorem eval_negativeExponentialPolynomialTerm
    (rho : Nat → Q') (action : RatPoly) :
    ∀ k : Nat,
      evalRatPoly rho
          (negativeExponentialPolynomialTerm action k) ≈
        ExpNeg.term (evalRatPoly rho action) k
  | 0 => evalRatPoly_one rho
  | k + 1 => by
      refine Q'.eqv_trans _ _ _
        (evalRatPoly_smul rho (-Q'.invSucc k)
          (polyMul
            (negativeExponentialPolynomialTerm action k)
            action)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (-Q'.invSucc k) _ _
          (evalRatPoly_mul rho
            (negativeExponentialPolynomialTerm action k)
            action)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (-Q'.invSucc k) _ _
          (Q'.mul_eqv_congr_right _ _ _
            (eval_negativeExponentialPolynomialTerm
              rho action k))) ?_
      show
        (-Q'.invSucc k) *
            (ExpNeg.term (evalRatPoly rho action) k *
              evalRatPoly rho action) ≈
          ExpNeg.term (evalRatPoly rho action) k *
            ((-(evalRatPoly rho action)) *
              Q'.invSucc k)
      refine Q'.eqv_trans _
        ((ExpNeg.term (evalRatPoly rho action) k *
            evalRatPoly rho action) *
          (-Q'.invSucc k))
        _ (Q'.mul_comm_eqv _ _) ?_
      refine Q'.eqv_trans _
        (ExpNeg.term (evalRatPoly rho action) k *
          (evalRatPoly rho action *
            (-Q'.invSucc k)))
        _ (Q'.mul_assoc_eqv _ _ _) ?_
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_neg_eqv
            (evalRatPoly rho action)
            (Q'.invSucc k))
          (Q'.eqv_symm
            (Q'.neg_mul_eqv
              (evalRatPoly rho action)
              (Q'.invSucc k))))

private theorem abs_neg_nonnegative_le
    (value : Q') (hvalue : (0 : Q') ≤ value) :
    Q'.abs (-value) ≤ value := by
  apply Q'.abs_le
  · exact Q'.le_refl' (-value)
  · have hneg : -value ≤ (0 : Q') := by
      exact Q'.le_trans' _ _ _
        (Q'.neg_le_neg hvalue)
        (Q'.le_of_eqv
          (Q'.neg_eqv_congr 0 0
            (Q'.eqv_refl 0)))
    exact Q'.le_trans' _ _ _ hneg hvalue

theorem negativeExponentialPolynomialTerm_l1_le
    (action : RatPoly) :
    ∀ k : Nat,
      polynomialCoefficientL1
          (negativeExponentialPolynomialTerm action k) ≤
        ExpNeg.termAbs
          (polynomialCoefficientL1 action) k
  | 0 => by
      change Q'.abs (1 : Q') + 0 ≤ 1
      decide
  | k + 1 => by
      let inverse := Q'.invSucc k
      let previous :=
        negativeExponentialPolynomialTerm action k
      let actionL1 := polynomialCoefficientL1 action
      have hinverse0 : (0 : Q') ≤ inverse :=
        Q'.invSucc_nonneg k
      have hprevious0 :
          (0 : Q') ≤ polynomialCoefficientL1 previous :=
        polynomialCoefficientL1_nonnegative previous
      have haction0 : (0 : Q') ≤ actionL1 :=
        polynomialCoefficientL1_nonnegative action
      have hproduct0 :
          (0 : Q') ≤
            polynomialCoefficientL1
              (polyMul previous action) :=
        polynomialCoefficientL1_nonnegative _
      have hscale :=
        polynomialCoefficientL1_smul_le
          (-inverse) (polyMul previous action)
      have habs : Q'.abs (-inverse) ≤ inverse :=
        abs_neg_nonnegative_le inverse hinverse0
      have hmul :=
        polynomialCoefficientL1_mul_le previous action
      have hstep1 :
          polynomialCoefficientL1
              (polySmul (-inverse)
                (polyMul previous action)) ≤
            inverse *
              (polynomialCoefficientL1 previous *
                actionL1) := by
        exact Q'.le_trans' _ _ _ hscale
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right
              (Q'.abs (-inverse)) inverse
              (polynomialCoefficientL1
                (polyMul previous action))
              habs hproduct0)
            (Q'.mul_le_mul_of_nonneg_left
              (polynomialCoefficientL1
                (polyMul previous action))
              (polynomialCoefficientL1 previous *
                actionL1)
              inverse hmul hinverse0))
      have hinduction :=
        negativeExponentialPolynomialTerm_l1_le
          action k
      have hstep2 :
          inverse *
              (polynomialCoefficientL1 previous *
                actionL1) ≤
            inverse *
              (ExpNeg.termAbs actionL1 k *
                actionL1) :=
        Q'.mul_le_mul_of_nonneg_left _ _ inverse
          (Q'.mul_le_mul_of_nonneg_right _ _ actionL1
            hinduction haction0)
          hinverse0
      exact Q'.le_trans' _ _ _ hstep1
        (Q'.le_trans' _ _ _ hstep2
          (Q'.le_of_eqv
            (Q'.eqv_trans _ _ _
              (Q'.mul_comm_eqv inverse
                (ExpNeg.termAbs actionL1 k *
                  actionL1))
              (Q'.mul_assoc_eqv
                (ExpNeg.termAbs actionL1 k)
                actionL1 inverse))))

/-- Exact `k`-th double-Haar coefficient
`∫∫ ψ_left(x) ψ_right(y) (-A(x,y))^k/k! dx dy`. -/
def geometricMehlerTaylorTerm
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (k : Nat) : Q' :=
  tenfoldHaar
    (polyMul
      (polyMul
        (sourceGeometricWavefunction left)
        (targetGeometricWavefunction right))
      (negativeExponentialPolynomialTerm
        compactCoupledBF4ActionPolynomial k))

/-- The exact source/target polynomial multiplying every kernel Taylor term. -/
def geometricBoundaryProduct
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    RatPoly :=
  polyMul
    (sourceGeometricWavefunction left)
    (targetGeometricWavefunction right)

def geometricBoundaryL1
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    Q' :=
  polynomialCoefficientL1
    (geometricBoundaryProduct left right)

def compactCoupledBF4ActionL1 : Q' :=
  polynomialCoefficientL1
    compactCoupledBF4ActionPolynomial

theorem geometricBoundaryL1_nonnegative
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    (0 : Q') ≤ geometricBoundaryL1 left right :=
  polynomialCoefficientL1_nonnegative _

theorem compactCoupledBF4ActionL1_nonnegative :
    (0 : Q') ≤ compactCoupledBF4ActionL1 :=
  polynomialCoefficientL1_nonnegative _

/-- Quantitative all-order domination of the exact double-Haar Taylor
coefficient by one scalar factorial series. -/
theorem geometricMehlerTaylorTerm_abs_le
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (k : Nat) :
    Q'.abs (geometricMehlerTaylorTerm left right k) ≤
      geometricBoundaryL1 left right *
        ExpNeg.termAbs compactCoupledBF4ActionL1 k := by
  let boundary := geometricBoundaryProduct left right
  let kernelTerm :=
    negativeExponentialPolynomialTerm
      compactCoupledBF4ActionPolynomial k
  exact Q'.le_trans' _ _ _
    (quaternionHaar_abs_le_coefficientL1 10
      (polyMul boundary kernelTerm))
    (Q'.le_trans' _ _ _
      (polynomialCoefficientL1_mul_le
        boundary kernelTerm)
      (Q'.mul_le_mul_of_nonneg_left
        (polynomialCoefficientL1 kernelTerm)
        (ExpNeg.termAbs
          compactCoupledBF4ActionL1 k)
        (polynomialCoefficientL1 boundary)
        (negativeExponentialPolynomialTerm_l1_le
          compactCoupledBF4ActionPolynomial k)
        (polynomialCoefficientL1_nonnegative boundary)))

/-- The exact `N`-term double-Haar Taylor approximation. -/
def geometricMehlerTaylorPartial
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    Nat → Q'
  | 0 => 0
  | N + 1 =>
      geometricMehlerTaylorPartial left right N +
        geometricMehlerTaylorTerm left right N

/-! ## 5. Constructive-real convergence of the double-Haar projection -/

/-- The scaled factorial majorant block for Taylor orders `[start,start+d)`. -/
def scaledTaylorBlockAbs
    (scale actionL1 : Q') (start : Nat) : Nat → Q'
  | 0 => 0
  | d + 1 =>
      scaledTaylorBlockAbs scale actionL1 start d +
        scale * ExpNeg.termAbs actionL1 (start + d)

theorem scaledTaylorBlockAbs_nonnegative
    (scale actionL1 : Q')
    (hscale : (0 : Q') ≤ scale)
    (haction : (0 : Q') ≤ actionL1)
    (start : Nat) :
    ∀ d : Nat,
      (0 : Q') ≤
        scaledTaylorBlockAbs scale actionL1 start d
  | 0 => Q'.le_refl' 0
  | d + 1 =>
      Q'.zero_le_add _ _
        (scaledTaylorBlockAbs_nonnegative
          scale actionL1 hscale haction start d)
        (Q'.mul_nonneg _ _ hscale
          (ExpNeg.termAbs_nonneg
            actionL1 haction (start + d)))

theorem scaledTaylorBlockAbs_eq
    (scale actionL1 : Q') (start : Nat) :
    ∀ d : Nat,
      scaledTaylorBlockAbs scale actionL1 start d ≈
        scale * ExpNeg.blockAbs actionL1 start d
  | 0 =>
      Q'.eqv_symm (Q'.mul_zero_eqv scale)
  | d + 1 => by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _
          (scale * ExpNeg.termAbs actionL1 (start + d))
          (scaledTaylorBlockAbs_eq
            scale actionL1 start d)) ?_
      exact Q'.eqv_symm
        (Q'.mul_add_eqv scale
          (ExpNeg.blockAbs actionL1 start d)
          (ExpNeg.termAbs actionL1 (start + d)))

private theorem geometricMehlerTaylorTerm_two_sided
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (k : Nat) :
    geometricMehlerTaylorTerm left right k ≤
        geometricBoundaryL1 left right *
          ExpNeg.termAbs compactCoupledBF4ActionL1 k ∧
      (-(geometricMehlerTaylorTerm left right k)) ≤
        geometricBoundaryL1 left right *
          ExpNeg.termAbs compactCoupledBF4ActionL1 k := by
  have h :=
    geometricMehlerTaylorTerm_abs_le left right k
  exact
    ⟨Q'.le_trans' _ _ _
      (Q'.le_abs_self
        (geometricMehlerTaylorTerm left right k)) h,
     Q'.le_trans' _ _ _
      (Q'.neg_le_abs
        (geometricMehlerTaylorTerm left right k)) h⟩

private theorem geometricMehlerTaylorPartial_block_upper
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (start : Nat) :
    ∀ d : Nat,
      geometricMehlerTaylorPartial left right (start + d) ≤
        geometricMehlerTaylorPartial left right start +
          scaledTaylorBlockAbs
            (geometricBoundaryL1 left right)
            compactCoupledBF4ActionL1 start d
  | 0 => by
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.le_refl' 0)
  | d + 1 => by
      have hinduction :=
        geometricMehlerTaylorPartial_block_upper
          left right start d
      have hterm :=
        (geometricMehlerTaylorTerm_two_sided
          left right (start + d)).1
      change
        geometricMehlerTaylorPartial left right (start + d) +
            geometricMehlerTaylorTerm left right (start + d) ≤
          geometricMehlerTaylorPartial left right start +
            (scaledTaylorBlockAbs
                (geometricBoundaryL1 left right)
                compactCoupledBF4ActionL1 start d +
              geometricBoundaryL1 left right *
                ExpNeg.termAbs compactCoupledBF4ActionL1
                  (start + d))
      exact Q'.le_trans' _ _ _
        (ExpNeg.add_le_add2 hinduction hterm)
        (Q'.le_of_eqv
          (Q'.add_assoc_eqv
            (geometricMehlerTaylorPartial left right start)
            (scaledTaylorBlockAbs
              (geometricBoundaryL1 left right)
              compactCoupledBF4ActionL1 start d)
            (geometricBoundaryL1 left right *
              ExpNeg.termAbs compactCoupledBF4ActionL1
                (start + d))))

private theorem geometricMehlerTaylorPartial_block_lower
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (start : Nat) :
    ∀ d : Nat,
      geometricMehlerTaylorPartial left right start ≤
        geometricMehlerTaylorPartial left right (start + d) +
          scaledTaylorBlockAbs
            (geometricBoundaryL1 left right)
            compactCoupledBF4ActionL1 start d
  | 0 => by
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.le_refl' 0)
  | d + 1 => by
      have hinduction :=
        geometricMehlerTaylorPartial_block_lower
          left right start d
      have hnegative :=
        (geometricMehlerTaylorTerm_two_sided
          left right (start + d)).2
      have hpair :
          (0 : Q') ≤
            geometricMehlerTaylorTerm left right (start + d) +
              geometricBoundaryL1 left right *
                ExpNeg.termAbs compactCoupledBF4ActionL1
                  (start + d) := by
        exact Q'.le_trans' _ _ _
          (Q'.ge_of_eqv
            (Q'.neg_add_self_eqv
              (geometricMehlerTaylorTerm left right
                (start + d))))
          (Q'.le_trans' _ _ _
            (Q'.add_le_add_right
              (-(geometricMehlerTaylorTerm left right
                (start + d)))
              (geometricBoundaryL1 left right *
                ExpNeg.termAbs compactCoupledBF4ActionL1
                  (start + d))
              (geometricMehlerTaylorTerm left right
                (start + d))
              hnegative)
            (Q'.le_of_eqv
              (Q'.add_comm_eqv _ _)))
      refine Q'.le_trans' _ _ _ hinduction ?_
      exact Q'.le_trans' _ _ _
        (Q'.add_le_self_of_nonneg
          (geometricMehlerTaylorPartial left right (start + d) +
            scaledTaylorBlockAbs
              (geometricBoundaryL1 left right)
              compactCoupledBF4ActionL1 start d)
          (geometricMehlerTaylorTerm left right (start + d) +
            geometricBoundaryL1 left right *
              ExpNeg.termAbs compactCoupledBF4ActionL1
                (start + d))
          hpair)
        (Q'.le_of_eqv
          (Q'.add_swap_inner
            (geometricMehlerTaylorPartial left right (start + d))
            (scaledTaylorBlockAbs
              (geometricBoundaryL1 left right)
              compactCoupledBF4ActionL1 start d)
            (geometricMehlerTaylorTerm left right (start + d))
            (geometricBoundaryL1 left right *
              ExpNeg.termAbs compactCoupledBF4ActionL1
                (start + d))))

private theorem epsilon_mul_invSucc_pos
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (n : Nat) :
    (0 : Q') < epsilon * Q'.invSucc n := by
  show (0 : Int) * ((epsilon * Q'.invSucc n).den : Int) <
      (epsilon * Q'.invSucc n).num * ((0 : Q').den : Int)
  rw [Int.zero_mul]
  have hepsilonNum : (0 : Int) < epsilon.num := by
    have h : (0 : Int) * (epsilon.den : Int) <
        epsilon.num * ((0 : Q').den : Int) := hepsilon
    rw [Int.zero_mul] at h
    have h' : (0 : Int) < epsilon.num * (1 : Int) := h
    rwa [Int.mul_one] at h'
  change (0 : Int) < (epsilon.num * 1) * (1 : Int)
  simpa only [Int.mul_one] using hepsilonNum

/-- Type-level modulus for the exact double-Haar Taylor sequence. -/
def geometricMehlerTaylorModulus
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (epsilon : Q') : Nat :=
  let scale := geometricBoundaryL1 left right
  let delta := epsilon * Q'.invSucc scale.num.toNat
  max
    (halfRatioCutoff compactCoupledBF4ActionL1)
    (ExpNeg.termAbsModulus
      compactCoupledBF4ActionL1
      (HalfPow.half * delta))

theorem geometricMehlerTaylorPartial_cauchy
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (m n : Nat)
    (hm : geometricMehlerTaylorModulus left right epsilon ≤ m)
    (hn : geometricMehlerTaylorModulus left right epsilon ≤ n) :
    geometricMehlerTaylorPartial left right m ≤
          geometricMehlerTaylorPartial left right n + epsilon ∧
      geometricMehlerTaylorPartial left right n ≤
          geometricMehlerTaylorPartial left right m + epsilon := by
  let scale := geometricBoundaryL1 left right
  let actionL1 := compactCoupledBF4ActionL1
  let delta := epsilon * Q'.invSucc scale.num.toNat
  have hscale0 : (0 : Q') ≤ scale :=
    geometricBoundaryL1_nonnegative left right
  have haction0 : (0 : Q') ≤ actionL1 :=
    compactCoupledBF4ActionL1_nonnegative
  have hepsilon0 : (0 : Q') ≤ epsilon :=
    Q'.le_of_lt hepsilon
  have hdeltaPos : (0 : Q') < delta :=
    epsilon_mul_invSucc_pos epsilon hepsilon
      scale.num.toNat
  have hdelta0 : (0 : Q') ≤ delta :=
    Q'.le_of_lt hdeltaPos
  have hhalfDeltaPos :
      (0 : Q') < HalfPow.half * delta :=
    ExpNeg.half_mul_pos delta hdeltaPos
  have dir :
      ∀ smaller larger : Nat,
        geometricMehlerTaylorModulus left right epsilon ≤ smaller →
        smaller ≤ larger →
        geometricMehlerTaylorPartial left right larger ≤
              geometricMehlerTaylorPartial left right smaller + epsilon ∧
          geometricMehlerTaylorPartial left right smaller ≤
              geometricMehlerTaylorPartial left right larger + epsilon := by
    intro smaller larger hsmaller horder
    obtain ⟨d, rfl⟩ :=
      Nat.exists_eq_add_of_le horder
    have hcut :
        halfRatioCutoff actionL1 ≤ smaller :=
      Nat.le_trans
        (Nat.le_max_left _ _)
        hsmaller
    have hterm :
        ExpNeg.termAbs actionL1 smaller ≤
          HalfPow.half * delta :=
      ExpNeg.termAbs_le_of_modulus_le
        actionL1 (HalfPow.half * delta)
        haction0 hhalfDeltaPos smaller
        (Nat.le_trans
          (Nat.le_max_right _ _)
          hsmaller)
    have htail :
        ExpNeg.blockAbs actionL1 smaller d ≤ delta :=
      ExpNeg.expNeg_tail_bound
        actionL1 haction0 delta hdelta0
        smaller hcut hterm d
    have hscaled :
        scaledTaylorBlockAbs scale actionL1 smaller d ≤
          epsilon := by
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (scaledTaylorBlockAbs_eq
              scale actionL1 smaller d))
          (Q'.mul_le_mul_of_nonneg_left
            (ExpNeg.blockAbs actionL1 smaller d)
            delta scale htail hscale0))
        (ExpNeg.mul_le_of_mul_invSucc_toNat
          scale epsilon hscale0 hepsilon0)
    exact
      ⟨Q'.le_trans' _ _ _
        (geometricMehlerTaylorPartial_block_upper
          left right smaller d)
        (Q'.add_le_add_left
          (geometricMehlerTaylorPartial left right smaller)
          (scaledTaylorBlockAbs scale actionL1 smaller d)
          epsilon hscaled),
       Q'.le_trans' _ _ _
        (geometricMehlerTaylorPartial_block_lower
          left right smaller d)
        (Q'.add_le_add_left
          (geometricMehlerTaylorPartial left right (smaller + d))
          (scaledTaylorBlockAbs scale actionL1 smaller d)
          epsilon hscaled)⟩
  rcases Nat.le_total m n with hmn | hnm
  · exact
      ⟨(dir m n hm hmn).2,
       (dir m n hm hmn).1⟩
  · exact
      ⟨(dir n m hn hnm).1,
       (dir n m hn hnm).2⟩

/-- The genuine constructive-real double-Haar endpoint coefficient of the
coupled BF4 Mehler kernel between two geometric all-spin boundary states. -/
def geometricMehlerHaarCoefficient
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    CReal where
  approx :=
    geometricMehlerTaylorPartial left right
  cauchy := by
    intro epsilon hepsilon
    exact
      ⟨geometricMehlerTaylorModulus left right epsilon,
       fun m n hm hn =>
        geometricMehlerTaylorPartial_cauchy
          left right epsilon hepsilon m n hm hn⟩

@[simp] theorem geometricMehlerHaarCoefficient_approx
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling)
    (N : Nat) :
    (geometricMehlerHaarCoefficient left right).approx N =
      geometricMehlerTaylorPartial left right N := rfl

/-! ## 6. Corrected geometric transform package -/

/-- Exact fivefold-Haar pairing of the two contracted geometric boundary
wavefunctions.  Unlike the earlier faithful-character coding, this definition
does not assert pairwise orthogonality of distinct face labelings. -/
def geometricFivefoldHaarPairing
    (left right :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling) :
    Q' :=
  fivefoldHaarInner
    (geometricBF4WavefunctionOfState left)
    (geometricBF4WavefunctionOfState right)

/-- A faithful interface for the geometric BF4 boundary transform and its
raw coupled-Mehler projection.  Its convergence rate is stored as data.  The
separate partition-positivity theorem needed to divide by the vacuum row is
deliberately not a field here: this package is the raw double-Haar transform,
not a falsely normalized Markov kernel. -/
structure GeometricBF4DoubleHaarTransform : Type where
  wavefunction :
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
      RatPoly
  haarPairing :
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
        Q'
  rawMehlerCoefficient :
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
        CReal
  convergenceModulus :
    YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling →
        Q' → Nat
  wavefunction_exact :
    ∀ state,
      wavefunction state =
        geometricBF4WavefunctionOfState state
  haarPairing_exact :
    ∀ left right,
      haarPairing left right =
        fivefoldHaarInner
          (geometricBF4WavefunctionOfState left)
          (geometricBF4WavefunctionOfState right)
  rawMehler_approx_exact :
    ∀ left right N,
      (rawMehlerCoefficient left right).approx N =
        geometricMehlerTaylorPartial left right N
  convergenceModulus_sound :
    ∀ left right epsilon,
      (0 : Q') < epsilon →
      ∀ m n,
        convergenceModulus left right epsilon ≤ m →
        convergenceModulus left right epsilon ≤ n →
        (rawMehlerCoefficient left right).approx m ≤
              (rawMehlerCoefficient left right).approx n + epsilon ∧
          (rawMehlerCoefficient left right).approx n ≤
              (rawMehlerCoefficient left right).approx m + epsilon

/-- The corrected geometric, all-spin, coupled-kernel transform is inhabited
without orthogonality assumptions or rationalizing the exponential. -/
def geometricBF4DoubleHaarTransform :
    GeometricBF4DoubleHaarTransform where
  wavefunction :=
    geometricBF4WavefunctionOfState
  haarPairing :=
    geometricFivefoldHaarPairing
  rawMehlerCoefficient :=
    geometricMehlerHaarCoefficient
  convergenceModulus :=
    geometricMehlerTaylorModulus
  wavefunction_exact := by
    intro state
    rfl
  haarPairing_exact := by
    intro left right
    rfl
  rawMehler_approx_exact := by
    intro left right N
    rfl
  convergenceModulus_sound := by
    intro left right epsilon hepsilon m n hm hn
    exact geometricMehlerTaylorPartial_cauchy
      left right epsilon hepsilon m n hm hn

/-- The vacuum zeroth coefficient is exactly one. -/
theorem geometricMehlerTaylorTerm_vacuum_zero :
    geometricMehlerTaylorTerm (fun _ => 0) (fun _ => 0) 0 ≈ 1 := by
  have hsource :
      sourceGeometricWavefunction (fun _ => 0) =
        [(List.replicate 20 0, 1)] := by
    decide
  have htarget :
      targetGeometricWavefunction (fun _ => 0) =
        [(List.replicate 40 0, 1)] := by
    decide
  rw [geometricMehlerTaylorTerm, hsource, htarget]
  decide

end YMGap.Continuum.BF4GeometricHaarMehlerProjection

#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.tenfoldHaar_one
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.eval_exprToRatPoly
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.eval_substituteVariables
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.eval_compactCoupledBF4ActionPolynomial
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.sphereMoment4_le_one
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.quaternionHaar_abs_le_coefficientL1
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.polynomialCoefficientL1_mul_le
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.eval_negativeExponentialPolynomialTerm
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.geometricMehlerTaylorTerm_abs_le
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.geometricMehlerTaylorPartial_cauchy
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.geometricMehlerHaarCoefficient
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.geometricBF4DoubleHaarTransform
#print axioms YMGap.Continuum.BF4GeometricHaarMehlerProjection.geometricMehlerTaylorTerm_vacuum_zero
