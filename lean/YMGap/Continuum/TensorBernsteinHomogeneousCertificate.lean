/-
# Homogeneous tensor-Bernstein certificate kernel

An exact tensor Bernstein table becomes a polynomial in four independent
nonnegative homogeneous coordinates

  `x₀^i x₁^(d₀-i) y₀^j y₁^(d₁-j)`.

This module supplies the small trusted consumer used by the lower-six local
second-flux certificates.  Concrete tables are closed integer data.  Their
coefficient signs and their substituted physical polynomial identities are
checked by kernel reduction through the proved eager ring normaliser.
-/

import YMGap.Continuum.CoreBResidualSimplex
import YMGap.Continuum.BernsteinMonomialReconstruction

namespace YMGap.Continuum.TensorBernsteinHomogeneousCertificate

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG
open YMGap.Continuum.CoreBResidualSimplex

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr₂ {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## Closed tensor-table syntax -/

/-- One homogeneous tensor-Bernstein monomial.  The supplied table entry is
the normalized Bernstein coefficient after a common positive denominator has
been cleared; the two binomial factors are part of the basis. -/
def homogeneousTensorTerm
    (degreeX degreeY i j : Nat) (coefficient : Int) :
    RingNormaliser.PolyExpr :=
  .mul
    (.const (coefficient *
      Int.ofNat (binom degreeX i * binom degreeY j)))
    (.mul
      (.mul (.pow (.var 0) i) (.pow (.var 1) (degreeX - i)))
      (.mul (.pow (.var 2) j) (.pow (.var 3) (degreeY - j))))

private def homogeneousTensorRow
    (degreeX degreeY i : Nat) : Nat → List Int →
    RingNormaliser.PolyExpr
  | _, [] => .const 0
  | j, coefficient :: rest =>
      .add (homogeneousTensorTerm degreeX degreeY i j coefficient)
        (homogeneousTensorRow degreeX degreeY i (j + 1) rest)

private def homogeneousTensorRows
    (degreeX degreeY : Nat) : Nat → List (List Int) →
    RingNormaliser.PolyExpr
  | _, [] => .const 0
  | i, row :: rest =>
      .add (homogeneousTensorRow degreeX degreeY i 0 row)
        (homogeneousTensorRows degreeX degreeY (i + 1) rest)

/-- Reflect a dense row-major integer Bernstein table into its homogeneous
four-variable polynomial. -/
def homogeneousTensorExpr
    (degreeX degreeY : Nat) (rows : List (List Int)) :
    RingNormaliser.PolyExpr :=
  homogeneousTensorRows degreeX degreeY 0 rows

/-- A consecutive block of rows in a homogeneous tensor-Bernstein table.
The explicit starting row lets large certificates check their substituted
polynomial identities blockwise instead of normalizing the entire table in
one kernel reduction. -/
def homogeneousTensorBlockExpr
    (degreeX degreeY startRow : Nat) (rows : List (List Int)) :
    RingNormaliser.PolyExpr :=
  homogeneousTensorRows degreeX degreeY startRow rows

/-- Closed Boolean sign check for one integer row. -/
def IntegerRowNonnegative : List Int → Bool
  | [] => true
  | coefficient :: rest =>
      decide ((0 : Int) ≤ coefficient) && IntegerRowNonnegative rest

/-- Closed Boolean sign check for a dense tensor table. -/
def IntegerRowsNonnegative : List (List Int) → Bool
  | [] => true
  | row :: rest =>
      IntegerRowNonnegative row && IntegerRowsNonnegative rest

private theorem ofInt_nonnegative {coefficient : Int}
    (hcoefficient : (0 : Int) ≤ coefficient) :
    (0 : Q') ≤ Q'.ofInt coefficient := by
  change (0 : Int) * (1 : Int) ≤ coefficient * (1 : Int)
  simpa using hcoefficient

private theorem rnqpow_nonnegative {value : Q'}
    (hvalue : (0 : Q') ≤ value) : ∀ exponent,
    (0 : Q') ≤ RingNormaliser.qpow value exponent
  | 0 => by
      change (0 : Q') ≤ (1 : Q')
      decide
  | exponent + 1 =>
      Q'.mul_nonneg _ _ (rnqpow_nonnegative hvalue exponent) hvalue

private theorem eval_homogeneousTensorTerm_nonnegative
    (degreeX degreeY i j : Nat) (coefficient : Int)
    (rho : Nat → Q') (hrho : ∀ index, (0 : Q') ≤ rho index)
    (hcoefficient : (0 : Int) ≤ coefficient) :
    (0 : Q') ≤ RingNormaliser.eval rho
      (homogeneousTensorTerm degreeX degreeY i j coefficient) := by
  unfold homogeneousTensorTerm
  have hinteger : (0 : Int) ≤
      coefficient * Int.ofNat (binom degreeX i * binom degreeY j) :=
    Int.mul_nonneg hcoefficient (Int.natCast_nonneg _)
  exact Q'.mul_nonneg _ _ (ofInt_nonnegative hinteger)
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (rnqpow_nonnegative (hrho 0) i)
        (rnqpow_nonnegative (hrho 1) (degreeX - i)))
      (Q'.mul_nonneg _ _
        (rnqpow_nonnegative (hrho 2) j)
        (rnqpow_nonnegative (hrho 3) (degreeY - j))))

private theorem eval_homogeneousTensorRow_nonnegative
    (degreeX degreeY i : Nat) (rho : Nat → Q')
    (hrho : ∀ index, (0 : Q') ≤ rho index) :
    ∀ j row, IntegerRowNonnegative row = true →
      (0 : Q') ≤ RingNormaliser.eval rho
        (homogeneousTensorRow degreeX degreeY i j row)
  | _, [], _ => Q'.le_refl' 0
  | j, coefficient :: rest, hrow => by
      have hsplit := (Bool.and_eq_true _ _).mp hrow
      exact Q'.zero_le_add _ _
        (eval_homogeneousTensorTerm_nonnegative
          degreeX degreeY i j coefficient rho hrho
          (of_decide_eq_true hsplit.1))
        (eval_homogeneousTensorRow_nonnegative degreeX degreeY i rho hrho
          (j + 1) rest hsplit.2)

private theorem eval_homogeneousTensorRows_nonnegative
    (degreeX degreeY : Nat) (rho : Nat → Q')
    (hrho : ∀ index, (0 : Q') ≤ rho index) :
    ∀ i rows, IntegerRowsNonnegative rows = true →
      (0 : Q') ≤ RingNormaliser.eval rho
        (homogeneousTensorRows degreeX degreeY i rows)
  | _, [], _ => Q'.le_refl' 0
  | i, row :: rest, hrows => by
      have hsplit := (Bool.and_eq_true _ _).mp hrows
      exact Q'.zero_le_add _ _
        (eval_homogeneousTensorRow_nonnegative
          degreeX degreeY i rho hrho 0 row hsplit.1)
        (eval_homogeneousTensorRows_nonnegative degreeX degreeY rho hrho
          (i + 1) rest hsplit.2)

/-- A closed nonnegative integer table evaluates nonnegatively at every four
nonnegative homogeneous coordinates.  This linear-time consumer avoids
normalizing a large already-positive table merely to rediscover its signs. -/
theorem eval_homogeneousTensorExpr_nonnegative
    (degreeX degreeY : Nat) (rows : List (List Int))
    (rho : Nat → Q') (hrho : ∀ index, (0 : Q') ≤ rho index)
    (hrows : IntegerRowsNonnegative rows = true) :
    (0 : Q') ≤ RingNormaliser.eval rho
      (homogeneousTensorExpr degreeX degreeY rows) :=
  eval_homogeneousTensorRows_nonnegative
    degreeX degreeY rho hrho 0 rows hrows

/-- Nonnegativity consumer for a consecutive table block. -/
theorem eval_homogeneousTensorBlockExpr_nonnegative
    (degreeX degreeY startRow : Nat) (rows : List (List Int))
    (rho : Nat → Q') (hrho : ∀ index, (0 : Q') ≤ rho index)
    (hrows : IntegerRowsNonnegative rows = true) :
    (0 : Q') ≤ RingNormaliser.eval rho
      (homogeneousTensorBlockExpr degreeX degreeY startRow rows) :=
  eval_homogeneousTensorRows_nonnegative
    degreeX degreeY rho hrho startRow rows hrows

/-- One sparse bivariate integer power term, with variables `0` and `1`. -/
def bivariatePowerTerm (term : Nat × Nat × Int) :
    RingNormaliser.PolyExpr :=
  .mul (.const term.2.2)
    (.mul (.pow (.var 0) term.1) (.pow (.var 1) term.2.1))

/-- Reflect a sparse list `(degreeX, degreeY, coefficient)` into an integer
power polynomial. -/
def bivariatePowerExpr : List (Nat × Nat × Int) →
    RingNormaliser.PolyExpr
  | [] => .const 0
  | term :: rest =>
      .add (bivariatePowerTerm term) (bivariatePowerExpr rest)

/-! ## Exact substitution -/

/-- Syntactic simultaneous substitution of a polynomial environment. -/
def substitute (sigma : Nat → RingNormaliser.PolyExpr) :
    RingNormaliser.PolyExpr → RingNormaliser.PolyExpr
  | .const c => .const c
  | .var i => sigma i
  | .add a b => .add (substitute sigma a) (substitute sigma b)
  | .mul a b => .mul (substitute sigma a) (substitute sigma b)
  | .neg a => .neg (substitute sigma a)
  | .pow a n => .pow (substitute sigma a) n

/-- Polynomial substitution has its literal evaluation semantics. -/
theorem eval_substitute (rho : Nat → Q')
    (sigma : Nat → RingNormaliser.PolyExpr) : ∀ e,
    RingNormaliser.eval rho (substitute sigma e) ≈
      RingNormaliser.eval
        (fun i => RingNormaliser.eval rho (sigma i)) e
  | .const _ => Q'.eqv_refl _
  | .var _ => Q'.eqv_refl _
  | .add a b => Q'.add_eqv_congr'
      (eval_substitute rho sigma a) (eval_substitute rho sigma b)
  | .mul a b => mul_eqv_congr₂
      (eval_substitute rho sigma a) (eval_substitute rho sigma b)
  | .neg a => Q'.neg_eqv_congr _ _ (eval_substitute rho sigma a)
  | .pow a n =>
      RingNormaliser.qpow_eqv_congr (eval_substitute rho sigma a) n

/-! ## Eager-normalizer identity and positivity consumers -/

/-- Equality of eager normal forms is a sound polynomial identity. -/
theorem eval_eqv_of_fastNormalize_eq
    (left right : RingNormaliser.PolyExpr)
    (h : fastNormalize left = fastNormalize right)
    (rho : Nat → Q') :
    RingNormaliser.eval rho left ≈ RingNormaliser.eval rho right := by
  have hleft := evalRaw_fastNormalize rho left
  have hright := evalRaw_fastNormalize rho right
  rw [h] at hleft
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft) hright

/-- Generic consumer for a closed homogeneous table.  Positivity is checked
before substitution in independent nonnegative coordinates; the physical
identity is checked after exact syntactic substitution. -/
theorem physical_nonnegative_of_homogeneous_certificate
    (rho : Nat → Q') (sigma : Nat → RingNormaliser.PolyExpr)
    (bernstein physical : RingNormaliser.PolyExpr)
    (hcoordinates : ∀ i,
      (0 : Q') ≤ RingNormaliser.eval rho (sigma i))
    (hcoefficients :
      RawCoefficientsNonnegative (fastNormalize bernstein) = true)
    (hidentity :
      fastNormalize (substitute sigma bernstein) =
        fastNormalize physical) :
    (0 : Q') ≤ RingNormaliser.eval rho physical := by
  let chartRho : Nat → Q' :=
    fun i => RingNormaliser.eval rho (sigma i)
  have hbernstein : (0 : Q') ≤ RingNormaliser.eval chartRho bernstein :=
    eval_nonneg_of_fast_coefficients hcoordinates hcoefficients
  have hsubstitution := eval_substitute rho sigma bernstein
  have hsubstituted :
      (0 : Q') ≤ RingNormaliser.eval rho (substitute sigma bernstein) :=
    Q'.le_trans' _ _ _ hbernstein (Q'.ge_of_eqv hsubstitution)
  exact Q'.le_trans' _ _ _ hsubstituted
    (Q'.le_of_eqv
      (eval_eqv_of_fastNormalize_eq _ _ hidentity rho))

/-- Variant of the physical consumer using the direct dense-table sign check.
This is preferable for larger exact Bernstein tables. -/
theorem physical_nonnegative_of_homogeneous_rows_certificate
    (degreeX degreeY : Nat) (rows : List (List Int))
    (rho : Nat → Q') (sigma : Nat → RingNormaliser.PolyExpr)
    (physical : RingNormaliser.PolyExpr)
    (hcoordinates : ∀ i,
      (0 : Q') ≤ RingNormaliser.eval rho (sigma i))
    (hrows : IntegerRowsNonnegative rows = true)
    (hidentity :
      fastNormalize
          (substitute sigma (homogeneousTensorExpr degreeX degreeY rows)) =
        fastNormalize physical) :
    (0 : Q') ≤ RingNormaliser.eval rho physical := by
  let chartRho : Nat → Q' :=
    fun i => RingNormaliser.eval rho (sigma i)
  have hbernstein :
      (0 : Q') ≤ RingNormaliser.eval chartRho
        (homogeneousTensorExpr degreeX degreeY rows) :=
    eval_homogeneousTensorExpr_nonnegative
      degreeX degreeY rows chartRho hcoordinates hrows
  have hsubstitution := eval_substitute rho sigma
    (homogeneousTensorExpr degreeX degreeY rows)
  have hsubstituted :
      (0 : Q') ≤ RingNormaliser.eval rho
        (substitute sigma (homogeneousTensorExpr degreeX degreeY rows)) :=
    Q'.le_trans' _ _ _ hbernstein (Q'.ge_of_eqv hsubstitution)
  exact Q'.le_trans' _ _ _ hsubstituted
    (Q'.le_of_eqv
      (eval_eqv_of_fastNormalize_eq _ _ hidentity rho))

/-- Blockwise variant for large tables.  A concrete certificate may prove
each small substituted block equal to a sparse physical contribution, add
the resulting nonnegative contributions, and perform only a sparse final
aggregation check. -/
theorem physical_nonnegative_of_homogeneous_block_rows_certificate
    (degreeX degreeY startRow : Nat) (rows : List (List Int))
    (rho : Nat → Q') (sigma : Nat → RingNormaliser.PolyExpr)
    (physical : RingNormaliser.PolyExpr)
    (hcoordinates : ∀ i,
      (0 : Q') ≤ RingNormaliser.eval rho (sigma i))
    (hrows : IntegerRowsNonnegative rows = true)
    (hidentity :
      fastNormalize
          (substitute sigma
            (homogeneousTensorBlockExpr degreeX degreeY startRow rows)) =
        fastNormalize physical) :
    (0 : Q') ≤ RingNormaliser.eval rho physical := by
  let chartRho : Nat → Q' :=
    fun i => RingNormaliser.eval rho (sigma i)
  have hbernstein :
      (0 : Q') ≤ RingNormaliser.eval chartRho
        (homogeneousTensorBlockExpr degreeX degreeY startRow rows) :=
    eval_homogeneousTensorBlockExpr_nonnegative
      degreeX degreeY startRow rows chartRho hcoordinates hrows
  have hsubstitution := eval_substitute rho sigma
    (homogeneousTensorBlockExpr degreeX degreeY startRow rows)
  have hsubstituted :
      (0 : Q') ≤ RingNormaliser.eval rho
        (substitute sigma
          (homogeneousTensorBlockExpr degreeX degreeY startRow rows)) :=
    Q'.le_trans' _ _ _ hbernstein (Q'.ge_of_eqv hsubstitution)
  exact Q'.le_trans' _ _ _ hsubstituted
    (Q'.le_of_eqv
      (eval_eqv_of_fastNormalize_eq _ _ hidentity rho))

#print axioms homogeneousTensorExpr
#print axioms homogeneousTensorBlockExpr
#print axioms bivariatePowerExpr
#print axioms eval_homogeneousTensorExpr_nonnegative
#print axioms eval_homogeneousTensorBlockExpr_nonnegative
#print axioms eval_substitute
#print axioms eval_eqv_of_fastNormalize_eq
#print axioms physical_nonnegative_of_homogeneous_certificate
#print axioms physical_nonnegative_of_homogeneous_rows_certificate
#print axioms physical_nonnegative_of_homogeneous_block_rows_certificate

end YMGap.Continuum.TensorBernsteinHomogeneousCertificate
