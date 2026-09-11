/-
# Constructive substitution for finite-support rational polynomials

The direct active-polynomial route repeatedly pulls a polynomial on one
coordinate family back along polynomial coordinate maps.  This leaf supplies
that operation directly on the repository's raw `RatPoly` carrier.

For a substitution `sigma : Nat -> RatPoly`, a monomial exponent list

    [e_0, ..., e_n]

is sent to the finite product

    sigma(0)^e_0 * ... * sigma(n)^e_n.

Coefficients are retained by rational scalar multiplication, and a polynomial
is substituted by a structural recursion over its finite term list.  The main
theorem proves the exact semantic law

    eval rho (substitute sigma p)
      ~= eval (fun i => eval rho (sigma i)) p.

Identity and composition are consequently proved extensionally in
`RatPolyEqv`.  Every recursion is on `Nat` or `List`; no choice or infinitary
support construction is involved.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionWilsonWeightSOS

namespace YMGap.Continuum.RatPolySubstitution

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-! ## 1. Polynomial powers -/

/-- A literal `Nat` power in the raw `RatPoly` carrier.  The multiplication
order agrees with `RingNormaliser.qpow`. -/
def polyPow (polynomial : RatPoly) : Nat → RatPoly
  | 0 => polyOne
  | exponent + 1 => polyMul (polyPow polynomial exponent) polynomial

/-- Evaluation commutes with the literal polynomial power. -/
theorem eval_polyPow (rho : Nat → Q') (polynomial : RatPoly) :
    ∀ exponent : Nat,
      evalRatPoly rho (polyPow polynomial exponent) ≈
        qpow (evalRatPoly rho polynomial) exponent
  | 0 => evalRatPoly_one rho
  | exponent + 1 => by
      exact Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho (polyPow polynomial exponent) polynomial)
        (q_mul_congr (eval_polyPow rho polynomial exponent)
          (Q'.eqv_refl _))

/-! ## 2. Substitution of one monomial -/

/-- Substitute an exponent list beginning at the source coordinate `start`.
The empty exponent vector is the multiplicative unit. -/
def substituteMonoFrom (sigma : Nat → RatPoly) :
    Nat → List Nat → RatPoly
  | _, [] => polyOne
  | start, exponent :: tail =>
      polyMul (polyPow (sigma start) exponent)
        (substituteMonoFrom sigma (start + 1) tail)

/-- Substitution of a monomial whose first exponent is at coordinate zero. -/
def substituteMono (sigma : Nat → RatPoly) (monomial : List Nat) : RatPoly :=
  substituteMonoFrom sigma 0 monomial

/-- Exact evaluation of a substituted exponent list from an arbitrary source
coordinate. -/
theorem eval_substituteMonoFrom (sigma : Nat → RatPoly) (rho : Nat → Q') :
    ∀ (start : Nat) (monomial : List Nat),
      evalRatPoly rho (substituteMonoFrom sigma start monomial) ≈
        evalMonoFrom (fun coordinate => evalRatPoly rho (sigma coordinate))
          start monomial
  | _, [] => evalRatPoly_one rho
  | start, exponent :: tail => by
      exact Q'.eqv_trans _ _ _
        (evalRatPoly_mul rho (polyPow (sigma start) exponent)
          (substituteMonoFrom sigma (start + 1) tail))
        (q_mul_congr
          (eval_polyPow rho (sigma start) exponent)
          (eval_substituteMonoFrom sigma rho (start + 1) tail))

/-- Exact evaluation of a substituted monomial at source coordinate zero. -/
theorem eval_substituteMono (sigma : Nat → RatPoly) (rho : Nat → Q')
    (monomial : List Nat) :
    evalRatPoly rho (substituteMono sigma monomial) ≈
      evalMono (fun coordinate => evalRatPoly rho (sigma coordinate))
        monomial :=
  eval_substituteMonoFrom sigma rho 0 monomial

/-! ## 3. Substitution of terms and polynomials -/

/-- Substitute the monomial of one rational term and retain its coefficient. -/
def substituteTerm (sigma : Nat → RatPoly) (term : RatTerm) : RatPoly :=
  polySmul term.2 (substituteMono sigma term.1)

theorem eval_substituteTerm (sigma : Nat → RatPoly) (rho : Nat → Q')
    (term : RatTerm) :
    evalRatPoly rho (substituteTerm sigma term) ≈
      term.2 *
        evalMono (fun coordinate => evalRatPoly rho (sigma coordinate))
          term.1 := by
  exact Q'.eqv_trans _ _ _
    (evalRatPoly_smul rho term.2 (substituteMono sigma term.1))
    (Q'.mul_eqv_congr_left term.2 _ _
      (eval_substituteMono sigma rho term.1))

/-- Constructive arbitrary-variable substitution on `RatPoly`. -/
def substitute (sigma : Nat → RatPoly) : RatPoly → RatPoly
  | [] => polyZero
  | term :: tail =>
      polyAdd (substituteTerm sigma term) (substitute sigma tail)

/-- **Exact substitution evaluation theorem.**  Evaluating a substituted raw
polynomial at `rho` equals evaluating the original polynomial in the
environment obtained by evaluating each substituted coordinate at `rho`. -/
theorem eval_substitute (sigma : Nat → RatPoly) (polynomial : RatPoly)
    (rho : Nat → Q') :
    evalRatPoly rho (substitute sigma polynomial) ≈
      evalRatPoly
        (fun coordinate => evalRatPoly rho (sigma coordinate)) polynomial := by
  induction polynomial with
  | nil =>
      exact Q'.eqv_refl _
  | cons term tail ih =>
      exact Q'.eqv_trans _ _ _
        (evalRatPoly_add rho (substituteTerm sigma term)
          (substitute sigma tail))
        (q_add_congr (eval_substituteTerm sigma rho term) ih)

/-! ## 4. Environment congruence -/

/-- Monomial evaluation respects pointwise equivalent environments, from any
starting source coordinate. -/
theorem evalMonoFrom_environment_congr {left right : Nat → Q'}
    (henvironment : ∀ coordinate, left coordinate ≈ right coordinate) :
    ∀ (start : Nat) (monomial : List Nat),
      evalMonoFrom left start monomial ≈ evalMonoFrom right start monomial
  | _, [] => Q'.eqv_refl _
  | start, exponent :: tail =>
      q_mul_congr
        (qpow_eqv_congr (henvironment start) exponent)
        (evalMonoFrom_environment_congr henvironment (start + 1) tail)

theorem evalMono_environment_congr {left right : Nat → Q'}
    (henvironment : ∀ coordinate, left coordinate ≈ right coordinate)
    (monomial : List Nat) :
    evalMono left monomial ≈ evalMono right monomial :=
  evalMonoFrom_environment_congr henvironment 0 monomial

/-- Raw polynomial evaluation respects pointwise equivalent environments. -/
theorem evalRatPoly_environment_congr {left right : Nat → Q'}
    (henvironment : ∀ coordinate, left coordinate ≈ right coordinate) :
    ∀ polynomial : RatPoly,
      evalRatPoly left polynomial ≈ evalRatPoly right polynomial
  | [] => Q'.eqv_refl _
  | term :: tail =>
      q_add_congr
        (q_mul_congr (Q'.eqv_refl term.2)
          (evalMono_environment_congr henvironment term.1))
        (evalRatPoly_environment_congr henvironment tail)

/-! ## 5. Congruence and algebra laws -/

/-- Substitution respects extensional equality of source polynomials. -/
theorem substitute_source_congr (sigma : Nat → RatPoly)
    {left right : RatPoly} (hsource : RatPolyEqv left right) :
    RatPolyEqv (substitute sigma left) (substitute sigma right) := by
  intro rho
  calc
    evalRatPoly rho (substitute sigma left) ≈
        evalRatPoly
          (fun coordinate => evalRatPoly rho (sigma coordinate)) left :=
      eval_substitute sigma left rho
    _ ≈ evalRatPoly
          (fun coordinate => evalRatPoly rho (sigma coordinate)) right :=
      hsource _
    _ ≈ evalRatPoly rho (substitute sigma right) :=
      Q'.eqv_symm (eval_substitute sigma right rho)

/-- Substitution respects pointwise extensional equality of coordinate maps. -/
theorem substitute_map_congr {left right : Nat → RatPoly}
    (hmap : ∀ coordinate, RatPolyEqv (left coordinate) (right coordinate))
    (polynomial : RatPoly) :
    RatPolyEqv
      (substitute left polynomial)
      (substitute right polynomial) := by
  intro rho
  calc
    evalRatPoly rho (substitute left polynomial) ≈
        evalRatPoly
          (fun coordinate => evalRatPoly rho (left coordinate))
          polynomial :=
      eval_substitute left polynomial rho
    _ ≈ evalRatPoly
          (fun coordinate => evalRatPoly rho (right coordinate))
          polynomial :=
      evalRatPoly_environment_congr
        (fun coordinate => hmap coordinate rho) polynomial
    _ ≈ evalRatPoly rho (substitute right polynomial) :=
      Q'.eqv_symm (eval_substitute right polynomial rho)

/-- Substitution preserves polynomial addition extensionally. -/
theorem substitute_add (sigma : Nat → RatPoly) (left right : RatPoly) :
    RatPolyEqv
      (substitute sigma (polyAdd left right))
      (polyAdd (substitute sigma left) (substitute sigma right)) := by
  intro rho
  calc
    evalRatPoly rho (substitute sigma (polyAdd left right)) ≈
        evalRatPoly
          (fun coordinate => evalRatPoly rho (sigma coordinate))
          (polyAdd left right) :=
      eval_substitute sigma (polyAdd left right) rho
    _ ≈
        evalRatPoly
            (fun coordinate => evalRatPoly rho (sigma coordinate)) left +
          evalRatPoly
            (fun coordinate => evalRatPoly rho (sigma coordinate)) right :=
      evalRatPoly_add _ left right
    _ ≈
        evalRatPoly rho (substitute sigma left) +
          evalRatPoly rho (substitute sigma right) :=
      q_add_congr
        (Q'.eqv_symm (eval_substitute sigma left rho))
        (Q'.eqv_symm (eval_substitute sigma right rho))
    _ ≈ evalRatPoly rho
          (polyAdd (substitute sigma left) (substitute sigma right)) :=
      Q'.eqv_symm
        (evalRatPoly_add rho
          (substitute sigma left) (substitute sigma right))

/-- Substitution preserves polynomial multiplication extensionally. -/
theorem substitute_mul (sigma : Nat → RatPoly) (left right : RatPoly) :
    RatPolyEqv
      (substitute sigma (polyMul left right))
      (polyMul (substitute sigma left) (substitute sigma right)) := by
  intro rho
  calc
    evalRatPoly rho (substitute sigma (polyMul left right)) ≈
        evalRatPoly
          (fun coordinate => evalRatPoly rho (sigma coordinate))
          (polyMul left right) :=
      eval_substitute sigma (polyMul left right) rho
    _ ≈
        evalRatPoly
            (fun coordinate => evalRatPoly rho (sigma coordinate)) left *
          evalRatPoly
            (fun coordinate => evalRatPoly rho (sigma coordinate)) right :=
      evalRatPoly_mul _ left right
    _ ≈
        evalRatPoly rho (substitute sigma left) *
          evalRatPoly rho (substitute sigma right) :=
      q_mul_congr
        (Q'.eqv_symm (eval_substitute sigma left rho))
        (Q'.eqv_symm (eval_substitute sigma right rho))
    _ ≈ evalRatPoly rho
          (polyMul (substitute sigma left) (substitute sigma right)) :=
      Q'.eqv_symm
        (evalRatPoly_mul rho
          (substitute sigma left) (substitute sigma right))

/-! ## 6. Identity and composition laws -/

/-- Substitution by the coordinate variables is extensionally the identity. -/
theorem substitute_identity (polynomial : RatPoly) :
    RatPolyEqv
      (substitute (fun coordinate => polyVar coordinate) polynomial)
      polynomial := by
  intro rho
  exact Q'.eqv_trans _ _ _
    (eval_substitute (fun coordinate => polyVar coordinate) polynomial rho)
    (evalRatPoly_environment_congr
      (fun coordinate => evalRatPoly_var rho coordinate) polynomial)

/-- Substitution is associative up to the carrier's extensional equality.
The left side first substitutes `inner`, then pulls every resulting coordinate
back along `outer`; the right side substitutes the composed coordinate map. -/
theorem substitute_compose (outer inner : Nat → RatPoly)
    (polynomial : RatPoly) :
    RatPolyEqv
      (substitute outer (substitute inner polynomial))
      (substitute (fun coordinate => substitute outer (inner coordinate))
        polynomial) := by
  intro rho
  let pulledEnvironment : Nat → Q' :=
    fun coordinate => evalRatPoly rho (outer coordinate)
  calc
    evalRatPoly rho (substitute outer (substitute inner polynomial))
        ≈ evalRatPoly pulledEnvironment (substitute inner polynomial) :=
          eval_substitute outer (substitute inner polynomial) rho
    _ ≈ evalRatPoly
          (fun coordinate =>
            evalRatPoly pulledEnvironment (inner coordinate)) polynomial :=
        eval_substitute inner polynomial pulledEnvironment
    _ ≈ evalRatPoly
          (fun coordinate =>
            evalRatPoly rho (substitute outer (inner coordinate)))
          polynomial :=
        evalRatPoly_environment_congr
          (fun coordinate =>
            Q'.eqv_symm
              (eval_substitute outer (inner coordinate) rho)) polynomial
    _ ≈ evalRatPoly rho
          (substitute
            (fun coordinate => substitute outer (inner coordinate))
            polynomial) :=
        Q'.eqv_symm
          (eval_substitute
            (fun coordinate => substitute outer (inner coordinate))
            polynomial rho)

#print axioms eval_polyPow
#print axioms eval_substituteMonoFrom
#print axioms eval_substitute
#print axioms substitute_source_congr
#print axioms substitute_map_congr
#print axioms substitute_add
#print axioms substitute_mul
#print axioms substitute_identity
#print axioms substitute_compose

end YMGap.Continuum.RatPolySubstitution
