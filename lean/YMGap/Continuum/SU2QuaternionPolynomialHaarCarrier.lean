/-
# Rational quaternion-polynomial carrier and exact `S^3` moment block

The five Peter--Weyl coordinates are a linear block but not an observable
algebra: their first product already exposes spin two.  This file replaces
that truncation by an honest multiplication-closed carrier.  An observable is
a finite list of rational-coefficient monomials in the eight quaternion
coordinates of a two-boundary pair `(g,h) in S^3 x S^3`.  No spin cutoff is
present; multiplication simply adds exponent vectors, so arbitrary iterated
products remain in the carrier.

The reference functional is approached constructively through the exact
normalized `S^3` monomial formula

  E[x_0^(2k_0) ... x_3^(2k_3)]
    = prod_i (2k_i-1)!! / prod_{r<K} (4+2r),

and zero when an exponent is odd.  The historically named `productHaar`
functional is the product of two such sphere-moment formulas.  From it, rather
than from a free Schur table, we derive

  * unit normalization of the retained raw polynomial kernel;
  * the vacuum/first-coordinate reflected block `diag(1,1/8)`;
  * the exact polynomial kernel `2 sum_i g_i h_i`, with the Hamilton-group
    character bridge deliberately deferred to the rational unit-quaternion
    development.

This leaf exposes all-degree positivity and weighted positivity as explicit
inputs.  Later modules prove the bare all-degree result on the strict
eight-coordinate carrier.  None of those moment identities, nor the legacy
record name `ProbFunctional`, supplies left/right group-translation invariance;
that genuinely Haar-theoretic bridge remains separate.
-/

import YMGap.Continuum.SU2PeterWeylPlaquetteAlgebraClosureFence
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2PeterWeylWilsonBlock
open YMGap.Continuum.SU2PeterWeylReferenceWeightCarrierFence

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
private theorem zero_num_cast : (0 : Q').num = 0 := rfl
private theorem zero_den_cast : ((0 : Q').den : Int) = 1 := rfl
private theorem one_num_cast : (1 : Q').num = 1 := rfl
private theorem one_den_cast : ((1 : Q').den : Int) = 1 := rfl
private theorem two_num_cast : (2 : Q').num = 2 := rfl
private theorem two_den_cast : ((2 : Q').den : Int) = 1 := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Q'.mkPos_num,
               Q'.mkPos_den, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast, zero_den_cast, one_num_cast, one_den_cast,
               two_num_cast, two_den_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg,
               Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero,
               Int.zero_add, Int.add_zero] <;>
             ac_rfl))

/-! ## A full finite-support rational polynomial carrier -/

/-- A rational-coefficient monomial term.  The exponent list is finite; index
`i` is the exponent of variable `i`. -/
abbrev RatTerm := List Nat × Q'

/-- Finite-support rational polynomials.  Duplicate monomials are allowed:
the semantic equality below quotients them extensionally when needed. -/
abbrev RatPoly := List RatTerm

def polyZero : RatPoly := []
def polyOne : RatPoly := [([], 1)]
def polyConst (c : Q') : RatPoly := [([], c)]
def polyVar (i : Nat) : RatPoly := [(varMono i, 1)]
def polyAdd (p q : RatPoly) : RatPoly := p ++ q
def polyNeg (p : RatPoly) : RatPoly := p.map fun t => (t.1, -t.2)
def polySmul (c : Q') (p : RatPoly) : RatPoly :=
  p.map fun t => (t.1, c * t.2)

/-- Multiplication has no degree or spin cutoff. -/
def polyMul (p q : RatPoly) : RatPoly :=
  p.flatMap fun s => q.map fun t => (monoMul s.1 t.1, s.2 * t.2)

def evalRatPoly (rho : Nat → Q') : RatPoly → Q'
  | [] => 0
  | t :: p => t.2 * evalMono rho t.1 + evalRatPoly rho p

def RatPolyEqv (p q : RatPoly) : Prop :=
  forall rho, evalRatPoly rho p ≈ evalRatPoly rho q

theorem evalRatPoly_add (rho : Nat → Q') (p q : RatPoly) :
    evalRatPoly rho (polyAdd p q) ≈
      evalRatPoly rho p + evalRatPoly rho q := by
  induction p with
  | nil => exact Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | cons t p ih =>
      change
        (t.2 * evalMono rho t.1 + evalRatPoly rho (p ++ q)) ≈
          (t.2 * evalMono rho t.1 + evalRatPoly rho p) + evalRatPoly rho q
      exact Q'.eqv_trans _
        (t.2 * evalMono rho t.1 +
          (evalRatPoly rho p + evalRatPoly rho q)) _
        (Q'.add_eqv_congr_left _ _ _ ih)
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem evalRatPoly_scaleTerm (rho : Nat → Q')
    (s : RatTerm) (q : RatPoly) :
    evalRatPoly rho
        (q.map fun t => (monoMul s.1 t.1, s.2 * t.2)) ≈
      (s.2 * evalMono rho s.1) * evalRatPoly rho q := by
  induction q with
  | nil => exact Q'.eqv_symm (Q'.mul_zero_eqv _)
  | cons t q ih =>
      unfold evalRatPoly
      refine Q'.eqv_trans _
        (((s.2 * evalMono rho s.1) *
            (t.2 * evalMono rho t.1)) +
          (s.2 * evalMono rho s.1) * evalRatPoly rho q) _ ?_ ?_
      · refine Q'.add_eqv_congr' ?_ ih
        refine Q'.eqv_trans _
          ((s.2 * t.2) * (evalMono rho s.1 * evalMono rho t.1)) _
          (Q'.mul_eqv_congr_left (s.2 * t.2) _ _
            (evalMono_monoMul rho s.1 t.1)) ?_
        exact q_mul4_swap s.2 t.2 (evalMono rho s.1) (evalMono rho t.1)
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv (s.2 * evalMono rho s.1)
            (t.2 * evalMono rho t.1) (evalRatPoly rho q))

/-- The concrete carrier multiplication evaluates pointwise. -/
theorem evalRatPoly_mul (rho : Nat → Q') (p q : RatPoly) :
    evalRatPoly rho (polyMul p q) ≈
      evalRatPoly rho p * evalRatPoly rho q := by
  induction p with
  | nil => exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  | cons s p ih =>
      unfold polyMul List.flatMap
      refine Q'.eqv_trans _
        (evalRatPoly rho
            (q.map fun t => (monoMul s.1 t.1, s.2 * t.2)) +
          evalRatPoly rho (polyMul p q)) _ ?_ ?_
      · exact evalRatPoly_add rho _ _
      · refine Q'.eqv_trans _
          ((s.2 * evalMono rho s.1) * evalRatPoly rho q +
            evalRatPoly rho p * evalRatPoly rho q) _
          (Q'.add_eqv_congr'
            (evalRatPoly_scaleTerm rho s q) ih) ?_
        exact Q'.eqv_symm
          (Q'.add_mul_eqv (s.2 * evalMono rho s.1)
            (evalRatPoly rho p) (evalRatPoly rho q))

/-- Package the polynomial carrier's raw operations into the repository's
legacy `ObsAlg` interface.  That record does not itself require the full
unital associative star-algebra laws.  Since the coefficients are rational,
the intended coefficient involution is the identity; Euclidean boundary
exchange is the separate `theta` below. -/
def quaternionPairAlg : ObservableMeasure.ObsAlg where
  carrier := RatPoly
  one := polyOne
  mul := polyMul
  star := fun p => p

/-! ## Exact normalized S^3 monomial moments -/

def oddDoubleFactorial : Nat → Nat
  | 0 => 1
  | k + 1 => (2 * k + 1) * oddDoubleFactorial k

/-- `4 * 6 * ... * (4+2(K-1))`. -/
def sphereFourDenominator : Nat → Nat
  | 0 => 1
  | k + 1 => (4 + 2 * k) * sphereFourDenominator k

theorem sphereFourDenominator_pos (k : Nat) :
    0 < sphereFourDenominator k := by
  induction k with
  | zero => decide
  | succ k ih =>
      unfold sphereFourDenominator
      exact Nat.mul_pos (by omega) ih

/-- Exact normalized `S^3` monomial-moment formula in four real quaternion
coordinates.  Its identification with group Haar requires the later
translation-invariance bridge. -/
def sphereMoment4 (e0 e1 e2 e3 : Nat) : Q' :=
  if _hEven : e0 % 2 = 0 ∧ e1 % 2 = 0 ∧ e2 % 2 = 0 ∧ e3 % 2 = 0 then
    let k0 := e0 / 2
    let k1 := e1 / 2
    let k2 := e2 / 2
    let k3 := e3 / 2
    Q'.mkPos
      (Int.ofNat
        (oddDoubleFactorial k0 * oddDoubleFactorial k1 *
          oddDoubleFactorial k2 * oddDoubleFactorial k3))
      (sphereFourDenominator (k0 + k1 + k2 + k3))
      (sphereFourDenominator_pos _)
  else 0

def exponentAt (m : List Nat) (i : Nat) : Nat := m.getD i 0

def allZero : List Nat → Bool
  | [] => true
  | e :: es => decide (e = 0) && allZero es

/-- Exact product of two `S^3` monomial-moment formulas.  The declaration keeps
its historical Haar-oriented name, but no group invariance is asserted here.
Variables above index seven evaluate as zero unless their exponent is zero. -/
def productHaarMono (m : List Nat) : Q' :=
  if allZero (m.drop 8) then
    sphereMoment4 (exponentAt m 0) (exponentAt m 1)
        (exponentAt m 2) (exponentAt m 3) *
      sphereMoment4 (exponentAt m 4) (exponentAt m 5)
        (exponentAt m 6) (exponentAt m 7)
  else 0

/-- The explicit rational product sphere-moment functional on the full
finite-support carrier, retaining its historical declaration name. -/
def productHaar : RatPoly → Q'
  | [] => 0
  | t :: p =>
      let mu := productHaarMono t.1
      match mu.num with
      | Int.ofNat 0 => productHaar p
      | _ => t.2 * mu + productHaar p

theorem sphereMoment4_one : sphereMoment4 0 0 0 0 ≈ 1 := by decide

theorem sphereMoment4_coordinate (i : Fin 4) :
    sphereMoment4 (if i.val = 0 then 1 else 0)
      (if i.val = 1 then 1 else 0)
      (if i.val = 2 then 1 else 0)
      (if i.val = 3 then 1 else 0) ≈ 0 := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases hi with h0 | h1 | h2 | h3
  · simp [h0, sphereMoment4]; exact Q'.eqv_refl 0
  · simp [h1, sphereMoment4]; exact Q'.eqv_refl 0
  · simp [h2, sphereMoment4]; exact Q'.eqv_refl 0
  · simp [h3, sphereMoment4]; exact Q'.eqv_refl 0

theorem sphereMoment4_covariance (i j : Fin 4) :
    sphereMoment4
      ((if i.val = 0 then 1 else 0) + (if j.val = 0 then 1 else 0))
      ((if i.val = 1 then 1 else 0) + (if j.val = 1 then 1 else 0))
      ((if i.val = 2 then 1 else 0) + (if j.val = 2 then 1 else 0))
      ((if i.val = 3 then 1 else 0) + (if j.val = 3 then 1 else 0)) ≈
        (if i = j then quarter else 0) := by
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
  rcases hi with hi | hi | hi | hi <;> rcases hj with hj | hj | hj | hj
  <;> have hieq : i = ⟨i.val, i.isLt⟩ := rfl
  <;> simp [hi, hj, Fin.ext_iff] <;> decide

/-! ## Two-boundary reflection and the retained relative kernel -/

/-- Exchange the two four-coordinate boundary blocks. -/
def swapBoundaryExponents (m : List Nat) : List Nat :=
  [exponentAt m 4, exponentAt m 5, exponentAt m 6, exponentAt m 7,
    exponentAt m 0, exponentAt m 1, exponentAt m 2, exponentAt m 3]

def theta (p : RatPoly) : RatPoly :=
  p.map fun t => (swapBoundaryExponents t.1, t.2)

def gCoordinate (i : Nat) : RatPoly := polyVar i
def hCoordinate (i : Nat) : RatPoly := polyVar (4 + i)

def relativeDot : RatPoly :=
  polyAdd (polyMul (gCoordinate 0) (hCoordinate 0))
    (polyAdd (polyMul (gCoordinate 1) (hCoordinate 1))
      (polyAdd (polyMul (gCoordinate 2) (hCoordinate 2))
        (polyMul (gCoordinate 3) (hCoordinate 3))))

/-- The polynomial `2 dot(g,h)` intended to become
`chi_1(g h⁻¹)` after a separate Hamilton-group evaluation bridge is proved.
This module itself has no quaternion multiplication or inversion. -/
def relativeFundamentalCharacter : RatPoly :=
  polySmul 2 relativeDot

/-- The retained polynomial kernel `1 + (1/4)·(2 dot(g,h))`.
Calling it the Wilson character kernel requires the later group-evaluation
bridge; no such identification is assumed here. -/
def retainedRelativeWeight : RatPoly :=
  polyAdd polyOne (polySmul quarter relativeFundamentalCharacter)

/-- The raw boundary polynomial `2g_0`, intended to become the fundamental
character only after the rational quaternion matrix-trace bridge. -/
def boundaryFundamental : RatPoly := polySmul 2 (gCoordinate 0)

def boundaryObservable (a : ModeVec) : RatPoly :=
  [([], a.1), (varMono 0, (2 : Q') * a.2)]

theorem boundary_vacuum_eqv :
    RatPolyEqv (boundaryObservable vacuumMode) polyOne := by
  intro rho
  simp [boundaryObservable, vacuumMode, polyOne, evalRatPoly, varMono,
    evalMono, evalMonoFrom, qpow]
  ring_qeqv

/-- Definitional expansion of the raw four-coordinate dot product.

Despite the historical theorem name, the inputs are arbitrary raw tuples and
this proof is reflexivity: it does **not** establish unit norm, Hamilton
multiplication, inversion, or a character identity.  Those claims belong to a
future bridge from the realized rational unit-quaternion group. -/
theorem relative_character_value (g h : RationalSU2Point) :
    (2 : Q') * relativeClassCoordinate g h ≈
      (2 : Q') *
        (g.1 * h.1 +
          (g.2.1 * h.2.1 +
            (g.2.2.1 * h.2.2.1 + g.2.2.2 * h.2.2.2))) :=
  Q'.eqv_refl _

/-! ### Exact scalar-type fence for the four complex matrix coefficients -/

/-- A literal complex fundamental matrix in a scalar `Q'` carrier would need
an element whose square is `-1`.  The real quaternion coordinates themselves
are present, but assembling `D00=a+ib`, etc. therefore requires the honest
complexification `RatPoly x RatPoly` (with conjugation on the second factor),
not four falsely real scalar entries. -/
theorem no_rational_imaginary_unit (u : Q') :
    ¬ (u * u ≈ (-1 : Q')) := by
  intro h
  have hsquare : (0 : Q') ≤ u * u := SumOfSquares.q_mul_self_nonneg u
  have hneg : (0 : Q') ≤ (-1 : Q') :=
    Q'.le_trans' _ _ _ hsquare (Q'.le_of_eqv h)
  exact (by decide : ¬ ((0 : Q') ≤ (-1 : Q'))) hneg

structure RationalScalarImaginaryUnit : Type where
  value : Q'
  square_neg_one : value * value ≈ (-1 : Q')

theorem no_rational_scalar_complex_fundamental :
    ¬ Nonempty RationalScalarImaginaryUnit := by
  rintro ⟨u⟩
  exact no_rational_imaginary_unit u.value u.square_neg_one

/-! ## Normalization and the exact two-coordinate block -/

/-- The explicit product sphere-moment functional is normalized on the
polynomial unit.  This statement alone is not Haar invariance. -/
theorem productHaar_one : productHaar polyOne ≈ 1 := by decide

/-- Every term of the raw relative dot kernel has one odd coordinate on each
boundary, so its product sphere-moment value is zero. -/
theorem productHaar_relativeFundamental_zero :
    productHaar relativeFundamentalCharacter ≈ 0 := by decide

/-- Exact partition normalization of the retained interacting kernel. -/
theorem retained_partition_exact :
    productHaar retainedRelativeWeight ≈ 1 := by decide

/-- The smart zero-moment fold also makes the normalized partition a literal
carrier equality, as required by `ReferenceWeight`, not only a rational
equivalence. -/
theorem retained_partition_strict :
    productHaar (polyMul retainedRelativeWeight polyOne) = (1 : Q') := by decide

/-- Vacuum/first-coordinate cross terms vanish directly from the odd-moment
rule. -/
theorem retained_vacuum_fundamental_cross :
    productHaar
      (polyMul retainedRelativeWeight
        (polyMul (theta polyOne) boundaryFundamental)) ≈ 0 := by decide

theorem retained_fundamental_vacuum_cross :
    productHaar
      (polyMul retainedRelativeWeight
        (polyMul (theta boundaryFundamental) polyOne)) ≈ 0 := by decide

/-- The first-coordinate reflected norm is derived from
`E[g_0 g_i] E[h_0 h_i] = delta_(0i)/16` and the kernel coefficient `1/2`.
The result is exactly `1/8`. -/
theorem retained_fundamental_norm :
    productHaar
      (polyMul retainedRelativeWeight
        (polyMul (theta boundaryFundamental) boundaryFundamental)) ≈
      eighth := by decide

/-- The full retained two-mode coordinate block, computed by the explicit
all-degree polynomial carrier and the `S^3` moment formula.  Identifying the
second mode with a representation character is a later bridge. -/
theorem retained_doubleHaar_schur (a b : ModeVec) :
    productHaar
      (polyMul retainedRelativeWeight
        (polyMul (theta (boundaryObservable a)) (boundaryObservable b))) ≈
      a.1 * b.1 + eighth * (a.2 * b.2) := by
  simp [boundaryObservable, retainedRelativeWeight,
    relativeFundamentalCharacter, relativeDot, gCoordinate, hCoordinate,
    theta, swapBoundaryExponents, polyVar, polyOne, polyAdd, polySmul, polyMul,
    productHaar, productHaarMono, sphereMoment4, exponentAt, allZero,
    oddDoubleFactorial, sphereFourDenominator, varMono, monoMul]
  unfold quarter eighth
  ring_qeqv

/-- The computed raw numerator agrees algebraically with the pre-existing
legacy Wilson-block formula, but this equality does not itself supply the
missing quaternion character or group-invariance bridges. -/
theorem retained_doubleHaar_matches_Wilson (a b : ModeVec) :
    productHaar
      (polyMul retainedRelativeWeight
        (polyMul (theta (boundaryObservable a)) (boundaryObservable b))) ≈
      reflectedWilsonGram a b :=
  Q'.eqv_trans _ _ _ (retained_doubleHaar_schur a b)
    (Q'.eqv_symm (reflectedWilsonGram_diagonal a b))

/-! ## Explicit positivity interfaces -/

/-- Bare square positivity for the explicit moment functional.  It is stated
on the concrete carrier rather than assumed as an opaque field; later modules
construct this proof for the strict eight-coordinate support. -/
def ProductHaarAllDegreePositive : Prop :=
  forall p : RatPoly, (0 : Q') ≤ productHaar (polyMul p p)

/-- All-degree positivity after reweighting by the retained raw polynomial
kernel on the same concrete carrier.  Calling that kernel Wilson-theoretic
requires the later character bridge. -/
def RetainedWeightedAllDegreePositive : Prop :=
  forall p : RatPoly,
    (0 : Q') ≤
      productHaar
        (polyMul retainedRelativeWeight (polyMul p p))

/-- Package normalization and square positivity into the repository's legacy
`ProbFunctional` record.  That record does not itself carry additivity,
homogeneity, or group-translation invariance, so this constructor is not yet a
measure-theoretic Haar probability functional. -/
def productHaarProbFunctional
    (hpos : ProductHaarAllDegreePositive) :
    ObservableMeasure.ProbFunctional quaternionPairAlg where
  E := productHaar
  normalized := by decide
  positive := hpos

/-- Once the two displayed positivity statements are supplied, package the
raw polynomial data into the repository's `ReferenceWeight` interface; its
partition is definitionally one.  This packaging does not add the absent
character or Haar-invariance theorems. -/
def retainedReferenceWeight
    (hpos : ProductHaarAllDegreePositive)
    (hweighted : RetainedWeightedAllDegreePositive) :
    FiniteVolume.ReferenceWeight quaternionPairAlg where
  I₀ := productHaarProbFunctional hpos
  w := retainedRelativeWeight
  Z := 1
  Z_eq := retained_partition_strict
  Z_pos := by decide
  weighted_pos := hweighted

theorem retainedReferenceWeight_partition
    (hpos : ProductHaarAllDegreePositive)
    (hweighted : RetainedWeightedAllDegreePositive) :
    (retainedReferenceWeight hpos hweighted).Z = (1 : Q') := rfl

theorem retainedReferenceWeight_bare_schur
    (hpos : ProductHaarAllDegreePositive)
    (hweighted : RetainedWeightedAllDegreePositive)
    (a b : ModeVec) :
    (retainedReferenceWeight hpos hweighted).I₀.E
      (polyMul (retainedReferenceWeight hpos hweighted).w
        (polyMul (theta (boundaryObservable a)) (boundaryObservable b))) ≈
      a.1 * b.1 + eighth * (a.2 * b.2) :=
  retained_doubleHaar_schur a b

end YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.evalRatPoly_mul
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.sphereMoment4_covariance
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.retained_partition_exact
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.no_rational_scalar_complex_fundamental
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.retained_partition_strict
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.retained_fundamental_norm
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.retained_doubleHaar_schur
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.retained_doubleHaar_matches_Wilson
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.productHaarProbFunctional
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.retainedReferenceWeight
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier.retainedReferenceWeight_bare_schur
