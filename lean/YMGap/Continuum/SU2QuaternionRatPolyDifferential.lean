/-
# Constructive differential algebra on the rational quaternion carrier

This file defines formal partial derivatives and the four-coordinate head
Laplacian directly on `RatPoly`.  Equality is coefficientwise, expressed
without quotients or choice: two finite polynomials are equivalent when every
monomial-weighted rational sum agrees.  This relation sees arbitrary tail
monomials and therefore transports directly to the Gaussian-tail functional.
-/

import YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
import YMGap.Continuum.SU2QuaternionHeadGaussianLaplacian

namespace YMGap.Continuum.SU2QuaternionRatPolyDifferential

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionHeadGaussianLaplacian
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarSphereIdeal
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.SU2QuaternionHaarRadiusHomogenization

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl
private theorem zero_num_cast_local : (0 : Q').num = 0 := rfl
private theorem zero_den_cast_local : ((0 : Q').den : Int) = 1 := rfl
private theorem two_num_cast_local : (2 : Q').num = 2 := rfl
private theorem two_den_cast_local : ((2 : Q').den : Int) = 1 := rfl
private theorem one_num_cast_local : (1 : Q').num = 1 := rfl
private theorem one_den_cast_local : ((1 : Q').den : Int) = 1 := rfl
private theorem four_num_cast_local : (4 : Q').num = 4 := rfl
private theorem four_den_cast_local : ((4 : Q').den : Int) = 1 := rfl
private theorem eight_num_cast_local : (8 : Q').num = 8 := rfl
private theorem eight_den_cast_local : ((8 : Q').den : Int) = 1 := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               zero_num_cast_local, zero_den_cast_local,
               two_num_cast_local, two_den_cast_local,
               one_num_cast_local, one_den_cast_local,
               four_num_cast_local, four_den_cast_local,
               eight_num_cast_local, eight_den_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try push_cast;
             try simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl;
             try omega))

private theorem two_mul_eqv_add_self (value : Q') :
    (2 : Q') * value ≈ value + value := by
  refine Q'.eqv_trans _
    ((Q'.ofNat 1 + Q'.ofNat 1) * value) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_symm (Q'.ofNat_add_eqv 1 1))) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 1 * value + Q'.ofNat 1 * value) _
    (q_add_mul _ _ _) ?_
  exact Q'.add_eqv_congr'
    (Q'.one_mul_eqv value) (Q'.one_mul_eqv value)

theorem four_mul_ofNat_add_two_eqv (degree : Nat) :
    (4 : Q') * Q'.ofNat (degree + 2) ≈
      8 + 4 * Q'.ofNat degree := by
  refine Q'.eqv_trans _
    ((4 : Q') * (Q'.ofNat degree + Q'.ofNat 2)) _
    (Q'.mul_eqv_congr_left 4 _ _
      (Q'.ofNat_add_eqv degree 2)) ?_
  q_ring

theorem two_add_ofNat_succ_eqv (degree : Nat) :
    (2 : Q') + Q'.ofNat (degree + 1) ≈
      Q'.ofNat (degree + 3) := by
  refine Q'.eqv_trans _
    (Q'.ofNat 2 + Q'.ofNat (degree + 1)) _
    (Q'.eqv_refl _) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (2 + (degree + 1))) _
    (Q'.eqv_symm (Q'.ofNat_add_eqv 2 (degree + 1))) ?_
  have : 2 + (degree + 1) = degree + 3 := by omega
  rw [this]
  exact Q'.eqv_refl _

theorem two_mul_two_mul_eqv (value : Q') :
    (2 : Q') * (2 * value) ≈ 4 * value := by
  q_ring

/-! ## Coefficient-probe equality -/

/-- Equality of every finitely supported coefficient probe.  In particular,
unmentioned quaternion blocks remain genuine polynomial coefficients. -/
def RatPolyCoeffEqv (left right : RatPoly) : Prop :=
  ∀ weight : List Nat → Q',
    ratWeightedSum weight left ≈ ratWeightedSum weight right

theorem RatPolyCoeffEqv.refl (polynomial : RatPoly) :
    RatPolyCoeffEqv polynomial polynomial := by
  intro weight
  exact Q'.eqv_refl _

theorem RatPolyCoeffEqv.symm
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv right left := by
  intro weight
  exact Q'.eqv_symm (h weight)

theorem RatPolyCoeffEqv.trans
    {first middle last : RatPoly}
    (hfirst : RatPolyCoeffEqv first middle)
    (hlast : RatPolyCoeffEqv middle last) :
    RatPolyCoeffEqv first last := by
  intro weight
  exact Q'.eqv_trans _ _ _ (hfirst weight) (hlast weight)

theorem ratWeightedSum_add
    (weight : List Nat → Q') : ∀ left right : RatPoly,
    ratWeightedSum weight (polyAdd left right) ≈
      ratWeightedSum weight left + ratWeightedSum weight right
  | [], right => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | term :: rest, right => by
      change
        term.2 * weight term.1 +
              ratWeightedSum weight (polyAdd rest right) ≈
          (term.2 * weight term.1 + ratWeightedSum weight rest) +
            ratWeightedSum weight right
      exact Q'.eqv_trans _
        (term.2 * weight term.1 +
          (ratWeightedSum weight rest + ratWeightedSum weight right)) _
        (Q'.add_eqv_congr_left _ _ _
          (ratWeightedSum_add weight rest right))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

theorem ratWeightedSum_smul
    (weight : List Nat → Q') (scale : Q') : ∀ polynomial : RatPoly,
    ratWeightedSum weight (polySmul scale polynomial) ≈
      scale * ratWeightedSum weight polynomial
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | term :: rest => by
      change
        (scale * term.2) * weight term.1 +
              ratWeightedSum weight (polySmul scale rest) ≈
          scale *
            (term.2 * weight term.1 + ratWeightedSum weight rest)
      refine Q'.eqv_trans _
        (scale * (term.2 * weight term.1) +
          scale * ratWeightedSum weight rest) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.mul_assoc_eqv scale term.2 (weight term.1))
          (ratWeightedSum_smul weight scale rest)
      · exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

theorem RatPolyCoeffEqv.add
    {left left' right right' : RatPoly}
    (hleft : RatPolyCoeffEqv left left')
    (hright : RatPolyCoeffEqv right right') :
    RatPolyCoeffEqv
      (polyAdd left right) (polyAdd left' right') := by
  intro weight
  refine Q'.eqv_trans _
    (ratWeightedSum weight left + ratWeightedSum weight right) _
    (ratWeightedSum_add weight left right) ?_
  refine Q'.eqv_trans _
    (ratWeightedSum weight left' + ratWeightedSum weight right') _
    (Q'.add_eqv_congr' (hleft weight) (hright weight)) ?_
  exact Q'.eqv_symm (ratWeightedSum_add weight left' right')

theorem RatPolyCoeffEqv.smul
    (scale : Q') {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (polySmul scale left) (polySmul scale right) := by
  intro weight
  refine Q'.eqv_trans _
    (scale * ratWeightedSum weight left) _
    (ratWeightedSum_smul weight scale left) ?_
  refine Q'.eqv_trans _
    (scale * ratWeightedSum weight right) _
    (Q'.mul_eqv_congr_left scale _ _ (h weight)) ?_
  exact Q'.eqv_symm (ratWeightedSum_smul weight scale right)

theorem RatPolyCoeffEqv.zero_smul (polynomial : RatPoly) :
    RatPolyCoeffEqv (polySmul 0 polynomial) polyZero := by
  intro weight
  refine Q'.eqv_trans _
    (0 * ratWeightedSum weight polynomial) _
    (ratWeightedSum_smul weight 0 polynomial) ?_
  exact Q'.zero_mul_eqv _

theorem RatPolyCoeffEqv.add_zero (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyAdd polynomial polyZero) polynomial := by
  intro weight
  refine Q'.eqv_trans _
    (ratWeightedSum weight polynomial + 0) _
    (ratWeightedSum_add weight polynomial polyZero) ?_
  exact QPoly.q_add_zero_eqv _

theorem RatPolyCoeffEqv.zero_add (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyAdd polyZero polynomial) polynomial := by
  intro weight
  exact Q'.eqv_refl _

theorem RatPolyCoeffEqv.add_comm (left right : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd left right) (polyAdd right left) := by
  intro weight
  refine Q'.eqv_trans _
    (ratWeightedSum weight left + ratWeightedSum weight right) _
    (ratWeightedSum_add weight left right) ?_
  refine Q'.eqv_trans _
    (ratWeightedSum weight right + ratWeightedSum weight left) _
    (Q'.add_comm_eqv _ _) ?_
  exact Q'.eqv_symm (ratWeightedSum_add weight right left)

theorem RatPolyCoeffEqv.add_assoc
    (first second third : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd first second) third)
      (polyAdd first (polyAdd second third)) := by
  intro weight
  have hleft :
      ratWeightedSum weight (polyAdd (polyAdd first second) third) ≈
        (ratWeightedSum weight first + ratWeightedSum weight second) +
          ratWeightedSum weight third := by
    exact Q'.eqv_trans _
      (ratWeightedSum weight (polyAdd first second) +
        ratWeightedSum weight third) _
      (ratWeightedSum_add weight (polyAdd first second) third)
      (Q'.add_eqv_congr_right _ _ _
        (ratWeightedSum_add weight first second))
  have hright :
      ratWeightedSum weight (polyAdd first (polyAdd second third)) ≈
        ratWeightedSum weight first +
          (ratWeightedSum weight second + ratWeightedSum weight third) := by
    exact Q'.eqv_trans _
      (ratWeightedSum weight first +
        ratWeightedSum weight (polyAdd second third)) _
      (ratWeightedSum_add weight first (polyAdd second third))
      (Q'.add_eqv_congr_left _ _ _
        (ratWeightedSum_add weight second third))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.eqv_symm hright))

theorem RatPolyCoeffEqv.smul_coefficient
    {first second : Q'} (hscale : first ≈ second)
    (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (polySmul first polynomial)
      (polySmul second polynomial) := by
  intro weight
  refine Q'.eqv_trans _
    (first * ratWeightedSum weight polynomial) _
    (ratWeightedSum_smul weight first polynomial) ?_
  refine Q'.eqv_trans _
    (second * ratWeightedSum weight polynomial) _
    (Q'.mul_eqv_congr_right _ _ _ hscale) ?_
  exact Q'.eqv_symm
    (ratWeightedSum_smul weight second polynomial)

theorem RatPolyCoeffEqv.smul_assoc
    (first second : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (polySmul first (polySmul second polynomial))
      (polySmul (first * second) polynomial) := by
  intro weight
  refine Q'.eqv_trans _
    (first * (second * ratWeightedSum weight polynomial)) _
    (Q'.eqv_trans _
      (first * ratWeightedSum weight (polySmul second polynomial)) _
      (ratWeightedSum_smul weight first _)
      (Q'.mul_eqv_congr_left _ _ _
        (ratWeightedSum_smul weight second polynomial))) ?_
  refine Q'.eqv_trans _
    ((first * second) * ratWeightedSum weight polynomial) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  exact Q'.eqv_symm
    (ratWeightedSum_smul weight (first * second) polynomial)

theorem twice_twice_smul (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (polySmul 2 (polySmul 2 polynomial))
      (polySmul 4 polynomial) :=
  RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.smul_assoc 2 2 polynomial)
    (RatPolyCoeffEqv.smul_coefficient (by decide) polynomial)

theorem RatPolyCoeffEqv.smul_add
    (scale : Q') (left right : RatPoly) :
    RatPolyCoeffEqv
      (polySmul scale (polyAdd left right))
      (polyAdd (polySmul scale left) (polySmul scale right)) := by
  simp only [polySmul, polyAdd, List.map_append]
  exact RatPolyCoeffEqv.refl _

theorem ratWeightedSum_termwise_eqv
    (weight : List Nat → Q') : ∀ {left right : RatPoly},
    RatPolyTermwiseEqv left right →
      ratWeightedSum weight left ≈ ratWeightedSum weight right
  | [], [], _ => Q'.eqv_refl 0
  | left :: leftRest, right :: rightRest, h => by
      change
        left.2 * weight left.1 + ratWeightedSum weight leftRest ≈
          right.2 * weight right.1 + ratWeightedSum weight rightRest
      rw [h.1]
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ h.2.1)
        (ratWeightedSum_termwise_eqv weight h.2.2)

/-- A checked rational canonical equality is a coefficient equality. -/
theorem RatPolyCoeffEqv.of_canon_termwise
    {left right : RatPoly}
    (h : RatPolyTermwiseEqv (canonRat left) (canonRat right)) :
    RatPolyCoeffEqv left right := by
  intro weight
  refine Q'.eqv_trans _
    (ratWeightedSum weight (canonRat left)) _
    (Q'.eqv_symm (ratWeightedSum_canon weight left)) ?_
  refine Q'.eqv_trans _
    (ratWeightedSum weight (canonRat right)) _
    (ratWeightedSum_termwise_eqv weight h) ?_
  exact ratWeightedSum_canon weight right

private theorem ratWeightedSum_mulRow
    (weight : List Nat → Q') (source : RatTerm) :
    ∀ right : RatPoly,
    ratWeightedSum weight
        (right.map fun target =>
          (monoMul source.1 target.1,
            source.2 * target.2)) ≈
      source.2 *
        ratWeightedSum
          (fun monomial => weight (monoMul source.1 monomial)) right
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv _)
  | target :: rest => by
      change
        (source.2 * target.2) *
              weight (monoMul source.1 target.1) +
            ratWeightedSum weight
              (rest.map fun other =>
                (monoMul source.1 other.1,
                  source.2 * other.2)) ≈
          source.2 *
            (target.2 * weight (monoMul source.1 target.1) +
              ratWeightedSum
                (fun monomial => weight (monoMul source.1 monomial)) rest)
      refine Q'.eqv_trans _
        (source.2 *
              (target.2 * weight (monoMul source.1 target.1)) +
            source.2 *
              ratWeightedSum
                (fun monomial => weight (monoMul source.1 monomial)) rest) _
        (Q'.add_eqv_congr'
          (Q'.mul_assoc_eqv _ _ _)
          (ratWeightedSum_mulRow weight source rest)) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv _ _ _)

/-- Multiplication by a fixed left polynomial preserves coefficient equality. -/
theorem RatPolyCoeffEqv.mul_left
    (factor : RatPoly) {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (polyMul factor left) (polyMul factor right) := by
  intro weight
  induction factor with
  | nil => exact Q'.eqv_refl 0
  | cons source rest induction =>
      change
        ratWeightedSum weight
            (polyAdd
              (left.map fun target =>
                (monoMul source.1 target.1,
                  source.2 * target.2))
              (polyMul rest left)) ≈
          ratWeightedSum weight
            (polyAdd
              (right.map fun target =>
                (monoMul source.1 target.1,
                  source.2 * target.2))
              (polyMul rest right))
      refine Q'.eqv_trans _
        (ratWeightedSum weight
            (left.map fun target =>
              (monoMul source.1 target.1,
                source.2 * target.2)) +
          ratWeightedSum weight (polyMul rest left)) _
        (ratWeightedSum_add weight _ _) ?_
      refine Q'.eqv_trans _
        (ratWeightedSum weight
            (right.map fun target =>
              (monoMul source.1 target.1,
                source.2 * target.2)) +
          ratWeightedSum weight (polyMul rest right)) _ ?_ ?_
      · apply Q'.add_eqv_congr'
        · refine Q'.eqv_trans _
            (source.2 *
              ratWeightedSum
                (fun monomial => weight (monoMul source.1 monomial))
                left) _
            (ratWeightedSum_mulRow weight source left) ?_
          refine Q'.eqv_trans _
            (source.2 *
              ratWeightedSum
                (fun monomial => weight (monoMul source.1 monomial))
                right) _
            (Q'.mul_eqv_congr_left _ _ _ (h _)) ?_
          exact Q'.eqv_symm
            (ratWeightedSum_mulRow weight source right)
        · exact induction
      · exact Q'.eqv_symm (ratWeightedSum_add weight _ _)

private theorem ratWeightedSum_polyMul
    (weight : List Nat → Q') : ∀ left right : RatPoly,
    ratWeightedSum weight (polyMul left right) ≈
      ratWeightedSum
        (fun monomial =>
          ratWeightedSum
            (fun other => weight (monoMul monomial other)) right)
        left
  | [], _ => Q'.eqv_refl 0
  | source :: rest, right => by
      change
        ratWeightedSum weight
            (polyAdd
              (right.map fun target =>
                (monoMul source.1 target.1,
                  source.2 * target.2))
              (polyMul rest right)) ≈
          source.2 *
              ratWeightedSum
                (fun other => weight (monoMul source.1 other)) right +
            ratWeightedSum
              (fun monomial =>
                ratWeightedSum
                  (fun other => weight (monoMul monomial other)) right)
              rest
      refine Q'.eqv_trans _
        (ratWeightedSum weight
            (right.map fun target =>
              (monoMul source.1 target.1,
                source.2 * target.2)) +
          ratWeightedSum weight (polyMul rest right)) _
        (ratWeightedSum_add weight _ _) ?_
      exact Q'.add_eqv_congr'
        (ratWeightedSum_mulRow weight source right)
        (ratWeightedSum_polyMul weight rest right)

/-- Multiplication by a fixed right polynomial preserves coefficient equality. -/
theorem RatPolyCoeffEqv.mul_right
    {left right : RatPoly} (h : RatPolyCoeffEqv left right)
    (factor : RatPoly) :
    RatPolyCoeffEqv
      (polyMul left factor) (polyMul right factor) := by
  intro weight
  let transformed : List Nat → Q' := fun monomial =>
    ratWeightedSum
      (fun other => weight (monoMul monomial other)) factor
  refine Q'.eqv_trans _
    (ratWeightedSum transformed left) _
    (ratWeightedSum_polyMul weight left factor) ?_
  refine Q'.eqv_trans _
    (ratWeightedSum transformed right) _
    (h transformed) ?_
  exact Q'.eqv_symm
    (ratWeightedSum_polyMul weight right factor)

theorem RatPolyCoeffEqv.mul
    {left left' right right' : RatPoly}
    (hleft : RatPolyCoeffEqv left left')
    (hright : RatPolyCoeffEqv right right') :
    RatPolyCoeffEqv
      (polyMul left right) (polyMul left' right') :=
  RatPolyCoeffEqv.trans
    (hleft.mul_right right)
    (RatPolyCoeffEqv.mul_left left' hright)

theorem RatPolyCoeffEqv.polyMul_smul_left
    (scale : Q') (left right : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polySmul scale left) right)
      (polySmul scale (polyMul left right)) := by
  intro weight
  let transformed : List Nat → Q' := fun monomial =>
    ratWeightedSum
      (fun other => weight (monoMul monomial other)) right
  refine Q'.eqv_trans _
    (ratWeightedSum transformed (polySmul scale left)) _
    (ratWeightedSum_polyMul weight (polySmul scale left) right) ?_
  refine Q'.eqv_trans _
    (scale * ratWeightedSum transformed left) _
    (ratWeightedSum_smul transformed scale left) ?_
  refine Q'.eqv_trans _
    (scale * ratWeightedSum weight (polyMul left right)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (ratWeightedSum_polyMul weight left right))) ?_
  exact Q'.eqv_symm
    (ratWeightedSum_smul weight scale (polyMul left right))

/-! ## Formal monomial derivatives -/

/-- Decrement one exponent, preserving the literal exponent-vector length. -/
def lowerExponentAt : Nat → List Nat → List Nat
  | _, [] => []
  | 0, exponent :: rest => (exponent - 1) :: rest
  | coordinate + 1, exponent :: rest =>
      exponent :: lowerExponentAt coordinate rest

theorem exponentAt_monoMul
    (left right : List Nat) (coordinate : Nat) :
    exponentAt (monoMul left right) coordinate =
      exponentAt left coordinate + exponentAt right coordinate := by
  induction left generalizing right coordinate with
  | nil => simp [monoMul, exponentAt]
  | cons exponent rest induction =>
      cases right with
      | nil => simp [monoMul, exponentAt]
      | cons other otherRest =>
          cases coordinate with
          | zero => simp [monoMul, exponentAt]
          | succ coordinate =>
              change exponentAt (monoMul rest otherRest) coordinate =
                exponentAt rest coordinate +
                  exponentAt otherRest coordinate
              exact induction otherRest coordinate

theorem lowerExponentAt_monoMul_left
    (coordinate : Nat) (left right : List Nat)
    (hpositive : 0 < exponentAt left coordinate) :
    lowerExponentAt coordinate (monoMul left right) =
      monoMul (lowerExponentAt coordinate left) right := by
  induction coordinate generalizing left right with
  | zero =>
      cases left with
      | nil => simp [exponentAt] at hpositive
      | cons exponent rest =>
          cases right with
          | nil => rfl
          | cons other otherRest =>
              simp only [lowerExponentAt, monoMul]
              congr 1
              simp [exponentAt] at hpositive
              omega
  | succ coordinate induction =>
      cases left with
      | nil => simp [exponentAt] at hpositive
      | cons exponent rest =>
          cases right with
          | nil => rfl
          | cons other otherRest =>
              simp only [lowerExponentAt, monoMul]
              congr 1
              apply induction rest otherRest
              exact hpositive

theorem lowerExponentAt_monoMul_right
    (coordinate : Nat) (left right : List Nat)
    (hpositive : 0 < exponentAt right coordinate) :
    lowerExponentAt coordinate (monoMul left right) =
      monoMul left (lowerExponentAt coordinate right) := by
  induction coordinate generalizing left right with
  | zero =>
      cases right with
      | nil => simp [exponentAt] at hpositive
      | cons exponent rest =>
          cases left with
          | nil => rfl
          | cons other otherRest =>
              simp only [lowerExponentAt, monoMul]
              congr 1
              simp [exponentAt] at hpositive
              omega
  | succ coordinate induction =>
      cases right with
      | nil => simp [exponentAt] at hpositive
      | cons exponent rest =>
          cases left with
          | nil => rfl
          | cons other otherRest =>
              simp only [lowerExponentAt, monoMul]
              congr 1
              apply induction otherRest rest
              exact hpositive

theorem monoMul_varMono_lowerExponentAt
    (coordinate : Nat) (monomial : List Nat)
    (hpositive : 0 < exponentAt monomial coordinate) :
    monoMul (varMono coordinate)
        (lowerExponentAt coordinate monomial) = monomial := by
  induction coordinate generalizing monomial with
  | zero =>
      cases monomial with
      | nil => simp [exponentAt] at hpositive
      | cons exponent rest =>
          simp only [varMono, List.replicate_zero, List.nil_append,
            lowerExponentAt, monoMul]
          congr 1
          simp [exponentAt] at hpositive
          omega
  | succ coordinate induction =>
      cases monomial with
      | nil => simp [exponentAt] at hpositive
      | cons exponent rest =>
          change
            monoMul (0 :: varMono coordinate)
                (exponent :: lowerExponentAt coordinate rest) =
              exponent :: rest
          simp only [monoMul, Nat.zero_add, List.cons.injEq, true_and]
          exact induction rest hpositive

/-- Formal partial derivative in one carrier coordinate.  Terms with zero
exponent are retained with coefficient zero; coefficient-probe equality
removes them constructively. -/
def ratDerivative (coordinate : Nat) (polynomial : RatPoly) : RatPoly :=
  polynomial.map fun term =>
    (lowerExponentAt coordinate term.1,
      Q'.ofNat (exponentAt term.1 coordinate) * term.2)

/-- The selected quaternion is block zero, hence coordinates `0,1,2,3`. -/
def headLaplacian (polynomial : RatPoly) : RatPoly :=
  polyAdd (ratDerivative 0 (ratDerivative 0 polynomial))
    (polyAdd (ratDerivative 1 (ratDerivative 1 polynomial))
      (polyAdd (ratDerivative 2 (ratDerivative 2 polynomial))
        (ratDerivative 3 (ratDerivative 3 polynomial))))

/-- Dot product of selected-head gradients. -/
def headGradientDot (left right : RatPoly) : RatPoly :=
  polyAdd (polyMul (ratDerivative 0 left) (ratDerivative 0 right))
    (polyAdd
      (polyMul (ratDerivative 1 left) (ratDerivative 1 right))
      (polyAdd
        (polyMul (ratDerivative 2 left) (ratDerivative 2 right))
        (polyMul (ratDerivative 3 left) (ratDerivative 3 right))))

/-- Polynomial Euler field in the selected quaternion block. -/
def headEuler (polynomial : RatPoly) : RatPoly :=
  polyAdd (polyMul (polyVar 0) (ratDerivative 0 polynomial))
    (polyAdd
      (polyMul (polyVar 1) (ratDerivative 1 polynomial))
      (polyAdd
        (polyMul (polyVar 2) (ratDerivative 2 polynomial))
        (polyMul (polyVar 3) (ratDerivative 3 polynomial))))

def derivativeProbe
    (coordinate : Nat) (weight : List Nat → Q')
    (monomial : List Nat) : Q' :=
  Q'.ofNat (exponentAt monomial coordinate) *
    weight (lowerExponentAt coordinate monomial)

/-- A formal derivative is the transpose of the corresponding transformed
coefficient probe. -/
theorem ratWeightedSum_derivative
    (coordinate : Nat) (weight : List Nat → Q') :
    ∀ polynomial : RatPoly,
    ratWeightedSum weight (ratDerivative coordinate polynomial) ≈
      ratWeightedSum (derivativeProbe coordinate weight) polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (Q'.ofNat (exponentAt term.1 coordinate) * term.2) *
              weight (lowerExponentAt coordinate term.1) +
            ratWeightedSum weight (ratDerivative coordinate rest) ≈
          term.2 *
              (Q'.ofNat (exponentAt term.1 coordinate) *
                weight (lowerExponentAt coordinate term.1)) +
            ratWeightedSum (derivativeProbe coordinate weight) rest
      apply Q'.add_eqv_congr'
      · refine Q'.eqv_trans _
          (Q'.ofNat (exponentAt term.1 coordinate) *
            (term.2 * weight (lowerExponentAt coordinate term.1))) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat (exponentAt term.1 coordinate) *
            (weight (lowerExponentAt coordinate term.1) * term.2)) _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)) ?_
        refine Q'.eqv_trans _
          ((Q'.ofNat (exponentAt term.1 coordinate) *
              weight (lowerExponentAt coordinate term.1)) * term.2) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
        exact Q'.mul_comm_eqv _ _
      · exact ratWeightedSum_derivative coordinate weight rest

def eulerCoordinateProbe
    (coordinate : Nat) (weight : List Nat → Q')
    (monomial : List Nat) : Q' :=
  Q'.ofNat (exponentAt monomial coordinate) * weight monomial

private theorem ratWeightedSum_eulerCoordinate
    (coordinate : Nat) (weight : List Nat → Q') :
    ∀ polynomial : RatPoly,
    ratWeightedSum weight
        (polyMul (polyVar coordinate)
          (ratDerivative coordinate polynomial)) ≈
      ratWeightedSum (eulerCoordinateProbe coordinate weight) polynomial
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (1 * (Q'.ofNat (exponentAt term.1 coordinate) * term.2)) *
              weight
                (monoMul (varMono coordinate)
                  (lowerExponentAt coordinate term.1)) +
            ratWeightedSum weight
              (polyMul (polyVar coordinate)
                (ratDerivative coordinate rest)) ≈
          term.2 *
              (Q'.ofNat (exponentAt term.1 coordinate) *
                weight term.1) +
            ratWeightedSum (eulerCoordinateProbe coordinate weight) rest
      apply Q'.add_eqv_congr'
      · by_cases hzero : exponentAt term.1 coordinate = 0
        · rw [hzero]
          q_ring
        · rw [monoMul_varMono_lowerExponentAt coordinate term.1
            (Nat.pos_of_ne_zero hzero)]
          q_ring
      · exact ratWeightedSum_eulerCoordinate coordinate weight rest

private theorem eulerProbeSum_homogeneous
    (degree : Nat) (weight : List Nat → Q') :
    ∀ polynomial : RatPoly,
    HasQuaternionBlockDegree 0 degree polynomial →
    ratWeightedSum (eulerCoordinateProbe 0 weight) polynomial +
        (ratWeightedSum (eulerCoordinateProbe 1 weight) polynomial +
          (ratWeightedSum (eulerCoordinateProbe 2 weight) polynomial +
            ratWeightedSum (eulerCoordinateProbe 3 weight) polynomial)) ≈
      Q'.ofNat degree * ratWeightedSum weight polynomial
  | [], _ => by
      change (0 : Q') + (0 + (0 + 0)) ≈ Q'.ofNat degree * 0
      q_ring
  | term :: rest, hdegree => by
      have hterm := hdegree term List.mem_cons_self
      have hrest : HasQuaternionBlockDegree 0 degree rest := by
        intro other hother
        exact hdegree other (List.mem_cons_of_mem term hother)
      let e0 := exponentAt term.1 0
      let e1 := exponentAt term.1 1
      let e2 := exponentAt term.1 2
      let e3 := exponentAt term.1 3
      let value := weight term.1
      let tail0 := ratWeightedSum (eulerCoordinateProbe 0 weight) rest
      let tail1 := ratWeightedSum (eulerCoordinateProbe 1 weight) rest
      let tail2 := ratWeightedSum (eulerCoordinateProbe 2 weight) rest
      let tail3 := ratWeightedSum (eulerCoordinateProbe 3 weight) rest
      let tail := ratWeightedSum weight rest
      change
        (term.2 * (Q'.ofNat e0 * value) + tail0) +
            ((term.2 * (Q'.ofNat e1 * value) + tail1) +
              ((term.2 * (Q'.ofNat e2 * value) + tail2) +
                (term.2 * (Q'.ofNat e3 * value) + tail3))) ≈
          Q'.ofNat degree * (term.2 * value + tail)
      refine Q'.eqv_trans _
        ((term.2 * (Q'.ofNat e0 * value) +
            (term.2 * (Q'.ofNat e1 * value) +
              (term.2 * (Q'.ofNat e2 * value) +
                term.2 * (Q'.ofNat e3 * value)))) +
          (tail0 + (tail1 + (tail2 + tail3)))) _ ?_ ?_
      · q_ring
      refine Q'.eqv_trans _
        ((term.2 * (Q'.ofNat e0 * value) +
            (term.2 * (Q'.ofNat e1 * value) +
              (term.2 * (Q'.ofNat e2 * value) +
                term.2 * (Q'.ofNat e3 * value)))) +
          Q'.ofNat degree * tail) _
        (Q'.add_eqv_congr_left _ _ _
          (eulerProbeSum_homogeneous degree weight rest hrest)) ?_
      unfold quaternionBlockDegree at hterm
      simp only [Nat.mul_zero, Nat.zero_add] at hterm
      have hsum : e0 + (e1 + (e2 + e3)) = degree := by
        omega
      rw [← hsum]
      q_ring

/-- Constructive Euler identity for every polynomial homogeneous in the
selected quaternion block. -/
theorem headEuler_of_blockDegree
    (degree : Nat) (polynomial : RatPoly)
    (hdegree : HasQuaternionBlockDegree 0 degree polynomial) :
    RatPolyCoeffEqv (headEuler polynomial)
      (polySmul (Q'.ofNat degree) polynomial) := by
  intro weight
  unfold headEuler
  refine Q'.eqv_trans _
    (ratWeightedSum weight
        (polyMul (polyVar 0) (ratDerivative 0 polynomial)) +
      (ratWeightedSum weight
          (polyMul (polyVar 1) (ratDerivative 1 polynomial)) +
        (ratWeightedSum weight
            (polyMul (polyVar 2) (ratDerivative 2 polynomial)) +
          ratWeightedSum weight
            (polyMul (polyVar 3) (ratDerivative 3 polynomial))))) _ ?_ ?_
  · exact Q'.eqv_trans _
      (ratWeightedSum weight
          (polyMul (polyVar 0) (ratDerivative 0 polynomial)) +
        ratWeightedSum weight
          (polyAdd
            (polyMul (polyVar 1) (ratDerivative 1 polynomial))
            (polyAdd
              (polyMul (polyVar 2) (ratDerivative 2 polynomial))
              (polyMul (polyVar 3) (ratDerivative 3 polynomial))))) _
      (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _
          (ratWeightedSum weight
              (polyMul (polyVar 1) (ratDerivative 1 polynomial)) +
            ratWeightedSum weight
              (polyAdd
                (polyMul (polyVar 2) (ratDerivative 2 polynomial))
                (polyMul (polyVar 3) (ratDerivative 3 polynomial)))) _
          (ratWeightedSum_add weight _ _)
          (Q'.add_eqv_congr_left _ _ _
            (ratWeightedSum_add weight _ _))))
  · refine Q'.eqv_trans _
      (ratWeightedSum (eulerCoordinateProbe 0 weight) polynomial +
        (ratWeightedSum (eulerCoordinateProbe 1 weight) polynomial +
          (ratWeightedSum (eulerCoordinateProbe 2 weight) polynomial +
            ratWeightedSum (eulerCoordinateProbe 3 weight) polynomial))) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (ratWeightedSum_eulerCoordinate 0 weight polynomial)
        (Q'.add_eqv_congr'
          (ratWeightedSum_eulerCoordinate 1 weight polynomial)
          (Q'.add_eqv_congr'
            (ratWeightedSum_eulerCoordinate 2 weight polynomial)
            (ratWeightedSum_eulerCoordinate 3 weight polynomial)))
    · exact Q'.eqv_trans _
        (Q'.ofNat degree * ratWeightedSum weight polynomial) _
        (eulerProbeSum_homogeneous degree weight polynomial hdegree)
        (Q'.eqv_symm
          (ratWeightedSum_smul weight (Q'.ofNat degree) polynomial))

/-- Formal differentiation respects coefficient equality. -/
theorem RatPolyCoeffEqv.derivative
    (coordinate : Nat) {left right : RatPoly}
    (h : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv
      (ratDerivative coordinate left)
      (ratDerivative coordinate right) := by
  intro weight
  refine Q'.eqv_trans _
    (ratWeightedSum (derivativeProbe coordinate weight) left) _
    (ratWeightedSum_derivative coordinate weight left) ?_
  refine Q'.eqv_trans _
    (ratWeightedSum (derivativeProbe coordinate weight) right) _
    (h _) ?_
  exact Q'.eqv_symm
    (ratWeightedSum_derivative coordinate weight right)

private theorem exponentAt_eq_zero_of_headDegree_zero
    (coordinate : Nat) (hcoordinate : coordinate < 4)
    (monomial : List Nat)
    (hdegree : quaternionBlockDegree monomial 0 = 0) :
    exponentAt monomial coordinate = 0 := by
  unfold quaternionBlockDegree at hdegree
  simp only [Nat.mul_zero, Nat.zero_add] at hdegree
  have hcases :
      coordinate = 0 ∨ coordinate = 1 ∨
        coordinate = 2 ∨ coordinate = 3 := by
    omega
  rcases hcases with h | h | h | h <;> subst coordinate <;> omega

/-- A polynomial of selected-head degree zero has zero formal derivative in
each of the four selected coordinates.  Tail monomials are retained. -/
theorem ratDerivative_eq_zero_of_headDegree_zero
    (coordinate : Nat) (hcoordinate : coordinate < 4) :
    ∀ (polynomial : RatPoly),
      HasQuaternionBlockDegree 0 0 polynomial →
      RatPolyCoeffEqv (ratDerivative coordinate polynomial) polyZero
  | [], _ => RatPolyCoeffEqv.refl polyZero
  | term :: rest, hdegree => by
      have htermDegree := hdegree term List.mem_cons_self
      have hrestDegree : HasQuaternionBlockDegree 0 0 rest := by
        intro other hother
        exact hdegree other (List.mem_cons_of_mem term hother)
      have hzero : exponentAt term.1 coordinate = 0 :=
        exponentAt_eq_zero_of_headDegree_zero
          coordinate hcoordinate term.1 htermDegree
      intro weight
      change
        (Q'.ofNat (exponentAt term.1 coordinate) * term.2) *
              weight (lowerExponentAt coordinate term.1) +
            ratWeightedSum weight (ratDerivative coordinate rest) ≈ 0
      rw [hzero]
      refine Q'.eqv_trans _
        (ratWeightedSum weight (ratDerivative coordinate rest)) _ ?_ ?_
      · q_ring
      · exact ratDerivative_eq_zero_of_headDegree_zero
          coordinate hcoordinate rest hrestDegree weight

/-- The derivative of the selected squared radius is twice its matching
coordinate. -/
theorem ratDerivative_headRadius
    (coordinate : Nat) (hcoordinate : coordinate < 4) :
    RatPolyCoeffEqv
      (ratDerivative coordinate (quaternionRadiusPolynomial 0))
      (polySmul 2 (polyVar coordinate)) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  have hcases :
      coordinate = 0 ∨ coordinate = 1 ∨
        coordinate = 2 ∨ coordinate = 3 := by
    omega
  rcases hcases with h | h | h | h <;> subst coordinate <;> decide

private theorem derivative_single_mul_single
    (coordinate : Nat) (first second : RatTerm) :
    RatPolyCoeffEqv
      (ratDerivative coordinate (polyMul [first] [second]))
      (polyAdd
        (polyMul (ratDerivative coordinate [first]) [second])
        (polyMul [first] (ratDerivative coordinate [second]))) := by
  intro weight
  simp [ratDerivative, polyMul, polyAdd, ratWeightedSum]
  change
    (Q'.ofNat
          (exponentAt (monoMul first.1 second.1) coordinate) *
        (first.2 * second.2)) *
          weight
            (lowerExponentAt coordinate
              (monoMul first.1 second.1)) + 0 ≈
      ((Q'.ofNat (exponentAt first.1 coordinate) * first.2) *
          second.2) *
            weight
              (monoMul
                (lowerExponentAt coordinate first.1) second.1) +
        ((first.2 *
              (Q'.ofNat (exponentAt second.1 coordinate) * second.2)) *
                weight
                  (monoMul first.1
                    (lowerExponentAt coordinate second.1)) +
            0)
  rw [exponentAt_monoMul]
  by_cases hfirst : exponentAt first.1 coordinate = 0
  · by_cases hsecond : exponentAt second.1 coordinate = 0
    · rw [hfirst, hsecond]
      q_ring
    · have hsecondPositive :
          0 < exponentAt second.1 coordinate :=
        Nat.pos_of_ne_zero hsecond
      rw [hfirst,
        lowerExponentAt_monoMul_right coordinate first.1 second.1
          hsecondPositive]
      q_ring
  · have hfirstPositive :
        0 < exponentAt first.1 coordinate :=
      Nat.pos_of_ne_zero hfirst
    rw [lowerExponentAt_monoMul_left coordinate first.1 second.1
      hfirstPositive]
    by_cases hsecond : exponentAt second.1 coordinate = 0
    · rw [hsecond]
      q_ring
    · have hsecondPositive :
          0 < exponentAt second.1 coordinate :=
        Nat.pos_of_ne_zero hsecond
      have hright :=
        lowerExponentAt_monoMul_right coordinate first.1 second.1
          hsecondPositive
      have hleft :=
        lowerExponentAt_monoMul_left coordinate first.1 second.1
          hfirstPositive
      have hsame :
          monoMul (lowerExponentAt coordinate first.1) second.1 =
            monoMul first.1 (lowerExponentAt coordinate second.1) := by
        exact hleft.symm.trans hright
      rw [hsame]
      q_ring

theorem RatPolyCoeffEqv.four_add_swap
    (first second third fourth : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyAdd first second) (polyAdd third fourth))
      (polyAdd (polyAdd first third) (polyAdd second fourth)) := by
  intro weight
  let a := ratWeightedSum weight first
  let b := ratWeightedSum weight second
  let c := ratWeightedSum weight third
  let d := ratWeightedSum weight fourth
  have hleft :
      ratWeightedSum weight
          (polyAdd (polyAdd first second) (polyAdd third fourth)) ≈
        (a + b) + (c + d) := by
    exact Q'.eqv_trans _
      (ratWeightedSum weight (polyAdd first second) +
        ratWeightedSum weight (polyAdd third fourth)) _
      (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr'
        (ratWeightedSum_add weight first second)
        (ratWeightedSum_add weight third fourth))
  have hright :
      ratWeightedSum weight
          (polyAdd (polyAdd first third) (polyAdd second fourth)) ≈
        (a + c) + (b + d) := by
    exact Q'.eqv_trans _
      (ratWeightedSum weight (polyAdd first third) +
        ratWeightedSum weight (polyAdd second fourth)) _
      (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr'
        (ratWeightedSum_add weight first third)
        (ratWeightedSum_add weight second fourth))
  refine Q'.eqv_trans _ _ _ hleft ?_
  refine Q'.eqv_trans _ ((a + c) + (b + d)) _ ?_
    (Q'.eqv_symm hright)
  q_ring

theorem ratDerivative_add_exact
    (coordinate : Nat) (left right : RatPoly) :
    ratDerivative coordinate (polyAdd left right) =
      polyAdd (ratDerivative coordinate left)
        (ratDerivative coordinate right) := by
  simp [ratDerivative, polyAdd]

theorem polyMul_add_left_exact
    (left right factor : RatPoly) :
    polyMul (polyAdd left right) factor =
      polyAdd (polyMul left factor) (polyMul right factor) := by
  simp [polyMul, polyAdd]

theorem polyMul_cons_left_exact
    (first : RatTerm) (rest right : RatPoly) :
    polyMul (first :: rest) right =
      polyAdd (polyMul [first] right) (polyMul rest right) := by
  simp [polyMul, polyAdd]

theorem polyMul_single_add_right_exact
    (factor : RatTerm) (left right : RatPoly) :
    polyMul [factor] (polyAdd left right) =
      polyAdd (polyMul [factor] left) (polyMul [factor] right) := by
  simp [polyMul, polyAdd]

theorem polyMul_single_cons_right_exact
    (first second : RatTerm) (rest : RatPoly) :
    polyMul [first] (second :: rest) =
      polyAdd (polyMul [first] [second])
        (polyMul [first] rest) := by
  simp [polyMul, polyAdd]

theorem polyMul_derivative_single_add_right_exact
    (coordinate : Nat) (factor : RatTerm) (left right : RatPoly) :
    polyMul (ratDerivative coordinate [factor]) (polyAdd left right) =
      polyAdd
        (polyMul (ratDerivative coordinate [factor]) left)
        (polyMul (ratDerivative coordinate [factor]) right) := by
  simp [ratDerivative, polyMul, polyAdd]

private theorem termwise_assoc_row
    (first second : RatTerm) : ∀ rest : RatPoly,
    RatPolyTermwiseEqv
      (rest.map fun third =>
        (monoMul (monoMul first.1 second.1) third.1,
          (first.2 * second.2) * third.2))
      (rest.map fun third =>
        (monoMul first.1 (monoMul second.1 third.1),
          first.2 * (second.2 * third.2)))
  | [] => True.intro
  | third :: rest =>
      ⟨monoMul_assoc first.1 second.1 third.1,
       Q'.mul_assoc_eqv first.2 second.2 third.2,
       termwise_assoc_row first second rest⟩

private theorem termwise_polyMul_assoc_single
    (first : RatTerm) : ∀ middle right : RatPoly,
    RatPolyTermwiseEqv
      (polyMul (polyMul [first] middle) right)
      (polyMul [first] (polyMul middle right))
  | [], _ => True.intro
  | second :: rest, right => by
      rw [polyMul_single_cons_right_exact first second rest,
        polyMul_add_left_exact
          (polyMul [first] [second])
          (polyMul [first] rest) right,
        polyMul_cons_left_exact second rest right,
        polyMul_single_add_right_exact
          first (polyMul [second] right) (polyMul rest right)]
      exact RatPolyTermwiseEqv.append
        (by
          simpa [polyMul, polyAdd, Function.comp_def]
            using termwise_assoc_row first second right)
        (termwise_polyMul_assoc_single first rest right)

private theorem termwise_polyMul_assoc : ∀ first second third : RatPoly,
    RatPolyTermwiseEqv
      (polyMul (polyMul first second) third)
      (polyMul first (polyMul second third))
  | [], _, _ => True.intro
  | first :: rest, second, third => by
      rw [polyMul_cons_left_exact first rest second,
        polyMul_add_left_exact
          (polyMul [first] second)
          (polyMul rest second) third,
        polyMul_cons_left_exact
          first rest (polyMul second third)]
      exact RatPolyTermwiseEqv.append
        (termwise_polyMul_assoc_single first second third)
        (termwise_polyMul_assoc rest second third)

theorem RatPolyCoeffEqv.mul_assoc
    (first second third : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polyMul first second) third)
      (polyMul first (polyMul second third)) := by
  intro weight
  exact ratWeightedSum_termwise_eqv weight
    (termwise_polyMul_assoc first second third)

/-! ## Finite polynomial sums in the coefficient quotient -/

def polySum : List RatPoly → RatPoly
  | [] => polyZero
  | polynomial :: rest => polyAdd polynomial (polySum rest)

def qListSum : List Q' → Q'
  | [] => 0
  | value :: rest => value + qListSum rest

theorem ratWeightedSum_polySum
    (weight : List Nat → Q') : ∀ polynomials : List RatPoly,
    ratWeightedSum weight (polySum polynomials) ≈
      qListSum (polynomials.map (ratWeightedSum weight))
  | [] => Q'.eqv_refl 0
  | polynomial :: rest => by
      refine Q'.eqv_trans _
        (ratWeightedSum weight polynomial +
          ratWeightedSum weight (polySum rest)) _
        (ratWeightedSum_add weight polynomial (polySum rest)) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (ratWeightedSum_polySum weight rest)

theorem RatPolyCoeffEqv.polySum_append
    (first second : List RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polySum first) (polySum second))
      (polySum (first ++ second)) := by
  intro weight
  refine Q'.eqv_trans _
    (ratWeightedSum weight (polySum first) +
      ratWeightedSum weight (polySum second)) _
    (ratWeightedSum_add weight _ _) ?_
  refine Q'.eqv_trans _
    (qListSum (first.map (ratWeightedSum weight)) +
      qListSum (second.map (ratWeightedSum weight))) _
    (Q'.add_eqv_congr'
      (ratWeightedSum_polySum weight first)
      (ratWeightedSum_polySum weight second)) ?_
  refine Q'.eqv_trans _
    (qListSum ((first ++ second).map (ratWeightedSum weight))) _ ?_
    (Q'.eqv_symm (ratWeightedSum_polySum weight (first ++ second)))
  induction first with
  | nil => exact QPoly.q_zero_add_eqv _
  | cons value rest induction =>
      change
        ratWeightedSum weight value +
              qListSum (rest.map (ratWeightedSum weight)) +
              qListSum (second.map (ratWeightedSum weight)) ≈
          ratWeightedSum weight value +
            qListSum ((rest ++ second).map (ratWeightedSum weight))
      exact Q'.eqv_trans _
        (ratWeightedSum weight value +
          (qListSum (rest.map (ratWeightedSum weight)) +
            qListSum (second.map (ratWeightedSum weight)))) _
        (Q'.add_assoc_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ induction)

theorem RatPolyCoeffEqv.polySum_mul_right
    (polynomials : List RatPoly) (factor : RatPoly) :
    RatPolyCoeffEqv
      (polyMul (polySum polynomials) factor)
      (polySum (polynomials.map fun polynomial =>
        polyMul polynomial factor)) := by
  induction polynomials with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons polynomial rest induction =>
      change RatPolyCoeffEqv
        (polyMul (polyAdd polynomial (polySum rest)) factor)
        (polyAdd (polyMul polynomial factor)
          (polySum (rest.map fun other => polyMul other factor)))
      rw [polyMul_add_left_exact]
      exact RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.refl _) induction

/-- Right distributivity, at coefficient equality (the literal list orders
are different when the left factor contains more than one term). -/
theorem RatPolyCoeffEqv.mul_add_right
    (factor left right : RatPoly) :
    RatPolyCoeffEqv
      (polyMul factor (polyAdd left right))
      (polyAdd (polyMul factor left) (polyMul factor right)) := by
  induction factor with
  | nil => exact RatPolyCoeffEqv.refl polyZero
  | cons source rest induction =>
      have hrow :
          RatPolyCoeffEqv
            (polyMul [source] (polyAdd left right))
            (polyAdd (polyMul [source] left)
              (polyMul [source] right)) := by
        rw [polyMul_single_add_right_exact]
        exact RatPolyCoeffEqv.refl _
      have hcombined := RatPolyCoeffEqv.add hrow induction
      have hswap := RatPolyCoeffEqv.four_add_swap
        (polyMul [source] left) (polyMul [source] right)
        (polyMul rest left) (polyMul rest right)
      rw [polyMul_cons_left_exact source rest (polyAdd left right),
        polyMul_cons_left_exact source rest left,
        polyMul_cons_left_exact source rest right]
      change RatPolyCoeffEqv
        (polyAdd (polyMul [source] (polyAdd left right))
          (polyMul rest (polyAdd left right)))
        (polyAdd
          (polyAdd (polyMul [source] left) (polyMul rest left))
          (polyAdd (polyMul [source] right) (polyMul rest right)))
      exact RatPolyCoeffEqv.trans hcombined hswap

theorem RatPolyCoeffEqv.mul_polySum_right
    (factor : RatPoly) (polynomials : List RatPoly) :
    RatPolyCoeffEqv
      (polyMul factor (polySum polynomials))
      (polySum (polynomials.map fun polynomial =>
        polyMul factor polynomial)) := by
  induction polynomials with
  | nil =>
      have hzero : polyMul factor polyZero = polyZero := by
        induction factor with
        | nil => rfl
        | cons term rest induction =>
            simp [polyMul, polyZero, induction]
      change RatPolyCoeffEqv (polyMul factor polyZero) polyZero
      rw [hzero]
      exact RatPolyCoeffEqv.refl polyZero
  | cons polynomial rest induction =>
      change RatPolyCoeffEqv
        (polyMul factor (polyAdd polynomial (polySum rest)))
        (polyAdd (polyMul factor polynomial)
          (polySum (rest.map fun other => polyMul factor other)))
      exact RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.mul_add_right factor polynomial (polySum rest))
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) induction)

private theorem single_mul_single_comm
    (first second : RatTerm) :
    RatPolyCoeffEqv (polyMul [first] [second])
      (polyMul [second] [first]) := by
  intro weight
  change
    (first.2 * second.2) * weight (monoMul first.1 second.1) + 0 ≈
      (second.2 * first.2) * weight (monoMul second.1 first.1) + 0
  rw [monoMul_comm first.1 second.1]
  q_ring

private theorem single_mul_comm
    (first : RatTerm) : ∀ right : RatPoly,
    RatPolyCoeffEqv (polyMul [first] right)
      (polyMul right [first])
  | [] => by
      simp [polyMul, polyZero]
      exact RatPolyCoeffEqv.refl polyZero
  | second :: rest => by
      rw [polyMul_single_cons_right_exact,
        polyMul_cons_left_exact second rest [first]]
      exact RatPolyCoeffEqv.add
        (single_mul_single_comm first second)
        (single_mul_comm first rest)

theorem RatPolyCoeffEqv.mul_comm : ∀ left right : RatPoly,
    RatPolyCoeffEqv (polyMul left right) (polyMul right left)
  | [], right => by
      have hzero : polyMul right polyZero = polyZero := by
        induction right with
        | nil => rfl
        | cons term rest induction =>
            simp [polyMul, polyZero]
      change RatPolyCoeffEqv polyZero (polyMul right polyZero)
      rw [hzero]
      exact RatPolyCoeffEqv.refl polyZero
  | first :: rest, right => by
      rw [polyMul_cons_left_exact first rest right]
      refine RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add
          (single_mul_comm first right)
          (RatPolyCoeffEqv.mul_comm rest right)) ?_
      exact RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.mul_add_right right [first] rest)

theorem RatPolyCoeffEqv.polyMul_smul_right
    (scale : Q') (left right : RatPoly) :
    RatPolyCoeffEqv
      (polyMul left (polySmul scale right))
      (polySmul scale (polyMul left right)) :=
  RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_comm left (polySmul scale right))
    (RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.polyMul_smul_left scale right left)
      ((RatPolyCoeffEqv.mul_comm right left).smul scale))

theorem RatPolyCoeffEqv.add_smul_same
    (first second : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polySmul first polynomial)
        (polySmul second polynomial))
      (polySmul (first + second) polynomial) := by
  intro weight
  refine Q'.eqv_trans _
    (ratWeightedSum weight (polySmul first polynomial) +
      ratWeightedSum weight (polySmul second polynomial)) _
    (ratWeightedSum_add weight _ _) ?_
  refine Q'.eqv_trans _
    (first * ratWeightedSum weight polynomial +
      second * ratWeightedSum weight polynomial) _
    (Q'.add_eqv_congr'
      (ratWeightedSum_smul weight first polynomial)
      (ratWeightedSum_smul weight second polynomial)) ?_
  refine Q'.eqv_trans _
    ((first + second) * ratWeightedSum weight polynomial) _
    (Q'.eqv_symm (q_add_mul _ _ _)) ?_
  exact Q'.eqv_symm
    (ratWeightedSum_smul weight (first + second) polynomial)

theorem RatPolyCoeffEqv.smul_zero (scale : Q') :
    RatPolyCoeffEqv (polySmul scale polyZero) polyZero := by
  exact RatPolyCoeffEqv.refl polyZero

theorem RatPolyCoeffEqv.mul_zero_left (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polyZero polynomial) polyZero := by
  exact RatPolyCoeffEqv.refl polyZero

theorem RatPolyCoeffEqv.mul_zero_right (polynomial : RatPoly) :
    RatPolyCoeffEqv (polyMul polynomial polyZero) polyZero :=
  RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_comm polynomial polyZero)
    (RatPolyCoeffEqv.mul_zero_left polynomial)

private theorem derivative_single_mul
    (coordinate : Nat) (first : RatTerm) : ∀ right : RatPoly,
    RatPolyCoeffEqv
      (ratDerivative coordinate (polyMul [first] right))
      (polyAdd
        (polyMul (ratDerivative coordinate [first]) right)
        (polyMul [first] (ratDerivative coordinate right)))
  | [] => by
      simp [ratDerivative, polyMul, polyAdd]
      exact RatPolyCoeffEqv.refl polyZero
  | second :: rest => by
      have hpair := derivative_single_mul_single coordinate first second
      have hrest := derivative_single_mul coordinate first rest
      have hcombined := RatPolyCoeffEqv.add hpair hrest
      have hswap := RatPolyCoeffEqv.four_add_swap
        (polyMul (ratDerivative coordinate [first]) [second])
        (polyMul [first] (ratDerivative coordinate [second]))
        (polyMul (ratDerivative coordinate [first]) rest)
        (polyMul [first] (ratDerivative coordinate rest))
      rw [show second :: rest = polyAdd [second] rest by rfl,
        polyMul_single_add_right_exact,
        ratDerivative_add_exact,
        polyMul_derivative_single_add_right_exact,
        ratDerivative_add_exact,
        polyMul_single_add_right_exact]
      exact RatPolyCoeffEqv.trans hcombined
        hswap

/-- Formal Leibniz rule on the full rational polynomial carrier. -/
theorem ratDerivative_mul
    (coordinate : Nat) : ∀ left right : RatPoly,
    RatPolyCoeffEqv
      (ratDerivative coordinate (polyMul left right))
      (polyAdd
        (polyMul (ratDerivative coordinate left) right)
        (polyMul left (ratDerivative coordinate right)))
  | [], right => by
      simp [ratDerivative, polyMul, polyAdd]
      exact RatPolyCoeffEqv.refl polyZero
  | first :: rest, right => by
      have hfirst := derivative_single_mul coordinate first right
      have hrest := ratDerivative_mul coordinate rest right
      have hcombined := RatPolyCoeffEqv.add hfirst hrest
      have hswap := RatPolyCoeffEqv.four_add_swap
        (polyMul (ratDerivative coordinate [first]) right)
        (polyMul [first] (ratDerivative coordinate right))
        (polyMul (ratDerivative coordinate rest) right)
        (polyMul rest (ratDerivative coordinate right))
      rw [show first :: rest = polyAdd [first] rest by rfl,
        polyMul_add_left_exact,
        ratDerivative_add_exact,
        ratDerivative_add_exact,
        polyMul_add_left_exact,
        polyMul_add_left_exact]
      exact RatPolyCoeffEqv.trans hcombined
        hswap

theorem ratDerivative_smul
    (coordinate : Nat) (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (ratDerivative coordinate (polySmul scale polynomial))
      (polySmul scale (ratDerivative coordinate polynomial)) := by
  intro weight
  refine Q'.eqv_trans _
    (ratWeightedSum (derivativeProbe coordinate weight)
      (polySmul scale polynomial)) _
    (ratWeightedSum_derivative coordinate weight _) ?_
  refine Q'.eqv_trans _
    (scale *
      ratWeightedSum (derivativeProbe coordinate weight) polynomial) _
    (ratWeightedSum_smul _ scale polynomial) ?_
  refine Q'.eqv_trans _
    (scale *
      ratWeightedSum weight (ratDerivative coordinate polynomial)) _
    (Q'.mul_eqv_congr_left scale _ _
      (Q'.eqv_symm
        (ratWeightedSum_derivative coordinate weight polynomial))) ?_
  exact Q'.eqv_symm
    (ratWeightedSum_smul weight scale
      (ratDerivative coordinate polynomial))

/-- One-coordinate second-order Leibniz rule, kept in an expanded form that
does not hide any coefficient regrouping. -/
theorem ratSecondDerivative_mul
    (coordinate : Nat) (left right : RatPoly) :
    RatPolyCoeffEqv
      (ratDerivative coordinate
        (ratDerivative coordinate (polyMul left right)))
      (polyAdd
        (polyAdd
          (polyMul
            (ratDerivative coordinate (ratDerivative coordinate left))
            right)
          (polyMul (ratDerivative coordinate left)
            (ratDerivative coordinate right)))
        (polyAdd
          (polyMul (ratDerivative coordinate left)
            (ratDerivative coordinate right))
          (polyMul left
            (ratDerivative coordinate (ratDerivative coordinate right))))) := by
  let leftFirst := ratDerivative coordinate left
  let rightFirst := ratDerivative coordinate right
  have houter :=
    RatPolyCoeffEqv.derivative coordinate
      (ratDerivative_mul coordinate left right)
  have hlinear :
      RatPolyCoeffEqv
        (ratDerivative coordinate
          (polyAdd (polyMul leftFirst right)
            (polyMul left rightFirst)))
        (polyAdd
          (ratDerivative coordinate (polyMul leftFirst right))
          (ratDerivative coordinate (polyMul left rightFirst))) := by
    rw [ratDerivative_add_exact]
    exact RatPolyCoeffEqv.refl _
  have hparts := RatPolyCoeffEqv.add
    (ratDerivative_mul coordinate leftFirst right)
    (ratDerivative_mul coordinate left rightFirst)
  exact RatPolyCoeffEqv.trans houter
    (RatPolyCoeffEqv.trans hlinear hparts)

/-- The head Laplacian respects coefficient equality. -/
theorem RatPolyCoeffEqv.headLaplacian
    {left right : RatPoly} (h : RatPolyCoeffEqv left right) :
    RatPolyCoeffEqv (headLaplacian left) (headLaplacian right) := by
  unfold SU2QuaternionRatPolyDifferential.headLaplacian
  exact RatPolyCoeffEqv.add
    ((h.derivative 0).derivative 0)
    (RatPolyCoeffEqv.add
      ((h.derivative 1).derivative 1)
      (RatPolyCoeffEqv.add
        ((h.derivative 2).derivative 2)
        ((h.derivative 3).derivative 3)))

/-- Expanded four-coordinate Laplacian product rule. -/
theorem headLaplacian_mul_expanded
    (left right : RatPoly) :
    RatPolyCoeffEqv
      (headLaplacian (polyMul left right))
      (polyAdd
        (polyAdd
          (polyAdd
            (polyMul (ratDerivative 0 (ratDerivative 0 left)) right)
            (polyMul (ratDerivative 0 left) (ratDerivative 0 right)))
          (polyAdd
            (polyMul (ratDerivative 0 left) (ratDerivative 0 right))
            (polyMul left (ratDerivative 0 (ratDerivative 0 right)))))
        (polyAdd
          (polyAdd
            (polyAdd
              (polyMul (ratDerivative 1 (ratDerivative 1 left)) right)
              (polyMul (ratDerivative 1 left) (ratDerivative 1 right)))
            (polyAdd
              (polyMul (ratDerivative 1 left) (ratDerivative 1 right))
              (polyMul left (ratDerivative 1 (ratDerivative 1 right)))))
          (polyAdd
            (polyAdd
              (polyAdd
                (polyMul (ratDerivative 2 (ratDerivative 2 left)) right)
                (polyMul (ratDerivative 2 left) (ratDerivative 2 right)))
              (polyAdd
                (polyMul (ratDerivative 2 left) (ratDerivative 2 right))
                (polyMul left (ratDerivative 2 (ratDerivative 2 right)))))
            (polyAdd
              (polyAdd
                (polyMul (ratDerivative 3 (ratDerivative 3 left)) right)
                (polyMul (ratDerivative 3 left) (ratDerivative 3 right)))
              (polyAdd
                (polyMul (ratDerivative 3 left) (ratDerivative 3 right))
                (polyMul left
                  (ratDerivative 3 (ratDerivative 3 right)))))))) := by
  unfold headLaplacian
  exact RatPolyCoeffEqv.add
    (ratSecondDerivative_mul 0 left right)
    (RatPolyCoeffEqv.add
      (ratSecondDerivative_mul 1 left right)
      (RatPolyCoeffEqv.add
        (ratSecondDerivative_mul 2 left right)
        (ratSecondDerivative_mul 3 left right)))

def polyFour (first second third fourth : RatPoly) : RatPoly :=
  polyAdd first (polyAdd second (polyAdd third fourth))

theorem polyFour_eq_polySum
    (first second third fourth : RatPoly) :
    RatPolyCoeffEqv
      (polyFour first second third fourth)
      (polySum [first, second, third, fourth]) := by
  unfold polyFour polySum
  exact RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
    (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
        (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.add_zero fourth))))

theorem headLaplacian_eq_polySum (polynomial : RatPoly) :
    RatPolyCoeffEqv (headLaplacian polynomial)
      (polySum
        [ratDerivative 0 (ratDerivative 0 polynomial),
         ratDerivative 1 (ratDerivative 1 polynomial),
         ratDerivative 2 (ratDerivative 2 polynomial),
         ratDerivative 3 (ratDerivative 3 polynomial)]) := by
  change RatPolyCoeffEqv
    (polyFour
      (ratDerivative 0 (ratDerivative 0 polynomial))
      (ratDerivative 1 (ratDerivative 1 polynomial))
      (ratDerivative 2 (ratDerivative 2 polynomial))
      (ratDerivative 3 (ratDerivative 3 polynomial))) _
  exact polyFour_eq_polySum _ _ _ _

theorem headGradientDot_eq_polySum (left right : RatPoly) :
    RatPolyCoeffEqv (headGradientDot left right)
      (polySum
        [polyMul (ratDerivative 0 left) (ratDerivative 0 right),
         polyMul (ratDerivative 1 left) (ratDerivative 1 right),
         polyMul (ratDerivative 2 left) (ratDerivative 2 right),
         polyMul (ratDerivative 3 left) (ratDerivative 3 right)]) := by
  change RatPolyCoeffEqv
    (polyFour
      (polyMul (ratDerivative 0 left) (ratDerivative 0 right))
      (polyMul (ratDerivative 1 left) (ratDerivative 1 right))
      (polyMul (ratDerivative 2 left) (ratDerivative 2 right))
      (polyMul (ratDerivative 3 left) (ratDerivative 3 right))) _
  exact polyFour_eq_polySum _ _ _ _

theorem polyFour_smul
    (scale : Q') (first second third fourth : RatPoly) :
    RatPolyCoeffEqv
      (polyFour (polySmul scale first) (polySmul scale second)
        (polySmul scale third) (polySmul scale fourth))
      (polySmul scale (polyFour first second third fourth)) := by
  unfold polyFour
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
        (RatPolyCoeffEqv.symm
          (RatPolyCoeffEqv.smul_add scale third fourth)))) ?_
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
      (RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.smul_add scale second
          (polyAdd third fourth)))) ?_
  exact RatPolyCoeffEqv.symm
    (RatPolyCoeffEqv.smul_add scale first
      (polyAdd second (polyAdd third fourth)))

theorem ratWeightedSum_polyFour
    (weight : List Nat → Q')
    (first second third fourth : RatPoly) :
    ratWeightedSum weight (polyFour first second third fourth) ≈
      ratWeightedSum weight first +
        (ratWeightedSum weight second +
          (ratWeightedSum weight third +
            ratWeightedSum weight fourth)) := by
  unfold polyFour
  exact Q'.eqv_trans _ _ _
    (ratWeightedSum_add weight first
      (polyAdd second (polyAdd third fourth)))
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ _ _
        (ratWeightedSum_add weight second (polyAdd third fourth))
        (Q'.add_eqv_congr_left _ _ _
          (ratWeightedSum_add weight third fourth))))

/-- Componentwise addition distributes through a four-coordinate sum. -/
theorem polyFour_add
    (a0 a1 a2 a3 b0 b1 b2 b3 : RatPoly) :
    RatPolyCoeffEqv
      (polyFour (polyAdd a0 b0) (polyAdd a1 b1)
        (polyAdd a2 b2) (polyAdd a3 b3))
      (polyAdd (polyFour a0 a1 a2 a3)
        (polyFour b0 b1 b2 b3)) := by
  intro weight
  let A0 := ratWeightedSum weight a0
  let A1 := ratWeightedSum weight a1
  let A2 := ratWeightedSum weight a2
  let A3 := ratWeightedSum weight a3
  let B0 := ratWeightedSum weight b0
  let B1 := ratWeightedSum weight b1
  let B2 := ratWeightedSum weight b2
  let B3 := ratWeightedSum weight b3
  refine Q'.eqv_trans _
    ((A0 + B0) + ((A1 + B1) + ((A2 + B2) + (A3 + B3)))) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (ratWeightedSum_polyFour weight _ _ _ _)
      (Q'.add_eqv_congr'
        (ratWeightedSum_add weight a0 b0)
        (Q'.add_eqv_congr'
          (ratWeightedSum_add weight a1 b1)
          (Q'.add_eqv_congr'
            (ratWeightedSum_add weight a2 b2)
            (ratWeightedSum_add weight a3 b3))))
  refine Q'.eqv_trans _
    ((A0 + (A1 + (A2 + A3))) +
      (B0 + (B1 + (B2 + B3)))) _ ?_ ?_
  · q_ring
  refine Q'.eqv_trans _
    (ratWeightedSum weight (polyFour a0 a1 a2 a3) +
      ratWeightedSum weight (polyFour b0 b1 b2 b3)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.eqv_symm (ratWeightedSum_polyFour weight a0 a1 a2 a3))
      (Q'.eqv_symm (ratWeightedSum_polyFour weight b0 b1 b2 b3))
  · exact Q'.eqv_symm
      (ratWeightedSum_add weight
        (polyFour a0 a1 a2 a3) (polyFour b0 b1 b2 b3))

/-- The selected gradient dot product is symmetric coefficientwise. -/
theorem headGradientDot_comm (left right : RatPoly) :
    RatPolyCoeffEqv
      (headGradientDot left right)
      (headGradientDot right left) := by
  unfold headGradientDot
  exact RatPolyCoeffEqv.add
    (RatPolyCoeffEqv.mul_comm
      (ratDerivative 0 left) (ratDerivative 0 right))
    (RatPolyCoeffEqv.add
      (RatPolyCoeffEqv.mul_comm
        (ratDerivative 1 left) (ratDerivative 1 right))
      (RatPolyCoeffEqv.add
        (RatPolyCoeffEqv.mul_comm
          (ratDerivative 2 left) (ratDerivative 2 right))
        (RatPolyCoeffEqv.mul_comm
          (ratDerivative 3 left) (ratDerivative 3 right))))

/-- Gradient of the selected squared radius is twice the Euler field. -/
theorem headGradientDot_headRadius_left (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (headGradientDot (quaternionRadiusPolynomial 0) polynomial)
      (polySmul 2 (headEuler polynomial)) := by
  unfold headGradientDot headEuler
  have coordinate (index : Nat) (hindex : index < 4) :
      RatPolyCoeffEqv
        (polyMul
          (ratDerivative index (quaternionRadiusPolynomial 0))
          (ratDerivative index polynomial))
        (polySmul 2
          (polyMul (polyVar index)
            (ratDerivative index polynomial))) :=
    RatPolyCoeffEqv.trans
      ((ratDerivative_headRadius index hindex).mul_right
        (ratDerivative index polynomial))
      (RatPolyCoeffEqv.polyMul_smul_left 2
        (polyVar index) (ratDerivative index polynomial))
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (coordinate 0 (by omega))
      (RatPolyCoeffEqv.add (coordinate 1 (by omega))
        (RatPolyCoeffEqv.add
          (coordinate 2 (by omega)) (coordinate 3 (by omega)))))
    (polyFour_smul 2
      (polyMul (polyVar 0) (ratDerivative 0 polynomial))
      (polyMul (polyVar 1) (ratDerivative 1 polynomial))
      (polyMul (polyVar 2) (ratDerivative 2 polynomial))
      (polyMul (polyVar 3) (ratDerivative 3 polynomial)))

theorem headGradientDot_headRadius_right (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (headGradientDot polynomial (quaternionRadiusPolynomial 0))
      (polySmul 2 (headEuler polynomial)) :=
  RatPolyCoeffEqv.trans
    (headGradientDot_comm polynomial (quaternionRadiusPolynomial 0))
    (headGradientDot_headRadius_left polynomial)

/-- A head-degree-zero right factor has zero selected directional gradient. -/
theorem headGradientDot_headIndependent_right
    (differentiated independent : RatPoly)
    (hindependent : HasQuaternionBlockDegree 0 0 independent) :
    RatPolyCoeffEqv
      (headGradientDot differentiated independent) polyZero := by
  unfold headGradientDot
  have coordinate (index : Nat) (hindex : index < 4) :
      RatPolyCoeffEqv
        (polyMul (ratDerivative index differentiated)
          (ratDerivative index independent))
        polyZero :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul_left (ratDerivative index differentiated)
        (ratDerivative_eq_zero_of_headDegree_zero
          index hindex independent hindependent))
      (RatPolyCoeffEqv.mul_zero_right
        (ratDerivative index differentiated))
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (coordinate 0 (by omega))
      (RatPolyCoeffEqv.add (coordinate 1 (by omega))
        (RatPolyCoeffEqv.add
          (coordinate 2 (by omega)) (coordinate 3 (by omega)))))
    (RatPolyCoeffEqv.zero_add polyZero)

/-- Linearity of the selected Laplacian under polynomial addition. -/
theorem headLaplacian_add (left right : RatPoly) :
    RatPolyCoeffEqv
      (headLaplacian (polyAdd left right))
      (polyAdd (headLaplacian left) (headLaplacian right)) := by
  unfold headLaplacian
  simp only [ratDerivative_add_exact]
  exact polyFour_add
    (ratDerivative 0 (ratDerivative 0 left))
    (ratDerivative 1 (ratDerivative 1 left))
    (ratDerivative 2 (ratDerivative 2 left))
    (ratDerivative 3 (ratDerivative 3 left))
    (ratDerivative 0 (ratDerivative 0 right))
    (ratDerivative 1 (ratDerivative 1 right))
    (ratDerivative 2 (ratDerivative 2 right))
    (ratDerivative 3 (ratDerivative 3 right))

/-- Linearity of the selected Laplacian under rational scaling. -/
theorem headLaplacian_smul
    (scale : Q') (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (headLaplacian (polySmul scale polynomial))
      (polySmul scale (headLaplacian polynomial)) := by
  unfold headLaplacian
  have coordinate (index : Nat) : RatPolyCoeffEqv
      (ratDerivative index
        (ratDerivative index (polySmul scale polynomial)))
      (polySmul scale
        (ratDerivative index (ratDerivative index polynomial))) :=
    RatPolyCoeffEqv.trans
      ((ratDerivative_smul index scale polynomial).derivative index)
      (ratDerivative_smul index scale
        (ratDerivative index polynomial))
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (coordinate 0)
      (RatPolyCoeffEqv.add (coordinate 1)
        (RatPolyCoeffEqv.add (coordinate 2) (coordinate 3))))
    (polyFour_smul scale
      (ratDerivative 0 (ratDerivative 0 polynomial))
      (ratDerivative 1 (ratDerivative 1 polynomial))
      (ratDerivative 2 (ratDerivative 2 polynomial))
      (ratDerivative 3 (ratDerivative 3 polynomial)))

/-- Linearity of a selected directional gradient in its right argument. -/
theorem headGradientDot_add_right
    (differentiated left right : RatPoly) :
    RatPolyCoeffEqv
      (headGradientDot differentiated (polyAdd left right))
      (polyAdd
        (headGradientDot differentiated left)
        (headGradientDot differentiated right)) := by
  unfold headGradientDot
  simp only [ratDerivative_add_exact]
  have coordinate (index : Nat) :=
    RatPolyCoeffEqv.mul_add_right
      (ratDerivative index differentiated)
      (ratDerivative index left) (ratDerivative index right)
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (coordinate 0)
      (RatPolyCoeffEqv.add (coordinate 1)
        (RatPolyCoeffEqv.add (coordinate 2) (coordinate 3))))
    (polyFour_add
      (polyMul (ratDerivative 0 differentiated)
        (ratDerivative 0 left))
      (polyMul (ratDerivative 1 differentiated)
        (ratDerivative 1 left))
      (polyMul (ratDerivative 2 differentiated)
        (ratDerivative 2 left))
      (polyMul (ratDerivative 3 differentiated)
        (ratDerivative 3 left))
      (polyMul (ratDerivative 0 differentiated)
        (ratDerivative 0 right))
      (polyMul (ratDerivative 1 differentiated)
        (ratDerivative 1 right))
      (polyMul (ratDerivative 2 differentiated)
        (ratDerivative 2 right))
      (polyMul (ratDerivative 3 differentiated)
        (ratDerivative 3 right)))

/-- Additive cancellation in the coefficient-sensitive polynomial quotient. -/
theorem RatPolyCoeffEqv.add_neg_smul (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd polynomial (polySmul (-1) polynomial)) polyZero := by
  intro weight
  change ratWeightedSum weight
      (polyAdd polynomial (polySmul (-1) polynomial)) ≈ (0 : Q')
  refine Q'.eqv_trans _
    (ratWeightedSum weight polynomial +
      ratWeightedSum weight (polySmul (-1) polynomial)) _
    (ratWeightedSum_add weight _ _) ?_
  refine Q'.eqv_trans _
    (ratWeightedSum weight polynomial +
      (-1) * ratWeightedSum weight polynomial) _
    (Q'.add_eqv_congr_left _ _ _
      (ratWeightedSum_smul weight (-1) polynomial)) ?_
  q_ring

theorem headGradientDot_smul_left
    (scale : Q') (left right : RatPoly) :
    RatPolyCoeffEqv
      (headGradientDot (polySmul scale left) right)
      (polySmul scale (headGradientDot left right)) := by
  unfold headGradientDot
  have coordinate : ∀ index : Nat,
      RatPolyCoeffEqv
        (polyMul
          (ratDerivative index (polySmul scale left))
          (ratDerivative index right))
        (polySmul scale
          (polyMul (ratDerivative index left)
            (ratDerivative index right))) := by
    intro index
    exact RatPolyCoeffEqv.trans
      ((ratDerivative_smul index scale left).mul_right
        (ratDerivative index right))
      (RatPolyCoeffEqv.polyMul_smul_left scale
        (ratDerivative index left) (ratDerivative index right))
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (coordinate 0)
      (RatPolyCoeffEqv.add (coordinate 1)
        (RatPolyCoeffEqv.add (coordinate 2) (coordinate 3))))
    (polyFour_smul scale
      (polyMul (ratDerivative 0 left) (ratDerivative 0 right))
      (polyMul (ratDerivative 1 left) (ratDerivative 1 right))
      (polyMul (ratDerivative 2 left) (ratDerivative 2 right))
      (polyMul (ratDerivative 3 left) (ratDerivative 3 right)))

theorem headGradientDot_smul_right
    (scale : Q') (left right : RatPoly) :
    RatPolyCoeffEqv
      (headGradientDot left (polySmul scale right))
      (polySmul scale (headGradientDot left right)) :=
  RatPolyCoeffEqv.trans
    (headGradientDot_comm left (polySmul scale right))
    (RatPolyCoeffEqv.trans
      (headGradientDot_smul_left scale right left)
      ((headGradientDot_comm right left).smul scale))

private theorem gradientCoordinate_mul
    (differentiated factor right : RatPoly) (coordinate : Nat) :
    RatPolyCoeffEqv
      (polyMul (ratDerivative coordinate differentiated)
        (ratDerivative coordinate (polyMul factor right)))
      (polyAdd
        (polyMul
          (polyMul (ratDerivative coordinate differentiated)
            (ratDerivative coordinate factor)) right)
        (polyMul factor
          (polyMul (ratDerivative coordinate differentiated)
            (ratDerivative coordinate right)))) := by
  let dl := ratDerivative coordinate differentiated
  let df := ratDerivative coordinate factor
  let dr := ratDerivative coordinate right
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_left dl
      (ratDerivative_mul coordinate factor right)) ?_
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.mul_add_right dl
      (polyMul df right) (polyMul factor dr)) ?_
  apply RatPolyCoeffEqv.add
  · exact RatPolyCoeffEqv.symm
      (RatPolyCoeffEqv.mul_assoc dl df right)
  · refine RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.symm
        (RatPolyCoeffEqv.mul_assoc dl factor dr)) ?_
    refine RatPolyCoeffEqv.trans
      ((RatPolyCoeffEqv.mul_comm dl factor).mul_right dr) ?_
    exact RatPolyCoeffEqv.mul_assoc factor dl dr

private theorem polySum_fourGroups_flatten
    (group0 group1 group2 group3 : List RatPoly) :
    RatPolyCoeffEqv
      (polySum [polySum group0, polySum group1,
        polySum group2, polySum group3])
      (polySum (group0 ++ group1 ++ group2 ++ group3)) := by
  change RatPolyCoeffEqv
    (polyAdd (polySum group0)
      (polyAdd (polySum group1)
        (polyAdd (polySum group2)
          (polyAdd (polySum group3) polyZero))))
    (polySum (group0 ++ group1 ++ group2 ++ group3))
  have h3 : RatPolyCoeffEqv
      (polyAdd (polySum group3) polyZero) (polySum group3) :=
    RatPolyCoeffEqv.add_zero _
  have h23 : RatPolyCoeffEqv
      (polyAdd (polySum group2)
        (polyAdd (polySum group3) polyZero))
      (polySum (group2 ++ group3)) :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) h3)
      (RatPolyCoeffEqv.polySum_append group2 group3)
  have h123 : RatPolyCoeffEqv
      (polyAdd (polySum group1)
        (polyAdd (polySum group2)
          (polyAdd (polySum group3) polyZero)))
      (polySum (group1 ++ group2 ++ group3)) := by
    refine RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) h23) ?_
    simpa only [List.append_assoc] using
      RatPolyCoeffEqv.polySum_append group1 (group2 ++ group3)
  refine RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) h123) ?_
  simpa only [List.append_assoc] using
    RatPolyCoeffEqv.polySum_append group0 (group1 ++ group2 ++ group3)

private theorem polySum_gradient_shuffle
    (a0 a1 a2 a3 b0 b1 b2 b3 : RatPoly) :
    RatPolyCoeffEqv
      (polySum [a0, b0, a1, b1, a2, b2, a3, b3])
      (polySum [a0, a1, a2, a3, b0, b1, b2, b3]) := by
  intro weight
  refine Q'.eqv_trans _
    (qListSum ([a0, b0, a1, b1, a2, b2, a3, b3].map
      (ratWeightedSum weight))) _
    (ratWeightedSum_polySum weight _) ?_
  refine Q'.eqv_trans _
    (qListSum ([a0, a1, a2, a3, b0, b1, b2, b3].map
      (ratWeightedSum weight))) _ ?_
    (Q'.eqv_symm (ratWeightedSum_polySum weight _))
  simp only [List.map, qListSum]
  q_ring

/-- Directional-gradient product rule in the selected quaternion block. -/
theorem headGradientDot_mul_right
    (differentiated factor right : RatPoly) :
    RatPolyCoeffEqv
      (headGradientDot differentiated (polyMul factor right))
      (polyAdd
        (polyMul (headGradientDot differentiated factor) right)
        (polyMul factor (headGradientDot differentiated right))) := by
  let a : Nat → RatPoly := fun coordinate =>
    polyMul
      (polyMul (ratDerivative coordinate differentiated)
        (ratDerivative coordinate factor)) right
  let b : Nat → RatPoly := fun coordinate =>
    polyMul factor
      (polyMul (ratDerivative coordinate differentiated)
        (ratDerivative coordinate right))
  have hinterleaved : RatPolyCoeffEqv
      (headGradientDot differentiated (polyMul factor right))
      (polySum [a 0, b 0, a 1, b 1, a 2, b 2, a 3, b 3]) := by
    refine RatPolyCoeffEqv.trans
      (headGradientDot_eq_polySum differentiated (polyMul factor right)) ?_
    change RatPolyCoeffEqv
      (polySum
        [polyMul (ratDerivative 0 differentiated)
            (ratDerivative 0 (polyMul factor right)),
         polyMul (ratDerivative 1 differentiated)
            (ratDerivative 1 (polyMul factor right)),
         polyMul (ratDerivative 2 differentiated)
            (ratDerivative 2 (polyMul factor right)),
         polyMul (ratDerivative 3 differentiated)
            (ratDerivative 3 (polyMul factor right))]) _
    have hpackets := RatPolyCoeffEqv.add
        (gradientCoordinate_mul differentiated factor right 0)
        (RatPolyCoeffEqv.add
          (gradientCoordinate_mul differentiated factor right 1)
          (RatPolyCoeffEqv.add
            (gradientCoordinate_mul differentiated factor right 2)
            (RatPolyCoeffEqv.add
              (gradientCoordinate_mul differentiated factor right 3)
              (RatPolyCoeffEqv.refl polyZero))))
    have pairToSum (first second : RatPoly) :
        RatPolyCoeffEqv (polyAdd first second)
          (polySum [first, second]) := by
      change RatPolyCoeffEqv (polyAdd first second)
        (polyAdd first (polyAdd second polyZero))
      exact RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
        (RatPolyCoeffEqv.symm (RatPolyCoeffEqv.add_zero second))
    have hgroups : RatPolyCoeffEqv
        (polySum
          [polyAdd (a 0) (b 0), polyAdd (a 1) (b 1),
           polyAdd (a 2) (b 2), polyAdd (a 3) (b 3)])
        (polySum
          [polySum [a 0, b 0], polySum [a 1, b 1],
           polySum [a 2, b 2], polySum [a 3, b 3]]) :=
      RatPolyCoeffEqv.add (pairToSum (a 0) (b 0))
        (RatPolyCoeffEqv.add (pairToSum (a 1) (b 1))
          (RatPolyCoeffEqv.add (pairToSum (a 2) (b 2))
            (RatPolyCoeffEqv.add (pairToSum (a 3) (b 3))
              (RatPolyCoeffEqv.refl polyZero))))
    exact RatPolyCoeffEqv.trans hpackets
      (RatPolyCoeffEqv.trans hgroups
        (polySum_fourGroups_flatten
          [a 0, b 0] [a 1, b 1] [a 2, b 2] [a 3, b 3]))
  have hcollected := RatPolyCoeffEqv.trans hinterleaved
    (polySum_gradient_shuffle
      (a 0) (a 1) (a 2) (a 3) (b 0) (b 1) (b 2) (b 3))
  have ha : RatPolyCoeffEqv
      (polyMul (headGradientDot differentiated factor) right)
      (polySum [a 0, a 1, a 2, a 3]) :=
    RatPolyCoeffEqv.trans
      ((headGradientDot_eq_polySum differentiated factor).mul_right right)
      (RatPolyCoeffEqv.polySum_mul_right _ right)
  have hb : RatPolyCoeffEqv
      (polyMul factor (headGradientDot differentiated right))
      (polySum [b 0, b 1, b 2, b 3]) :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul_left factor
        (headGradientDot_eq_polySum differentiated right))
      (RatPolyCoeffEqv.mul_polySum_right factor _)
  have htarget := RatPolyCoeffEqv.add ha hb
  have happend := RatPolyCoeffEqv.polySum_append
    [a 0, a 1, a 2, a 3] [b 0, b 1, b 2, b 3]
  exact RatPolyCoeffEqv.trans hcollected
    (RatPolyCoeffEqv.symm
      (RatPolyCoeffEqv.trans htarget happend))

def secondProductPacket (left right : RatPoly)
    (coordinate : Nat) : RatPoly :=
  polyAdd
    (polyAdd
      (polyMul (ratDerivative coordinate (ratDerivative coordinate left))
        right)
      (polyMul (ratDerivative coordinate left)
        (ratDerivative coordinate right)))
    (polyAdd
      (polyMul (ratDerivative coordinate left)
        (ratDerivative coordinate right))
      (polyMul left
        (ratDerivative coordinate (ratDerivative coordinate right))))

private theorem secondProductPacket_eq_polySum
    (left right : RatPoly) (coordinate : Nat) :
    RatPolyCoeffEqv (secondProductPacket left right coordinate)
      (polySum
        [polyMul (ratDerivative coordinate (ratDerivative coordinate left))
            right,
         polyMul (ratDerivative coordinate left)
            (ratDerivative coordinate right),
         polyMul (ratDerivative coordinate left)
            (ratDerivative coordinate right),
         polyMul left
            (ratDerivative coordinate (ratDerivative coordinate right))]) := by
  intro weight
  let a := ratWeightedSum weight
    (polyMul (ratDerivative coordinate (ratDerivative coordinate left)) right)
  let b := ratWeightedSum weight
    (polyMul (ratDerivative coordinate left)
      (ratDerivative coordinate right))
  let c := ratWeightedSum weight
    (polyMul left
      (ratDerivative coordinate (ratDerivative coordinate right)))
  refine Q'.eqv_trans _ ((a + b) + (b + c)) _ ?_ ?_
  · unfold secondProductPacket
    exact Q'.eqv_trans _
      (ratWeightedSum weight
          (polyAdd
            (polyMul
              (ratDerivative coordinate (ratDerivative coordinate left))
              right)
            (polyMul (ratDerivative coordinate left)
              (ratDerivative coordinate right))) +
        ratWeightedSum weight
          (polyAdd
            (polyMul (ratDerivative coordinate left)
              (ratDerivative coordinate right))
            (polyMul left
              (ratDerivative coordinate (ratDerivative coordinate right))))) _
      (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr'
        (ratWeightedSum_add weight _ _)
        (ratWeightedSum_add weight _ _))
  · refine Q'.eqv_trans _
      (qListSum
        [a, b, b, c]) _ ?_
      (Q'.eqv_symm
        (ratWeightedSum_polySum weight
          [polyMul (ratDerivative coordinate (ratDerivative coordinate left))
              right,
           polyMul (ratDerivative coordinate left)
              (ratDerivative coordinate right),
           polyMul (ratDerivative coordinate left)
              (ratDerivative coordinate right),
           polyMul left
              (ratDerivative coordinate (ratDerivative coordinate right))]))
    simp only [qListSum]
    q_ring

private theorem headLaplacianExpansion_eq_interleavedPolySum
    (left right : RatPoly) :
    RatPolyCoeffEqv
      (polyFour
        (secondProductPacket left right 0)
        (secondProductPacket left right 1)
        (secondProductPacket left right 2)
        (secondProductPacket left right 3))
      (polySum
        [polyMul (ratDerivative 0 (ratDerivative 0 left)) right,
         polyMul (ratDerivative 0 left) (ratDerivative 0 right),
         polyMul (ratDerivative 0 left) (ratDerivative 0 right),
         polyMul left (ratDerivative 0 (ratDerivative 0 right)),
         polyMul (ratDerivative 1 (ratDerivative 1 left)) right,
         polyMul (ratDerivative 1 left) (ratDerivative 1 right),
         polyMul (ratDerivative 1 left) (ratDerivative 1 right),
         polyMul left (ratDerivative 1 (ratDerivative 1 right)),
         polyMul (ratDerivative 2 (ratDerivative 2 left)) right,
         polyMul (ratDerivative 2 left) (ratDerivative 2 right),
         polyMul (ratDerivative 2 left) (ratDerivative 2 right),
         polyMul left (ratDerivative 2 (ratDerivative 2 right)),
         polyMul (ratDerivative 3 (ratDerivative 3 left)) right,
         polyMul (ratDerivative 3 left) (ratDerivative 3 right),
         polyMul (ratDerivative 3 left) (ratDerivative 3 right),
         polyMul left (ratDerivative 3 (ratDerivative 3 right))]) := by
  let group : Nat → List RatPoly := fun coordinate =>
    [polyMul (ratDerivative coordinate (ratDerivative coordinate left)) right,
     polyMul (ratDerivative coordinate left) (ratDerivative coordinate right),
     polyMul (ratDerivative coordinate left) (ratDerivative coordinate right),
     polyMul left (ratDerivative coordinate (ratDerivative coordinate right))]
  refine RatPolyCoeffEqv.trans (polyFour_eq_polySum _ _ _ _) ?_
  refine RatPolyCoeffEqv.trans
    (by
      exact RatPolyCoeffEqv.add
        (secondProductPacket_eq_polySum left right 0)
        (RatPolyCoeffEqv.add
          (secondProductPacket_eq_polySum left right 1)
          (RatPolyCoeffEqv.add
            (secondProductPacket_eq_polySum left right 2)
            (RatPolyCoeffEqv.add
              (secondProductPacket_eq_polySum left right 3)
              (RatPolyCoeffEqv.refl polyZero))))) ?_
  change RatPolyCoeffEqv
    (polySum [polySum (group 0), polySum (group 1),
      polySum (group 2), polySum (group 3)]) _
  exact polySum_fourGroups_flatten (group 0) (group 1) (group 2) (group 3)

private theorem headLaplacian_mul_interleaved
    (left right : RatPoly) :
    RatPolyCoeffEqv (headLaplacian (polyMul left right))
      (polySum
        [polyMul (ratDerivative 0 (ratDerivative 0 left)) right,
         polyMul (ratDerivative 0 left) (ratDerivative 0 right),
         polyMul (ratDerivative 0 left) (ratDerivative 0 right),
         polyMul left (ratDerivative 0 (ratDerivative 0 right)),
         polyMul (ratDerivative 1 (ratDerivative 1 left)) right,
         polyMul (ratDerivative 1 left) (ratDerivative 1 right),
         polyMul (ratDerivative 1 left) (ratDerivative 1 right),
         polyMul left (ratDerivative 1 (ratDerivative 1 right)),
         polyMul (ratDerivative 2 (ratDerivative 2 left)) right,
         polyMul (ratDerivative 2 left) (ratDerivative 2 right),
         polyMul (ratDerivative 2 left) (ratDerivative 2 right),
         polyMul left (ratDerivative 2 (ratDerivative 2 right)),
         polyMul (ratDerivative 3 (ratDerivative 3 left)) right,
         polyMul (ratDerivative 3 left) (ratDerivative 3 right),
         polyMul (ratDerivative 3 left) (ratDerivative 3 right),
         polyMul left (ratDerivative 3 (ratDerivative 3 right))]) := by
  refine RatPolyCoeffEqv.trans
    (headLaplacian_mul_expanded left right) ?_
  change RatPolyCoeffEqv
    (polyFour
      (secondProductPacket left right 0)
      (secondProductPacket left right 1)
      (secondProductPacket left right 2)
      (secondProductPacket left right 3)) _
  exact headLaplacianExpansion_eq_interleavedPolySum left right

private theorem polySum_leibniz_shuffle
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : RatPoly) :
    RatPolyCoeffEqv
      (polySum
        [a0, b0, b0, c0, a1, b1, b1, c1,
         a2, b2, b2, c2, a3, b3, b3, c3])
      (polySum
        [a0, a1, a2, a3,
         b0, b0, b1, b1, b2, b2, b3, b3,
         c0, c1, c2, c3]) := by
  intro weight
  refine Q'.eqv_trans _
    (qListSum
      ([a0, b0, b0, c0, a1, b1, b1, c1,
        a2, b2, b2, c2, a3, b3, b3, c3].map
        (ratWeightedSum weight))) _
    (ratWeightedSum_polySum weight _) ?_
  refine Q'.eqv_trans _
    (qListSum
      ([a0, a1, a2, a3,
        b0, b0, b1, b1, b2, b2, b3, b3,
        c0, c1, c2, c3].map
        (ratWeightedSum weight))) _ ?_
    (Q'.eqv_symm (ratWeightedSum_polySum weight _))
  simp only [List.map, qListSum]
  q_ring

private theorem smul_two_polySum_four
    (first second third fourth : RatPoly) :
    RatPolyCoeffEqv
      (polySmul 2 (polySum [first, second, third, fourth]))
      (polySum
        [first, first, second, second, third, third, fourth, fourth]) := by
  intro weight
  refine Q'.eqv_trans _
    (2 * ratWeightedSum weight
      (polySum [first, second, third, fourth])) _
    (ratWeightedSum_smul weight 2 _) ?_
  refine Q'.eqv_trans _
    (2 * qListSum
      ([first, second, third, fourth].map
        (ratWeightedSum weight))) _
    (Q'.mul_eqv_congr_left _ _ _
      (ratWeightedSum_polySum weight _)) ?_
  refine Q'.eqv_trans _
    (qListSum ([first, second, third, fourth].map
        (ratWeightedSum weight)) +
      qListSum ([first, second, third, fourth].map
        (ratWeightedSum weight))) _
    (two_mul_eqv_add_self _) ?_
  refine Q'.eqv_trans _
    (qListSum
      ([first, first, second, second, third, third, fourth, fourth].map
        (ratWeightedSum weight))) _ ?_
    (Q'.eqv_symm (ratWeightedSum_polySum weight _))
  simp only [List.map, qListSum]
  q_ring

private theorem headLaplacianLeibnizTarget_eq_collected
    (left right : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd
        (polyMul (headLaplacian left) right)
        (polyAdd
          (polySmul 2 (headGradientDot left right))
          (polyMul left (headLaplacian right))))
      (polySum
        [polyMul (ratDerivative 0 (ratDerivative 0 left)) right,
         polyMul (ratDerivative 1 (ratDerivative 1 left)) right,
         polyMul (ratDerivative 2 (ratDerivative 2 left)) right,
         polyMul (ratDerivative 3 (ratDerivative 3 left)) right,
         polyMul (ratDerivative 0 left) (ratDerivative 0 right),
         polyMul (ratDerivative 0 left) (ratDerivative 0 right),
         polyMul (ratDerivative 1 left) (ratDerivative 1 right),
         polyMul (ratDerivative 1 left) (ratDerivative 1 right),
         polyMul (ratDerivative 2 left) (ratDerivative 2 right),
         polyMul (ratDerivative 2 left) (ratDerivative 2 right),
         polyMul (ratDerivative 3 left) (ratDerivative 3 right),
         polyMul (ratDerivative 3 left) (ratDerivative 3 right),
         polyMul left (ratDerivative 0 (ratDerivative 0 right)),
         polyMul left (ratDerivative 1 (ratDerivative 1 right)),
         polyMul left (ratDerivative 2 (ratDerivative 2 right)),
         polyMul left (ratDerivative 3 (ratDerivative 3 right))]) := by
  let a : List RatPoly :=
    [polyMul (ratDerivative 0 (ratDerivative 0 left)) right,
     polyMul (ratDerivative 1 (ratDerivative 1 left)) right,
     polyMul (ratDerivative 2 (ratDerivative 2 left)) right,
     polyMul (ratDerivative 3 (ratDerivative 3 left)) right]
  let b : List RatPoly :=
    [polyMul (ratDerivative 0 left) (ratDerivative 0 right),
     polyMul (ratDerivative 0 left) (ratDerivative 0 right),
     polyMul (ratDerivative 1 left) (ratDerivative 1 right),
     polyMul (ratDerivative 1 left) (ratDerivative 1 right),
     polyMul (ratDerivative 2 left) (ratDerivative 2 right),
     polyMul (ratDerivative 2 left) (ratDerivative 2 right),
     polyMul (ratDerivative 3 left) (ratDerivative 3 right),
     polyMul (ratDerivative 3 left) (ratDerivative 3 right)]
  let c : List RatPoly :=
    [polyMul left (ratDerivative 0 (ratDerivative 0 right)),
     polyMul left (ratDerivative 1 (ratDerivative 1 right)),
     polyMul left (ratDerivative 2 (ratDerivative 2 right)),
     polyMul left (ratDerivative 3 (ratDerivative 3 right))]
  have ha : RatPolyCoeffEqv
      (polyMul (headLaplacian left) right) (polySum a) :=
    RatPolyCoeffEqv.trans
      ((headLaplacian_eq_polySum left).mul_right right)
      (RatPolyCoeffEqv.polySum_mul_right _ right)
  have hb : RatPolyCoeffEqv
      (polySmul 2 (headGradientDot left right)) (polySum b) := by
    refine RatPolyCoeffEqv.trans
      ((headGradientDot_eq_polySum left right).smul 2) ?_
    exact smul_two_polySum_four
      (polyMul (ratDerivative 0 left) (ratDerivative 0 right))
      (polyMul (ratDerivative 1 left) (ratDerivative 1 right))
      (polyMul (ratDerivative 2 left) (ratDerivative 2 right))
      (polyMul (ratDerivative 3 left) (ratDerivative 3 right))
  have hc : RatPolyCoeffEqv
      (polyMul left (headLaplacian right)) (polySum c) :=
    RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.mul_left left (headLaplacian_eq_polySum right))
      (RatPolyCoeffEqv.mul_polySum_right left _)
  have habc := RatPolyCoeffEqv.add ha (RatPolyCoeffEqv.add hb hc)
  have hbc : RatPolyCoeffEqv
      (polyAdd (polySum b) (polySum c)) (polySum (b ++ c)) :=
    RatPolyCoeffEqv.polySum_append b c
  have hall : RatPolyCoeffEqv
      (polyAdd (polySum a) (polyAdd (polySum b) (polySum c)))
      (polySum (a ++ b ++ c)) := by
    refine RatPolyCoeffEqv.trans
      (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _) hbc) ?_
    simpa only [List.append_assoc] using
      RatPolyCoeffEqv.polySum_append a (b ++ c)
  exact RatPolyCoeffEqv.trans habc hall

/-- The genuine four-coordinate Laplacian product rule in `RatPoly`. -/
theorem headLaplacian_mul (left right : RatPoly) :
    RatPolyCoeffEqv
      (headLaplacian (polyMul left right))
      (polyAdd
        (polyMul (headLaplacian left) right)
        (polyAdd
          (polySmul 2 (headGradientDot left right))
          (polyMul left (headLaplacian right)))) := by
  let a0 := polyMul (ratDerivative 0 (ratDerivative 0 left)) right
  let a1 := polyMul (ratDerivative 1 (ratDerivative 1 left)) right
  let a2 := polyMul (ratDerivative 2 (ratDerivative 2 left)) right
  let a3 := polyMul (ratDerivative 3 (ratDerivative 3 left)) right
  let b0 := polyMul (ratDerivative 0 left) (ratDerivative 0 right)
  let b1 := polyMul (ratDerivative 1 left) (ratDerivative 1 right)
  let b2 := polyMul (ratDerivative 2 left) (ratDerivative 2 right)
  let b3 := polyMul (ratDerivative 3 left) (ratDerivative 3 right)
  let c0 := polyMul left (ratDerivative 0 (ratDerivative 0 right))
  let c1 := polyMul left (ratDerivative 1 (ratDerivative 1 right))
  let c2 := polyMul left (ratDerivative 2 (ratDerivative 2 right))
  let c3 := polyMul left (ratDerivative 3 (ratDerivative 3 right))
  refine RatPolyCoeffEqv.trans
    (headLaplacian_mul_interleaved left right) ?_
  refine RatPolyCoeffEqv.trans
    (polySum_leibniz_shuffle
      a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3) ?_
  exact RatPolyCoeffEqv.symm
    (headLaplacianLeibnizTarget_eq_collected left right)

/-! ## Bridge to the existing Gaussian Laplacian consumer -/

/-- Coefficient equality is respected by every linear monomial functional. -/
theorem RatPolyCoeffEqv.weightedSum
    {left right : RatPoly} (h : RatPolyCoeffEqv left right)
    (weight : List Nat → Q') :
    ratWeightedSum weight left ≈ ratWeightedSum weight right :=
  h weight

end YMGap.Continuum.SU2QuaternionRatPolyDifferential

#print axioms YMGap.Continuum.SU2QuaternionRatPolyDifferential.RatPolyCoeffEqv.derivative
