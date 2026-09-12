/-
# Complex polynomial algebra retaining arbitrary coefficient probes

The relation is componentwise RatPolyCoeffEqv, not equality after pointwise
evaluation. Small complex ring identities are transported by the existing
coefficient-sensitive reflective normalizer under arbitrary polynomial
substitution. Raw polynomials and all spectator coefficients remain data.
No new quotient, classical choice, or extensional Haar principle is used.
-/

import YMGap.Continuum.SU2QuaternionSymmetricPowerPolynomial
import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

namespace YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalTraceInversion
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infixl:65 " ⊞ " => complexRatPolyAdd
local infixl:70 " ⊠ " => complexRatPolyMul
local notation "𝟘" => complexRatPolyZero
local notation "𝟙" => complexRatPolyOne

/-- Both real and imaginary parts agree against EVERY monomial probe. -/
def ComplexCoeffEqv (p q : ComplexRatPoly) : Prop :=
  RatPolyCoeffEqv p.1 q.1 ∧ RatPolyCoeffEqv p.2 q.2

local infix:50 " ≈c " => ComplexCoeffEqv

theorem ComplexCoeffEqv.refl (p : ComplexRatPoly) : p ≈c p :=
  ⟨RatPolyCoeffEqv.refl _, RatPolyCoeffEqv.refl _⟩

theorem ComplexCoeffEqv.symm {p q : ComplexRatPoly} (h : p ≈c q) : q ≈c p := ⟨h.1.symm, h.2.symm⟩

theorem ComplexCoeffEqv.trans {p q r : ComplexRatPoly} (h : p ≈c q) (h' : q ≈c r) : p ≈c r :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem ComplexCoeffEqv.add {p p' q q' : ComplexRatPoly} (h : p ≈c p') (h' : q ≈c q') :
    (p ⊞ q) ≈c (p' ⊞ q') := ⟨h.1.add h'.1, h.2.add h'.2⟩

theorem ComplexCoeffEqv.mul {p p' q q' : ComplexRatPoly} (h : p ≈c p') (h' : q ≈c q') :
    (p ⊠ q) ≈c (p' ⊠ q') :=
  ⟨(h.1.mul h'.1).add (RatPolyCoeffEqv.neg (h.2.mul h'.2)),
    (h.1.mul h'.2).add (h.2.mul h'.1)⟩

theorem add_zero (p : ComplexRatPoly) : (p ⊞ 𝟘) ≈c p :=
  ⟨RatPolyCoeffEqv.add_zero _, RatPolyCoeffEqv.add_zero _⟩

theorem zero_add (p : ComplexRatPoly) : (𝟘 ⊞ p) ≈c p :=
  ⟨RatPolyCoeffEqv.zero_add _, RatPolyCoeffEqv.zero_add _⟩

theorem add_comm (p q : ComplexRatPoly) : (p ⊞ q) ≈c (q ⊞ p) :=
  ⟨RatPolyCoeffEqv.add_comm _ _, RatPolyCoeffEqv.add_comm _ _⟩

theorem add_assoc (p q r : ComplexRatPoly) : ((p ⊞ q) ⊞ r) ≈c (p ⊞ (q ⊞ r)) :=
  ⟨RatPolyCoeffEqv.add_assoc _ _ _, RatPolyCoeffEqv.add_assoc _ _ _⟩

theorem add_swap (p q r s : ComplexRatPoly) : ((p ⊞ q) ⊞ (r ⊞ s)) ≈c ((p ⊞ r) ⊞ (q ⊞ s)) :=
  ⟨RatPolyCoeffEqv.four_add_swap _ _ _ _, RatPolyCoeffEqv.four_add_swap _ _ _ _⟩

theorem mul_zero (p : ComplexRatPoly) : (p ⊠ 𝟘) ≈c 𝟘 := by
  constructor
  · exact ((RatPolyCoeffEqv.mul_zero_right _).add
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_right _))).trans
      (RatPolyCoeffEqv.zero_add _)
  · exact ((RatPolyCoeffEqv.mul_zero_right _).add (RatPolyCoeffEqv.mul_zero_right _)).trans
      (RatPolyCoeffEqv.zero_add _)

theorem zero_mul (p : ComplexRatPoly) : (𝟘 ⊠ p) ≈c 𝟘 := by
  constructor
  · exact ((RatPolyCoeffEqv.mul_zero_left _).add
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_left _))).trans
      (RatPolyCoeffEqv.zero_add _)
  · exact ((RatPolyCoeffEqv.mul_zero_left _).add (RatPolyCoeffEqv.mul_zero_left _)).trans
      (RatPolyCoeffEqv.zero_add _)

theorem one_mul (p : ComplexRatPoly) : (𝟙 ⊠ p) ≈c p := by
  constructor
  · exact ((RatPolyCoeffEqv.one_mul _).add
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_left _))).trans (RatPolyCoeffEqv.add_zero _)
  · exact ((RatPolyCoeffEqv.one_mul _).add (RatPolyCoeffEqv.mul_zero_left _)).trans
      (RatPolyCoeffEqv.add_zero _)

theorem mul_one (p : ComplexRatPoly) : (p ⊠ 𝟙) ≈c p := by
  constructor
  · exact ((RatPolyCoeffEqv.mul_one _).add
      (RatPolyCoeffEqv.neg (RatPolyCoeffEqv.mul_zero_right _))).trans (RatPolyCoeffEqv.add_zero _)
  · exact ((RatPolyCoeffEqv.mul_zero_right _).add (RatPolyCoeffEqv.mul_one _)).trans
      (RatPolyCoeffEqv.zero_add _)

private abbrev CExpr := PolyExpr × PolyExpr
private def ev (i : Nat) : CExpr := (.var (2 * i), .var (2 * i + 1))
private def ea (x y : CExpr) : CExpr := (.add x.1 y.1, .add x.2 y.2)
private def em (x y : CExpr) : CExpr :=
  (.add (.mul x.1 y.1) (.neg (.mul x.2 y.2)), .add (.mul x.1 y.2) (.mul x.2 y.1))

private def env (a b c d e f g : ComplexRatPoly) : Nat → RatPoly
  | 0 => a.1 | 1 => a.2 | 2 => b.1 | 3 => b.2 | 4 => c.1 | 5 => c.2
  | 6 => d.1 | 7 => d.2 | 8 => e.1 | 9 => e.2 | 10 => f.1 | 11 => f.2
  | 12 => g.1 | 13 => g.2 | _ => polyZero

private theorem certificate (l r : CExpr)
    (hr : normalize l.1 = normalize r.1) (hi : normalize l.2 = normalize r.2)
    (environment : Nat → RatPoly) :
    (coeffEvalExpr environment l.1, coeffEvalExpr environment l.2) ≈c
      (coeffEvalExpr environment r.1, coeffEvalExpr environment r.2) :=
  ⟨coeffEvalExpr_eqv_of_normalize_eq _ _ hr environment,
    coeffEvalExpr_eqv_of_normalize_eq _ _ hi environment⟩

theorem mul_add (a b c : ComplexRatPoly) : (a ⊠ (b ⊞ c)) ≈c ((a ⊠ b) ⊞ (a ⊠ c)) := by
  exact certificate (em (ev 0) (ea (ev 1) (ev 2)))
    (ea (em (ev 0) (ev 1)) (em (ev 0) (ev 2))) (by decide) (by decide) (env a b c 𝟘 𝟘 𝟘 𝟘)

theorem add_mul (a b c : ComplexRatPoly) : ((a ⊞ b) ⊠ c) ≈c ((a ⊠ c) ⊞ (b ⊠ c)) := by
  exact certificate (em (ea (ev 0) (ev 1)) (ev 2))
    (ea (em (ev 0) (ev 2)) (em (ev 1) (ev 2))) (by decide) (by decide) (env a b c 𝟘 𝟘 𝟘 𝟘)

theorem mul_comm (a b : ComplexRatPoly) : (a ⊠ b) ≈c (b ⊠ a) := by
  exact certificate (em (ev 0) (ev 1)) (em (ev 1) (ev 0)) (by decide) (by decide) (env a b 𝟘 𝟘 𝟘 𝟘 𝟘)

theorem mul_assoc (a b c : ComplexRatPoly) : ((a ⊠ b) ⊠ c) ≈c (a ⊠ (b ⊠ c)) := by
  exact certificate (em (em (ev 0) (ev 1)) (ev 2)) (em (ev 0) (em (ev 1) (ev 2)))
    (by decide) (by decide) (env a b c 𝟘 𝟘 𝟘 𝟘)

private def mix (a b x y : CExpr) : CExpr := ea (em a x) (em b y)

theorem mix_swap (a b c d x y z : ComplexRatPoly) :
    ((c ⊠ ((a ⊠ x) ⊞ (b ⊠ y))) ⊞ (d ⊠ ((a ⊠ y) ⊞ (b ⊠ z)))) ≈c
      ((a ⊠ ((c ⊠ x) ⊞ (d ⊠ y))) ⊞ (b ⊠ ((c ⊠ y) ⊞ (d ⊠ z)))) := by
  exact certificate
    (mix (ev 2) (ev 3) (mix (ev 0) (ev 1) (ev 4) (ev 5)) (mix (ev 0) (ev 1) (ev 5) (ev 6)))
    (mix (ev 0) (ev 1) (mix (ev 2) (ev 3) (ev 4) (ev 5)) (mix (ev 2) (ev 3) (ev 5) (ev 6)))
    (by decide) (by decide) (env a b c d x y z)

theorem mixed_balance (a b c d x y z : ComplexRatPoly) :
    (((c ⊠ ((a ⊠ x) ⊞ (b ⊠ y))) ⊞ (d ⊠ ((a ⊠ y) ⊞ (b ⊠ z)))) ⊞ ((a ⊠ d) ⊠ y)) ≈c
      (((a ⊠ ((c ⊠ x) ⊞ (d ⊠ y))) ⊞ (d ⊠ ((a ⊠ y) ⊞ (b ⊠ z)))) ⊞ ((b ⊠ c) ⊠ y)) := by
  exact certificate
    (ea (mix (ev 2) (ev 3) (mix (ev 0) (ev 1) (ev 4) (ev 5)) (mix (ev 0) (ev 1) (ev 5) (ev 6)))
      (em (em (ev 0) (ev 3)) (ev 5)))
    (ea (mix (ev 0) (ev 3) (mix (ev 2) (ev 3) (ev 4) (ev 5)) (mix (ev 0) (ev 1) (ev 5) (ev 6)))
      (em (em (ev 1) (ev 2)) (ev 5)))
    (by decide) (by decide) (env a b c d x y z)

theorem balance_reorder (a d x y i t : ComplexRatPoly) :
    ((((a ⊠ x) ⊞ i) ⊞ (d ⊠ y)) ⊞ t) ≈c (((a ⊠ x) ⊞ (i ⊞ t)) ⊞ (d ⊠ y)) := by
  exact certificate
    (ea (ea (ea (em (ev 0) (ev 2)) (ev 4)) (em (ev 1) (ev 3))) (ev 5))
    (ea (ea (em (ev 0) (ev 2)) (ea (ev 4) (ev 5))) (em (ev 1) (ev 3)))
    (by decide) (by decide) (env a d x y i t 𝟘)

theorem balance_contract (a d x y j p t : ComplexRatPoly) :
    (((a ⊠ x) ⊞ (((a ⊠ j) ⊞ (d ⊠ p)) ⊞ t)) ⊞ (d ⊠ y)) ≈c
      (((a ⊠ (x ⊞ j)) ⊞ (d ⊠ (p ⊞ y))) ⊞ t) := by
  exact certificate
    (ea (ea (em (ev 0) (ev 2)) (ea (mix (ev 0) (ev 1) (ev 4) (ev 5)) (ev 6))) (em (ev 1) (ev 3)))
    (ea (mix (ev 0) (ev 1) (ea (ev 2) (ev 4)) (ea (ev 5) (ev 3))) (ev 6))
    (by decide) (by decide) (env a d x y j p t)

end YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra

#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.ComplexCoeffEqv
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.ComplexCoeffEqv.refl
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.ComplexCoeffEqv.symm
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.ComplexCoeffEqv.trans
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.ComplexCoeffEqv.add
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.ComplexCoeffEqv.mul
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.add_zero
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.zero_add
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.add_comm
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.add_assoc
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.add_swap
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.mul_zero
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.zero_mul
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.one_mul
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.mul_one
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.mul_add
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.add_mul
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.mul_comm
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.mul_assoc
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.mix_swap
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.mixed_balance
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.balance_reorder
#print axioms YMGap.Continuum.SU2QuaternionComplexCoefficientAlgebra.balance_contract
