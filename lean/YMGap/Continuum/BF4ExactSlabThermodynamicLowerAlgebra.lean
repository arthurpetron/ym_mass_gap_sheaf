/-
# Algebra laws on the semantic thermodynamic lower-observable quotient

Computed common-base operations obey the actual commutative rational
polynomial algebra laws after semantic descent. Equality is on the original
Haar carrier under arbitrary insertions, independently of the state value.
These laws supply the algebra underlying the constructed positive functional;
they neither assert factorization of its moments nor supply an OS time map.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional

namespace YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- A finite-volume algebraic identity gives equality of semantic observables. -/
theorem embed_eq_of_coeff (p q : Presentation) (cutoff : Nat)
    (hp : p.base ≤ cutoff) (hq : q.base ≤ cutoff)
    (he : ∀ volume, cutoff ≤ volume → RatPolyCoeffEqv (polynomial p volume) (polynomial q volume)) :
    embed p = embed q :=
  Quotient.sound ⟨⟨cutoff, hp, hq, fun volume hv => RatPolyCoeffEqv.haarCarrier (he volume hv)⟩⟩

theorem qadd_comm (x y : Observable) : qadd x y = qadd y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  apply embed_eq_of_coeff (add p q) (add q p) (p.base+q.base)
  · exact Nat.le_refl _
  · change q.base+p.base ≤ p.base+q.base; omega
  · intro volume hv
    rw [polynomial_add p q volume hv, polynomial_add q p volume (by omega)]
    exact RatPolyCoeffEqv.add_comm _ _

theorem qadd_assoc (x y z : Observable) : qadd (qadd x y) z = qadd x (qadd y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro p q r
  apply embed_eq_of_coeff (add (add p q) r) (add p (add q r)) (p.base+q.base+r.base)
  · exact Nat.le_refl _
  · change p.base+(q.base+r.base) ≤ p.base+q.base+r.base; omega
  · intro volume hv
    rw [polynomial_add (add p q) r volume hv,
      polynomial_add p (add q r) volume (by change p.base+(q.base+r.base) ≤ volume; omega),
      polynomial_add p q volume (by omega), polynomial_add q r volume (by omega)]
    exact RatPolyCoeffEqv.add_assoc _ _ _

theorem qmul_comm (x y : Observable) : qmul x y = qmul y x := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  apply embed_eq_of_coeff (mul p q) (mul q p) (p.base+q.base)
  · exact Nat.le_refl _
  · change q.base+p.base ≤ p.base+q.base; omega
  · intro volume hv
    rw [polynomial_mul p q volume hv, polynomial_mul q p volume (by omega)]
    exact RatPolyCoeffEqv.mul_comm _ _

theorem qmul_assoc (x y z : Observable) : qmul (qmul x y) z = qmul x (qmul y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro p q r
  apply embed_eq_of_coeff (mul (mul p q) r) (mul p (mul q r)) (p.base+q.base+r.base)
  · exact Nat.le_refl _
  · change p.base+(q.base+r.base) ≤ p.base+q.base+r.base; omega
  · intro volume hv
    rw [polynomial_mul (mul p q) r volume hv,
      polynomial_mul p (mul q r) volume (by change p.base+(q.base+r.base) ≤ volume; omega),
      polynomial_mul p q volume (by omega), polynomial_mul q r volume (by omega)]
    exact RatPolyCoeffEqv.mul_assoc _ _ _

theorem unit_mul (x : Observable) : qmul unit x = x := by
  refine Quotient.inductionOn x ?_
  intro p
  apply embed_eq_of_coeff (mul one p) p p.base
  · change 0+p.base ≤ p.base; omega
  · exact Nat.le_refl _
  · intro volume hv
    rw [polynomial_mul one p volume (by change 0+p.base ≤ volume; omega), polynomial_one]
    exact RatPolyCoeffEqv.one_mul _

theorem mul_unit (x : Observable) : qmul x unit = x := (qmul_comm _ _).trans (unit_mul x)

theorem qmul_add (x y z : Observable) : qmul x (qadd y z) = qadd (qmul x y) (qmul x z) := by
  refine Quotient.inductionOn₃ x y z ?_
  intro p q r
  apply embed_eq_of_coeff (mul p (add q r)) (add (mul p q) (mul p r)) (p.base+p.base+q.base+r.base)
  · change p.base+(q.base+r.base) ≤ p.base+p.base+q.base+r.base; omega
  · change (p.base+q.base)+(p.base+r.base) ≤ p.base+p.base+q.base+r.base; omega
  · intro volume hv
    rw [polynomial_mul p (add q r) volume (by change p.base+(q.base+r.base) ≤ volume; omega),
      polynomial_add (mul p q) (mul p r) volume (by change (p.base+q.base)+(p.base+r.base) ≤ volume; omega),
      polynomial_add q r volume (by omega), polynomial_mul p q volume (by omega), polynomial_mul p r volume (by omega)]
    exact RatPolyCoeffEqv.mul_add_right _ _ _

theorem zero_add (x : Observable) : qadd zero x = x := by
  refine Quotient.inductionOn x ?_
  intro p
  apply embed_eq_of_coeff (add (smul 0 one) p) p p.base
  · change 0+p.base ≤ p.base; omega
  · exact Nat.le_refl _
  · intro volume hv
    rw [polynomial_add (smul 0 one) p volume (by change 0+p.base ≤ volume; omega), polynomial_smul, polynomial_one]
    exact ((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)

theorem neg_add (x : Observable) : qadd (qsmul (-1) x) x = zero := by
  refine Quotient.inductionOn x ?_
  intro p
  apply embed_eq_of_coeff (add (smul (-1) p) p) (smul 0 one) (p.base+p.base)
  · exact Nat.le_refl _
  · exact Nat.zero_le _
  · intro volume hv
    rw [polynomial_add (smul (-1) p) p volume hv, polynomial_smul, polynomial_smul, polynomial_one]
    exact (RatPolyCoeffEqv.add_comm _ _).trans
      ((RatPolyCoeffEqv.add_neg_smul _).trans (RatPolyCoeffEqv.zero_smul polyOne).symm)

theorem qsmul_add (c : Q') (x y : Observable) : qsmul c (qadd x y) = qadd (qsmul c x) (qsmul c y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  apply embed_eq_of_coeff (smul c (add p q)) (add (smul c p) (smul c q)) (p.base+q.base)
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · intro volume hv
    rw [polynomial_smul, polynomial_add p q volume hv,
      polynomial_add (smul c p) (smul c q) volume hv, polynomial_smul, polynomial_smul]
    exact RatPolyCoeffEqv.smul_add _ _ _

theorem qsmul_assoc (c d : Q') (x : Observable) : qsmul c (qsmul d x) = qsmul (c*d) x := by
  refine Quotient.inductionOn x ?_
  intro p
  apply embed_eq_of_coeff (smul c (smul d p)) (smul (c*d) p) p.base (Nat.le_refl _) (Nat.le_refl _)
  intro volume _
  rw [polynomial_smul, polynomial_smul, polynomial_smul]
  exact RatPolyCoeffEqv.smul_assoc _ _ _

theorem one_smul (x : Observable) : qsmul 1 x = x := by
  refine Quotient.inductionOn x ?_
  intro p
  apply embed_eq_of_coeff (smul 1 p) p p.base (Nat.le_refl _) (Nat.le_refl _)
  intro volume _
  rw [polynomial_smul]
  exact RatPolyCoeffEqv.one_smul _

theorem add_smul (c d : Q') (x : Observable) : qsmul (c+d) x = qadd (qsmul c x) (qsmul d x) := by
  refine Quotient.inductionOn x ?_
  intro p
  apply embed_eq_of_coeff (smul (c+d) p) (add (smul c p) (smul d p)) (p.base+p.base)
  · exact Nat.le_add_right _ _
  · exact Nat.le_refl _
  · intro volume hv
    rw [polynomial_smul, polynomial_add (smul c p) (smul d p) volume hv, polynomial_smul, polynomial_smul]
    exact (RatPolyCoeffEqv.add_smul_same _ _ _).symm

theorem qsmul_mul (c : Q') (x y : Observable) : qmul (qsmul c x) y = qsmul c (qmul x y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  apply embed_eq_of_coeff (mul (smul c p) q) (smul c (mul p q)) (p.base+q.base) (Nat.le_refl _) (Nat.le_refl _)
  intro volume hv
  rw [polynomial_mul (smul c p) q volume hv, polynomial_smul, polynomial_smul, polynomial_mul p q volume hv]
  exact RatPolyCoeffEqv.polyMul_smul_left _ _ _

theorem qsmul_coefficient {c d : Q'} (h : Q'.eqv c d) (x : Observable) : qsmul c x = qsmul d x := by
  refine Quotient.inductionOn x ?_
  intro p
  apply embed_eq_of_coeff (smul c p) (smul d p) p.base (Nat.le_refl _) (Nat.le_refl _)
  intro volume _
  rw [polynomial_smul, polynomial_smul]
  exact RatPolyCoeffEqv.smul_coefficient h _

end YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.embed_eq_of_coeff
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qadd_comm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qadd_assoc
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qmul_comm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qmul_assoc
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.unit_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.mul_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qmul_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.zero_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.neg_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qsmul_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qsmul_assoc
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.one_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.add_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qsmul_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra.qsmul_coefficient
