/-
# One positive thermodynamic functional on semantic lower observables

The quotient identifies eventual ORIGINAL Haar-carrier equality, with its
comparison threshold retained in SameObservable. Its relation is independent
of the interacting state. Addition and multiplication use a computed common
base, then descend; scaling and the unit descend too. The original limit
functional is well defined, normalized, rational-linear and positive on
ordinary squares. Its unit is distinct from zero.

Every presented value retains meanLimit and meanLimitCauchy as explicit
constructive data; quotient descent chooses no representative. This is the
lower plaquette-generated observable algebra at w=1/1024 and fixed spacing.
It is NOT the full spacetime state, an OS positive form, a stationary vacuum,
a physical transfer operator or a mass-gap/continuum result.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPresentation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation

def presentationSetoid : Setoid Presentation where
  r p q := Nonempty (SameObservable p q)
  iseqv := ⟨fun p => ⟨SameObservable.refl p⟩,
    fun ⟨h⟩ => ⟨h.symm⟩, fun ⟨h⟩ ⟨k⟩ => ⟨h.trans k⟩⟩

def Observable : Type := Quotient presentationSetoid

def embed (p : Presentation) : Observable := Quotient.mk _ p

def qadd : Observable → Observable → Observable :=
  Quotient.lift₂ (fun p q => embed (add p q))
    (fun _ _ _ _ ⟨h⟩ ⟨k⟩ => Quotient.sound ⟨h.add k⟩)

def qmul : Observable → Observable → Observable :=
  Quotient.lift₂ (fun p q => embed (mul p q))
    (fun _ _ _ _ ⟨h⟩ ⟨k⟩ => Quotient.sound ⟨h.mul k⟩)

def qsmul (c : Q') : Observable → Observable :=
  Quotient.lift (fun p => embed (smul c p)) (fun _ _ ⟨h⟩ => Quotient.sound ⟨h.smul c⟩)

def unit : Observable := embed one

def zero : Observable := qsmul 0 unit

def value : Observable → RC :=
  Quotient.lift (fun p => Quotient.mk crealSetoid (meanLimit p.expression))
    (fun _ _ ⟨h⟩ => Quotient.sound (meanLimit_same h))

theorem value_embed (p : Presentation) : value (embed p) = Quotient.mk crealSetoid (meanLimit p.expression) := rfl

/-- A presented observable returns its real representative, modulus and quotient
pin as data. No representative is selected from an arbitrary quotient class. -/
def valueRepresentative (p : Presentation) :
    Σ' r : CReal, QCauchy r.approx ×' (value (embed p) = Quotient.mk crealSetoid r) :=
  ⟨meanLimit p.expression, meanLimitCauchy p.expression, rfl⟩

theorem embed_atBase (p : Presentation) (target : Nat) (hp : p.base ≤ target) :
    embed ⟨target, atBase p target hp⟩ = embed p := Quotient.sound ⟨SameObservable.rebase p target hp⟩

theorem value_unit : value unit = Quotient.mk crealSetoid CReal.cone := Quotient.sound (meanLimit_one 0)

theorem value_add (x y : Observable) : value (qadd x y) = RCadd (value x) (value y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro p q
  apply Quotient.sound
  exact (meanLimit_add (atBase p (p.base+q.base) (Nat.le_add_right _ _))
    (atBase q (p.base+q.base) (Nat.le_add_left _ _))).trans
    ((CReal.add_congr_left (meanLimit_atBase p _ _)).trans (CReal.add_congr_right (meanLimit_atBase q _ _)))

theorem value_smul (c : Q') (x : Observable) :
    value (qsmul c x) = RCmul (Quotient.mk crealSetoid (ofQ' c)) (value x) := by
  refine Quotient.inductionOn x ?_
  intro p
  exact Quotient.sound (meanLimit_smul c p.expression)

theorem value_square_nonnegative (x : Observable) : RCnonneg (value (qmul x x)) := by
  refine Quotient.inductionOn x ?_
  intro p
  exact meanLimit_square_nonnegative (atBase p (p.base+p.base) (Nat.le_add_right _ _))

theorem value_zero : value zero = RCzero := by
  rw [zero, value_smul]
  change RCmul _ (value unit) = RCzero
  refine Quotient.inductionOn (value unit) ?_
  intro a
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (a.approx n)))

theorem unit_ne_zero : unit ≠ zero := by
  intro h
  have he := congrArg value h
  rw [value_unit, value_zero] at he
  have hreal : Equiv cone czero := Quotient.exact he
  obtain ⟨N, hN⟩ := hreal HalfPow.half (by decide)
  exact (by decide : ¬ ((1 : Q') ≤ 0 + HalfPow.half)) (hN N (Nat.le_refl N)).1

end YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.presentationSetoid
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.Observable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.embed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.qadd
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.qmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.qsmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.value_embed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.valueRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.embed_atBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.value_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.value_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.value_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.value_square_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.value_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional.unit_ne_zero
