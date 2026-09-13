/-
# Physical time laws for ORIGINAL presented observables

Actual successive translations, rebasing, sums, products and rational scales
agree on the existing semantic observable quotient. Each comparison returns
the explicit common-volume threshold and equality under every Haar insertion.
Arbitrary bulk padding represents the same physical lag.

The domain of timeObservable is still Presentation, not Observable. These
specific identities do not yet prove preservation of an arbitrary
SameObservable witness. No map on the OS null quotient or completion, no
state homogeneity and no operator-norm bound is claimed here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
import YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

def sameOfPolynomial (p q : Presentation) (cutoff : Nat)
    (hp : p.base ≤ cutoff) (hq : q.base ≤ cutoff)
    (he : ∀ volume, cutoff ≤ volume → polynomial p volume = polynomial q volume) :
    SameObservable p q :=
  ⟨cutoff, hp, hq, fun volume hv => by rw [he volume hv]; exact HaarCarrierEqv.refl _ _⟩

theorem translate_zero (p : Presentation) : translate 0 p = p := by
  cases p with
  | mk base e =>
      change (Presentation.mk base (bulkAtTime 0 ⟨0, Nat.lt_succ_self 0⟩ e)) = ⟨base, e⟩
      rw [bulkAtTime_zero]

def sameTranslate_comp (s t : Nat) (p : Presentation) :
    SameObservable (translate t (translate s p)) (translate (s+t) p) := by
  refine sameOfPolynomial _ _ (p.base+s+t) (Nat.le_refl _) (by change p.base+(s+t) ≤ _; omega) ?_
  intro volume hv
  rw [polynomial_translate t (translate s p) volume hv,
    timePolynomial_translate s t p volume hv,
    polynomial_translate (s+t) p volume (by omega)]

def sameTranslate_rebase (lag : Nat) (p : Presentation) (target : Nat) (hp : p.base ≤ target) :
    SameObservable (translate lag ⟨target, atBase p target hp⟩) (translate lag p) := by
  refine sameOfPolynomial _ _ (target+lag) (Nat.le_refl _) (by change p.base+lag ≤ _; omega) ?_
  intro volume hv
  rw [polynomial_translate lag ⟨target, atBase p target hp⟩ volume hv,
    timePolynomial_atBase lag p target hp volume hv,
    polynomial_translate lag p volume (by omega)]

def sameBulkTime {base : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression base) :
    SameObservable ⟨base+padding, bulkAtTime padding s e⟩ (translate s.val ⟨base, e⟩) := by
  have hs := s.isLt
  refine sameOfPolynomial _ _ (base+padding) (Nat.le_refl _) (by change base+s.val ≤ _; omega) ?_
  intro volume hv
  rw [polynomial_bulkAtTime padding s e volume hv,
    polynomial_translate s.val ⟨base, e⟩ volume (by change base+s.val ≤ volume; omega)]

def sameTranslate_add (lag : Nat) (p q : Presentation) :
    SameObservable (translate lag (add p q)) (add (translate lag p) (translate lag q)) := by
  refine sameOfPolynomial _ _ (p.base+q.base+lag+lag)
    (by change p.base+q.base+lag ≤ _; omega)
    (by change (p.base+lag)+(q.base+lag) ≤ _; omega) ?_
  intro volume hv
  rw [polynomial_translate lag (add p q) volume (by change p.base+q.base+lag ≤ _; omega),
    timePolynomial_add lag p q volume (by omega),
    polynomial_add (translate lag p) (translate lag q) volume
      (by change (p.base+lag)+(q.base+lag) ≤ _; omega),
    polynomial_translate lag p volume (by omega), polynomial_translate lag q volume (by omega)]

def sameTranslate_mul (lag : Nat) (p q : Presentation) :
    SameObservable (translate lag (mul p q)) (mul (translate lag p) (translate lag q)) := by
  refine sameOfPolynomial _ _ (p.base+q.base+lag+lag)
    (by change p.base+q.base+lag ≤ _; omega)
    (by change (p.base+lag)+(q.base+lag) ≤ _; omega) ?_
  intro volume hv
  rw [polynomial_translate lag (mul p q) volume (by change p.base+q.base+lag ≤ _; omega),
    timePolynomial_mul lag p q volume (by omega),
    polynomial_mul (translate lag p) (translate lag q) volume
      (by change (p.base+lag)+(q.base+lag) ≤ _; omega),
    polynomial_translate lag p volume (by omega), polynomial_translate lag q volume (by omega)]

theorem translate_smul (lag : Nat) (c : Q') (p : Presentation) :
    translate lag (smul c p) = smul c (translate lag p) := rfl

def sameTranslate_one (lag : Nat) : SameObservable (translate lag one) one := by
  refine sameOfPolynomial _ _ lag (by change 0+lag ≤ lag; omega) (Nat.zero_le _) ?_
  intro volume hv
  rw [polynomial_translate lag one volume (by change 0+lag ≤ volume; omega), timePolynomial_one, polynomial_one]

def timeObservable (lag : Nat) (p : Presentation) : Observable := embed (translate lag p)

theorem timeObservable_zero (p : Presentation) : timeObservable 0 p = embed p := by
  unfold timeObservable
  rw [translate_zero]

theorem timeObservable_comp (s t : Nat) (p : Presentation) :
    timeObservable t (translate s p) = timeObservable (s+t) p :=
  Quotient.sound ⟨sameTranslate_comp s t p⟩

theorem timeObservable_rebase (lag : Nat) (p : Presentation) (target : Nat) (hp : p.base ≤ target) :
    timeObservable lag ⟨target, atBase p target hp⟩ = timeObservable lag p :=
  Quotient.sound ⟨sameTranslate_rebase lag p target hp⟩

theorem timeObservable_bulk {base : Nat} (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression base) :
    embed ⟨base+padding, bulkAtTime padding s e⟩ = timeObservable s.val ⟨base, e⟩ :=
  Quotient.sound ⟨sameBulkTime padding s e⟩

theorem timeObservable_add (lag : Nat) (p q : Presentation) :
    timeObservable lag (add p q) = qadd (timeObservable lag p) (timeObservable lag q) :=
  Quotient.sound ⟨sameTranslate_add lag p q⟩

theorem timeObservable_mul (lag : Nat) (p q : Presentation) :
    timeObservable lag (mul p q) = qmul (timeObservable lag p) (timeObservable lag q) :=
  Quotient.sound ⟨sameTranslate_mul lag p q⟩

theorem timeObservable_smul (lag : Nat) (c : Q') (p : Presentation) :
    timeObservable lag (smul c p) = qsmul c (timeObservable lag p) := rfl

theorem timeObservable_one (lag : Nat) : timeObservable lag one = unit :=
  Quotient.sound ⟨sameTranslate_one lag⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.sameOfPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.translate_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.sameTranslate_comp
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.sameTranslate_rebase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.sameBulkTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.sameTranslate_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.sameTranslate_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.translate_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.sameTranslate_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable_comp
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable_rebase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable_bulk
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAlgebra.timeObservable_one
