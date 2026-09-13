/-
# The ORIGINAL thermodynamic OS pairing on one semantic observable carrier

A computed common base supplies a real representative and its Cauchy data.
Finite-volume Haar-carrier equality, independent of the interacting state,
makes this representative independent of both observable presentations.
The pairing therefore descends to the EXISTING lower-observable quotient.

Common-base representatives and their explicit error moduli are retained;
no real or observable representative is chosen from an arbitrary quotient.
The state is still the original fixed-nome, fixed-spacing plaquette theory,
not a physical transfer operator or a continuum construction.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm

namespace YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm (formLimit)

/-- The common base is computed, not selected from existence. -/
def presentedForm (p q : Presentation) : CReal :=
  basedForm p q (p.base+q.base) (Nat.le_add_right _ _) (Nat.le_add_left _ _)

def presentedFormCauchy (p q : Presentation) : QCauchy (presentedForm p q).approx :=
  basedFormCauchy p q (p.base+q.base) (Nat.le_add_right _ _) (Nat.le_add_left _ _)

def presentedVolumeModulus (p q : Presentation) : Q' → Nat :=
  basedVolumeModulus p q (p.base+q.base) (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem presentedForm_atBase (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) :
    Equiv (presentedForm p q) (basedForm p q base hp hq) :=
  basedForm_compatible p q (p.base+q.base) base (Nat.le_add_right _ _) (Nat.le_add_left _ _) hp hq

private theorem formLimit_congr_eq {base : Nat} {e e' f f' : PlaquetteExpression base}
    (he : e=e') (hf : f=f') : Equiv (formLimit e f) (formLimit e' f') := by
  cases he
  cases hf
  exact Equiv.refl _

theorem presentedForm_sameBase {base : Nat} (e f : PlaquetteExpression base) :
    Equiv (presentedForm ⟨base,e⟩ ⟨base,f⟩) (formLimit e f) :=
  (presentedForm_atBase ⟨base,e⟩ ⟨base,f⟩ base (Nat.le_refl _) (Nat.le_refl _)).trans
    (formLimit_congr_eq (atBase_self ⟨base,e⟩) (atBase_self ⟨base,f⟩))

theorem presentedForm_converges_at (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) :
    ConvergesTo (formAtSequence p q base hp hq) (presentedForm p q) :=
  convergesTo_limit_congr (formAt_converges p q base hp hq) (presentedForm_atBase p q base hp hq).symm

theorem presentedForm_error_le_at (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : basedVolumeModulus p q base hp hq epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (presentedForm p q) (formAtSequence p q base hp hq margin))) (ofQ' epsilon) :=
  leEv_trans
    (leEv_of_equiv (abs_equiv_congr (CReal.sub_congr_left (presentedForm_atBase p q base hp hq))))
    (formAt_error_le p q base hp hq epsilon he margin hm)

/-- State-independent semantic equality preserves the actual interacting form. -/
theorem presentedForm_same {p p' q q' : Presentation} (h : SameObservable p p') (k : SameObservable q q') :
    Equiv (presentedForm p q) (presentedForm p' q') := by
  let N := h.cutoff+k.cutoff
  have hp := h.left_le
  have hp' := h.right_le
  have hq := k.left_le
  have hq' := k.right_le
  have hpN : p.base ≤ N := by omega
  have hpN' : p'.base ≤ N := by omega
  have hqN : q.base ≤ N := by omega
  have hqN' : q'.base ≤ N := by omega
  apply Equiv_of_limit_of_equal
    (aSeq := formAtSequence p q N hpN hqN) (bSeq := formAtSequence p' q' N hpN' hqN')
  · intro margin
    exact formAt_carrier_congr (N+margin) (by omega) (by omega) (by omega) (by omega)
      (h.equal (N+margin) (by omega)) (k.equal (N+margin) (by omega))
  · exact presentedForm_converges_at p q N hpN hqN
  · exact presentedForm_converges_at p' q' N hpN' hqN'

def pairing : Observable → Observable → RC :=
  Quotient.lift₂ (fun p q => Quotient.mk crealSetoid (presentedForm p q))
    (fun _ _ _ _ ⟨h⟩ ⟨k⟩ => Quotient.sound (presentedForm_same h k))

theorem pairing_embed (p q : Presentation) :
    pairing (embed p) (embed q) = Quotient.mk crealSetoid (presentedForm p q) := rfl

/-- Data for a presented pairing; quotient descent never selects representatives. -/
def pairingRepresentative (p q : Presentation) :
    Σ' r : CReal, QCauchy r.approx ×' (pairing (embed p) (embed q) = Quotient.mk crealSetoid r) :=
  ⟨presentedForm p q, presentedFormCauchy p q, rfl⟩

theorem pairing_atBase (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) :
    pairing (embed p) (embed q) =
      Quotient.mk crealSetoid (formLimit (atBase p base hp) (atBase q base hq)) :=
  Quotient.sound (presentedForm_atBase p q base hp hq)

theorem pairing_sameBase {base : Nat} (e f : PlaquetteExpression base) :
    pairing (embed ⟨base,e⟩) (embed ⟨base,f⟩) = Quotient.mk crealSetoid (formLimit e f) :=
  Quotient.sound (presentedForm_sameBase e f)

end YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.presentedForm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.presentedFormCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.presentedVolumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.presentedForm_atBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.presentedForm_sameBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.presentedForm_converges_at
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.presentedForm_error_le_at
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.presentedForm_same
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.pairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.pairing_embed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.pairingRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.pairing_atBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable.pairing_sameBase
