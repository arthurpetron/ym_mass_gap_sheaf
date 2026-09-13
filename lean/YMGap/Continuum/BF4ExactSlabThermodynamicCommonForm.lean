/-
# Common-volume compatibility of the ORIGINAL thermodynamic reflected form

Original Haar-carrier equality of lower observables preserves the second
slot of the finite OS form; symmetry preserves the first. Thus no new
reflection-equivariance assumption is needed for semantic descent.

At any common base, the actual finite-volume pairings converge to the
constructed reflected form with its explicit volume and representative
moduli. Comparing two tails at a common volume proves base independence.
This is not time homogeneity, a transfer operator, or a spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicCovarianceRate
import YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm (form)
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabSpacetimeExpression (evaluate_lower_enlarge evaluate_fromLower)
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression (shiftedExpression)
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

theorem form_lower_right_congr (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} (e : PlaquetteExpression half) {f g : PlaquetteExpression half}
    (h : HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length (lower f) (lower g)) :
    Equiv (form w hw0 hw1 e f) (form w hw0 hw1 e g) :=
  expectation_carrier_congr w hw0 hw1 half (HaarCarrierEqv.mul (HaarCarrierEqv.refl _ (upper e)) h)

theorem form_lower_congr (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {half : Nat} {e e' f f' : PlaquetteExpression half}
    (he : HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length (lower e) (lower e'))
    (hf : HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent half)).length (lower f) (lower f')) :
    Equiv (form w hw0 hw1 e f) (form w hw0 hw1 e' f') :=
  (form_lower_right_congr w hw0 hw1 e hf).trans
    ((BF4ExactSlabPlaquetteReflectedForm.form_symm w hw0 hw1 e f').trans
      ((form_lower_right_congr w hw0 hw1 f' he).trans
        (BF4ExactSlabPlaquetteReflectedForm.form_symm w hw0 hw1 f' e')))

theorem lower_transport {a b : Nat} (h : a=b) (e : PlaquetteExpression a) :
    lower (transport h e) = lower e := by cases h; rfl

theorem lower_enlarge {base : Nat} (margin : Nat) (e : PlaquetteExpression base) :
    lower (enlarge margin e) = shiftedExpression margin e :=
  (evaluate_lower_enlarge margin e).symm.trans (evaluate_fromLower margin e)

private theorem transport_enlarge_zero {base : Nat} (padding : Nat) (hp : padding=0)
    (h : base+padding=base) (e : PlaquetteExpression base) : transport h (enlarge padding e) = e := by
  subst padding
  change enlarge 0 e = e
  exact BF4ExactSlabPlaquetteBulkEmbedding.bulkAtTime_zero e

theorem atBase_self (p : Presentation) : atBase p p.base (Nat.le_refl _) = p.expression :=
  transport_enlarge_zero (p.base-p.base) (Nat.sub_self _) (Nat.add_sub_of_le (Nat.le_refl _)) p.expression

theorem lower_atBase (p : Presentation) (volume : Nat) (hp : p.base ≤ volume) :
    lower (atBase p volume hp) = polynomial p volume := by
  unfold atBase
  rw [lower_transport, lower_enlarge]
  rfl

def formAt (p q : Presentation) (volume : Nat) (hp : p.base ≤ volume) (hq : q.base ≤ volume) : CReal :=
  form nome nome_pos nome_lt_one (atBase p volume hp) (atBase q volume hq)

theorem formAt_volume_eq (p q : Presentation) {volume volume' : Nat} (h : volume=volume')
    (hp : p.base ≤ volume) (hq : q.base ≤ volume) (hp' : p.base ≤ volume') (hq' : q.base ≤ volume') :
    formAt p q volume hp hq = formAt p q volume' hp' hq' := by cases h; rfl

theorem formAt_carrier_congr {p p' q q' : Presentation} (volume : Nat)
    (hp : p.base ≤ volume) (hq : q.base ≤ volume) (hp' : p'.base ≤ volume) (hq' : q'.base ≤ volume)
    (he : HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent volume)).length (polynomial p volume) (polynomial p' volume))
    (hf : HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent volume)).length (polynomial q volume) (polynomial q' volume)) :
    Equiv (formAt p q volume hp hq) (formAt p' q' volume hp' hq') := by
  have he' : HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent volume)).length
      (lower (atBase p volume hp)) (lower (atBase p' volume hp')) := by
    rw [lower_atBase p volume hp, lower_atBase p' volume hp']
    exact he
  have hf' : HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent volume)).length
      (lower (atBase q volume hq)) (lower (atBase q' volume hq')) := by
    rw [lower_atBase q volume hq, lower_atBase q' volume hq']
    exact hf
  exact form_lower_congr nome nome_pos nome_lt_one he' hf'

def basedForm (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) : CReal :=
  formLimit (atBase p base hp) (atBase q base hq)

def basedFormCauchy (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) :
    QCauchy (basedForm p q base hp hq).approx :=
  formLimitCauchy (atBase p base hp) (atBase q base hq)

def basedVolumeModulus (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) : Q' → Nat :=
  formVolumeModulus (atBase p base hp) (atBase q base hq)

def formAtSequence (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) (margin : Nat) : CReal :=
  formAt p q (base+margin) (Nat.le_trans hp (Nat.le_add_right _ _)) (Nat.le_trans hq (Nat.le_add_right _ _))

private theorem common_lower_pin (p : Presentation) (base : Nat) (hp : p.base ≤ base) (margin : Nat) :
    lower (atBase p (base+margin) (Nat.le_trans hp (Nat.le_add_right _ _))) =
      lower (enlarge margin (atBase p base hp)) := by
  rw [lower_atBase, lower_enlarge]
  have h := atBase_polynomial p base hp (base+margin) (Nat.le_add_right _ _)
  rw [Nat.add_sub_cancel_left] at h
  exact h.symm

theorem formAtSequence_pin (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) (margin : Nat) :
    Equiv (formAtSequence p q base hp hq margin)
      (formSequence (atBase p base hp) (atBase q base hq) margin) := by
  apply form_lower_congr nome nome_pos nome_lt_one
  · rw [common_lower_pin p base hp margin]
    exact HaarCarrierEqv.refl _ _
  · rw [common_lower_pin q base hq margin]
    exact HaarCarrierEqv.refl _ _

theorem formAt_converges (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base) :
    ConvergesTo (formAtSequence p q base hp hq) (basedForm p q base hp hq) :=
  TrigAddCReal.convergesTo_congr_seq (fun margin => (formAtSequence_pin p q base hp hq margin).symm)
    (form_converges (atBase p base hp) (atBase q base hq))

theorem formAt_error_le (p q : Presentation) (base : Nat) (hp : p.base ≤ base) (hq : q.base ≤ base)
    (epsilon : Q') (he : (0 : Q') < epsilon) (margin : Nat)
    (hm : basedVolumeModulus p q base hp hq epsilon ≤ margin) :
    leEv (CReal.abs (CReal.sub (basedForm p q base hp hq) (formAtSequence p q base hp hq margin))) (ofQ' epsilon) :=
  leEv_trans
    (leEv_of_equiv (abs_equiv_congr (CReal.sub_congr_right (formAtSequence_pin p q base hp hq margin))))
    (form_error_le (atBase p base hp) (atBase q base hq) epsilon he margin hm)

private theorem tail_converges {s : Nat → CReal} {L : CReal} (h : ConvergesTo s L) (padding : Nat) :
    ConvergesTo (fun n => s (padding+n)) L := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  exact ⟨N, fun n hn => hN (padding+n) (Nat.le_trans hn (Nat.le_add_left _ _))⟩

private theorem realEquiv_of_eq {a b : CReal} (h : a=b) : Equiv a b := by
  cases h
  exact Equiv.refl a

/-- Compare the two actual tails at the same absolute volume, then use uniqueness. -/
theorem basedForm_compatible (p q : Presentation) (base target : Nat)
    (hp : p.base ≤ base) (hq : q.base ≤ base) (hp' : p.base ≤ target) (hq' : q.base ≤ target) :
    Equiv (basedForm p q base hp hq) (basedForm p q target hp' hq') := by
  apply Equiv_of_limit_of_equal
    (aSeq := fun n => formAtSequence p q base hp hq (target+n))
    (bSeq := fun n => formAtSequence p q target hp' hq' (base+n))
  · intro n
    have h : base+(target+n) = target+(base+n) := by omega
    have heq : formAtSequence p q base hp hq (target+n) = formAtSequence p q target hp' hq' (base+n) :=
      formAt_volume_eq p q h (by omega) (by omega) (by omega) (by omega)
    exact realEquiv_of_eq heq
  · exact tail_converges (formAt_converges p q base hp hq) target
  · exact tail_converges (formAt_converges p q target hp' hq') base

end YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.form_lower_right_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.form_lower_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.lower_transport
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.lower_enlarge
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.atBase_self
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.lower_atBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.formAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.formAt_volume_eq
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.formAt_carrier_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.basedForm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.basedFormCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.basedVolumeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.formAtSequence
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.formAtSequence_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.formAt_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.formAt_error_le
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCommonForm.basedForm_compatible
