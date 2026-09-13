/-
# Bilinear OS geometry on the SAME semantic thermodynamic observable algebra

Computed common-base representatives reduce the laws to the original
thermodynamic reflected form. The pairing is symmetric, rational-bilinear,
positive, normalized and sharp-CS; its radical pairs to zero. Its unit
rows equal the already-constructed original mean functional.

The connected pairing also descends to this same carrier and is pinned
to the constructed thermodynamic covariance, with positivity and sharp CS.
No thermodynamic completion, physical stationary vacuum or time operator
is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable

namespace YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (PlaquetteExpression)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerFunctional
open YMGap.Continuum.BF4ExactSlabThermodynamicLowerAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedObservable
open YMGap.Continuum.BF4ExactSlabThermodynamicReflectedForm
open YMGap.Continuum.BF4ExactSlabThermodynamicConnectedCovariance
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction

private theorem observable_inductionOn {P : Observable → Prop} (x : Observable)
    (h : ∀ p : Presentation, P (embed p)) : P x := Quotient.inductionOn x h

private theorem observable_inductionOn₂ {P : Observable → Observable → Prop} (x y : Observable)
    (h : ∀ p q : Presentation, P (embed p) (embed q)) : P x y := Quotient.inductionOn₂ x y h

private theorem observable_inductionOn₃ {P : Observable → Observable → Observable → Prop} (x y z : Observable)
    (h : ∀ p q r : Presentation, P (embed p) (embed q) (embed r)) : P x y z := Quotient.inductionOn₃ x y z h

theorem qadd_sameBase {base : Nat} (e f : PlaquetteExpression base) :
    qadd (embed ⟨base,e⟩) (embed ⟨base,f⟩) = embed ⟨base,.add e f⟩ := by
  apply embed_eq_of_coeff (add ⟨base,e⟩ ⟨base,f⟩) ⟨base,.add e f⟩ (base+base) (Nat.le_refl _) (Nat.le_add_right _ _)
  intro volume hv
  rw [polynomial_add ⟨base,e⟩ ⟨base,f⟩ volume hv]
  exact RatPolyCoeffEqv.refl _

theorem qsmul_sameBase {base : Nat} (c : Q') (e : PlaquetteExpression base) :
    qsmul c (embed ⟨base,e⟩) = embed ⟨base,.smul c e⟩ := rfl

theorem embed_unit (base : Nat) : embed ⟨base,(.unit : PlaquetteExpression base)⟩ = unit := by
  apply Quotient.sound
  refine ⟨⟨base, Nat.le_refl _, Nat.zero_le _, ?_⟩⟩
  intro volume _
  exact HaarCarrierEqv.refl _ polyOne

theorem pairing_symm (x y : Observable) : pairing x y = pairing y x := by
  refine observable_inductionOn₂ (P := fun a b => pairing a b = pairing b a) x y ?_
  intro p q
  rw [pairing_atBase p q (p.base+q.base) (Nat.le_add_right _ _) (Nat.le_add_left _ _),
    pairing_atBase q p (p.base+q.base) (Nat.le_add_left _ _) (Nat.le_add_right _ _)]
  exact Quotient.sound (form_symm _ _)

theorem pairing_add_left (x y z : Observable) :
    pairing (qadd x y) z = RCadd (pairing x z) (pairing y z) := by
  refine observable_inductionOn₃
    (P := fun a b d => pairing (qadd a b) d = RCadd (pairing a d) (pairing b d)) x y z ?_
  intro p q r
  let N := p.base+q.base+r.base
  have hp : p.base ≤ N := by omega
  have hq : q.base ≤ N := by omega
  have hr : r.base ≤ N := by omega
  rw [← embed_atBase p N hp, ← embed_atBase q N hq, ← embed_atBase r N hr,
    qadd_sameBase, pairing_sameBase, pairing_sameBase, pairing_sameBase]
  exact Quotient.sound (form_add_left _ _ _)

theorem pairing_add_right (x y z : Observable) :
    pairing x (qadd y z) = RCadd (pairing x y) (pairing x z) := by
  rw [pairing_symm x (qadd y z), pairing_add_left, pairing_symm y x, pairing_symm z x]

theorem pairing_smul_left (c : Q') (x y : Observable) :
    pairing (qsmul c x) y = RCmul (Quotient.mk crealSetoid (ofQ' c)) (pairing x y) := by
  refine observable_inductionOn₂
    (P := fun a b => pairing (qsmul c a) b = RCmul (Quotient.mk crealSetoid (ofQ' c)) (pairing a b)) x y ?_
  intro p q
  let N := p.base+q.base
  rw [← embed_atBase p N (Nat.le_add_right _ _), ← embed_atBase q N (Nat.le_add_left _ _),
    qsmul_sameBase, pairing_sameBase, pairing_sameBase]
  exact Quotient.sound (form_smul_left c _ _)

theorem pairing_smul_right (c : Q') (x y : Observable) :
    pairing x (qsmul c y) = RCmul (Quotient.mk crealSetoid (ofQ' c)) (pairing x y) := by
  rw [pairing_symm x (qsmul c y), pairing_smul_left, pairing_symm y x]

theorem pairing_nonnegative (x : Observable) : RCnonneg (pairing x x) := by
  refine observable_inductionOn (P := fun a => RCnonneg (pairing a a)) x ?_
  intro p
  rw [pairing_sameBase]
  exact form_nonnegative p.expression

theorem pairing_unit : pairing unit unit = Quotient.mk crealSetoid cone := by
  rw [← embed_unit 0, pairing_sameBase]
  exact Quotient.sound (form_unit 0)

theorem pairing_unit_left_value (x : Observable) : pairing unit x = value x := by
  refine observable_inductionOn (P := fun a => pairing unit a = value a) x ?_
  intro p
  rw [← embed_unit p.base, pairing_sameBase, value_embed]
  exact Quotient.sound (form_unit_left_mean p.expression)

theorem pairing_unit_right_value (x : Observable) : pairing x unit = value x := by
  rw [pairing_symm, pairing_unit_left_value]

theorem pairing_cauchySchwarz (x y : Observable) :
    RCle (RCmul (pairing x y) (pairing x y)) (RCmul (pairing x x) (pairing y y)) := by
  refine observable_inductionOn₂
    (P := fun a b => RCle (RCmul (pairing a b) (pairing a b)) (RCmul (pairing a a) (pairing b b))) x y ?_
  intro p q
  let N := p.base+q.base
  rw [← embed_atBase p N (Nat.le_add_right _ _), ← embed_atBase q N (Nat.le_add_left _ _),
    pairing_sameBase, pairing_sameBase, pairing_sameBase]
  exact form_cauchySchwarz _ _

theorem pairing_radical_zero (x y : Observable) (hx : pairing x x = RCzero) : pairing x y = RCzero := by
  revert hx
  refine observable_inductionOn₂ (P := fun a b => pairing a a = RCzero → pairing a b = RCzero) x y ?_
  intro p q hx
  let N := p.base+q.base
  rw [← embed_atBase p N (Nat.le_add_right _ _)] at hx ⊢
  rw [← embed_atBase q N (Nat.le_add_left _ _), pairing_sameBase]
  rw [pairing_sameBase] at hx
  exact Quotient.sound (form_radical_zero _ _ (Quotient.exact hx))

private theorem rc_zero_mul (x : RC) : RCmul RCzero x = RCzero := by
  refine Quotient.inductionOn x ?_
  intro a
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (a.approx n)))

theorem pairing_zero_left (x : Observable) : pairing zero x = RCzero := by
  rw [zero, pairing_smul_left]
  exact rc_zero_mul _

theorem pairing_zero_right (x : Observable) : pairing x zero = RCzero := by
  rw [pairing_symm, pairing_zero_left]

def connectedPairing (x y : Observable) : RC :=
  RCsub (pairing x y) (RCmul (value x) (value y))

theorem connectedPairing_sameBase {base : Nat} (e f : PlaquetteExpression base) :
    connectedPairing (embed ⟨base,e⟩) (embed ⟨base,f⟩) = Quotient.mk crealSetoid (covarianceLimit e f) := by
  unfold connectedPairing
  rw [pairing_sameBase, value_embed, value_embed]
  rfl

theorem connectedPairing_nonnegative (x : Observable) : RCnonneg (connectedPairing x x) := by
  refine observable_inductionOn (P := fun a => RCnonneg (connectedPairing a a)) x ?_
  intro p
  rw [connectedPairing_sameBase]
  exact covariance_nonnegative p.expression

theorem connectedPairing_cauchySchwarz (x y : Observable) :
    RCle (RCmul (connectedPairing x y) (connectedPairing x y))
      (RCmul (connectedPairing x x) (connectedPairing y y)) := by
  refine observable_inductionOn₂
    (P := fun a b => RCle (RCmul (connectedPairing a b) (connectedPairing a b))
      (RCmul (connectedPairing a a) (connectedPairing b b))) x y ?_
  intro p q
  let N := p.base+q.base
  rw [← embed_atBase p N (Nat.le_add_right _ _), ← embed_atBase q N (Nat.le_add_left _ _),
    connectedPairing_sameBase, connectedPairing_sameBase, connectedPairing_sameBase]
  exact covariance_cauchySchwarz _ _

end YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.qadd_sameBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.qsmul_sameBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.embed_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_add_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_add_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_unit_left_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_unit_right_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_radical_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_zero_left
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.pairing_zero_right
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.connectedPairing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.connectedPairing_sameBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.connectedPairing_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicReflectedBilinear.connectedPairing_cauchySchwarz
