/-
# The finite rational span of a positive kernel

Vectors retain an explicit list of (state, coefficient) terms; the state type
need not be finite or have decidable equality. Carrier equivalence means
equality of pairings against every kernel section, not equality of coefficient
presentations. Thus repeated states and negative coefficients are allowed,
and only the form radical can be identified. The GNS quotient is still the
generic, positive-definite quotient of this same form.

This is algebraic machinery, not a physical positivity assumption discharged
by definition: the caller must prove symmetry and positivity for every finite
term list. The physical cube application supplies those proofs from its actual
common-cutoff boundary Gram.
-/

import YMGap.Continuum.GNSQuotient
import YMGap.Continuum.FiniteWeightedGramSOS
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

namespace YMGap.Continuum.RationalKernelSpan

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm

local infix:50 " ≈ " => Q'.eqv

abbrev Span (State : Type) := List (State × Q')

def sectionPairing {State : Type} (kernel : State → State → Q')
    (terms : Span State) (test : State) : Q' :=
  listQSum (fun term => term.2 * kernel term.1 test) terms

def form {State : Type} (kernel : State → State → Q')
    (left right : Span State) : Q' :=
  listQSum (fun term => term.2 * sectionPairing kernel left term.1) right

def scale {State : Type} (scalar : Q') (terms : Span State) : Span State :=
  terms.map (fun term => (term.1, scalar * term.2))

def sectionEq {State : Type} (kernel : State → State → Q')
    (left right : Span State) : Prop :=
  ∀ test, sectionPairing kernel left test ≈ sectionPairing kernel right test

def basis {State : Type} (state : State) : Span State := [(state, 1)]

theorem pairing_append {State : Type} (kernel : State → State → Q')
    (left right : Span State) (test : State) :
    sectionPairing kernel (left ++ right) test ≈
      sectionPairing kernel left test + sectionPairing kernel right test :=
  listQSum_append _ left right

theorem pairing_scale {State : Type} (kernel : State → State → Q')
    (scalar : Q') (terms : Span State) (test : State) :
    sectionPairing kernel (scale scalar terms) test ≈
      scalar * sectionPairing kernel terms test := by
  unfold sectionPairing scale
  rw [listQSum_map]
  exact Q'.eqv_trans _ _ _
    (listQSum_congr (fun term => Q'.mul_assoc_eqv scalar term.2
      (kernel term.1 test)) terms)
    (listQSum_mul_left scalar _ terms)

theorem pairing_basis {State : Type} (kernel : State → State → Q')
    (state test : State) : sectionPairing kernel (basis state) test ≈ kernel state test := by
  change 1 * kernel state test + 0 ≈ kernel state test
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (Q'.one_mul_eqv _)

theorem form_basis {State : Type} (kernel : State → State → Q')
    (left right : State) : form kernel (basis left) (basis right) ≈ kernel left right := by
  change 1 * sectionPairing kernel (basis left) right + 0 ≈ kernel left right
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))
    (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (pairing_basis kernel left right))

private theorem mul_exchange (a b c : Q') : a * (b * c) ≈ b * (a * c) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b))
      (Q'.mul_assoc_eqv b a c))

/-- The original finite bilinear sum, with no state aggregation or selection. -/
theorem form_expansion {State : Type} (kernel : State → State → Q')
    (left right : Span State) : form kernel left right ≈
      listQSum (fun r => listQSum (fun l => (r.2 * l.2) * kernel l.1 r.1) left) right := by
  unfold form sectionPairing
  apply listQSum_congr
  intro r
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (listQSum_mul_left r.2 _ left))
    (listQSum_congr (fun l => Q'.eqv_symm
      (Q'.mul_assoc_eqv r.2 l.2 (kernel l.1 r.1))) left)

theorem form_symm {State : Type} (kernel : State → State → Q')
    (hsymm : ∀ left right, kernel left right ≈ kernel right left)
    (left right : Span State) : form kernel left right ≈ form kernel right left := by
  refine Q'.eqv_trans _ _ _ (form_expansion kernel left right) ?_
  refine Q'.eqv_trans _ _ _ (listQSum_swap _ left right) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (form_expansion kernel right left))
  apply listQSum_congr
  intro l
  apply listQSum_congr
  intro r
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv r.2 l.2))
    (Q'.mul_eqv_congr_left _ _ _ (hsymm l.1 r.1))

theorem form_congr_left {State : Type} (kernel : State → State → Q')
    {left left' : Span State} (right : Span State) (h : sectionEq kernel left left') :
    form kernel left right ≈ form kernel left' right := by
  unfold form
  exact listQSum_congr (fun term => Q'.mul_eqv_congr_left term.2 _ _ (h term.1)) right

theorem form_add_left {State : Type} (kernel : State → State → Q')
    (left middle right : Span State) : form kernel (left ++ middle) right ≈
      form kernel left right + form kernel middle right := by
  unfold form
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_add _ _ right)
  apply listQSum_congr
  intro term
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (pairing_append kernel left middle term.1)) (Q'.mul_add_eqv _ _ _)

theorem form_scale_left {State : Type} (kernel : State → State → Q')
    (scalar : Q') (left right : Span State) : form kernel (scale scalar left) right ≈
      scalar * form kernel left right := by
  unfold form
  refine Q'.eqv_trans _ _ _ ?_ (listQSum_mul_left scalar _ right)
  apply listQSum_congr
  intro term
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
    (pairing_scale kernel scalar left term.1)) (mul_exchange _ _ _)

theorem sectionEq_append {State : Type} (kernel : State → State → Q')
    {a a' b b' : Span State} (ha : sectionEq kernel a a') (hb : sectionEq kernel b b') :
    sectionEq kernel (a ++ b) (a' ++ b') := fun test =>
  Q'.eqv_trans _ _ _ (pairing_append kernel a b test)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (ha test) (hb test))
      (Q'.eqv_symm (pairing_append kernel a' b' test)))

theorem sectionEq_scale {State : Type} (kernel : State → State → Q')
    (scalar : Q') {a a' : Span State} (ha : sectionEq kernel a a') :
    sectionEq kernel (scale scalar a) (scale scalar a') := fun test =>
  Q'.eqv_trans _ _ _ (pairing_scale kernel scalar a test)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ha test))
      (Q'.eqv_symm (pairing_scale kernel scalar a' test)))

/-- A genuine rational GNS module for an arbitrary positive kernel. -/
def toGNSData {State : Type} (kernel : State → State → Q')
    (hsymm : ∀ left right, kernel left right ≈ kernel right left)
    (hpositive : ∀ terms : Span State, (0 : Q') ≤ form kernel terms terms) : GNSData where
  V := Span State
  veq := sectionEq kernel
  veq_refl := fun _ _ => Q'.eqv_refl _
  veq_symm := fun h test => Q'.eqv_symm (h test)
  veq_trans := fun h h' test => Q'.eqv_trans _ _ _ (h test) (h' test)
  zero := []
  add := List.append
  neg := scale (-1)
  smul := scale
  add_congr := sectionEq_append kernel
  neg_congr := sectionEq_scale kernel (-1)
  smul_congr := sectionEq_scale kernel
  add_assoc := by
    intro a b c test
    change sectionPairing kernel ((a ++ b) ++ c) test ≈
      sectionPairing kernel (a ++ (b ++ c)) test
    rw [List.append_assoc]
    exact Q'.eqv_refl _
  add_comm := fun a b test =>
    Q'.eqv_trans _ _ _ (pairing_append kernel a b test)
      (Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
        (Q'.eqv_symm (pairing_append kernel b a test)))
  zero_add := fun _ _ => Q'.eqv_refl _
  neg_add := by
    intro a test
    refine Q'.eqv_trans _ _ _ (pairing_append kernel (scale (-1) a) a test) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (pairing_scale kernel (-1) a test) (Q'.eqv_refl _)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ?_ (Q'.eqv_refl _))
      (Q'.neg_add_self_eqv _)
    exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 _)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _))
  B := form kernel
  B_congr_left := form_congr_left kernel
  B_add_left := form_add_left kernel
  B_smul_left := form_scale_left kernel
  B_symm := form_symm kernel hsymm
  self_nonneg := hpositive

end YMGap.Continuum.RationalKernelSpan

#print axioms YMGap.Continuum.RationalKernelSpan.pairing_append
#print axioms YMGap.Continuum.RationalKernelSpan.pairing_scale
#print axioms YMGap.Continuum.RationalKernelSpan.pairing_basis
#print axioms YMGap.Continuum.RationalKernelSpan.form_basis
#print axioms YMGap.Continuum.RationalKernelSpan.form_expansion
#print axioms YMGap.Continuum.RationalKernelSpan.form_symm
#print axioms YMGap.Continuum.RationalKernelSpan.form_congr_left
#print axioms YMGap.Continuum.RationalKernelSpan.form_add_left
#print axioms YMGap.Continuum.RationalKernelSpan.form_scale_left
#print axioms YMGap.Continuum.RationalKernelSpan.sectionEq_append
#print axioms YMGap.Continuum.RationalKernelSpan.sectionEq_scale
#print axioms YMGap.Continuum.RationalKernelSpan.toGNSData
