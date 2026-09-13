/-
# Presentation-independent ORIGINAL lower plaquette observables

A presentation carries a finite base and an existing lower plaquette
expression. Equality means equality on the original Haar carrier, under
EVERY polynomial insertion, at all sufficiently large common volumes.
The comparison threshold is Type-valued data. This relation does not mention
the interacting state or its limit; it is not equality of means by definition.

Base enlargement and algebra operations preserve this relation. The already
constructed thermodynamic means agree on it by a common-volume limit proof.
The scope is the lower plaquette-generated algebra, not a full spacetime
observable algebra, an OS form or a physical time-transfer construction.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPresentation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabExpressionExpectationDecay
open YMGap.Continuum.BF4ExactSlabExpressionThermodynamicLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

structure Presentation : Type where
  base : Nat
  expression : PlaquetteExpression base

def transport {a b : Nat} (h : a=b) (e : PlaquetteExpression a) : PlaquetteExpression b := h ▸ e

theorem shiftedExpression_transport {a b : Nat} (h : a=b) (margin : Nat) (e : PlaquetteExpression a) :
    shiftedExpression margin (transport h e) = shiftedExpression margin e := by cases h; rfl

theorem meanLimit_transport {a b : Nat} (h : a=b) (e : PlaquetteExpression a) :
    meanLimit (transport h e) = meanLimit e := by cases h; rfl

def atBase (p : Presentation) (target : Nat) (hp : p.base ≤ target) : PlaquetteExpression target :=
  transport (Nat.add_sub_of_le hp) (enlarge (target-p.base) p.expression)

def polynomial (p : Presentation) (volume : Nat) : RatPoly :=
  shiftedExpression (volume-p.base) p.expression

theorem atBase_polynomial (p : Presentation) (target : Nat) (hp : p.base ≤ target)
    (volume : Nat) (hv : target ≤ volume) :
    shiftedExpression (volume-target) (atBase p target hp) = polynomial p volume := by
  unfold atBase
  rw [shiftedExpression_transport, shiftedExpression_enlarge]
  rw [show target-p.base+(volume-target) = volume-p.base by omega]
  rfl

theorem meanLimit_atBase (p : Presentation) (target : Nat) (hp : p.base ≤ target) :
    Equiv (meanLimit (atBase p target hp)) (meanLimit p.expression) := by
  unfold atBase
  rw [meanLimit_transport]
  exact meanLimit_enlarge _ _

def add (p q : Presentation) : Presentation :=
  ⟨p.base+q.base, .add (atBase p _ (Nat.le_add_right _ _)) (atBase q _ (Nat.le_add_left _ _))⟩

def mul (p q : Presentation) : Presentation :=
  ⟨p.base+q.base, .mul (atBase p _ (Nat.le_add_right _ _)) (atBase q _ (Nat.le_add_left _ _))⟩

def smul (c : Q') (p : Presentation) : Presentation := ⟨p.base, .smul c p.expression⟩

def one : Presentation := ⟨0, .unit⟩

theorem polynomial_add (p q : Presentation) (volume : Nat) (hv : p.base+q.base ≤ volume) :
    polynomial (add p q) volume = polyAdd (polynomial p volume) (polynomial q volume) := by
  change polyAdd (shiftedExpression (volume-(p.base+q.base)) (atBase p (p.base+q.base) (Nat.le_add_right _ _)))
    (shiftedExpression (volume-(p.base+q.base)) (atBase q (p.base+q.base) (Nat.le_add_left _ _))) = _
  rw [atBase_polynomial p _ (Nat.le_add_right _ _) volume hv, atBase_polynomial q _ (Nat.le_add_left _ _) volume hv]

theorem polynomial_mul (p q : Presentation) (volume : Nat) (hv : p.base+q.base ≤ volume) :
    polynomial (mul p q) volume = polyMul (polynomial p volume) (polynomial q volume) := by
  change polyMul (shiftedExpression (volume-(p.base+q.base)) (atBase p (p.base+q.base) (Nat.le_add_right _ _)))
    (shiftedExpression (volume-(p.base+q.base)) (atBase q (p.base+q.base) (Nat.le_add_left _ _))) = _
  rw [atBase_polynomial p _ (Nat.le_add_right _ _) volume hv, atBase_polynomial q _ (Nat.le_add_left _ _) volume hv]

theorem polynomial_smul (c : Q') (p : Presentation) (volume : Nat) :
    polynomial (smul c p) volume = polySmul c (polynomial p volume) := rfl

theorem polynomial_one (volume : Nat) : polynomial one volume = polyOne := rfl

structure SameObservable (p q : Presentation) : Type where
  cutoff : Nat
  left_le : p.base ≤ cutoff
  right_le : q.base ≤ cutoff
  equal : ∀ volume, cutoff ≤ volume →
    HaarCarrierEqv (boundaryCompleteSlabLinks (centralExtent volume)).length (polynomial p volume) (polynomial q volume)

def SameObservable.refl (p : Presentation) : SameObservable p p :=
  ⟨p.base, Nat.le_refl _, Nat.le_refl _, fun _ _ => HaarCarrierEqv.refl _ _⟩

def SameObservable.symm {p q : Presentation} (h : SameObservable p q) : SameObservable q p :=
  ⟨h.cutoff, h.right_le, h.left_le, fun volume hv => (h.equal volume hv).symm⟩

def SameObservable.trans {p q r : Presentation} (h : SameObservable p q) (k : SameObservable q r) : SameObservable p r :=
  ⟨max h.cutoff k.cutoff, Nat.le_trans h.left_le (Nat.le_max_left _ _),
    Nat.le_trans k.right_le (Nat.le_max_right _ _), fun volume hv =>
      (h.equal volume (Nat.le_trans (Nat.le_max_left _ _) hv)).trans
        (k.equal volume (Nat.le_trans (Nat.le_max_right _ _) hv))⟩

def SameObservable.rebase (p : Presentation) (target : Nat) (hp : p.base ≤ target) :
    SameObservable ⟨target, atBase p target hp⟩ p := by
  refine ⟨target, Nat.le_refl _, hp, ?_⟩
  intro volume hv
  change HaarCarrierEqv _ (shiftedExpression (volume-target) (atBase p target hp)) _
  rw [atBase_polynomial p target hp volume hv]
  exact HaarCarrierEqv.refl _ _

def SameObservable.add {p p' q q' : Presentation} (h : SameObservable p p') (k : SameObservable q q') :
    SameObservable (add p q) (add p' q') := by
  let N := (p.base+q.base)+(p'.base+q'.base)+h.cutoff+k.cutoff
  refine ⟨N, by change p.base+q.base ≤ N; omega, by change p'.base+q'.base ≤ N; omega, ?_⟩
  intro volume hv
  rw [polynomial_add p q volume (by omega), polynomial_add p' q' volume (by omega)]
  exact HaarCarrierEqv.add (h.equal volume (by omega)) (k.equal volume (by omega))

def SameObservable.mul {p p' q q' : Presentation} (h : SameObservable p p') (k : SameObservable q q') :
    SameObservable (mul p q) (mul p' q') := by
  let N := (p.base+q.base)+(p'.base+q'.base)+h.cutoff+k.cutoff
  refine ⟨N, by change p.base+q.base ≤ N; omega, by change p'.base+q'.base ≤ N; omega, ?_⟩
  intro volume hv
  rw [polynomial_mul p q volume (by omega), polynomial_mul p' q' volume (by omega)]
  exact HaarCarrierEqv.mul (h.equal volume (by omega)) (k.equal volume (by omega))

def SameObservable.smul (c : Q') {p q : Presentation} (h : SameObservable p q) :
    SameObservable (smul c p) (smul c q) :=
  ⟨h.cutoff, h.left_le, h.right_le, fun volume hv => HaarCarrierEqv.smul c (h.equal volume hv)⟩

def meanAt (p : Presentation) (volume : Nat) : CReal :=
  expectation nome nome_pos nome_lt_one volume (polynomial p volume)

theorem meanAt_tail (p : Presentation) (cutoff : Nat) (hp : p.base ≤ cutoff) (margin : Nat) :
    meanAt p (cutoff+margin) = meanSequence p.expression ((cutoff-p.base)+margin) := by
  unfold meanAt meanSequence expressionMean polynomial
  rw [show p.base+(cutoff-p.base+margin) = cutoff+margin by omega]
  rw [show cutoff-p.base+margin = cutoff+margin-p.base by omega]

theorem meanAt_converges (p : Presentation) (cutoff : Nat) (hp : p.base ≤ cutoff) :
    ConvergesTo (fun margin => meanAt p (cutoff+margin)) (meanLimit p.expression) := by
  have he : (fun margin => meanAt p (cutoff+margin)) =
      (fun margin => meanSequence p.expression ((cutoff-p.base)+margin)) := funext (meanAt_tail p cutoff hp)
  rw [he]
  exact meanSequence_tail_converges _ _

/-- State compatibility follows from carrier equality, not conversely. -/
theorem meanLimit_same {p q : Presentation} (h : SameObservable p q) :
    Equiv (meanLimit p.expression) (meanLimit q.expression) :=
  Equiv_of_limit_of_equal
    (fun margin => expectation_carrier_congr nome nome_pos nome_lt_one (h.cutoff+margin)
      (h.equal (h.cutoff+margin) (Nat.le_add_right _ _)))
    (meanAt_converges p h.cutoff h.left_le) (meanAt_converges q h.cutoff h.right_le)

end YMGap.Continuum.BF4ExactSlabThermodynamicPresentation

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.Presentation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.transport
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.shiftedExpression_transport
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.meanLimit_transport
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.atBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.polynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.atBase_polynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.meanLimit_atBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.polynomial_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.polynomial_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.polynomial_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.polynomial_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.SameObservable
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.SameObservable.refl
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.SameObservable.symm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.SameObservable.trans
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.SameObservable.rebase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.SameObservable.add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.SameObservable.mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.SameObservable.smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.meanAt
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.meanAt_tail
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.meanAt_converges
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPresentation.meanLimit_same
