/-
# Literal outward time translation of ORIGINAL thermodynamic presentations

The coordinate convention puts the positive-time algebra in the lower half.
An outward lag t therefore subtracts t from the time coordinate relative to
the central reflection plane. Spatial recentering is unchanged. Translation
uses the existing bulk map, with a computed base large enough to contain it.

All identities below are literal polynomial identities on the same target
link variables. In particular, changing the base box commutes with physical
translation, and successive lags add. No invariance of the interacting state,
OS norm inequality, or descent through arbitrary semantic equality is assumed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPresentation

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteTimeEmbedding (evaluate_congr)
open YMGap.Continuum.BF4ExactSlabShiftedPlaquetteExpression
open YMGap.Continuum.BF4ExactSlabInnerMarginExpectationDecay (shiftedCharacter)
open YMGap.Continuum.BF4ExactSlabThermodynamicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

/-- Evaluate after shifting actual faces, with the target character map free. -/
def placed {base : Nat} (space time : Nat) (f : Z4Plaq → Nat → RatPoly)
    (e : PlaquetteExpression base) : RatPoly :=
  evaluate (fun id spin => f (shiftFace space time (slabPlaquetteAt (centralExtent base) id)) spin) e

theorem placed_bulkAtTime {base : Nat} (padding : Nat) (s : Fin (padding+1))
    (space time : Nat) (f : Z4Plaq → Nat → RatPoly) (e : PlaquetteExpression base) :
    placed space time f (bulkAtTime padding s e) =
      placed (padding+space) (padding-s.val+time) f e := by
  unfold placed
  rw [evaluate_bulkAtTime]
  apply evaluate_congr
  intro id hi spin
  rw [bulkFaceId_pin (mem_centralLowerFaceIds.mp hi).1, shiftFace_comp]

theorem placed_transport {a b : Nat} (h : a=b) (space time : Nat)
    (f : Z4Plaq → Nat → RatPoly) (e : PlaquetteExpression a) :
    placed space time f (transport h e) = placed space time f e := by cases h; rfl

theorem placed_atBase (p : Presentation) (target : Nat) (hp : p.base ≤ target)
    (space time : Nat) (f : Z4Plaq → Nat → RatPoly) :
    placed space time f (atBase p target hp) =
      placed (target-p.base+space) (target-p.base+time) f p.expression := by
  unfold atBase
  rw [placed_transport]
  unfold enlarge
  rw [placed_bulkAtTime]
  rfl

def faceCharacter (volume : Nat) (face : Z4Plaq) (spin : Nat) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial (centralExtent volume) face).scalar spin

theorem shiftedExpression_placed {base : Nat} (margin : Nat) (e : PlaquetteExpression base) :
    shiftedExpression margin e = placed margin margin (faceCharacter (base+margin)) e := rfl

/-- Positive physical lag is outward from the chosen reflection plane. -/
def translate (lag : Nat) (p : Presentation) : Presentation :=
  ⟨p.base+lag, bulkAtTime lag ⟨lag, Nat.lt_succ_self lag⟩ p.expression⟩

/-- The SAME target coordinates, with time displaced by lag and space fixed. -/
def timePolynomial (lag : Nat) (p : Presentation) (volume : Nat) : RatPoly :=
  placed (volume-p.base) (volume-p.base-lag) (faceCharacter volume) p.expression

theorem polynomial_bulkAtTime {base : Nat} (padding : Nat) (s : Fin (padding+1))
    (e : PlaquetteExpression base) (volume : Nat) (hv : base+padding ≤ volume) :
    polynomial ⟨base+padding, bulkAtTime padding s e⟩ volume =
      timePolynomial s.val ⟨base, e⟩ volume := by
  change shiftedExpression (volume-(base+padding)) (bulkAtTime padding s e) = _
  rw [shiftedExpression_placed, placed_bulkAtTime]
  have hs := s.isLt
  rw [show base+padding+(volume-(base+padding)) = volume by omega,
    show padding+(volume-(base+padding)) = volume-base by omega,
    show padding-s.val+(volume-(base+padding)) = volume-base-s.val by omega]
  rfl

theorem polynomial_translate (lag : Nat) (p : Presentation) (volume : Nat)
    (hv : p.base+lag ≤ volume) :
    polynomial (translate lag p) volume = timePolynomial lag p volume :=
  polynomial_bulkAtTime lag ⟨lag, Nat.lt_succ_self lag⟩ p.expression volume hv

theorem timePolynomial_zero (p : Presentation) (volume : Nat) (hv : p.base ≤ volume) :
    timePolynomial 0 p volume = polynomial p volume := by
  unfold polynomial
  rw [shiftedExpression_placed, show p.base+(volume-p.base) = volume by omega]
  rfl

theorem timePolynomial_translate (s t : Nat) (p : Presentation) (volume : Nat)
    (hv : p.base+s+t ≤ volume) :
    timePolynomial t (translate s p) volume = timePolynomial (s+t) p volume := by
  change placed (volume-(p.base+s)) (volume-(p.base+s)-t) (faceCharacter volume)
    (bulkAtTime s ⟨s, Nat.lt_succ_self s⟩ p.expression) = _
  rw [placed_bulkAtTime]
  simp only [Nat.sub_self, Nat.zero_add]
  rw [show s+(volume-(p.base+s)) = volume-p.base by omega,
    show volume-(p.base+s)-t = volume-p.base-(s+t) by omega]
  rfl

theorem timePolynomial_atBase (lag : Nat) (p : Presentation) (target : Nat)
    (hp : p.base ≤ target) (volume : Nat) (hv : target+lag ≤ volume) :
    timePolynomial lag ⟨target, atBase p target hp⟩ volume = timePolynomial lag p volume := by
  change placed (volume-target) (volume-target-lag) (faceCharacter volume) (atBase p target hp) = _
  rw [placed_atBase]
  rw [show target-p.base+(volume-target) = volume-p.base by omega,
    show target-p.base+(volume-target-lag) = volume-p.base-lag by omega]
  rfl

theorem timePolynomial_add (lag : Nat) (p q : Presentation) (volume : Nat)
    (hv : p.base+q.base+lag ≤ volume) :
    timePolynomial lag (add p q) volume =
      polyAdd (timePolynomial lag p volume) (timePolynomial lag q volume) := by
  change polyAdd (timePolynomial lag ⟨p.base+q.base, atBase p _ (Nat.le_add_right _ _)⟩ volume)
    (timePolynomial lag ⟨p.base+q.base, atBase q _ (Nat.le_add_left _ _)⟩ volume) = _
  rw [timePolynomial_atBase lag p _ (Nat.le_add_right _ _) volume hv,
    timePolynomial_atBase lag q _ (Nat.le_add_left _ _) volume hv]

theorem timePolynomial_mul (lag : Nat) (p q : Presentation) (volume : Nat)
    (hv : p.base+q.base+lag ≤ volume) :
    timePolynomial lag (mul p q) volume =
      polyMul (timePolynomial lag p volume) (timePolynomial lag q volume) := by
  change polyMul (timePolynomial lag ⟨p.base+q.base, atBase p _ (Nat.le_add_right _ _)⟩ volume)
    (timePolynomial lag ⟨p.base+q.base, atBase q _ (Nat.le_add_left _ _)⟩ volume) = _
  rw [timePolynomial_atBase lag p _ (Nat.le_add_right _ _) volume hv,
    timePolynomial_atBase lag q _ (Nat.le_add_left _ _) volume hv]

theorem timePolynomial_smul (lag : Nat) (c : Q') (p : Presentation) (volume : Nat) :
    timePolynomial lag (smul c p) volume = polySmul c (timePolynomial lag p volume) := rfl

theorem timePolynomial_one (lag volume : Nat) : timePolynomial lag one volume = polyOne := rfl

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.placed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.placed_bulkAtTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.placed_transport
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.placed_atBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.faceCharacter
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.shiftedExpression_placed
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.translate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.timePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.polynomial_bulkAtTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.polynomial_translate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.timePolynomial_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.timePolynomial_translate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.timePolynomial_atBase
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.timePolynomial_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.timePolynomial_mul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.timePolynomial_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeGeometry.timePolynomial_one
