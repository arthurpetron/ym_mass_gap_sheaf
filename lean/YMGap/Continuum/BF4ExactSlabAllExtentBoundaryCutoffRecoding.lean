/-
# The same boundary observables at all larger cutoffs and odd extents

The existing Boolean zero extension and actual label-carrier filtering
are used without change. All retained original heat weights agree, so the
lower and reflected upper polynomials stay fixed at their anchor cutoff.
The full ORIGINAL signed bilinear is consequently pinned to a mixed-cutoff
Haar form on the same slab carrier. Only its interface still varies.

No compatibility between slabs, time evolution, stationary vacuum, strict
gap, or thermodynamic/continuum claim follows from this recoding alone.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
import YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding

namespace YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentReflectionPositivity
open YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem weightedFacePolynomial_cutoff_eq (w : Q') {anchor later : Nat}
    (hcut : anchor ≤ later) (extent : Nat) (state : EdgeLabelling) (id : Nat)
    (hs : state id < anchor + 1) :
    weightedFacePolynomial w later extent state id = weightedFacePolynomial w anchor extent state id := by
  unfold weightedFacePolynomial
  rw [coeffAt_heatKernelPacket (by omega : state id < later + 1), coeffAt_heatKernelPacket hs]

theorem lowerPolynomial_cutoff_eq (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (half : Nat) {state : EdgeLabelling} (hs : state ∈ centralHalfStates anchor half) :
    lowerPolynomial w later half state = lowerPolynomial w anchor half state :=
  polynomialProduct_congr _ _ _ (fun id _ => weightedFacePolynomial_cutoff_eq w hcut _ state id
    (anchorState_bounded anchor half hs id))

theorem upperPolynomial_cutoff_eq (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (half : Nat) {state : EdgeLabelling} (hs : state ∈ centralHalfStates anchor half) :
    upperPolynomial w later half state = upperPolynomial w anchor half state :=
  polynomialProduct_congr _ _ _ (fun id _ => weightedFacePolynomial_cutoff_eq w hcut _ _ id
    (anchorState_bounded anchor half hs _))

private theorem sum_mask {A : Type} (test : A → Bool) (c : A → Q') (f : A → RatPoly) :
    ∀ xs : List A, RatPolyCoeffEqv
      (finitePolySum (fun a => polySmul (if test a then c a else 0) (f a)) xs)
      (finitePolySum (fun a => polySmul (c a) (f a)) (xs.filter test))
  | [] => RatPolyCoeffEqv.refl _
  | a :: xs => by
    cases ht : test a with
    | false =>
      simp only [finitePolySum, List.filter_cons, ht, Bool.false_eq_true, ↓reduceIte]
      exact ((RatPolyCoeffEqv.zero_smul _).add (sum_mask test c f xs)).trans (RatPolyCoeffEqv.zero_add _)
    | true =>
      simp only [finitePolySum, List.filter_cons, ht, ↓reduceIte]
      exact (RatPolyCoeffEqv.refl _).add (sum_mask test c f xs)

private theorem sum_eq_on {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → f a = g a) → finitePolySum f xs = finitePolySum g xs
  | [], _ => rfl
  | a :: xs, h => by
    simp only [finitePolySum, h a List.mem_cons_self,
      sum_eq_on f g xs (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- Every heat-dressed lower observable is preserved on the original carrier. -/
theorem lowerObservable_extension (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (half : Nat) (c : EdgeLabelling → Q') :
    RatPolyCoeffEqv (lowerObservable w later half (boundaryExtension anchor half c))
      (lowerObservable w anchor half c) := by
  have h := sum_mask (labelWithinB anchor (centralLowerFaceIds half)) c
    (lowerPolynomial w later half) (centralHalfStates later half)
  rw [centralHalfStates_filter hcut half] at h
  have he := sum_eq_on (fun state => polySmul (c state) (lowerPolynomial w later half state))
    (fun state => polySmul (c state) (lowerPolynomial w anchor half state)) (centralHalfStates anchor half)
    (fun state hs => congrArg (polySmul (c state)) (lowerPolynomial_cutoff_eq w hcut half hs))
  rw [he] at h
  exact h

/-- The SAME zero extension preserves the reflected upper observable. -/
theorem upperObservable_extension (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (half : Nat) (c : EdgeLabelling → Q') :
    RatPolyCoeffEqv (upperObservable w later half (boundaryExtension anchor half c))
      (upperObservable w anchor half c) := by
  have h := sum_mask (labelWithinB anchor (centralLowerFaceIds half)) c
    (upperPolynomial w later half) (centralHalfStates later half)
  rw [centralHalfStates_filter hcut half] at h
  have he := sum_eq_on (fun state => polySmul (c state) (upperPolynomial w later half state))
    (fun state => polySmul (c state) (upperPolynomial w anchor half state)) (centralHalfStates anchor half)
    (fun state hs => congrArg (polySmul (c state)) (upperPolynomial_cutoff_eq w hcut half hs))
  rw [he] at h
  exact h

def anchoredIntegrand (w : Q') (anchor later half : Nat) (a b : EdgeLabelling → Q') : RatPoly :=
  polyMul (lowerObservable w anchor half a)
    (polyMul (interfaceHeatInsertion w later half) (upperObservable w anchor half b))

theorem observableIntegrand_extension (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (half : Nat) (a b : EdgeLabelling → Q') :
    RatPolyCoeffEqv (observableIntegrand w later half (boundaryExtension anchor half a) (boundaryExtension anchor half b))
      (anchoredIntegrand w anchor later half a b) :=
  (lowerObservable_extension w hcut half a).mul
    ((upperObservable_extension w hcut half b).mul_left (interfaceHeatInsertion w later half))

/-- Full original signed kernel, same supported boundary observables and slab. -/
theorem exact_bilinear_anchored (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (half : Nat) (a b : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates later half) (boundaryExtension anchor half a) (boundaryExtension anchor half b)
      (exactCorrectedSlabReflectedKernel w later half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (anchoredIntegrand w anchor later half a b) :=
  Q'.eqv_trans _ _ _ (exact_bilinear_eq_haar w later half _ _)
    (haar_of_coeff_eqv _ (observableIntegrand_extension w hcut half a b))

theorem anchored_quadratic_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    {anchor later : Nat} (hcut : anchor ≤ later) (half : Nat) (c : EdgeLabelling → Q') :
    (0 : Q') ≤ quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
      (anchoredIntegrand w anchor later half c c) :=
  Q'.le_trans' _ _ _ (exact_quadratic_nonnegative hw later half (boundaryExtension anchor half c))
    (Q'.le_of_eqv (exact_bilinear_anchored w hcut half c c))

end YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.weightedFacePolynomial_cutoff_eq
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.lowerPolynomial_cutoff_eq
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.upperPolynomial_cutoff_eq
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.lowerObservable_extension
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.upperObservable_extension
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.anchoredIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.observableIntegrand_extension
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.exact_bilinear_anchored
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding.anchored_quadratic_nonnegative
