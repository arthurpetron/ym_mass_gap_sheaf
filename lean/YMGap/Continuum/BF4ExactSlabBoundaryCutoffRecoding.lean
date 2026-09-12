/-
# The SAME finite boundary observable at every larger exact-law cutoff

A finite Boolean test on the actual lower face IDs extends an anchor
coefficient by zero to larger representation cutoffs. The larger Cartesian
enumeration filters EXACTLY to the anchor enumeration. The retained heat
coefficients agree, so both literal boundary polynomials are unchanged
coefficientwise, not merely after Haar integration.

The original signed bilinear therefore has a mixed-cutoff Haar form: both
boundary observables stay fixed at the anchor while only the actual interface
heat insertion still depends on the later cutoff. Positivity of this anchored
form follows from the proved original-form positivity. Stabilization of that
remaining interface, cutoff-limit completion, physical time and gap remain
separate obligations. No positive-law comparison or new analytic input.
-/

import YMGap.Continuum.BF4ExactSlabFiniteCutoffGNS
import YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence

namespace YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumMomentExpansion
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabWeightedFaceFactorization
open YMGap.Continuum.BF4ExactSlabObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem range_nodup : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ]
    refine List.nodup_append.mpr ⟨range_nodup n,
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro x hx y hy hxy
    have hy' := List.mem_singleton.mp hy
    subst y
    subst x
    exact Nat.lt_irrefl n (List.mem_range.mp hx)

theorem lowerFaceIds_nodup (half : Nat) : (centralLowerFaceIds half).Nodup := by
  have hfull : (slabPhysicalFaceEdges (centralExtent half)).Nodup := range_nodup _
  have hparts := (centralSlabFaceIdParts_perm half).symm.nodup hfull
  exact (List.nodup_append.mp (List.nodup_append.mp hparts).1).1

/-- A finite label test, not an attempted equality decision on functions. -/
def boundaryExtension (anchor half : Nat) (c : EdgeLabelling → Q') (state : EdgeLabelling) : Q' :=
  if labelWithinB anchor (centralLowerFaceIds half) state then c state else 0

theorem centralHalfStates_filter {anchor later : Nat} (hcut : anchor ≤ later) (half : Nat) :
    (centralHalfStates later half).filter (labelWithinB anchor (centralLowerFaceIds half)) =
      centralHalfStates anchor half :=
  boundedEdgeLabellings_filter_cutoff hcut _ (lowerFaceIds_nodup half)

theorem boundaryExtension_on_anchor (anchor half : Nat) (c : EdgeLabelling → Q')
    {state : EdgeLabelling} (hs : state ∈ centralHalfStates anchor half) :
    boundaryExtension anchor half c state = c state := by
  have hbound := (boundedEdgeLabellings_sound anchor _ state hs).1
  have ht := (labelWithinB_true_iff anchor _ state).mpr hbound
  simp only [boundaryExtension, ht, ↓reduceIte]

theorem boundaryExtension_outside (anchor half : Nat) (c : EdgeLabelling → Q')
    {state : EdgeLabelling} (hs : labelWithinB anchor (centralLowerFaceIds half) state = false) :
    boundaryExtension anchor half c state = 0 := by
  simp only [boundaryExtension, hs, Bool.false_eq_true, ↓reduceIte]

theorem anchorState_bounded (anchor half : Nat) {state : EdgeLabelling}
    (hs : state ∈ centralHalfStates anchor half) (id : Nat) : state id < anchor + 1 := by
  have hb := boundedEdgeLabellings_sound anchor _ state hs
  by_cases hi : id ∈ centralLowerFaceIds half
  · exact hb.1 id hi
  · rw [hb.2 id hi]
    omega

theorem weightedFacePolynomial_cutoff_eq (w : Q') {anchor later : Nat}
    (hcut : anchor ≤ later) (state : EdgeLabelling) (id : Nat)
    (hs : state id < anchor + 1) :
    weightedFacePolynomial w later state id = weightedFacePolynomial w anchor state id := by
  unfold weightedFacePolynomial
  rw [coeffAt_heatKernelPacket (by omega : state id < later + 1), coeffAt_heatKernelPacket hs]

private theorem fold_eq_on {A : Type} (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → f a = g a) →
      xs.foldr (fun a p => polyMul (f a) p) polyOne = xs.foldr (fun a p => polyMul (g a) p) polyOne
  | [], _ => rfl
  | a :: xs, h => by
    simp only [List.foldr_cons, h a List.mem_cons_self,
      fold_eq_on f g xs (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem lowerPolynomial_cutoff_eq (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    {state : EdgeLabelling} (hs : state ∈ centralHalfStates anchor 0) :
    lowerPolynomial w later state = lowerPolynomial w anchor state := by
  rw [lowerPolynomial_eq_fold, lowerPolynomial_eq_fold]
  exact fold_eq_on _ _ _ (fun id _ => weightedFacePolynomial_cutoff_eq w hcut state id
    (anchorState_bounded anchor 0 hs id))

theorem upperPolynomial_cutoff_eq (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    {state : EdgeLabelling} (hs : state ∈ centralHalfStates anchor 0) :
    upperPolynomial w later state = upperPolynomial w anchor state := by
  rw [upperPolynomial_eq_fold, upperPolynomial_eq_fold]
  exact fold_eq_on _ _ _ (fun id _ => weightedFacePolynomial_cutoff_eq w hcut _ id
    (anchorState_bounded anchor 0 hs _))

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

/-- The ORIGINAL lower polynomial, including its heat dressing, is fixed. -/
theorem lowerObservable_extension (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (c : EdgeLabelling → Q') :
    RatPolyCoeffEqv (lowerObservable w later (boundaryExtension anchor 0 c)) (lowerObservable w anchor c) := by
  have h := sum_mask (labelWithinB anchor (centralLowerFaceIds 0)) c
    (lowerPolynomial w later) (centralHalfStates later 0)
  rw [centralHalfStates_filter hcut 0] at h
  have he := sum_eq_on (fun state => polySmul (c state) (lowerPolynomial w later state))
    (fun state => polySmul (c state) (lowerPolynomial w anchor state)) (centralHalfStates anchor 0)
    (fun state hs => congrArg (polySmul (c state)) (lowerPolynomial_cutoff_eq w hcut hs))
  rw [he] at h
  exact h

/-- The literal reflected-upper polynomial is fixed by the SAME recoding. -/
theorem upperObservable_extension (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (c : EdgeLabelling → Q') :
    RatPolyCoeffEqv (upperObservable w later (boundaryExtension anchor 0 c)) (upperObservable w anchor c) := by
  have h := sum_mask (labelWithinB anchor (centralLowerFaceIds 0)) c
    (upperPolynomial w later) (centralHalfStates later 0)
  rw [centralHalfStates_filter hcut 0] at h
  have he := sum_eq_on (fun state => polySmul (c state) (upperPolynomial w later state))
    (fun state => polySmul (c state) (upperPolynomial w anchor state)) (centralHalfStates anchor 0)
    (fun state hs => congrArg (polySmul (c state)) (upperPolynomial_cutoff_eq w hcut hs))
  rw [he] at h
  exact h

/-- Only the ORIGINAL interface insertion still varies with later cutoff. -/
def anchoredIntegrand (w : Q') (anchor later : Nat) (a b : EdgeLabelling → Q') : RatPoly :=
  polyMul (lowerObservable w anchor a) (polyMul (interfaceHeatInsertion w later) (upperObservable w anchor b))

theorem observableIntegrand_extension (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (a b : EdgeLabelling → Q') :
    RatPolyCoeffEqv (observableIntegrand w later (boundaryExtension anchor 0 a) (boundaryExtension anchor 0 b))
      (anchoredIntegrand w anchor later a b) :=
  (lowerObservable_extension w hcut a).mul
    ((upperObservable_extension w hcut b).mul_left (interfaceHeatInsertion w later))

private theorem haar_weighted (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks p = ratWeightedSum (quaternionHaarMono blocks) p
  | [] => rfl
  | _ :: p => by simp only [quaternionHaar, ratWeightedSum, haar_weighted blocks p]

theorem exact_bilinear_anchored (w : Q') {anchor later : Nat} (hcut : anchor ≤ later)
    (a b : EdgeLabelling → Q') :
    finiteJointBilinear (centralHalfStates later 0) (boundaryExtension anchor 0 a) (boundaryExtension anchor 0 b)
      (exactCorrectedSlabReflectedKernel w later 0) ≈ quaternionHaar 116 (anchoredIntegrand w anchor later a b) := by
  refine Q'.eqv_trans _ _ _ (exact_bilinear_eq_haar w later _ _) ?_
  rw [haar_weighted, haar_weighted]
  exact observableIntegrand_extension w hcut a b (quaternionHaarMono 116)

theorem anchored_quadratic_nonnegative {w : Q'} (hw : (0 : Q') ≤ w)
    {anchor later : Nat} (hcut : anchor ≤ later) (c : EdgeLabelling → Q') :
    (0 : Q') ≤ quaternionHaar 116 (anchoredIntegrand w anchor later c c) :=
  Q'.le_trans' _ _ _ (exact_quadratic_nonnegative hw later (boundaryExtension anchor 0 c))
    (Q'.le_of_eqv (exact_bilinear_anchored w hcut c c))

end YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding

#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.lowerFaceIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.boundaryExtension
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.centralHalfStates_filter
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.boundaryExtension_on_anchor
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.boundaryExtension_outside
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.anchorState_bounded
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.weightedFacePolynomial_cutoff_eq
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.lowerPolynomial_cutoff_eq
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.upperPolynomial_cutoff_eq
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.lowerObservable_extension
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.upperObservable_extension
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.anchoredIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.observableIntegrand_extension
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.exact_bilinear_anchored
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryCutoffRecoding.anchored_quadratic_nonnegative
