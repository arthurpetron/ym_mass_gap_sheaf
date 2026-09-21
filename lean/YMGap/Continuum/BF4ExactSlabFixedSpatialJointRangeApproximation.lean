/-
# Constructive finite approximate preimages of I - T^2

Finite geometric sums of the ACTUAL joint-completed physical time map
telescope on this same carrier. On its unit complement, the proved strict
one-step squared-norm contraction controls the literal residual vector.
Each supplied Cauchy representative has a computed norm ceiling, hence a
computed epsilon-to-index modulus and an explicit approximate preimage.

No quotient representative is selected. No exact inverse, convergence of
the preimages, metric completeness, Hamiltonian, changing-spacing estimate,
or continuum Yang--Mills conclusion is asserted. The rate and modulus
retain their nome and spatial-width dependence, including the zero-rate case.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance
import YMGap.Continuum.PositiveContractionResidual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds (normCeiling normCeiling_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_nonnegative twoStepRate_lt_one)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_sub_self)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_sub_zero)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream (centeredStream)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance
  (faceExcitation faceExcitation_norm_floor)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "A" => completedAdd hw0 hw1 width
local notation "Z" => completedZero hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width
local notation "subV" => completedSub hw0 hw1 width
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

/-- Iterated strict squared-norm decay on the SAME completed unit complement. -/
theorem time_norm_decay (x : V) (hx : B x U = RCzero) : ∀ n : Nat,
    RCle (B (T n x) (T n x)) (RCscale (q^n) (B x x))
  | 0 => by
      rw [jointCompletedTime_zero, show q^0 = (1 : Q') from rfl, RCscale_one]
      exact RCle_refl _
  | n+1 => by
      have h := unitComplement_oneStep_norm_gap hw0 hw1 width
        (unitComplementTime hw0 hw1 width n ⟨x,hx⟩)
      change RCle (B (T 1 (T n x)) (T 1 (T n x))) (RCscale q (B (T n x) (T n x))) at h
      have h' := RCle_trans h (RCscale_mono (twoStepRate_nonnegative hw0 hw1 width)
        (time_norm_decay x hx n))
      rw [RCscale_RCscale, ← jointCompletedTime_add, Nat.add_comm 1 n] at h'
      exact h'

/-- The finite sum x + T^2 x + ... + T^(2*(n-1)) x; no infinite sum. -/
def evenOrbitSum (x : V) : Nat → V
  | 0 => Z
  | n+1 => A (evenOrbitSum x n) (T (2*n) x)

def residual (x : V) : V := subV x (T 2 x)

private theorem rc_telescope (a b c : RC) :
    RCadd (RCsub a b) (RCsub b c) = RCsub a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro X Y Z'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 1) (.neg (.var 2))))
      (.add (.var 0) (.neg (.var 2))) (by decide)
      (fun | 0 => X.approx n | 1 => Y.approx n | _ => Z'.approx n)))

private theorem rc_sub_add_exchange (a b c d : RC) :
    RCsub (RCadd a b) (RCadd c d) = RCadd (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  refine Quotient.inductionOn₂ c d ?_
  intro Z' W
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3)))) (by decide)
      (fun | 0 => X.approx n | 1 => Y.approx n | 2 => Z'.approx n | _ => W.approx n)))

private theorem rc_sub_sub_left (a b : RC) : RCsub a (RCsub a b) = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1))))) (.var 1) (by decide)
      (fun | 0 => X.approx n | _ => Y.approx n)))

/-- Equality of actual vectors, proved using the separating original pairing. -/
theorem evenOrbitSum_residual (x : V) (n : Nat) :
    residual hw0 hw1 width (evenOrbitSum hw0 hw1 width x n) = subV x (T (2*n) x) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro test
  induction n with
  | zero =>
      simp only [evenOrbitSum, residual, completedTime_zero_element,
        completedInner_sub_left, completedInner_zero_left, Nat.mul_zero,
        jointCompletedTime_zero, rc_sub_self]
  | succ n ih =>
      have ht : T 2 (T (2*n) x) = T (2*(n+1)) x := by
        rw [← jointCompletedTime_add]
        congr 1
        omega
      change B (subV (evenOrbitSum hw0 hw1 width x n)
        (T 2 (evenOrbitSum hw0 hw1 width x n))) test = _ at ih
      rw [completedInner_sub_left] at ih
      simp only [evenOrbitSum, residual, completedTime_additive, ht, completedInner_sub_left,
        completedInner_add_left]
      rw [rc_sub_add_exchange, ih, completedInner_sub_left]
      exact rc_telescope _ _ _

/-- The approximation error is literally the remaining orbit tail. -/
theorem evenOrbitSum_error (x : V) (n : Nat) :
    subV x (residual hw0 hw1 width (evenOrbitSum hw0 hw1 width x n)) = T (2*n) x := by
  rw [evenOrbitSum_residual]
  apply completed_eq_of_pairings hw0 hw1 width
  intro test
  rw [completedInner_sub_left, completedInner_sub_left]
  exact rc_sub_sub_left _ _

theorem evenOrbitSum_orthogonal (x : V) (hx : B x U = RCzero) : ∀ n : Nat,
    B (evenOrbitSum hw0 hw1 width x n) U = RCzero
  | 0 => completedInner_zero_left hw0 hw1 width U
  | n+1 => by
      rw [evenOrbitSum, completedInner_add_left, evenOrbitSum_orthogonal x hx n,
        completedTime_preserves_orthogonal hw0 hw1 width (2*n) x hx]
      rfl

theorem evenOrbitSum_error_bound (x : V) (hx : B x U = RCzero) (n : Nat) :
    let e := subV x (residual hw0 hw1 width (evenOrbitSum hw0 hw1 width x n))
    RCle (B e e) (RCscale (q^(2*n)) (B x x)) := by
  dsimp only
  rw [evenOrbitSum_error]
  exact time_norm_decay hw0 hw1 width x hx (2*n)

/-- Computed from supplied representative data, never quotient choice.
Using q instead of q^2 costs only a conservative index bound. -/
def approximationModulus (X : (D).Cauchy) (epsilon : Q') : Nat :=
  geometricCutoff q (normCeiling hw0 hw1 width X) epsilon

theorem evenOrbitSum_error_small (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : approximationModulus hw0 hw1 width X epsilon ≤ n) :
    let x := Quotient.mk (D).completionSetoid X
    let e := subV x (residual hw0 hw1 width (evenOrbitSum hw0 hw1 width x n))
    RCle (B e e) (Rq epsilon) := by
  let x : V := Quotient.mk (D).completionSetoid X
  have hcap : RCle (B x x) (Rq (normCeiling hw0 hw1 width X)) :=
    representativeInner_le_normCeiling hw0 hw1 width X
  have h := RCle_trans (evenOrbitSum_error_bound hw0 hw1 width x hX n)
    (RCscale_mono (Q'.pow_nonneg _ (twoStepRate_nonnegative hw0 hw1 width) (2*n)) hcap)
  have hs := geometric_bound (twoStepRate_nonnegative hw0 hw1 width)
    (twoStepRate_lt_one hw0 hw1 width) (normCeiling_nonnegative hw0 hw1 width X)
    he (2*n) (Nat.le_trans hn (by omega : n ≤ 2*n))
  exact RCle_trans h (leEv_of_le (ofQ'_le_ofQ' hs))

/-- An actual finite approximate preimage, with an explicitly computed length. -/
def approximatePreimage (X : (D).Cauchy) (epsilon : Q') : V :=
  evenOrbitSum hw0 hw1 width (Quotient.mk (D).completionSetoid X)
    (approximationModulus hw0 hw1 width X epsilon)

theorem approximatePreimage_error (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    let e := subV (Quotient.mk (D).completionSetoid X)
      (residual hw0 hw1 width (approximatePreimage hw0 hw1 width X epsilon))
    RCle (B e e) (Rq epsilon) :=
  evenOrbitSum_error_small hw0 hw1 width X hX epsilon he _ (Nat.le_refl _)

theorem approximatePreimage_orthogonal (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) (epsilon : Q') :
    B (approximatePreimage hw0 hw1 width X epsilon) U = RCzero :=
  evenOrbitSum_orthogonal hw0 hw1 width _ hX _

/-- Concrete consumer: the existing nonconstant plaquette's actual centering
stream supplies all approximation data, with no additional analytic input. -/
def plaquettePreimage (face : Z4Plaq) (hf : face ∈ spatialFaces width) (epsilon : Q') : V :=
  approximatePreimage hw0 hw1 width
    (centeredStream hw0 hw1 width (faceSpan width face hf)) epsilon

theorem plaquettePreimage_error (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (epsilon : Q') (he : (0 : Q') < epsilon) :
    let v := (faceExcitation hw0 hw1 width face hf).val
    let e := subV v (residual hw0 hw1 width (plaquettePreimage hw0 hw1 width face hf epsilon))
    RCle (B e e) (Rq epsilon) :=
  approximatePreimage_error hw0 hw1 width _
    (faceExcitation hw0 hw1 width face hf).property epsilon he

theorem plaquettePreimage_orthogonal (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (epsilon : Q') : B (plaquettePreimage hw0 hw1 width face hf epsilon) U = RCzero :=
  approximatePreimage_orthogonal hw0 hw1 width _
    (faceExcitation hw0 hw1 width face hf).property epsilon

/-- At a requested squared-error tolerance below the already proved
positive variance floor, the constructed approximate preimage cannot be zero. -/
theorem plaquettePreimage_ne_zero (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (epsilon : Q') (he : (0 : Q') < epsilon) (hsmall : epsilon < starRatio w) :
    plaquettePreimage hw0 hw1 width face hf epsilon ≠ Z := by
  intro hz
  let v : V := (faceExcitation hw0 hw1 width face hf).val
  have h := plaquettePreimage_error hw0 hw1 width face hf epsilon he
  change RCle (B (subV v (residual hw0 hw1 width
    (plaquettePreimage hw0 hw1 width face hf epsilon)))
    (subV v (residual hw0 hw1 width
    (plaquettePreimage hw0 hw1 width face hf epsilon)))) (Rq epsilon) at h
  rw [hz, residual, completedTime_zero_element, completedSub_self] at h
  have hc : subV v Z = v := by
    apply completed_eq_of_pairings hw0 hw1 width
    intro test
    rw [completedInner_sub_left, completedInner_zero_left, rc_sub_zero]
  rw [hc] at h
  have hbound := RCle_trans (faceExcitation_norm_floor hw0 hw1 width face hf) h
  have hle : starRatio w ≤ epsilon := by
    apply Q'.le_of_forall_pos_add
    intro delta hd
    obtain ⟨N, hN⟩ := hbound delta hd
    exact hN N (Nat.le_refl N)
  exact (Int.lt_irrefl _) (Q'.lt_of_le_of_lt hle hsmall)

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.time_norm_decay
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.evenOrbitSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.residual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.evenOrbitSum_residual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.evenOrbitSum_error
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.evenOrbitSum_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.evenOrbitSum_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.approximationModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.evenOrbitSum_error_small
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.approximatePreimage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.approximatePreimage_error
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.approximatePreimage_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.plaquettePreimage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.plaquettePreimage_error
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.plaquettePreimage_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation.plaquettePreimage_ne_zero
