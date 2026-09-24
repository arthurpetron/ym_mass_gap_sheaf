/-
# Exact represented inverse of I - T^2 on the SAME vacuum complement

The finite original even-orbit sums are now a represented norm-Cauchy family.
Their explicit limit and continuity of the actual residual identify an exact
preimage of each supplied vacuum-orthogonal source.  Applying the existing
vacuum-complement projection gives a centered preimage.  The already proved
absence of centered fixed vectors makes that preimage unique.

The representative-level construction descends by uniqueness to an actual
map on the original quotient; no representative is selected from a quotient.
The construction retains the fixed nome/width-dependent contraction rate.
It is a discrete-transfer inverse, not a continuous Hamiltonian resolvent,
spatial/spacing-uniform gap, continuum construction or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannCauchy
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointUnitComplement
  (completedTime_preserves_orthogonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointVacuumProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointRangeApproximation
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedCompleteness
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPresentedLimitLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointResidualPresentedLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "subV" => completedSub hw0 hw1 width
local notation "Z" => completedZero hw0 hw1 width

/-- The original source is a candidate limit of the residuals of the finite
orbit sums, by the previously proved actual residual-error modulus. -/
def sourceCandidate (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) :
    CandidateLimit hw0 hw1 width
      (mapResidual hw0 hw1 width (orbitNormCauchy hw0 hw1 width X hX)) where
  representative := X
  modulus := approximationModulus hw0 hw1 width X
  converges := by
    intro epsilon he p hp
    change RCle (completedDistSq hw0 hw1 width
        (Quotient.mk (D).completionSetoid
          (residualRepresentative hw0 hw1 width (evenOrbitRep hw0 hw1 width X p)))
        (Quotient.mk (D).completionSetoid X))
      (Quotient.mk crealSetoid (ofQ' epsilon))
    rw [residualRepresentative_pin, mk_evenOrbitRep, completedDistSq_symm]
    exact evenOrbitSum_error_small hw0 hw1 width X hX epsilon he p hp

/-- The actual residual of the constructed orbit limit is exactly the
original source, not merely a sequence of small residual errors. -/
theorem orbitLimit_residual (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) :
    residual hw0 hw1 width (orbitLimit hw0 hw1 width X hX) =
      Quotient.mk (D).completionSetoid X := by
  have hs := (sourceCandidate hw0 hw1 width X hX).eq_constructed_limit
    hw0 hw1 width (mapResidual hw0 hw1 width (orbitNormCauchy hw0 hw1 width X hX))
  exact (hs.trans (mapResidual_limit hw0 hw1 width (orbitNormCauchy hw0 hw1 width X hX))).symm

/-- A constructed, centered exact preimage; no quotient representative
selection is used in its definition. -/
def exactPreimage (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) : V :=
  center hw0 hw1 width (orbitLimit hw0 hw1 width X hX)

theorem exactPreimage_orthogonal (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) :
    B (exactPreimage hw0 hw1 width X hX) U = RCzero :=
  center_orthogonal hw0 hw1 width _

theorem exactPreimage_residual (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero) :
    residual hw0 hw1 width (exactPreimage hw0 hw1 width X hX) =
      Quotient.mk (D).completionSetoid X := by
  unfold exactPreimage residual
  rw [completedTime_center, ← center_sub]
  change center hw0 hw1 width (residual hw0 hw1 width (orbitLimit hw0 hw1 width X hX)) = _
  rw [orbitLimit_residual]
  exact (center_fixed_iff hw0 hw1 width _).mpr hX

private theorem rc_sub_exchange (a b c d : RC) :
    RCsub (RCsub a b) (RCsub c d) = RCsub (RCsub a c) (RCsub b d) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B'
  refine Quotient.inductionOn₂ c d ?_
  intro C D'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide)
      (fun | 0 => A.approx n | 1 => B'.approx n | 2 => C.approx n | _ => D'.approx n)))

theorem residual_sub (x y : V) :
    residual hw0 hw1 width (subV x y) =
      subV (residual hw0 hw1 width x) (residual hw0 hw1 width y) := by
  apply completed_eq_of_pairings hw0 hw1 width
  intro z
  simp only [residual, completedTime_sub, completedInner_sub_left]
  exact rc_sub_exchange _ _ _ _

/-- Injectivity is on the actual unit complement and uses the proved strict
fixed-width bound, not an assumed inverse law. -/
theorem residual_injective_on_complement (x y : V)
    (hx : B x U = RCzero) (hy : B y U = RCzero)
    (h : residual hw0 hw1 width x = residual hw0 hw1 width y) : x = y := by
  have hz : residual hw0 hw1 width (subV x y) = Z := by
    rw [residual_sub, h, completedSub_self]
  have horth : B (subV x y) U = RCzero := by
    rw [completedInner_sub_left, hx, hy]
    rfl
  have ht : T 2 (subV x y) = subV x y := by
    have hc := completedSub_add_cancel hw0 hw1 width (subV x y) (T 2 (subV x y))
    change completedAdd hw0 hw1 width (residual hw0 hw1 width (subV x y))
      (T 2 (subV x y)) = subV x y at hc
    rw [hz, completedZero_add] at hc
    exact hc
  have hd := fixed_orthogonal_eq_zero hw0 hw1 width (subV x y) horth ht
  have hc := completedSub_add_cancel hw0 hw1 width x y
  rw [hd, completedZero_add] at hc
  exact hc.symm

theorem exactPreimage_unique (X : (D).Cauchy)
    (hX : B (Quotient.mk (D).completionSetoid X) U = RCzero)
    (y : V) (hy : B y U = RCzero)
    (hres : residual hw0 hw1 width y = Quotient.mk (D).completionSetoid X) :
    y = exactPreimage hw0 hw1 width X hX :=
  residual_injective_on_complement hw0 hw1 width y _ hy
    (exactPreimage_orthogonal hw0 hw1 width X hX)
    (hres.trans (exactPreimage_residual hw0 hw1 width X hX).symm)

/-- The source is centered by the existing explicit representative operation,
so this producer accepts every representative, without an extra hypothesis. -/
def centeredPreimage (X : (D).Cauchy) : V :=
  exactPreimage hw0 hw1 width (centerCauchy hw0 hw1 width X) (by
    rw [← center_mk]
    exact center_orthogonal hw0 hw1 width _)

theorem centeredPreimage_orthogonal (X : (D).Cauchy) :
    B (centeredPreimage hw0 hw1 width X) U = RCzero :=
  exactPreimage_orthogonal hw0 hw1 width _ _

theorem centeredPreimage_residual (X : (D).Cauchy) :
    residual hw0 hw1 width (centeredPreimage hw0 hw1 width X) =
      center hw0 hw1 width (Quotient.mk (D).completionSetoid X) := by
  rw [center_mk]
  exact exactPreimage_residual hw0 hw1 width _ _

/-- Uniqueness supplies quotient coherence.  This descends a constructed
function; it never lifts a quotient point to a chosen representative. -/
def inverse : V → V :=
  Quotient.lift (centeredPreimage hw0 hw1 width) (fun X Y h =>
    residual_injective_on_complement hw0 hw1 width _ _
      (centeredPreimage_orthogonal hw0 hw1 width X)
      (centeredPreimage_orthogonal hw0 hw1 width Y)
      ((centeredPreimage_residual hw0 hw1 width X).trans
        ((congrArg (center hw0 hw1 width) (Quotient.sound h)).trans
          (centeredPreimage_residual hw0 hw1 width Y).symm)))

theorem inverse_orthogonal (x : V) : B (inverse hw0 hw1 width x) U = RCzero := by
  refine Quotient.inductionOn x ?_
  exact centeredPreimage_orthogonal hw0 hw1 width

/-- The quotient-level inverse solves the centered-source equation on every
actual state of the SAME completion. -/
theorem inverse_residual (x : V) :
    residual hw0 hw1 width (inverse hw0 hw1 width x) = center hw0 hw1 width x := by
  refine Quotient.inductionOn x ?_
  exact centeredPreimage_residual hw0 hw1 width

theorem inverse_right (x : V) (hx : B x U = RCzero) :
    residual hw0 hw1 width (inverse hw0 hw1 width x) = x :=
  (inverse_residual hw0 hw1 width x).trans ((center_fixed_iff hw0 hw1 width x).mpr hx)

theorem inverse_left (x : V) (hx : B x U = RCzero) :
    inverse hw0 hw1 width (residual hw0 hw1 width x) = x := by
  have hr : B (residual hw0 hw1 width x) U = RCzero := by
    rw [residual, completedInner_sub_left, hx,
      completedTime_preserves_orthogonal hw0 hw1 width 2 x hx]
    rfl
  exact residual_injective_on_complement hw0 hw1 width _ x
    (inverse_orthogonal hw0 hw1 width _) hx
    (inverse_right hw0 hw1 width _ hr)

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.sourceCandidate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.orbitLimit_residual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.exactPreimage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.exactPreimage_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.exactPreimage_residual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.residual_sub
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.residual_injective_on_complement
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.exactPreimage_unique
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.centeredPreimage
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.centeredPreimage_residual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.inverse
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.inverse_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.inverse_residual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.inverse_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointNeumannInverse.inverse_left
