/-
# All-input bounded-degree approximation of the original conditional sweep

One computed inverse-iteration count works for EVERY supported polynomial,
with error relative to its original full-action squared norm. The output
degree in every original link is bounded independently of input degree.

The actual singleton block/star identity pins the approximated operator to
the existing physical-link conditional sweep. It is conditional L2 dynamics,
not physical OS time. No finite Gram certificate, strict gap, useful
volume-uniform error budget, cutoff-uniform degree or scaling theorem is
asserted. This is the omitted-input control prerequisite for such a finite
certificate, not an arbitrary low-degree principal truncation.
-/

import YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree
import YMGap.Continuum.BF4ExactSlabBlockConditionalApproximationError
import YMGap.Continuum.BF4ExactSlabBlockSingletonProjection
import YMGap.Continuum.GNSFiniteSweepApproximation

namespace YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSFiniteSweepApproximation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabPolynomialSweepDegree
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximationError
open YMGap.Continuum.SU2QuaternionBlockDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

private theorem singleton_valid (i : PhysicalLink extent) :
    ∀ j, j ∈ [i.val] → j ∈ boundaryCompleteSlabLinks extent := by
  intro j hj
  have he : j = i.val := List.mem_singleton.mp hj
  subst j
  exact i.property

private theorem scale_embed_norm (delta : Q') (p : (F).V) :
    RCscale delta (normSq (embedV F p)) =
      Quotient.mk crealSetoid (ofQ' (delta * (F).B p p)) := by
  change RCscale delta ((F).cinnerCompl (embedV F p) (embedV F p)) = _
  have h : (F).cinnerCompl (embedV F p) (embedV F p) =
      Quotient.mk crealSetoid (ofQ' ((F).B p p)) := (F).cinnerCompl_embed p p
  rw [h]
  exact Quotient.sound (CReal.Equiv_of_approx_eq (fun _ => rfl))

/-- The PURE polynomial update approximates the actual original star
projection, with one iteration count for every input and selected link. -/
theorem polynomialUpdate_error (i : PhysicalLink extent) (delta : Q')
    (hdelta : (0 : Q') < delta) (n : Nat)
    (hn : projectionCutoff w 1 delta ≤ n) (p : (F).V) :
    RCle (GNSTransferMetric.distanceSq F
      ((P).op i (embedV F p))
      (embedV F (polynomialUpdate hw0 hw1 K extent hK i n p)))
      (RCscale delta (normSq (embedV F p))) := by
  have h := conditionalProjection_error_tolerance hw0 hw1 K extent hK
    [i.val] (singleton_valid extent i) p delta hdelta n hn
  rw [BF4ExactSlabBlockSingletonProjection.conditionalProjection_singleton
    hw0 hw1 K extent hK i.val i.property] at h
  rw [scale_embed_norm hw0 hw1 K extent hK delta p]
  exact h

private theorem approximateSweep_pin (n : Nat) (xs : List (PhysicalLink extent))
    (p : (F).V) :
    approximateSweep (fun i => polynomialUpdate hw0 hw1 K extent hK i n) xs p =
      embedV F (polynomialSweep hw0 hw1 K extent hK n xs p) := by
  induction xs generalizing p with
  | nil => rfl
  | cons i rest ih => exact ih (polynomialUpdate hw0 hw1 K extent hK i n p)

/-- Explicit length-only propagation of the original singleton error.
All intermediate polynomials may have arbitrary degree. -/
theorem polynomialSweep_error (xs : List (PhysicalLink extent)) (delta : Q')
    (hdelta : (0 : Q') < delta) (hdelta1 : delta ≤ 1) (n : Nat)
    (hn : projectionCutoff w 1 delta ≤ n) (p : (F).V) :
    RCle (GNSTransferMetric.distanceSq F
      ((P).sweep xs (embedV F p))
      (embedV F (polynomialSweep hw0 hw1 K extent hK n xs p)))
      (RCscale (delta * errorCoefficient xs.length) (normSq (embedV F p))) := by
  have h := GNSFiniteSweepApproximation.Family.sweep_approximation_uniform P
    (fun i => polynomialUpdate hw0 hw1 K extent hK i n) delta
    (Q'.le_of_lt hdelta) hdelta1
    (fun i p => polynomialUpdate_error hw0 hw1 K extent hK i delta hdelta n hn p)
    xs p
  rw [approximateSweep_pin hw0 hw1 K extent hK n xs p] at h
  exact h

/-- A returned iteration count, independent of input polynomial and heat
cutoff. Its schedule-length dependence is explicit and may be expensive. -/
def sweepCutoff (w : Q') (extent : Nat) (epsilon : Q') : Nat :=
  projectionCutoff w 1 (stepTolerance epsilon (schedule extent).length)

/-- Requested relative squared-error tolerance for ALL supported inputs
with the SAME iteration count. -/
theorem physicalSweep_approximation_error (epsilon : Q')
    (hepsilon : (0 : Q') < epsilon) (n : Nat)
    (hn : sweepCutoff w extent epsilon ≤ n) (p : (F).V) :
    RCle (GNSTransferMetric.distanceSq F
      ((P).sweep (schedule extent) (embedV F p))
      (embedV F (polynomialSweep hw0 hw1 K extent hK n (schedule extent) p)))
      (RCscale epsilon (normSq (embedV F p))) := by
  let delta := stepTolerance epsilon (schedule extent).length
  have h := polynomialSweep_error hw0 hw1 K extent hK (schedule extent) delta
    (stepTolerance_pos hepsilon _)
    (stepTolerance_le_one epsilon (Q'.le_of_lt hepsilon) _) n hn p
  exact RCle_trans h (RCscale_scalar_mono
    (stepTolerance_coefficient_le epsilon (Q'.le_of_lt hepsilon) _)
    ((F).cinner_self_nonneg (embedV F p)))

/-- The actual polynomial output at the returned common tolerance cutoff. -/
def approximation (epsilon : Q') (p : (F).V) : (F).V :=
  polynomialSweep hw0 hw1 K extent hK (sweepCutoff w extent epsilon)
    (schedule extent) p

theorem approximation_error (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (p : (F).V) :
    RCle (GNSTransferMetric.distanceSq F
      ((P).sweep (schedule extent) (embedV F p))
      (embedV F (approximation hw0 hw1 K extent hK epsilon p)))
      (RCscale epsilon (normSq (embedV F p))) :=
  physicalSweep_approximation_error hw0 hw1 K extent hK epsilon hepsilon
    (sweepCutoff w extent epsilon) (Nat.le_refl _) p

/-- Explicit output-degree budget. Unlike a principal input truncation,
this bound is valid for every original supported polynomial input. -/
def degreeBudget (w : Q') (K extent : Nat) (epsilon : Q') (block : Nat) : Nat :=
  sweepDegreeBudget w K extent block (sweepCutoff w extent epsilon) (schedule extent)

theorem approximation_degree (epsilon : Q') (block : Nat)
    (hb : block < (boundaryCompleteSlabLinks extent).length) (p : (F).V) :
    DegreeLE block (degreeBudget w K extent epsilon block)
      (approximation hw0 hw1 K extent hK epsilon p).val :=
  physicalSweep_degree_bound hw0 hw1 K extent hK (sweepCutoff w extent epsilon)
    block hb p

end YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation

#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation.polynomialUpdate_error
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation.polynomialSweep_error
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation.sweepCutoff
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation.physicalSweep_approximation_error
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation.approximation
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation.approximation_error
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation.degreeBudget
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialSweepApproximation.approximation_degree
