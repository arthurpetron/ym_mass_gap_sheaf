/-
# Actual conditional variance versus explicit polynomial energy

For EVERY supported original polynomial p, its full-law conditional residual
equals the residual of p minus its computed free-link average. The local
six-face comparison consequently bounds the actual conditional variance
above and below by the star-deleted squared norm of that explicit polynomial.
The original complementary action is retained separately for every link.

Summing gives an inverse-free finite polynomial producer for the SAME
completed Dirichlet energy. No global variance lower bound is assumed or
proved. In particular the one-link bounds do not tensorize themselves,
and no neighboring preservation of the free-centered sector is asserted.
-/

import YMGap.Continuum.BF4ExactSlabStarLocalInfluence
import YMGap.Continuum.BF4ExactSlabConditionalSweepEnergy

namespace YMGap.Continuum.BF4ExactSlabPolynomialDirichletComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabStarCompletedInverse
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarFreeCentering
open YMGap.Continuum.BF4ExactSlabStarConditionalProjection
open YMGap.Continuum.BF4ExactSlabStarLocalInfluence
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem scale_rat (c q : Q') : RCscale c (rat q) = rat (c*q) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem add_rat (a b : Q') : RCadd (rat a) (rat b) = rat (a+b) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (CReal.sub_self_eqv_zero A)

private theorem embedded_norm (D : GNSData) (p : D.V) :
    normSq (embedV D p) = rat (D.B p p) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem embed_sub (D : GNSData) (p q : D.V) :
    embedV D (D.sub p q) = D.cSub (embedV D p) (embedV D q) := by
  apply GNSDenseCompletionLaws.eq_of_dense_pairings
  intro z
  rw [D.cinnerCompl_cSub_left]
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _ (D.B_add_left p (D.neg q) z)
      (Q'.add_eqv_congr_left _ _ _ (D.B_neg_left q z)))

private theorem residual_sub_fixed {D : GNSData} {I : Type} (P : Family D I)
    (i : I) (x z : GNSCompletionSpace D) (hz : P.op i z = z) :
    P.residual i (D.cSub x z) = P.residual i x := by
  have hrz : P.residual i z = embedV D D.zero := by
    apply GNSDenseCompletionLaws.eq_of_pairings_equal
    intro y
    unfold Family.residual
    rw [hz, D.cinnerCompl_cSub_left, sub_self, D.cinnerCompl_embedZero_left]
  apply GNSDenseCompletionLaws.eq_of_pairings_equal
  intro y
  rw [P.residual_adjoint, D.cinnerCompl_cSub_left,
    ← P.residual_adjoint i z y, hrz, D.cinnerCompl_embedZero_left,
    sub_zero, P.residual_adjoint]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK

section OneLink

variable (i : PhysicalLink extent)

local notation "D" => deletedData hw0 hw1 K extent hK i.val i.property
local notation "G" => exteriorData hw0 hw1 K extent hK i.val i.property
local notation "J" => probeMap hw0 hw1 K extent hK i.val i.property
local notation "A" => freeAverage hw0 hw1 K extent hK i.val i.property
local notation "fr" => freeResidual hw0 hw1 K extent hK i.val i.property

/-- Pure finite Haar/polynomial arithmetic: no conditional inverse appears. -/
def polynomialEnergyAt (p : (F).V) : Q' := (D).B (fr p) (fr p)

theorem polynomialEnergyAt_nonnegative (p : (F).V) :
    (0 : Q') ≤ polynomialEnergyAt hw0 hw1 K extent hK i p :=
  (D).self_nonneg (fr p)

/-- The original conditional projection fixes the lifted computed average;
subtracting it does not change the actual original-law residual. -/
theorem residual_free_pin (p : (F).V) :
    (P).residual i (embedV F (fr p)) = (P).residual i (embedV F p) := by
  have hfix : (P).op i (embedV F (J (A p))) = embedV F (J (A p)) := by
    change conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F (J (A p))) = _
    rw [← probeCompletion_embed hw0 hw1 K extent hK i.val i.property]
    exact conditionalProjection_fix_exterior hw0 hw1 K extent hK i.val i.property _
  change (P).residual i (embedV F ((F).sub p (J (A p)))) = _
  rw [embed_sub]
  exact residual_sub_fixed P i _ _ hfix

private theorem free_residual_floor (p : (F).V) :
    RCle (rat (lowerFactor w * polynomialEnergyAt hw0 hw1 K extent hK i p))
      (normSq ((P).residual i (embedV F (fr p)))) := by
  change RCle _ ((F).cinnerCompl
    ((F).cSub (embedV F (fr p))
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F (fr p))))
    ((F).cSub (embedV F (fr p))
      (conditionalProjection hw0 hw1 K extent hK i.val i.property (embedV F (fr p)))))
  rw [conditionalProjection_embed]
  change leEv (ofQ' (lowerFactor w * (D).B (fr p) (fr p)))
    ((F).cinnerRep
      ((F).subCauchy (constCauchy F (fr p))
        (probeCauchy hw0 hw1 K extent hK i.val i.property
          (inverseCauchy hw0 hw1 K extent hK i.val i.property
            (numeratorMap hw0 hw1 K extent hK i.val i.property (fr p)))))
      ((F).subCauchy (constCauchy F (fr p))
        (probeCauchy hw0 hw1 K extent hK i.val i.property
          (inverseCauchy hw0 hw1 K extent hK i.val i.property
            (numeratorMap hw0 hw1 K extent hK i.val i.property (fr p))))))
  apply leEv_ofQ'_of_approx_ge
  intro n
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (deleted_sub_norm_lower hw0 hw1 K extent hK i.val i.property (fr p) _
        (freeResidual_pair_zero hw0 hw1 K extent hK i.val i.property p _))
      (Q'.le_of_lt (lowerFactor_positive hw0 hw1)))
    (actual_deleted_form_bounds hw0 hw1 K extent hK i.val i.property _).1

/-- Two-sided conditional-variance comparison for EVERY original polynomial.
No free-centering or global-centering hypothesis is imposed on p. -/
theorem conditional_variance_comparison (p : (F).V) :
    RCle (RCscale (lowerFactor w) (rat (polynomialEnergyAt hw0 hw1 K extent hK i p)))
      (normSq ((P).residual i (embedV F p))) ∧
    RCle (normSq ((P).residual i (embedV F p)))
      (RCscale (upperFactor w) (rat (polynomialEnergyAt hw0 hw1 K extent hK i p))) := by
  constructor
  · rw [scale_rat, ← residual_free_pin hw0 hw1 K extent hK i p]
    exact free_residual_floor hw0 hw1 K extent hK i p
  · rw [scale_rat, ← residual_free_pin hw0 hw1 K extent hK i p]
    refine RCle_trans ((P).residual_norm i (embedV F (fr p))) ?_
    rw [embedded_norm]
    exact leEv_ofQ'_of_approx_ge (fun _ =>
      (actual_deleted_form_bounds hw0 hw1 K extent hK i.val i.property (fr p)).2)

end OneLink

/-- Explicit rational energy with the actual star-deleted background at
each link. This does NOT replace all backgrounds by one product-Haar law. -/
def polynomialEnergy (p : (F).V) : List (PhysicalLink extent) → Q'
  | [] => 0
  | i :: rest => polynomialEnergyAt hw0 hw1 K extent hK i p + polynomialEnergy p rest

private theorem sumOn_polynomialEnergy (p : (F).V) (links : List (PhysicalLink extent)) :
    sumOn links (fun i => rat (polynomialEnergyAt hw0 hw1 K extent hK i p)) =
      rat (polynomialEnergy hw0 hw1 K extent hK p links) := by
  induction links with
  | nil => rfl
  | cons i rest ih => simp only [sumOn, polynomialEnergy, ih, add_rat]

/-- The inverse-free finite polynomial energy controls the SAME completed
Dirichlet sum on dense inputs in both directions, with only local constants. -/
theorem dirichlet_comparison (p : (F).V) (links : List (PhysicalLink extent)) :
    RCle (RCscale (lowerFactor w) (rat (polynomialEnergy hw0 hw1 K extent hK p links)))
      ((P).finalEnergy links (embedV F p)) ∧
    RCle ((P).finalEnergy links (embedV F p))
      (RCscale (upperFactor w) (rat (polynomialEnergy hw0 hw1 K extent hK p links))) := by
  have hlo := sumOn_mono links _ _ (fun i _ =>
    (conditional_variance_comparison hw0 hw1 K extent hK i p).1)
  have hhi := sumOn_mono links _ _ (fun i _ =>
    (conditional_variance_comparison hw0 hw1 K extent hK i p).2)
  rw [sumOn_scale, sumOn_polynomialEnergy] at hlo hhi
  exact ⟨hlo, hhi⟩

#print axioms polynomialEnergyAt
#print axioms polynomialEnergyAt_nonnegative
#print axioms residual_free_pin
#print axioms conditional_variance_comparison
#print axioms polynomialEnergy
#print axioms dirichlet_comparison

end YMGap.Continuum.BF4ExactSlabPolynomialDirichletComparison
