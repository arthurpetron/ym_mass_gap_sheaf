/-
# Constructed finite-volume coercivity for the ORIGINAL full action

The free product-Haar variance inequality and the actual conditional
residual floor give m*||p||^2 <= M*sum_i ||R_i p||^2 for every original-law
centered polynomial. Here m=headFloor^faceCount and M=prefixCap^faceCount.
Both are constructed, positive, and independent of the late heat cutoff.
They depend on nome and extent. No scaling-uniform bound or OS-time gap
is claimed; the operator is the original conditional-update family.
-/

import YMGap.Continuum.BF4ExactSlabHaarVarianceComparison
import YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor
import YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex
import YMGap.Continuum.GNSProjectionSweepEnergyOrder

namespace YMGap.Continuum.BF4ExactSlabFiniteVolumeCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabHaarVarianceComparison
open YMGap.Continuum.BF4ExactSlabStarHaarResidualFloor
open YMGap.Continuum.BF4ExactSlabPhysicalScheduleIndex
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarEfronStein
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem scale_rat (c q : Q') : RCscale c (rat q) = rat (c*q) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem add_rat (a b : Q') : RCadd (rat a) (rat b) = rat (a+b) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem embedded_norm (D : GNSData) (p : D.V) :
    normSq (embedV D p) = rat (D.B p p) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem sumOn_map {A B : Type} (xs : List A) (f : A → B) (g : B → RC) :
    sumOn xs (fun i => g (f i)) = sumOn (xs.map f) g := by
  induction xs with
  | nil => rfl
  | cons i rest ih => simp only [sumOn, List.map_cons, ih]

private theorem sumOn_rat {A : Type} (xs : List A) (f : A → Q') :
    sumOn xs (fun i => rat (f i)) = rat (qListSum (xs.map f)) := by
  induction xs with
  | nil => rfl
  | cons i rest ih => simp only [sumOn, List.map_cons, qListSum, ih, add_rat]

/-- All original faces contribute to this explicit floor. -/
def volumeFloor (w : Q') (extent : Nat) : Q' :=
  (headFloor w)^(slabPhysicalFaceEdges extent).length

theorem volumeFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : (0 : Q') < volumeFloor w extent :=
  HKPos.pow_pos (headFloor_positive hw0 hw1) _

theorem volumeCap_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : (0 : Q') < volumeCap w extent := by
  have h := majorant_prefix_bound hw0 hw1 1
  change (1 : Q') ≤ prefixCap w at h
  exact HKPos.pow_pos (Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) h) _

/-- A positive rational coercivity coefficient, with its volume cost
exposed and no cutoff argument or assumed analytic estimate. -/
def coercivity {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : Q' :=
  Q'.recipPos (volumeCap w extent) (volumeCap_positive hw0 hw1 extent) *
    volumeFloor w extent

theorem coercivity_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) : (0 : Q') < coercivity hw0 hw1 extent :=
  Q'.mul_pos (Q'.recipPos_pos _ _) (volumeFloor_positive hw0 hw1 extent)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "U" => (Subtype.mk polyOne
  (supported_one (List.length (boundaryCompleteSlabLinks extent))))

private theorem free_energy_schedule (p : (F).V) :
    sumOn (schedule extent) (fun i => rat (haarSquare
      (boundaryCompleteSlabLinks extent).length
      (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val))) =
    rat (fluctuationEnergy (boundaryCompleteSlabLinks extent).length p.val) := by
  rw [sumOn_map (schedule extent)
    (fun i => (boundaryCompleteSlabLinks extent).idxOf i.val)
    (fun b => rat (haarSquare (boundaryCompleteSlabLinks extent).length
      (fluctuation b p.val)))]
  rw [sumOn_perm _ (physical_schedule_index_perm extent)]
  exact sumOn_rat _ _

/-- Sum the genuine completed conditional residual floors, with the
schedule-index permutation proving that every coordinate occurs once. -/
theorem free_energy_le_original_dirichlet (p : (F).V) :
    RCle (RCscale (volumeFloor w extent)
      (rat (fluctuationEnergy (boundaryCompleteSlabLinks extent).length p.val)))
      ((P).finalEnergy (schedule extent) (embedV F p)) := by
  have h := sumOn_mono (schedule extent)
    (fun i => RCscale (volumeFloor w extent) (rat (haarSquare
      (boundaryCompleteSlabLinks extent).length
      (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val))))
    (fun i => normSq ((P).residual i (embedV F p))) (fun i _ => by
      dsimp only
      rw [scale_rat]
      exact conditional_residual_inplace_floor hw0 hw1 K extent hK i p)
  rw [sumOn_scale, free_energy_schedule] at h
  exact h

/-- Division-free ORIGINAL dense centered coercivity, constructed from
the original action rather than supplied as a hypothesis. -/
theorem dense_centered_coercivity_mul (p : (F).V) (hcenter : (F).B p U ≈ 0) :
    RCle (RCscale (volumeFloor w extent) (normSq (embedV F p)))
      (RCscale (volumeCap w extent) ((P).finalEnergy (schedule extent) (embedV F p))) := by
  have hv : RCle (rat ((F).B p p))
      (RCscale (volumeCap w extent)
        (rat (fluctuationEnergy (boundaryCompleteSlabLinks extent).length p.val))) := by
    rw [scale_rat]
    exact leEv_ofQ'_of_approx_ge (fun _ =>
      centered_norm_le_free_energy hw0 hw1 K extent hK p hcenter)
  have hm := RCscale_mono (Q'.le_of_lt (volumeFloor_positive hw0 hw1 extent)) hv
  have he := RCscale_mono (volumeCap_nonnegative hw0 extent)
    (free_energy_le_original_dirichlet hw0 hw1 K extent hK p)
  rw [RCscale_RCscale] at hm he
  have hs : RCscale (volumeFloor w extent * volumeCap w extent)
      (rat (fluctuationEnergy (boundaryCompleteSlabLinks extent).length p.val)) =
      RCscale (volumeCap w extent * volumeFloor w extent)
        (rat (fluctuationEnergy (boundaryCompleteSlabLinks extent).length p.val)) := by
    rw [scale_rat, scale_rat]
    apply Quotient.sound
    exact ofQ'_equiv_of_eqv (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _))
  rw [hs] at hm
  rw [embedded_norm]
  exact RCle_trans hm he

/-- Every original centered polynomial has a positive finite-volume
Dirichlet lower bound, uniform over K >= headCutoff(w). This is NOT
uniform in nome or extent and is not an OS transfer-matrix statement. -/
theorem dense_centered_coercivity (p : (F).V) (hcenter : (F).B p U ≈ 0) :
    RCle (RCscale (coercivity hw0 hw1 extent) (normSq (embedV F p)))
      ((P).finalEnergy (schedule extent) (embedV F p)) := by
  let r := Q'.recipPos (volumeCap w extent) (volumeCap_positive hw0 hw1 extent)
  have h := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos
    (volumeCap w extent) (volumeCap_positive hw0 hw1 extent)))
    (dense_centered_coercivity_mul hw0 hw1 K extent hK p hcenter)
  change RCle (RCscale r (RCscale (volumeFloor w extent) (normSq (embedV F p))))
    (RCscale r (RCscale (volumeCap w extent)
      ((P).finalEnergy (schedule extent) (embedV F p)))) at h
  rw [RCscale_RCscale, RCscale_RCscale] at h
  have hr : r * volumeCap w extent ≈ 1 := Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)
  have hs (x : RC) : RCscale (r * volumeCap w extent) x = x := by
    refine Quotient.inductionOn x ?_
    intro X
    apply Quotient.sound
    exact SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hr) (Q'.one_mul_eqv (X.approx n)))
  rw [hs] at h
  exact h

#print axioms volumeFloor_positive
#print axioms volumeCap_positive
#print axioms coercivity_positive
#print axioms free_energy_le_original_dirichlet
#print axioms dense_centered_coercivity_mul
#print axioms dense_centered_coercivity

end YMGap.Continuum.BF4ExactSlabFiniteVolumeCoercivity
