/-
# Original conditional Dirichlet coercivity with support-only cost

The upper original norm estimate and all lower conditional residual estimates
retain the SAME detached action mass. Summing the exact physical schedule and
composing before division removes that mass. The positive coefficient depends
only on nome and a bound on the number of literal support links.

The residuals are in the actual completed full-action carrier. The INPUT is
an embedded polynomial with proved literal support and original mean zero.
No arbitrary-completed-vector, growing-cone, scaling or OS gap is inferred.
-/

import YMGap.Continuum.BF4ExactSlabLocalSupportHaarVariance
import YMGap.Continuum.BF4ExactSlabLocalSupportResidualFloor
import YMGap.Continuum.BF4ExactSlabFiniteVolumeCoercivity

namespace YMGap.Continuum.BF4ExactSlabLocalSupportCoercivity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.GNSProjectionSweep.Family
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportVariance
open YMGap.Continuum.BF4ExactSlabLocalSupportHaarVariance
open YMGap.Continuum.BF4ExactSlabLocalSupportResidualFloor
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionHaarEfronStein
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
private abbrev blocks (extent : Nat) := (boundaryCompleteSlabLinks extent).length
private def rat (q : Q') : RC := Quotient.mk crealSetoid (ofQ' q)

private theorem scale_rat (c q : Q') : RCscale c (rat q) = rat (c*q) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem embedded_norm (D : GNSData) (p : D.V) :
    normSq (embedV D p) = rat (D.B p p) := by
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

private theorem scale_eqv {a b : Q'} (h : a ≈ b) (x : RC) : RCscale a x = RCscale b x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.mul_eqv_congr_right _ _ (X.approx n) h)

private theorem scale_cancel (c : Q') (hc : (0 : Q') < c) (x : RC) :
    RCscale (Q'.recipPos c hc*c) x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  have he := Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv c hc)
  exact SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (X.approx n) he) (Q'.one_mul_eqv _))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (S : List Z4Link) (size : Nat) (hsize : S.length ≤ size)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "HB" => quaternionHaar (blocks extent) (background w K extent S)
local notation "U" => (Subtype.mk polyOne (supported_one (blocks extent)))

include hsize

/-- The same exterior mass factors out of the full physical sum. -/
theorem free_energy_le_local_dirichlet (p : (F).V) (hp : LinkLocal extent S p.val) :
    RCle (RCscale (supportFloor w size * HB)
      (rat (fluctuationEnergy (blocks extent) p.val)))
      ((P).finalEnergy (schedule extent) (embedV F p)) := by
  have h := sumOn_mono (schedule extent)
    (fun i => RCscale (supportFloor w size * HB)
      (rat (haarSquare (blocks extent)
        (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val))))
    (fun i => normSq ((P).residual i (embedV F p))) (fun i _ => by
      dsimp only
      rw [scale_rat]
      exact conditional_residual_local_floor hw0 hw1 K extent hK S size hsize i p hp)
  have hs : sumOn (schedule extent) (fun i =>
      rat (haarSquare (blocks extent)
        (fluctuation ((boundaryCompleteSlabLinks extent).idxOf i.val) p.val))) =
      rat (fluctuationEnergy (blocks extent) p.val) :=
    BF4ExactSlabFiniteVolumeCoercivity.free_energy_schedule hw0 hw1 K extent hK p
  rw [sumOn_scale, hs] at h
  exact h

/-- No exterior mass survives this division-free original Dirichlet
comparison. The full action, norm and completed residuals are unchanged. -/
theorem dense_local_coercivity_mul (p : (F).V) (hp : LinkLocal extent S p.val)
    (hcenter : (F).B p U ≈ 0) :
    RCle (RCscale (supportFloor w size) (normSq (embedV F p)))
      (RCscale (supportCap w size) ((P).finalEnergy (schedule extent) (embedV F p))) := by
  have hv : RCle (rat ((F).B p p))
      (RCscale (supportCap w size * HB) (rat (fluctuationEnergy (blocks extent) p.val))) := by
    rw [scale_rat]
    exact leEv_ofQ'_of_approx_ge (fun _ =>
      centered_norm_le_local_free_energy hw0 hw1 K extent hK size S hsize p hcenter hp)
  have hm := RCscale_mono (Q'.le_of_lt (supportFloor_positive hw0 hw1 size)) hv
  have he := RCscale_mono (Q'.le_of_lt (supportCap_positive hw0 hw1 size))
    (free_energy_le_local_dirichlet hw0 hw1 K extent hK S size hsize p hp)
  rw [RCscale_RCscale] at hm he
  have hcoef : supportFloor w size * (supportCap w size * HB) ≈
      supportCap w size * (supportFloor w size * HB) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => supportFloor w size | 1 => supportCap w size | _ => HB)
  rw [scale_eqv hcoef] at hm
  rw [embedded_norm]
  exact RCle_trans hm he

/-- Positive original-action coercivity for all literally supported,
original-centered polynomial inputs, with a coefficient independent of
extent, placement and late cutoff at fixed nome and support-size budget.
This is not an all-completed-state or growing-support bound. -/
theorem dense_local_coercivity (p : (F).V) (hp : LinkLocal extent S p.val)
    (hcenter : (F).B p U ≈ 0) :
    RCle (RCscale (supportRatio hw0 hw1 size) (normSq (embedV F p)))
      ((P).finalEnergy (schedule extent) (embedV F p)) := by
  let r := Q'.recipPos (supportCap w size) (supportCap_positive hw0 hw1 size)
  have h := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos
    (supportCap w size) (supportCap_positive hw0 hw1 size)))
    (dense_local_coercivity_mul hw0 hw1 K extent hK S size hsize p hp hcenter)
  change RCle (RCscale r (RCscale (supportFloor w size) (normSq (embedV F p))))
    (RCscale r (RCscale (supportCap w size)
      ((P).finalEnergy (schedule extent) (embedV F p)))) at h
  rw [RCscale_RCscale, RCscale_RCscale,
    scale_cancel (supportCap w size) (supportCap_positive hw0 hw1 size)] at h
  exact h

#print axioms free_energy_le_local_dirichlet
#print axioms dense_local_coercivity_mul
#print axioms dense_local_coercivity

end YMGap.Continuum.BF4ExactSlabLocalSupportCoercivity
