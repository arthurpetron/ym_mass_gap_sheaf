/-
# Relative normalization of the literal plaquette defect orbit

The improved original-action prediction floor supplies a nome-only lower
bound on the norm of the SAME completed source y=(I-T)v. Combining it with
the established absolute physical-time orbit bound gives an explicit
relative tolerance cutoff. The floor may vanish as the nome varies; this
does not assert a continuum mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeRelativePlaquetteEnergyFloor
import YMGap.Continuum.BF4WilsonAllNomePlaquetteDefectOrbit

namespace YMGap.Continuum.BF4WilsonAllNomeRelativeDefectNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabRelativePredictionError
  (relativePredictionFloor relativePredictionFloor_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defect)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse (plaquette_norm_le_four)
open YMGap.Continuum.BF4WilsonAllNomeRelativePlaquetteEnergyFloor
open YMGap.Continuum.BF4WilsonAllNomePlaquetteDefectOrbit

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local notation "hfour" => Q'.ofNat_succ_pos 3

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "y" => defect hw0 hw1 v
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

/-- The nome-only floor `(s/2)^2/4 = s^2/16`, where `s` is the relative
original-action prediction floor. -/
def relativeDefectNormFloor (w : Q') : Q' :=
  (HalfPow.half * relativePredictionFloor w) *
    (HalfPow.half * relativePredictionFloor w) * Q'.recipPos 4 hfour

theorem relativeDefectNormFloor_positive (w : Q') :
    (0 : Q') < relativeDefectNormFloor w := by
  have hs := Q'.mul_pos (by decide : (0 : Q') < HalfPow.half)
    (relativePredictionFloor_positive w)
  exact Q'.mul_pos (Q'.mul_pos hs hs) (Q'.recipPos_pos 4 hfour)

private theorem rational_scale (a b : Q') :
    RCscale a (Rq b) = Rq (a * b) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul a b).symm

private theorem inverse_scale_four (x : RC) :
    RCscale (Q'.recipPos 4 hfour) (RCmul (Rq 4) x) = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv 4 hfour)))
      (Q'.one_mul_eqv _))

private theorem square_mono {a b : RC} (ha : RCnonneg a) (hab : RCle a b) :
    RCle (RCmul a a) (RCmul b b) := by
  have h1 := RCmul_mono_nonneg_left ha hab
  have h2 := RCmul_mono_nonneg_left (RCle_trans ha hab) hab
  rw [RCmul_comm b a] at h2
  exact RCle_trans h1 h2

/-- Improved positive norm floor for the literal original Wilson defect. -/
theorem plaquette_relative_defect_norm_floor :
    RCle (Rq (relativeDefectNormFloor w)) (B y y) := by
  have hs : RCnonneg (Rq (HalfPow.half * relativePredictionFloor w)) := by
    apply leEv_of_le
    intro n
    exact Q'.zero_le_add _ _
      (Q'.le_of_lt (Q'.mul_pos (by decide : (0 : Q') < HalfPow.half)
        (relativePredictionFloor_positive w))) (Q'.invSucc_nonneg n)
  have hsq := RCle_trans
    (square_mono hs (plaquette_relative_defect_form_floor hw0 hw1 width face hf))
    (completedInner_cauchySchwarz hw0 hw1 v y)
  have hcap := RCmul_mono_nonneg_left (completedInner_nonnegative hw0 hw1 y)
    (plaquette_norm_le_four hw0 hw1 width face hf)
  rw [RCmul_comm (B y y) (B v v), RCmul_comm (B y y) (Rq 4)] at hcap
  have h := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos 4 hfour))
    (RCle_trans hsq hcap)
  rw [inverse_scale_four] at h
  have hp : RCscale (Q'.recipPos 4 hfour)
      (RCmul (Rq (HalfPow.half * relativePredictionFloor w))
        (Rq (HalfPow.half * relativePredictionFloor w))) =
      Rq (relativeDefectNormFloor w) := by
    change RCscale (Q'.recipPos 4 hfour)
      (Rq ((HalfPow.half * relativePredictionFloor w) *
        (HalfPow.half * relativePredictionFloor w))) = _
    rw [rational_scale]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_comm_eqv _ _))
  rw [hp] at h
  exact h

/-- The already-proved absolute orbit estimate, normalized by its actual
nome-only source norm floor. This is for one fixed plaquette defect, not a
uniform operator estimate or a scaling-family survival statement. -/
theorem plaquette_defect_orbit_relative_small (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : orbitModulus (epsilon * relativeDefectNormFloor w) ≤ n) :
    RCle (B (T n y) (T n y)) (RCscale epsilon (B y y)) := by
  have htol : (0 : Q') < epsilon * relativeDefectNormFloor w :=
    Q'.mul_pos he (relativeDefectNormFloor_positive w)
  have habs := plaquette_defect_orbit_small hw0 hw1 width face hf
    (epsilon * relativeDefectNormFloor w) htol n hn
  have hfloor := plaquette_relative_defect_norm_floor hw0 hw1 width face hf
  have hscaled := RCscale_mono (Q'.le_of_lt he) hfloor
  rw [rational_scale] at hscaled
  exact RCle_trans habs hscaled

#print axioms relativeDefectNormFloor
#print axioms relativeDefectNormFloor_positive
#print axioms plaquette_relative_defect_norm_floor
#print axioms plaquette_defect_orbit_relative_small

end YMGap.Continuum.BF4WilsonAllNomeRelativeDefectNormalization
