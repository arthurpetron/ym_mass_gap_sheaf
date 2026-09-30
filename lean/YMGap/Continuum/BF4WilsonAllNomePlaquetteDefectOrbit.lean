/-
# A supplied nonzero plaquette defect with physical-time polynomial decay

On the ORIGINAL literal Wilson completion, y=(I-T)v for the existing
centered plaquette has ||y||^2 >= starRatio(w)^2/16 > 0, while
||T^n y||^2 <= 4/(n+1)^2. Both estimates are independent of width.
The floor depends on nome and may vanish along a scaling family.

This is one explicit vacuum-complement observable, not exponential decay
on the entire complement, spatial-limit identification, or a mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteEnergyFloor
import YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteDefectOrbit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws (intrinsicForm_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
open YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse (plaquette_norm_le_four)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteEnergyFloor
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
  (relativeTailModulus mixedMoment_defect_decreasing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement (timeIncrement timeIncrement_nome_bound)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local notation "hfour" => Q'.ofNat_succ_pos 3

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "y" => defect hw0 hw1 v
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width

/-- The explicit nome-only number (s/2)^2/4 = s^2/16. -/
def defectNormFloor (w : Q') : Q' :=
  (HalfPow.half * starRatio w) * (HalfPow.half * starRatio w) * Q'.recipPos 4 hfour

include hw0 hw1 in
theorem defectNormFloor_positive : (0 : Q') < defectNormFloor w := by
  have h := Q'.mul_pos (by decide : (0 : Q') < HalfPow.half)
    (starRatio_positive hw0 hw1)
  exact Q'.mul_pos (Q'.mul_pos h h) (Q'.recipPos_pos 4 hfour)

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

/-- Completed Cauchy--Schwarz consumes the original energy floor and norm cap. -/
theorem plaquette_defect_norm_floor : RCle (Rq (defectNormFloor w)) (B y y) := by
  have hs : RCnonneg (Rq (HalfPow.half * starRatio w)) := by
    apply leEv_of_le
    intro n
    exact Q'.zero_le_add _ _
      (Q'.le_of_lt (Q'.mul_pos (by decide : (0 : Q') < HalfPow.half)
        (starRatio_positive hw0 hw1))) (Q'.invSucc_nonneg n)
  have hsq := RCle_trans
    (square_mono hs (plaquette_defect_form_floor hw0 hw1 width face hf))
    (completedInner_cauchySchwarz hw0 hw1 v y)
  have hcap := RCmul_mono_nonneg_left (completedInner_nonnegative hw0 hw1 y)
    (plaquette_norm_le_four hw0 hw1 width face hf)
  rw [RCmul_comm (B y y) (B v v), RCmul_comm (B y y) (Rq 4)] at hcap
  have h := RCscale_mono (Q'.le_of_lt (Q'.recipPos_pos 4 hfour))
    (RCle_trans hsq hcap)
  rw [inverse_scale_four] at h
  have hp : RCscale (Q'.recipPos 4 hfour)
      (RCmul (Rq (HalfPow.half * starRatio w)) (Rq (HalfPow.half * starRatio w))) =
      Rq (defectNormFloor w) := by
    change RCscale (Q'.recipPos 4 hfour)
      (Rq ((HalfPow.half * starRatio w) * (HalfPow.half * starRatio w))) = _
    rw [rational_scale]
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_comm_eqv _ _))
  rw [hp] at h
  exact h

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

theorem plaquette_defect_orthogonal : B U y = RCzero := by
  have h := congrArg (fun z => B U z) (time_add_defect hw0 hw1 v)
  dsimp only at h
  rw [completedInner_add_right,
    completedTime_preserves_vacuumComplement hw0 hw1 1 v
      (plaquetteExcitation hw0 hw1 width face hf).property,
    zero_add, (plaquetteExcitation hw0 hw1 width face hf).property] at h
  exact h

/-- This packages the actual time difference, without replacing the carrier. -/
def plaquetteDefectExcitation : VacuumComplement hw0 hw1 (width := width) :=
  ⟨y, plaquette_defect_orthogonal hw0 hw1 width face hf⟩

theorem plaquette_defect_norm_ne_zero : B y y ≠ RCzero := by
  intro hz
  have h := plaquette_defect_norm_floor hw0 hw1 width face hf
  rw [hz] at h
  have hle : defectNormFloor w ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (defectNormFloor_positive hw0 hw1) hle)

theorem plaquette_defect_ne_zero : y ≠ completedZero hw0 hw1 width := by
  intro hz
  apply plaquette_defect_norm_ne_zero hw0 hw1 width face hf
  rw [hz, completedZero, completedInner_embed]
  exact Quotient.sound (intrinsicForm_zero_left hw0 hw1 (zero width))

/-- Physical time, not an auxiliary iteration; no extent occurs in the bound. -/
theorem plaquette_defect_orbit_bound (n : Nat) :
    RCle (B (T n y) (T n y)) (Rq ((Q'.invSucc n * Q'.invSucc n) * 4)) := by
  have h := RCle_trans (timeDefect_bound hw0 hw1 n v)
    (RCscale_mono (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg n) (Q'.invSucc_nonneg n))
      (plaquette_norm_le_four hw0 hw1 width face hf))
  rwa [rational_scale] at h

/-- A rational tolerance produces a natural time cutoff, uniformly in width
and nome. It controls the unrenormalized source, not scaling survival. -/
def orbitModulus (epsilon : Q') : Nat :=
  relativeTailModulus (Q'.recipPos 4 hfour * epsilon)

theorem plaquette_defect_orbit_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : orbitModulus epsilon ≤ n) :
    RCle (B (T n y) (T n y)) (Rq epsilon) := by
  have he' := Q'.mul_pos (Q'.recipPos_pos 4 hfour) he
  have h := RCle_trans
    (timeDefect_small hw0 hw1 (Q'.recipPos 4 hfour * epsilon) he' n hn v)
    (RCscale_mono (Q'.le_of_lt he') (plaquette_norm_le_four hw0 hw1 width face hf))
  rw [rational_scale] at h
  have hp : Rq ((Q'.recipPos 4 hfour * epsilon) * 4) = Rq epsilon := by
    apply Quotient.sound
    apply SumOfSquares.Equiv_of_approx_eqv
    intro j
    exact Q'.eqv_trans _ _ _
      (RingNormaliser.poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.const 4))
        (.mul (.mul (.const 4) (.var 0)) (.var 1)) (by decide)
        (fun | 0 => Q'.recipPos 4 hfour | _ => epsilon))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_recipPos_eqv 4 hfour))
        (Q'.one_mul_eqv epsilon))
  rwa [hp] at h

/-- The same source can collapse as nome approaches one: its norm is at most
192*(1-w) when its four links are active. The nonzero fixed-nome witness is
therefore not an unrenormalized continuum-survival certificate. -/
theorem plaquette_defect_nome_bound
    (hactive : ∀ e, e ∈ (plaquetteLoop face hf).edges →
      (baseLinks width).idxOf e.link ∈ activeBlocks width) :
    RCle (B y y) (Rq (192 * (1 + -w))) := by
  have hd : RCle (B y y) (B v y) := by
    have h := mixedMoment_defect_decreasing hw0 hw1 v 0 1
    change RCle (B v (T 0 (defect hw0 hw1 y))) (B v (T 0 y)) at h
    rw [completedTime_zero, completedTime_zero, ← defect_symmetric] at h
    exact h
  have hi : RCle (Quotient.mk crealSetoid
      (timeIncrement hw0 hw1 (plaquetteLoop face hf) 1))
      (Rq (Q'.ofNat 1 *
        (24 * (Q'.ofNat (plaquetteLoop face hf).edges.length *
          Q'.ofNat (plaquetteLoop face hf).edges.length) * (1 + -w)))) :=
    timeIncrement_nome_bound hw0 hw1 (plaquetteLoop face hf) hactive 1
  rw [plaquette_timeIncrement_defect_pin] at hi
  have hh := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half) hi
  rw [RCscale_RCscale,
    RCSignedPairBudget.scale_congr (by decide : Q'.eqv (HalfPow.half * 2) 1),
    RCscale_one, rational_scale] at hh
  have hp : Rq (HalfPow.half * (Q'.ofNat 1 *
      (24 * (Q'.ofNat (plaquetteLoop face hf).edges.length *
        Q'.ofNat (plaquetteLoop face hf).edges.length) * (1 + -w)))) =
      Rq (192 * (1 + -w)) := by
    apply Quotient.sound
    apply SumOfSquares.Equiv_of_approx_eqv
    intro j
    exact Q'.eqv_trans _ _ _
      (RingNormaliser.poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.const 1)
          (.mul (.mul (.const 24) (.mul (.const 4) (.const 4))) (.var 1))))
        (.mul (.mul (.var 0) (.const 384)) (.var 1)) (by decide)
        (fun | 0 => HalfPow.half | _ => 1 + -w))
      (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (HalfPow.half * 384) 192))
  rw [hp] at hh
  exact RCle_trans hd hh

/-- An explicit source at every positive width, with no face-existence input. -/
def decayingExcitation (width : Nat) :
    {state : VacuumComplement hw0 hw1 (width := width+1) //
      RCle (Rq (defectNormFloor w)) (B state.val state.val) ∧
      state.val ≠ completedZero hw0 hw1 (width+1) ∧
      ∀ n, RCle (B (T n state.val) (T n state.val))
        (Rq ((Q'.invSucc n * Q'.invSucc n) * 4))} :=
  ⟨plaquetteDefectExcitation hw0 hw1 (width+1) originFace (originFace_mem width),
    plaquette_defect_norm_floor hw0 hw1 (width+1) originFace (originFace_mem width),
    plaquette_defect_ne_zero hw0 hw1 (width+1) originFace (originFace_mem width),
    plaquette_defect_orbit_bound hw0 hw1 (width+1) originFace (originFace_mem width)⟩

#print axioms defectNormFloor_positive
#print axioms plaquette_defect_norm_floor
#print axioms plaquette_defect_orthogonal
#print axioms plaquetteDefectExcitation
#print axioms plaquette_defect_norm_ne_zero
#print axioms plaquette_defect_ne_zero
#print axioms plaquette_defect_orbit_bound
#print axioms orbitModulus
#print axioms plaquette_defect_orbit_small
#print axioms plaquette_defect_nome_bound
#print axioms decayingExcitation

end YMGap.Continuum.BF4WilsonAllNomePlaquetteDefectOrbit
