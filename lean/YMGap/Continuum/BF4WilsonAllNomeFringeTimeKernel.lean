/-
# Time-kernel consequence of the inactive-face correlation pin

On the same all-nome width carrier, an inactive-face pin that kills all
centered lags at least two forces the one-step image of that centered face
to be zero. At width one the origin plaquette is nonzero, but its one-step
image vanishes, so the original completed time map is not injective there.
This is a fixed-parameter fringe obstruction, not a continuum statement.
-/

import YMGap.Continuum.BF4WilsonAllNomeFringeCorrelation
import YMGap.Continuum.BF4WilsonAllNomeGeometry
import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
import YMGap.Continuum.BF4ExactSlabWidthOneGeometry

namespace YMGap.Continuum.BF4WilsonAllNomeFringeTimeKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabWidthOneGeometry
  (far01_x0_index activeBlocks_one)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedTime_zero_element completedInner_zero_right)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
  (uniformFloor uniformFloor_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap (completedInner_even_diagonal)
open YMGap.Continuum.BF4WilsonAllNomeGeometry (completedInner_posdef)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero completedZero_embed)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
  (originFace originFace_mem plaquetteExcitation plaquetteExcitation_ne_zero
    plaquetteExcitation_response_floor)
open YMGap.Continuum.BF4WilsonAllNomeFringeCorrelation (centeredTimeMoment_zero)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "v" => Subtype.val (plaquetteExcitation hw0 hw1 width face hf)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Z" => completedZero hw0 hw1 width

/-- Every inactive retained face has zero one-step image on its actual
centered plaquette excitation, by the lag-two diagonal identity and
definiteness of the existing completion. -/
theorem inactive_face_time_one_zero
    (ha : ¬ FullyActive width face) :
    T 1 v = Z := by
  have hmoment := centeredTimeMoment_zero hw0 hw1 width face hf ha 1
  have hlag : B v (T 2 v) = RCzero := by
    change B (centeredVector hw0 hw1 (loopState (plaquetteLoop face hf)))
      (T 2 (centeredVector hw0 hw1 (loopState (plaquetteLoop face hf)))) = RCzero
    rw [centeredVector_time_pairing]
    exact Quotient.sound hmoment
  have hdiag := completedInner_even_diagonal hw0 hw1 width 1 v
  rw [hlag] at hdiag
  have hnorm : B (T 1 v) (T 1 v) = RCzero := hdiag.symm
  have hzero := (completedInner_posdef hw0 hw1 width (T 1 v)).mp hnorm
  simpa only [completedZero_embed] using hzero

/-- Width-one origin face has an incident retained link at the far fringe,
so it is not fully active. -/
theorem originFace_not_fully_active : ¬ FullyActive 1 originFace := by
  intro hactive
  have hlink := hactive ((0, 1, 0, 0), .x0) (by decide)
  rw [far01_x0_index, activeBlocks_one] at hlink
  exact (by decide : ¬ (2 : Nat) ∈ [0, 1, 4]) hlink

/-- The nonzero width-one origin excitation is annihilated by the original
one-step completed time map. -/
theorem originPlaquette_time_one_zero :
    completedTime hw0 hw1 (width := 1) 1
      (Subtype.val (plaquetteExcitation hw0 hw1 1 originFace
        (originFace_mem 0))) = completedZero hw0 hw1 1 :=
  inactive_face_time_one_zero hw0 hw1 1 originFace (originFace_mem 0)
    originFace_not_fully_active

/-- The actual width-one completed time map is not injective. The witness is
the already-proved nonzero centered origin plaquette, not an abstract kernel
vector. -/
theorem completedTime_one_not_injective_width_one :
    ¬ Function.Injective (completedTime hw0 hw1 (width := 1) 1) := by
  intro hinj
  let probe := Subtype.val (plaquetteExcitation hw0 hw1 1 originFace
    (originFace_mem 0))
  have htime : completedTime hw0 hw1 1 probe = completedZero hw0 hw1 1 :=
    originPlaquette_time_one_zero hw0 hw1
  have hsame : completedTime hw0 hw1 1 probe =
      completedTime hw0 hw1 1 (completedZero hw0 hw1 1) := by
    rw [htime, completedTime_zero_element]
  have hv : probe = completedZero hw0 hw1 1 := hinj hsame
  have hv' : probe = embed hw0 hw1
      (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.zero 1) := by
    simpa only [completedZero_embed] using hv
  exact (plaquetteExcitation_ne_zero hw0 hw1 1 originFace (originFace_mem 0)) hv'

/-- Strict spatial padding removes the particular fringe obstruction:
the original origin plaquette now has a positive one-step response. -/
theorem padded_origin_time_one_ne_zero (padding : Nat) :
    completedTime hw0 hw1 (width := padding+2) 1
      (Subtype.val (plaquetteExcitation hw0 hw1 (padding+2) originFace
        (originFace_mem (padding+1)))) ≠ completedZero hw0 hw1 (padding+2) := by
  intro hz
  have hfloor := plaquetteExcitation_response_floor hw0 hw1 (padding+2)
    originFace (originFace_mem (padding+1))
    (plaquette_active_after_padding (by omega : 1 < padding+2)
      originFace (originFace_mem 0))
  rw [hz, completedInner_zero_right] at hfloor
  have hbad : uniformFloor hw0 (padding+2) ≤ (0 : Q') :=
    GNSQuotient.GNSData.RCofQ'_le_reflect hfloor
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le (uniformFloor_positive hw0 hw1 (padding+2)) hbad)

/-- Syntactic width naturality cannot automatically supply this completed
transport. No isometry or linearity is assumed: even these three explicit
properties conflict. Each plaquette is centered by its OWN actual mean. -/
theorem no_centered_plaquette_time_transport (padding : Nat)
    (F : Completion hw0 hw1 1 → Completion hw0 hw1 (padding+2))
    (hzero : F (completedZero hw0 hw1 1) = completedZero hw0 hw1 (padding+2))
    (hprobe : F (Subtype.val (plaquetteExcitation hw0 hw1 1 originFace
        (originFace_mem 0))) =
      Subtype.val (plaquetteExcitation hw0 hw1 (padding+2) originFace
        (originFace_mem (padding+1))))
    (htime : F (completedTime hw0 hw1 1
        (Subtype.val (plaquetteExcitation hw0 hw1 1 originFace (originFace_mem 0)))) =
      completedTime hw0 hw1 1
        (F (Subtype.val (plaquetteExcitation hw0 hw1 1 originFace (originFace_mem 0))))) :
    False := by
  rw [originPlaquette_time_one_zero, hzero, hprobe] at htime
  exact padded_origin_time_one_ne_zero hw0 hw1 padding htime.symm

#print axioms inactive_face_time_one_zero
#print axioms originFace_not_fully_active
#print axioms originPlaquette_time_one_zero
#print axioms completedTime_one_not_injective_width_one
#print axioms padded_origin_time_one_ne_zero
#print axioms no_centered_plaquette_time_transport

end YMGap.Continuum.BF4WilsonAllNomeFringeTimeKernel
