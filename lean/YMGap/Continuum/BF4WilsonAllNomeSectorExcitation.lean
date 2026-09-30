/-
# Original connected Wilson sources inside the witnessed time sector

Center the vacuum-created positive-time insertion using the SAME original
unit projection. It is exactly S(t) times the original centered loop,
has an explicit sector witness, and is vacuum orthogonal. At original
integer times its lag is the original connected moment with the two
external time shifts, not a different covariance model.

For the padded origin plaquette at time one, the existing positive response
supplies a strictly positive squared-norm floor u^2/4. The very same source
is a point of the actual derivative domain. This gives a concrete nonzero
centered domain state, not continuum survival or a uniform physical mass.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorInsertion
import YMGap.Continuum.BF4WilsonAllNomeCenteringPin
import YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse
import YMGap.Continuum.BF4WilsonAllNomeSectorDerivative

namespace YMGap.Continuum.BF4WilsonAllNomeSectorExcitation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredStream centeredVector centeredVector_time_pairing centeredVector_orthogonal)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection
  (unitProjection unitProjection_pairing centeredPart)
open YMGap.Continuum.BF4WilsonAllNomeCenteringPin (centeredPart_embed)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeAction (positiveAction)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws
  (positiveAction_symmetric positiveAction_sub)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeVacuum
  (positiveAction_unit positiveAction_vacuum_pairing)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (positiveAction_original)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeRangeClosure (positiveAction_range)
open YMGap.Continuum.BF4WilsonAllNomeSectorInsertion (sandwich sandwich_unit)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint corePoint)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation (originFace originFace_mem)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteUniformCapResponse
  (absoluteFloor absoluteFloor_positive plaquette_twoStep_floor_four)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTwoStepResponseCore (completed_oneStep_diagonal)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (dyadicTime)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "F" => positiveAction hw0 hw1
local notation "P" => unitProjection hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Positive time commutes with the computed original vacuum projection. -/
theorem positiveAction_unitProjection (time : PositiveTime) (x : V) :
    F time (P x) = P (F time x) := by
  apply completed_eq_of_pairings hw0 hw1
  intro y
  rw [positiveAction_symmetric hw0 hw1 time (P x) y,
    unitProjection_pairing,unitProjection_pairing,positiveAction_vacuum_pairing,
    positiveAction_symmetric hw0 hw1 time x U,positiveAction_unit]

theorem centeredPart_positiveAction (time : PositiveTime) (x : V) :
    centeredPart hw0 hw1 (F time x) = F time (centeredPart hw0 hw1 x) := by
  unfold centeredPart
  rw [positiveAction_sub,positiveAction_unitProjection]

/-- The original centered loop is propagated at strictly positive real time;
its explicit centered stream computes the sector witness. -/
def centeredSource (time : PositiveTime) (loop : SourceLoop width) :
    State hw0 hw1 (width := width) where
  val := F time (centeredVector hw0 hw1 (loopState loop))
  range := positiveAction_range hw0 hw1 time (centeredStream hw0 hw1 (loopState loop))

/-- Exact pin to the centered vacuum-created insertion, not merely an
equality of norms or an independently supplied correlation certificate. -/
theorem centeredSource_insertion_pin (time : PositiveTime) (loop : SourceLoop width) :
    (centeredSource hw0 hw1 time loop).val =
      centeredPart hw0 hw1 (sandwich hw0 hw1 time loop 1 U) := by
  rw [sandwich_unit,centeredPart_positiveAction,centeredPart_embed]
  rfl

theorem centeredSource_orthogonal (time : PositiveTime) (loop : SourceLoop width) :
    B U (centeredSource hw0 hw1 time loop).val = RCzero := by
  change B U (F time (centeredVector hw0 hw1 (loopState loop))) = RCzero
  rw [positiveAction_vacuum_pairing,completedInner_symm]
  exact centeredVector_orthogonal hw0 hw1 (loopState loop)

theorem centeredSource_original (loop : SourceLoop width) (n : Nat) (hn : 0 < n) :
    (centeredSource hw0 hw1 (dyadicTime ⟨0,n⟩ hn) loop).val =
      T n (centeredVector hw0 hw1 (loopState loop)) :=
  positiveAction_original hw0 hw1 n hn (centeredVector hw0 hw1 (loopState loop))

/-- The correlation remains the original connected loop moment, with both
positive-time shifts present in the exact lag. -/
theorem centeredSource_lag (loop : SourceLoop width) (n : Nat) (hn : 0 < n) (lag : Nat) :
    B (centeredSource hw0 hw1 (dyadicTime ⟨0,n⟩ hn) loop).val
      (T lag (centeredSource hw0 hw1 (dyadicTime ⟨0,n⟩ hn) loop).val) =
      Quotient.mk crealSetoid
        (centeredTimeMoment hw0 hw1 ((n+lag)+n) (loopState loop) (loopState loop)) := by
  rw [centeredSource_original,completedInner_time_balance,
    ← completedTime_add,← completedTime_add]
  exact centeredVector_time_pairing hw0 hw1 ((n+lag)+n) (loopState loop)

/-- This SAME source at time one belongs to the actual derivative domain. -/
def sourceDomain (loop : SourceLoop width) : DomainPoint hw0 hw1 (width := width) :=
  corePoint hw0 hw1 (centeredStream hw0 hw1 (loopState loop))

theorem sourceDomain_pin (loop : SourceLoop width) :
    (sourceDomain hw0 hw1 loop).input.val =
      (centeredSource hw0 hw1 (dyadicTime ⟨0,1⟩ (Nat.succ_pos 0)) loop).val :=
  (centeredSource_original hw0 hw1 loop 1 (Nat.succ_pos 0)).symm

/-- A useful concrete lower floor, with all original nome/width dependence.
It applies only to a fully active face, not to the killed boundary fringe. -/
theorem sourceDomain_norm_floor (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (active : FullyActive width face) :
    RCle (rat (absoluteFloor hw0 width))
      (B (sourceDomain hw0 hw1 (plaquetteLoop face hf)).input.val
        (sourceDomain hw0 hw1 (plaquetteLoop face hf)).input.val) := by
  have h := plaquette_twoStep_floor_four hw0 hw1 width face hf active
  rw [← completed_oneStep_diagonal (hw0 := hw0) (hw1 := hw1) (width := width)] at h
  exact h

/-- Padded origin gives an actual centered derivative-domain point and an
explicit positive squared-norm floor. No observable-existence premise. -/
def paddedDomainCertificate (padding : Nat) :
    Σ' p : DomainPoint hw0 hw1 (width := padding+2), Σ' floor : Q',
      ((0 : Q') < floor) ×'
      (completedInner hw0 hw1 (unitState hw0 hw1 (padding+2)) p.input.val = RCzero) ×'
      RCle (rat floor) (completedInner hw0 hw1 p.input.val p.input.val) := by
  let loop := plaquetteLoop originFace (originFace_mem (padding+1))
  refine ⟨sourceDomain hw0 hw1 loop,absoluteFloor hw0 (padding+2),
    absoluteFloor_positive hw0 hw1 (padding+2),?_,?_⟩
  · rw [sourceDomain_pin]
    exact centeredSource_orthogonal hw0 hw1 _ loop
  · exact sourceDomain_norm_floor hw0 hw1 originFace (originFace_mem (padding+1))
      (plaquette_active_after_padding (by omega : 1 < padding+2) originFace (originFace_mem 0))

#print axioms positiveAction_unitProjection
#print axioms centeredPart_positiveAction
#print axioms centeredSource
#print axioms centeredSource_insertion_pin
#print axioms centeredSource_orthogonal
#print axioms centeredSource_original
#print axioms centeredSource_lag
#print axioms sourceDomain
#print axioms sourceDomain_pin
#print axioms sourceDomain_norm_floor
#print axioms paddedDomainCertificate

end YMGap.Continuum.BF4WilsonAllNomeSectorExcitation
