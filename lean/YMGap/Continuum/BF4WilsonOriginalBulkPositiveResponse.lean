/-
# A nonzero excitation in the ORIGINAL physical bulk carrier

The literal fundamental plaquette, at nome 1/1024, retains half the checked
spatial response floor in every sufficiently interior ORIGINAL finite-width
bond completion. The executable threshold is independent of larger ambient
width. Physical bond lags one and two correspond to spatial times two and
three: the central bond buffer is not erased.

The vector is centered by its OWN finite-width computed mean. Its scalar
Cauchy modulus and original-sector range witness are retained in the actual
BondCompletion construction. Original time contraction supplies the same
positive norm floor. No normalization or map between completed widths is used.

This is fixed-nome lattice nontriviality, not continuum survival, a physical
mass calibration, a changing-spacing estimate or the Clay theorem.
-/

import YMGap.Continuum.BF4WilsonOriginalBulkComparison
import YMGap.Continuum.BF4WilsonSpatialUnionPositiveResponse
import YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
import YMGap.Continuum.RCDistBridge

namespace YMGap.Continuum.BF4WilsonOriginalBulkPositiveResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonOriginalBulkComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (inclusion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4WilsonAllNomeBondReflectedForm (crossOdd)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (BondCompletion ofSource bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_ofSource bondValue_inner vacuum)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (image image_unit)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeDyadicRepresentatives
  (rootRepresentative rootRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection
  (unitCoefficient unitCoefficientCauchy unitProjection_mk centeredPart
    centeredPart_orthogonal centeredPart_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime completedTime_zero)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedInner_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap (completedCenteredScalar)
open YMGap.Continuum.BF4WilsonAllNomeBondOSConnectedDecay (connected)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm (plaquette)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor
  (responseFloor responseFloor_positive)
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCentralExcitation (origin_physical)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The SAME unnormalized fundamental plaquette used by the spatial floor. -/
def probe : IntrinsicExpression 1 :=
  plaquette originFace (origin_physical (by decide : 0 < 1))

/-- Half of the original response floor, still explicit rational data. -/
def floor : Q' := HalfPow.half * responseFloor

theorem floor_positive : (0 : Q') < floor :=
  ExpNeg.half_mul_pos responseFloor responseFloor_positive

/-- Source-sized threshold at the actual tolerance: F/2 response error and
F/4 in the included-width spatial modulus. Only lags one and two are used. -/
def responseModulus (lag : Nat) : Nat :=
  comparisonModulus hd hs (lag+1)
    (crossOdd probe (BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance lag probe))
    (crossOdd probe (unit 1)) (crossOdd (unit 1) probe) (HalfPow.half*floor)

/-- One computed threshold supplies both positive responses. -/
def excitationModulus : Nat := max (responseModulus 1) (responseModulus 2)

private theorem half_floor_of_close (actual target : RC)
    (hfloor : RCle (rat responseFloor) target)
    (hclose : RCle target (RCadd actual (rat floor))) : RCle (rat floor) actual := by
  have h := RCadd_le_add (RCle_trans hfloor hclose) (RCle_refl (rat (-floor)))
  have hl : RCadd (rat responseFloor) (rat (-floor)) = rat floor :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => by
      change (responseFloor + -floor).eqv floor
      decide))
  have hr : RCadd (RCadd actual (rat floor)) (rat (-floor)) = actual := by
    refine Quotient.inductionOn actual ?_
    exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0) (by decide)
        (fun | 0 => A.approx n | _ => floor)))
  simpa only [hl, hr] using h

private theorem spatial_lag_one_floor :
    RCle (rat responseFloor)
      (Quotient.mk crealSetoid (spatialConnected nome_pos nome_lt_one hsmall hd hs
        (by decide : 0 < 1) 1 probe probe)) := by
  have h := BF4WilsonSpatialUnionPositiveResponse.lagTwo_floor
  rw [BF4WilsonSpatialUnionPositiveResponse.vector_correlator_pin] at h
  exact h

private theorem spatial_lag_two_floor :
    RCle (rat responseFloor)
      (Quotient.mk crealSetoid (spatialConnected nome_pos nome_lt_one hsmall hd hs
        (by decide : 0 < 1) 2 probe probe)) := by
  have h := BF4WilsonSpatialUnionPositiveResponse.lagThree_floor
  rw [BF4WilsonSpatialUnionPositiveResponse.vector_correlator_pin] at h
  exact h

/-- Positive ACTUAL physical response, uniform in every larger ambient width. -/
theorem bulk_lag_one_floor {larger : Nat} (h : 1 ≤ larger) (r : Nat)
    (hr : responseModulus 1 ≤ r) :
    RCle (rat floor) (bulkConnected nome_pos nome_lt_one 1
      (inclusion h probe) (inclusion h probe) r) := by
  exact half_floor_of_close _ _ spatial_lag_one_floor
    (bulkConnected_included_spatial_close nome_pos nome_lt_one hsmall hd hs h
      (by decide : 0 < 1) 2 1 probe probe (by decide) (by decide)
      floor floor_positive r hr).2

/-- The second physical lag retains the same floor and its full bond clock. -/
theorem bulk_lag_two_floor {larger : Nat} (h : 1 ≤ larger) (r : Nat)
    (hr : responseModulus 2 ≤ r) :
    RCle (rat floor) (bulkConnected nome_pos nome_lt_one 2
      (inclusion h probe) (inclusion h probe) r) := by
  exact half_floor_of_close _ _ spatial_lag_two_floor
    (bulkConnected_included_spatial_close nome_pos nome_lt_one hsmall hd hs h
      (by decide : 0 < 1) 3 2 probe probe (by decide) (by decide)
      floor floor_positive r hr).2

section PhysicalCentering

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width

/-- Original source image representative with its explicit root-row modulus. -/
def physicalRepresentative (x : IntrinsicExpression width) : (D).Cauchy :=
  rootRepresentative hw0 hw1 1 ((D).constant x)

theorem physicalRepresentative_pin (x : IntrinsicExpression width) :
    Quotient.mk (D).completionSetoid (physicalRepresentative hw0 hw1 x) =
      bondValue hw0 hw1 (ofSource hw0 hw1 x) := by
  rw [bondValue_ofSource]
  exact rootRepresentative_pin hw0 hw1 1 ((D).constant x)

private theorem vacuum_value :
    bondValue hw0 hw1 (vacuum hw0 hw1 (width := width)) = U := by
  rw [vacuum, bondValue_ofSource, image_unit]

/-- Center INSIDE the physical completion by the OWN computed mean. Its
real scalar Cauchy witness is constructed before any quotient operation. -/
def centeredPhysical (x : IntrinsicExpression width) : H :=
  BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 (ofSource hw0 hw1 x)
    (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1
      (unitCoefficient hw0 hw1 (physicalRepresentative hw0 hw1 x))
      (unitCoefficientCauchy hw0 hw1 (physicalRepresentative hw0 hw1 x))
      (vacuum hw0 hw1))

theorem centeredPhysical_value (x : IntrinsicExpression width) :
    bondValue hw0 hw1 (centeredPhysical hw0 hw1 x) =
      centeredPart hw0 hw1 (bondValue hw0 hw1 (ofSource hw0 hw1 x)) := by
  unfold centeredPhysical centeredPart
  rw [BF4WilsonAllNomeBondOSLinear.bondValue_sub,
    BF4WilsonAllNomeBondOSLinear.bondValue_realSmul, vacuum_value,
    ← unitProjection_mk, physicalRepresentative_pin]

theorem centeredPhysical_orthogonal (x : IntrinsicExpression width) :
    bondCompletedInner hw0 hw1 (vacuum hw0 hw1) (centeredPhysical hw0 hw1 x) = RCzero := by
  rw [bondValue_inner, vacuum_value, centeredPhysical_value]
  exact centeredPart_orthogonal hw0 hw1 _

/-- Original physical connected scalar equals the correlation of this
actual mean-centered physical vector under the SAME original time operator. -/
theorem centeredPhysical_time_pairing (lag : Nat) (x : IntrinsicExpression width) :
    B (bondValue hw0 hw1 (centeredPhysical hw0 hw1 x))
      (completedTime hw0 hw1 lag (bondValue hw0 hw1 (centeredPhysical hw0 hw1 x))) =
      connected hw0 hw1 lag (ofSource hw0 hw1 x) (ofSource hw0 hw1 x) := by
  rw [centeredPhysical_value, centeredPart_time_pairing]
  rfl

theorem centeredPhysical_norm_pin (x : IntrinsicExpression width) :
    bondCompletedInner hw0 hw1 (centeredPhysical hw0 hw1 x) (centeredPhysical hw0 hw1 x) =
      connected hw0 hw1 0 (ofSource hw0 hw1 x) (ofSource hw0 hw1 x) := by
  rw [bondValue_inner, ← centeredPhysical_time_pairing, completedTime_zero]

end PhysicalCentering

/-- The literal included and recentered plaquette, centered on its actual
finite-width physical carrier. No completed-width inclusion is assumed. -/
def excitation {larger : Nat} (h : 1 ≤ larger) (r : Nat) :
    BondCompletion nome_pos nome_lt_one (width := paddedWidth larger r) :=
  centeredPhysical nome_pos nome_lt_one (bulkSource r (inclusion h probe))

theorem excitation_orthogonal {larger : Nat} (h : 1 ≤ larger) (r : Nat) :
    bondCompletedInner nome_pos nome_lt_one (vacuum nome_pos nome_lt_one)
      (excitation h r) = RCzero := centeredPhysical_orthogonal nome_pos nome_lt_one _

/-- Every scalar response is pinned to THIS original physical vector. -/
theorem excitation_time_pairing {larger : Nat} (h : 1 ≤ larger) (r lag : Nat) :
    completedInner nome_pos nome_lt_one (bondValue nome_pos nome_lt_one (excitation h r))
      (completedTime nome_pos nome_lt_one lag (bondValue nome_pos nome_lt_one (excitation h r))) =
      bulkConnected nome_pos nome_lt_one lag (inclusion h probe) (inclusion h probe) r :=
  centeredPhysical_time_pairing nome_pos nome_lt_one lag _

/-- A width-independent positive OWN norm floor on the original physical
excitation. The nome is FIXED, not a changing physical-spacing family. -/
theorem excitation_norm_floor {larger : Nat} (h : 1 ≤ larger) (r : Nat)
    (hr : responseModulus 1 ≤ r) :
    RCle (rat floor) (bondCompletedInner nome_pos nome_lt_one (excitation h r) (excitation h r)) := by
  have hresponse := bulk_lag_one_floor h r hr
  have hnorm := BF4WilsonAllNomeTimeDefectMoments.completedTime_form_le nome_pos nome_lt_one
    1 (bondValue nome_pos nome_lt_one (excitation h r))
  rw [excitation, centeredPhysical_time_pairing] at hnorm
  exact RCle_trans hresponse (by simpa only [bondValue_inner, excitation] using hnorm)

theorem excitation_ne_zero {larger : Nat} (h : 1 ≤ larger) (r : Nat)
    (hr : responseModulus 1 ≤ r) :
    excitation h r ≠ BF4WilsonAllNomeBondOSLinear.zero nome_pos nome_lt_one := by
  intro hz
  have hf := excitation_norm_floor h r hr
  rw [hz, bondValue_inner, BF4WilsonAllNomeBondOSLinear.bondValue_zero,
    completedInner_zero_left] at hf
  have hle := YMGap.Continuum.GNSQuotient.GNSData.RCofQ'_le_reflect hf
  exact (by decide : ¬ (0 : Q') < (0 : Q')) (Q'.pos_of_lt_of_le floor_positive hle)

/-- Return the actual physical vector, positive floor and response threshold
as data. Both finite-lag responses and its OWN norm retain that floor. -/
def positiveExcitation (larger : Nat) (h : 1 ≤ larger) :
    Σ' r : Nat, Σ' x : BondCompletion nome_pos nome_lt_one (width := paddedWidth larger r),
      Σ' c : Q', ((0 : Q') < c) ×'
        (bondCompletedInner nome_pos nome_lt_one (vacuum nome_pos nome_lt_one) x = RCzero) ×'
        RCle (rat c) (bondCompletedInner nome_pos nome_lt_one x x) ×'
        RCle (rat c) (completedInner nome_pos nome_lt_one (bondValue nome_pos nome_lt_one x)
          (completedTime nome_pos nome_lt_one 1 (bondValue nome_pos nome_lt_one x))) ×'
        RCle (rat c) (completedInner nome_pos nome_lt_one (bondValue nome_pos nome_lt_one x)
          (completedTime nome_pos nome_lt_one 2 (bondValue nome_pos nome_lt_one x))) :=
  ⟨excitationModulus, excitation h excitationModulus, floor, floor_positive,
    excitation_orthogonal h excitationModulus,
    excitation_norm_floor h excitationModulus (Nat.le_max_left _ _),
    by rw [excitation_time_pairing]; exact bulk_lag_one_floor h excitationModulus (Nat.le_max_left _ _),
    by rw [excitation_time_pairing]; exact bulk_lag_two_floor h excitationModulus (Nat.le_max_right _ _)⟩

#print axioms probe
#print axioms floor
#print axioms floor_positive
#print axioms responseModulus
#print axioms excitationModulus
#print axioms half_floor_of_close
#print axioms spatial_lag_one_floor
#print axioms spatial_lag_two_floor
#print axioms bulk_lag_one_floor
#print axioms bulk_lag_two_floor
#print axioms physicalRepresentative
#print axioms physicalRepresentative_pin
#print axioms vacuum_value
#print axioms centeredPhysical
#print axioms centeredPhysical_value
#print axioms centeredPhysical_orthogonal
#print axioms centeredPhysical_time_pairing
#print axioms centeredPhysical_norm_pin
#print axioms excitation
#print axioms excitation_orthogonal
#print axioms excitation_time_pairing
#print axioms excitation_norm_floor
#print axioms excitation_ne_zero
#print axioms positiveExcitation

end YMGap.Continuum.BF4WilsonOriginalBulkPositiveResponse
