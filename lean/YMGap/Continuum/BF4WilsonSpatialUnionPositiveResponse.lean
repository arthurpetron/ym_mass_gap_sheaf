/-
# Positive response of the EXISTING completed Wilson union excitation

The actual fixed-base completion map pins every time correlator of the
existing SmallNomeGap.vector to its original Wilson plaquette scalar. The
proved finite-probe/limit equality identifies that scalar with the old
original-action spatial response, without identifying the two vector carriers.
Consequently the already proved lag-three floor applies to THIS Wilson vector.

Positivity of the actual difference and original time contraction bound odd
response by the preceding even response. The full floor therefore also holds
at physical lag two, without an assumption of one-step positivity. The output
returns the existing vector and an explicit positive rational response floor.

This concerns SU(2) at the fixed nome 1/1024 and fixed lattice spacing. It
does not prove continuum survival, a physical mass calibration, full Hilbert
or OS/QFT reconstruction, or the every-compact-simple-group Clay statement.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteTimePin
import YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap
import YMGap.Continuum.BF4WilsonSpatialUnionBilinear
import YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
import YMGap.Continuum.BF4SpatialUnionPositiveResponse
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4WilsonSpatialUnionPositiveResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4WilsonSpatialUnionFixedBase (completionMap_time completedInner_map)
open YMGap.Continuum.BF4WilsonSpatialUnionSmallNomeGap (vector vector_orthogonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteForm (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments
  (centeredTimeMoment centeredVector_time_pairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquetteTimePin
  (centeredTimeMoment_plaquette_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCenteredForm (spatialCenteredMoment)
open YMGap.Continuum.BF4SpatialUnionResponseProbePins (centralProbe)
open YMGap.Continuum.BF4ExactSlabOriginalResponseNumeratorFloor
  (responseFloor responseFloor_positive)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCentralExcitation (origin_physical)
open YMGap.Continuum.BF4SpatialUnionBilinear (rc_add_zero)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

private theorem midpoint_cancel (a b c : RC) :
    RCadd (RCadd b b) (RCsub (RCsub a b) (RCsub b c)) = RCadd a c := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 1) (.var 1))
        (.add (.add (.var 0) (.neg (.var 1)))
          (.neg (.add (.var 1) (.neg (.var 2))))))
      (.add (.var 0) (.var 2)) (by decide)
      (fun | 0 => A.approx n | 1 => B.approx n | _ => C.approx n)))

private theorem half_double (a : RC) : RCscale HalfPow.half (RCadd a a) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half (A.approx n) (A.approx n))
      (ExpNeg.two_halves (A.approx n))))

section General

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

/-- Difference positivity and norm contraction, with no positivity assumption on time. -/
theorem completedTime_form_le (n : Nat) (x : V) :
    RCle (B x (T n x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (RCadd (B x (T n x)) (B x (T n x))))
    (completedInner_nonnegative hw0 hw1 hsmall hd hs
      (completedSub hw0 hw1 hsmall hd hs x (T n x)))
  rw [rc_add_zero, completedInner_sub_left, completedInner_sub_right,
    completedInner_sub_right, completedInner_symm hw0 hw1 hsmall hd hs (T n x) x,
    midpoint_cancel] at h
  have hdouble := RCle_trans h (RCadd_le_add (RCle_refl (B x x))
    (completedInner_time_contraction hw0 hw1 hsmall hd hs n x))
  have hhalf := RCscale_mono (by decide : (0 : Q') ≤ HalfPow.half) hdouble
  simpa only [half_double] using hhalf

/-- Every odd response is bounded above by its preceding even response. -/
theorem odd_response_le_even (n : Nat) (x : V) :
    RCle (B x (T (2*n+1) x)) (B x (T (2*n) x)) := by
  have h := completedTime_form_le hw0 hw1 hsmall hd hs 1 (T n x)
  rw [completedInner_time_balance, completedInner_time_balance,
    ← completedTime_add, ← completedTime_add, ← completedTime_add] at h
  simpa only [Nat.add_assoc, show n+(1+n) = 2*n+1 by omega,
    show n+n = 2*n by omega] using h

theorem lagTwo_floor_of_lagThree (x : V) (floor : RC)
    (hfloor : RCle floor (B x (T 3 x))) : RCle floor (B x (T 2 x)) :=
  RCle_trans hfloor (odd_response_le_even hw0 hw1 hsmall hd hs 1 x)

end General

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs
local notation "p" => plaquette originFace (origin_physical (by decide : 0 < 1))

/-- The already constructed vector, not a new centered vector on another carrier. -/
theorem vector_correlator_pin (n : Nat) :
    B vector (T n vector) = Quotient.mk crealSetoid
      (centeredTimeMoment nome_pos nome_lt_one hsmall hd hs (base := 1) (by decide) n p p) := by
  unfold vector
  rw [← completionMap_time, completedInner_map]
  exact centeredVector_time_pairing nome_pos nome_lt_one hsmall hd hs
    (base := 1) (by decide) n p p

/-- A scalar pin between original observables, not an isomorphism of the two completions. -/
theorem vector_spatial_correlator_pin (n : Nat) :
    B vector (T n vector) = Quotient.mk crealSetoid
      (spatialCenteredMoment nome_pos nome_lt_one 1 hsmall hd hs (by decide)
        n centralProbe centralProbe) :=
  (vector_correlator_pin n).trans (Quotient.sound
    (centeredTimeMoment_plaquette_pin nome_pos nome_lt_one hsmall hd hs
      (base := 1) (by decide) originFace (origin_physical (by decide)) n))

/-- The full original rational floor at physical separation THREE on THIS Wilson vector. -/
theorem lagThree_floor :
    RCle (Quotient.mk crealSetoid (ofQ' responseFloor)) (B vector (T 3 vector)) := by
  rw [vector_spatial_correlator_pin]
  exact BF4SpatialUnionPositiveResponse.spatial_response_floor

/-- The SAME full floor at lag two, without assuming one-step positivity. -/
theorem lagTwo_floor :
    RCle (Quotient.mk crealSetoid (ofQ' responseFloor)) (B vector (T 2 vector)) :=
  lagTwo_floor_of_lagThree nome_pos nome_lt_one hsmall hd hs vector _ lagThree_floor

/-- Both the existing vector and the positive rational floor are returned as data. -/
def positiveResponse : Σ' x : V, Σ' c : Q',
    (x = vector) ×' ((0 : Q') < c) ×' (B x U = RCzero) ×'
      RCle (Quotient.mk crealSetoid (ofQ' c)) (B x (T 2 x)) :=
  ⟨vector, responseFloor, rfl, responseFloor_positive, vector_orthogonal, lagTwo_floor⟩

#print axioms completedTime_form_le
#print axioms odd_response_le_even
#print axioms lagTwo_floor_of_lagThree
#print axioms vector_correlator_pin
#print axioms vector_spatial_correlator_pin
#print axioms lagThree_floor
#print axioms lagTwo_floor
#print axioms positiveResponse

end YMGap.Continuum.BF4WilsonSpatialUnionPositiveResponse
