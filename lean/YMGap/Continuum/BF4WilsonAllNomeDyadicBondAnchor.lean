/-
# Positive-time anchored Wilson squares in the ORIGINAL physical bond completion

The constructed norm-one dyadic excitation u has explicit original Cauchy
rows. Advancing it by side(scale)+lag, a positive original integer time,
constructs an exact time-range witness and then actual physical bond rows.
Their bond value is this SAME time image, with Gram kernel R(2*side+i+j).

This is positive-time anchoring, not another normalization or carrier. Its
norm may decrease with scale. It supplies neither changing-family scalar
convergence nor a positive limiting norm, canonical continuum OS root,
field identification, physical time calibration or a Yang--Mills mass gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
import YMGap.Continuum.BF4WilsonAllNomeBondOSTime
import YMGap.Continuum.BF4WilsonAllNomePositiveLagIncrement

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector (centeredStream)
open YMGap.Continuum.BF4WilsonAllNomeRealScalarCauchy (realScalarCauchy)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion Rows rowSetoid fromSectorRep fromSectorRep_limit toSectorRep
    bondCompletedInner bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_inner bondValue_distance bondValue_ofSource
    bondAction bondAction_value vacuum)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (image_unit)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (dyadicTime)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (positiveAction_original)
open YMGap.Continuum.BF4DyadicWilsonSquareSpectatorResponse
  (squareResponseFraction squareResponseFraction_positive)
open YMGap.Continuum.BF4WilsonAllNomePositiveLagIncrement
  (dyadicUnit_positiveLag_increment_bound dyadicUnit_positiveLag_spacing_bound
    dyadicUnit_positiveLag_increment_small incrementRadius)

local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "R" n:arg => dyadicUnitResponse hw0 hw1 scale width hwidth n
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- Explicit rows of the very unit excitation, before any range quotient. -/
def unitRepresentative : (D).Cauchy :=
  realScalarCauchy hw0 hw1
    (dyadicNormalizer hw0 hw1 scale width hwidth)
    (dyadicNormalizerCauchy hw0 hw1 scale width hwidth)
    (centeredStream hw0 hw1 (loopState (paddedSquare scale width hwidth)))

theorem unitRepresentative_pin :
    Class (unitRepresentative hw0 hw1 scale width hwidth) = u := rfl

/-- Exact supplied preimage: no inverse transfer or representative choice. -/
def anchoredPreimage (lag : Nat) : (D).Cauchy :=
  (timeNonexpansive hw0 hw1 (side scale+lag-1)).mapCauchy
    (unitRepresentative hw0 hw1 scale width hwidth)

/-- The existing range constructor keeps an exact T(1) preimage and modulus. -/
def anchoredSector (lag : Nat) : BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width) :=
  BF4WilsonAllNomeTimeSector.fromTime hw0 hw1
    (anchoredPreimage hw0 hw1 scale width hwidth lag)

theorem anchoredSector_pin (lag : Nat) :
    (anchoredSector hw0 hw1 scale width hwidth lag).val = T (side scale+lag) u := by
  change T 1 (T (side scale+lag-1)
    (Class (unitRepresentative hw0 hw1 scale width hwidth))) = _
  rw [unitRepresentative_pin, ← completedTime_add]
  exact congrArg (fun n => T n u) (by have h := side_positive scale; omega)

/-- Computed finite physical bond-source rows and their OWN all-tail modulus. -/
def anchoredBondRows (lag : Nat) : Rows hw0 hw1 (width := width) :=
  fromSectorRep hw0 hw1 (anchoredSector hw0 hw1 scale width hwidth lag)

/-- Actual point in the EXISTING physical bond completion, not a new carrier. -/
def anchoredBondExcitation (lag : Nat) : BondCompletion hw0 hw1 (width := width) :=
  Quotient.mk (rowSetoid hw0 hw1) (anchoredBondRows hw0 hw1 scale width hwidth lag)

local notation "x" j:arg => anchoredBondExcitation hw0 hw1 scale width hwidth j

theorem anchoredBond_value (lag : Nat) : bondValue hw0 hw1 (x lag) = T (side scale+lag) u := by
  change (toSectorRep hw0 hw1 (fromSectorRep hw0 hw1
    (anchoredSector hw0 hw1 scale width hwidth lag))).val = _
  rw [fromSectorRep_limit, anchoredSector_pin]

/-- All Gram entries are the SAME normalized original connected response. -/
theorem anchoredBond_pairing (i j : Nat) :
    bondCompletedInner hw0 hw1 (x i) (x j) =
      Quotient.mk crealSetoid (R (2*side scale+i+j)) := by
  rw [bondValue_inner, anchoredBond_value, anchoredBond_value, completedInner_time_sum]
  rw [show (side scale+i)+(side scale+j)=2*side scale+i+j by omega]
  exact dyadicUnitResponse_pin hw0 hw1 scale width hwidth _

/-- Original vacuum orthogonality is preserved in the physical bond form. -/
theorem anchoredBond_vacuum_orthogonal (lag : Nat) :
    bondCompletedInner hw0 hw1 (vacuum hw0 hw1 (width := width)) (x lag) = RCzero := by
  rw [bondValue_inner, vacuum, bondValue_ofSource, image_unit, anchoredBond_value]
  exact completedTime_preserves_vacuumComplement hw0 hw1 _ u
    (dyadicUnitExcitation hw0 hw1 scale width hwidth).property

/-- Existing physical positive-time action agrees with the anchored integer orbit. -/
theorem anchoredBond_time (lag j : Nat) (hj : 0 < j) :
    bondAction hw0 hw1 (dyadicTime ⟨0,j⟩ hj) (x lag) = x (lag+j) := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  rw [bondAction_value, anchoredBond_value, positiveAction_original hw0 hw1 j hj,
    ← completedTime_add, anchoredBond_value]
  exact congrArg (fun n => T n u) (by omega)

/-- Quadratic norm increments on the literal original physical bond points. -/
theorem anchoredBond_increment_bound (lag j : Nat) :
    RCle (bondCompletedDistance hw0 hw1 (x (lag+j)) (x lag))
      (Rq ((Q'.ofNat j*Q'.invSucc (side scale+lag))*
        (Q'.ofNat j*Q'.invSucc (side scale+lag)))) := by
  rw [bondValue_distance, anchoredBond_value, anchoredBond_value]
  rw [show side scale+(lag+j)=(side scale+lag)+j by omega]
  exact dyadicUnit_positiveLag_increment_bound hw0 hw1 scale hwidth _ j

/-- Nome/width-independent bound at assigned geometric time, on this SAME
bond completion. This does not identify carriers at different scales. -/
theorem anchoredBond_spacing_bound (lag j : Nat) :
    RCle (bondCompletedDistance hw0 hw1 (x (lag+j)) (x lag))
      (Rq ((Q'.ofNat j*spacing scale)*(Q'.ofNat j*spacing scale))) := by
  rw [bondValue_distance, anchoredBond_value, anchoredBond_value]
  rw [show side scale+(lag+j)=(side scale+lag)+j by omega]
  exact dyadicUnit_positiveLag_spacing_bound hw0 hw1 scale hwidth _ j (by omega)

/-- Explicit uniform integer-grid continuity at positive assigned anchor time.
The computed radius requires no raw-unit continuity at time zero. -/
theorem anchoredBond_increment_small (epsilon : Q') (he : (0 : Q') < epsilon)
    (lag j : Nat) (hj : Q'.ofNat j*spacing scale ≤ incrementRadius epsilon) :
    RCle (bondCompletedDistance hw0 hw1 (x (lag+j)) (x lag)) (Rq epsilon) := by
  rw [bondValue_distance, anchoredBond_value, anchoredBond_value]
  rw [show side scale+(lag+j)=(side scale+lag)+j by omega]
  exact dyadicUnit_positiveLag_increment_small hw0 hw1 scale hwidth
    epsilon he _ j (by omega) hj

/-- Explicit ORIGINAL positive norm floor at fixed nome, scale and lag.
Its known collapsing certificate is not a changing-family survival bound. -/
theorem anchoredBond_norm_floor (lag : Nat) :
    RCle (Rq ((squareResponseFraction hw0 hw1 scale)^(2*side scale+lag+lag)))
      (bondCompletedInner hw0 hw1 (x lag) (x lag)) := by
  rw [anchoredBond_pairing]
  exact dyadicUnitResponse_geometric_floor hw0 hw1 scale width hwidth _

private theorem power_positive (q : Q') (hq : (0 : Q') < q) :
    ∀ n : Nat, (0 : Q') < q^n
  | 0 => by change (0 : Q') < 1; decide
  | n+1 => Q'.mul_pos hq (power_positive q hq n)

theorem anchoredBond_norm_ne_zero (lag : Nat) :
    bondCompletedInner hw0 hw1 (x lag) (x lag) ≠ RCzero := by
  intro hz
  have h := anchoredBond_norm_floor hw0 hw1 scale width hwidth lag
  rw [hz] at h
  have hle : (squareResponseFraction hw0 hw1 scale)^(2*side scale+lag+lag) ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N,hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le
      (power_positive _ (squareResponseFraction_positive hw0 hw1 scale) _) hle)

#print axioms unitRepresentative
#print axioms unitRepresentative_pin
#print axioms anchoredPreimage
#print axioms anchoredSector
#print axioms anchoredSector_pin
#print axioms anchoredBondRows
#print axioms anchoredBondExcitation
#print axioms anchoredBond_value
#print axioms anchoredBond_pairing
#print axioms anchoredBond_vacuum_orthogonal
#print axioms anchoredBond_time
#print axioms anchoredBond_increment_bound
#print axioms anchoredBond_spacing_bound
#print axioms anchoredBond_increment_small
#print axioms anchoredBond_norm_floor
#print axioms anchoredBond_norm_ne_zero

end YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchor
