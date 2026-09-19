/-
# Fixed-spacing physical calibration of the current Wilson rate

The current completed Wilson carrier has a checked dimensionless transfer
mass `currentTransferMass = -log(currentRate)`.  This module adds only the
smallest missing dimensional datum: one explicit positive lattice spacing.
It constructs the corresponding rate

    currentTransferMass / a

as a constructive `CReal`, and proves eventual strict positivity in the
library's `PosEv` interface.  The spacing is
not claimed to be the Yang--Mills continuum spacing family, and no uniform
`a → 0` floor, canonical OS/GNS identification, or continuum theorem is
asserted.  The point is to make the forward fixed-carrier result and the
backward physical-rate consumer meet at a named, non-vacuous calibration
certificate.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap
import YMGap.Continuum.FullLogMarginLower
import YMGap.Continuum.PhysicalSeparatorLogRate

namespace YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.FullLogMarginLower
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap

/-! ## 1. The explicit dimensional input -/

/-- A single positive spacing for the current fixed-spacing carrier.  This is
deliberately data, not an inferred continuum trajectory. -/
structure CurrentSpacing : Type where
  a : Q'
  a_pos : (0 : Q') < a

/-- The reciprocal of the supplied positive spacing. -/
def spacingReciprocal (A : CurrentSpacing) : Q' :=
  Q'.recipPos A.a A.a_pos

theorem spacingReciprocal_pos (A : CurrentSpacing) :
    (0 : Q') < spacingReciprocal A :=
  Q'.recipPos_pos A.a A.a_pos

/-! ## 2. Reciprocal spacing order -/

/- A small local reciprocal-order lemma keeps the calibration module
   self-contained.  The proof is the positive-denominator cross-product
   calculation; no general division or classical order principle is used. -/
theorem spacingReciprocal_antitone {A B : CurrentSpacing} (hAB : A.a ≤ B.a) :
    spacingReciprocal B ≤ spacingReciprocal A := by
  show (Q'.recipPos B.a B.a_pos).num *
      ((Q'.recipPos A.a A.a_pos).den : Int) ≤
    (Q'.recipPos A.a A.a_pos).num *
      ((Q'.recipPos B.a B.a_pos).den : Int)
  rw [Q'.recipPos_num, Q'.recipPos_den,
      Q'.recipPos_num, Q'.recipPos_den]
  have hcross : A.a.num * (B.a.den : Int) ≤
      B.a.num * (A.a.den : Int) := hAB
  have hleft : (B.a.den : Int) * A.a.num =
      A.a.num * (B.a.den : Int) := Int.mul_comm _ _
  have hright : (A.a.den : Int) * B.a.num =
      B.a.num * (A.a.den : Int) := Int.mul_comm _ _
  rw [hleft, hright]
  exact hcross

/-- The exact dimensionful rate obtained from the current transfer mass. -/
def currentPhysicalRate (A : CurrentSpacing) : CReal :=
  CReal.mul currentTransferMass (CReal.ofQ' (spacingReciprocal A))

/-! ## 2. Positivity in the eventual-order interface -/

/-- The reciprocal spacing, embedded in `CReal`, is eventually positive. -/
theorem spacingReciprocal_posEv (A : CurrentSpacing) :
    PosEv (CReal.ofQ' (spacingReciprocal A)) := by
  refine posEv_of_eventually (spacingReciprocal_pos A) ⟨0, ?_⟩
  intro n hn
  exact Q'.le_refl' _

/-- The calibrated physical rate is strictly positive in the eventual order. -/
theorem currentPhysicalRate_posEv (A : CurrentSpacing) :
  PosEv (currentPhysicalRate A) := by
  exact posEv_mul (posEv_of_isPositive currentTransferMass_pos)
    (spacingReciprocal_posEv A)

/-! ## 3. Same-mass spacing monotonicity -/

/- The current transfer mass is positive, hence nonnegative in the eventual
   order.  This is the order witness needed to scale reciprocal-spacing
   inequalities without cancelling a potentially noncomputable real. -/
theorem currentTransferMass_nonnegative :
    CReal.leEv CReal.czero currentTransferMass := by
  obtain ⟨ε, hε, N, hN⟩ := eventually_ge_of_posEv
    (posEv_of_isPositive currentTransferMass_pos)
  intro δ hδ
  refine ⟨N, fun n hn => ?_⟩
  have happrox := hN n hn
  have happrox0 : (0 : Q') ≤ currentTransferMass.approx n :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt hε) happrox
  have hzero : (0 : Q') ≤ currentTransferMass.approx n + δ :=
    Q'.zero_le_add _ _ happrox0 (Q'.le_of_lt hδ)
  exact hzero

/-! ## 4. Explicit current mass floor -/

/-- The elementary rational margin of the current strict rate is an explicit
constructive lower floor for its exact logarithmic transfer mass. -/
def currentRateMargin : Q' := rationalMargin currentRate

theorem currentRateMargin_pos : (0 : Q') < currentRateMargin := by
  exact rationalMargin_pos currentRate currentRate_lt_one

theorem currentTransferMass_margin_floor :
    CReal.leEv (CReal.ofQ' currentRateMargin) currentTransferMass := by
  unfold currentRateMargin currentTransferMass
  exact rationalMargin_le_hamiltonianGapRealAll
    currentRate currentRateBinExp currentRate_num_pos

/-! ## 5. Uniform fixed-carrier floor under a spacing ceiling -/

/-- A positive spacing ceiling produces a positive rational physical-rate
floor for every current-carrier spacing below that ceiling. -/
theorem currentPhysicalRate_floor_pos
    (ceiling : Q') (hceiling : (0 : Q') < ceiling) :
    (0 : Q') < currentRateMargin * Q'.recipPos ceiling hceiling := by
  exact Q'.mul_pos currentRateMargin_pos
    (Q'.recipPos_pos ceiling hceiling)

/- The floor is uniform over the supplied spacing inequality, while retaining
  the exact current transfer mass and the same completed carrier. -/
theorem currentPhysicalRate_floor_of_spacing_le
    (A : CurrentSpacing) (ceiling : Q') (hceiling : (0 : Q') < ceiling)
    (hA : A.a ≤ ceiling) :
    CReal.leEv
      (CReal.ofQ' (currentRateMargin * Q'.recipPos ceiling hceiling))
      (currentPhysicalRate A) := by
  let C : CurrentSpacing := ⟨ceiling, hceiling⟩
  have hrecip : spacingReciprocal C ≤ spacingReciprocal A := by
    exact spacingReciprocal_antitone hA
  have hrecipC :
      CReal.leEv (CReal.ofQ' (spacingReciprocal C))
        (CReal.ofQ' (spacingReciprocal A)) := by
    exact CReal.leEv_ofQ'_of_approx_ge (fun _ => hrecip)
  have hscaled := CReal.leEv_smul_nonneg
    (Q'.le_of_lt (spacingReciprocal_pos C))
    currentTransferMass_margin_floor
  have hmassMon :
      CReal.leEv
        (CReal.mul currentTransferMass (CReal.ofQ' (spacingReciprocal C)))
        (currentPhysicalRate A) := by
    exact CReal.leEv_mul_nonneg_left currentTransferMass_nonnegative hrecipC
  have hmassMon_swapped :
      CReal.leEv
        (CReal.mul (CReal.ofQ' (spacingReciprocal C)) currentTransferMass)
        (currentPhysicalRate A) := by
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (CRealAlg.cmul_comm (CReal.ofQ' (spacingReciprocal C))
          currentTransferMass)) hmassMon
  have htotal :
      CReal.leEv
        (CReal.mul (CReal.ofQ' (spacingReciprocal C))
          (CReal.ofQ' currentRateMargin))
        (currentPhysicalRate A) :=
    CReal.leEv_trans hscaled hmassMon_swapped
  have hleft :
      CReal.Equiv
        (CReal.ofQ' (currentRateMargin * Q'.recipPos ceiling hceiling))
        (CReal.mul (CReal.ofQ' (spacingReciprocal C))
          (CReal.ofQ' currentRateMargin)) := by
    refine CReal.Equiv.trans ?_
      (CRealAlg.cmul_comm (CReal.ofQ' currentRateMargin)
        (CReal.ofQ' (spacingReciprocal C)))
    exact CRealAlg.ofQ'_mul currentRateMargin
      (Q'.recipPos ceiling hceiling)
  exact (CReal.leEv_congr hleft (CReal.Equiv.refl _)).mpr htotal

/-! ## 6. Fixed-mass obstruction at vanishing spacing -/

/-- A positive spacing schedule with an explicit modulus of convergence to zero.
This is only a schedule for the already fixed current transfer mass; it is not
an original changing-coupling Wilson family. -/
structure CurrentSpacingSchedule : Type where
  a : Nat → Q'
  a_pos : ∀ j, (0 : Q') < a j
  spacingModulus : Q' → Nat
  spacingTendsToZero : ∀ ε, (0 : Q') < ε → ∀ j,
    spacingModulus ε ≤ j → a j ≤ ε

/-- The explicit rational lower floor attached to one scheduled spacing. -/
def currentRateFloorAt (S : CurrentSpacingSchedule) (j : Nat) : Q' :=
  currentRateMargin * Q'.recipPos (S.a j) (S.a_pos j)

/-- The fixed positive dimensionless mass makes the scheduled physical-rate
floors cofinal as the spacing tends to zero.  Thus a fixed current rate cannot
supply a finite continuum physical-mass ceiling along such a schedule. -/
theorem currentRateFloor_cofinal
    (S : CurrentSpacingSchedule) (U : Q') (hU : (0 : Q') ≤ U) :
    ∃ j, U ≤ currentRateFloorAt S j := by
  let target : Q' := (1 : Q') + U
  have htarget : (0 : Q') < target := by
    exact Q'.pos_add_nonneg (by decide) hU
  let epsilon : Q' := Q'.divPos currentRateMargin target htarget
  have hepsilon : (0 : Q') < epsilon := by
    exact Q'.divPos_pos currentRateMargin target htarget currentRateMargin_pos
  let j := S.spacingModulus epsilon
  have hAj : S.a j ≤ epsilon := by
    exact S.spacingTendsToZero epsilon hepsilon j (Nat.le_refl _)
  have hmul : target * S.a j ≤ currentRateMargin := by
    have hstep : target * S.a j ≤ target * epsilon :=
      Q'.mul_le_mul_of_nonneg_left (S.a j) epsilon target hAj
        (Q'.le_of_lt htarget)
    have hEq : (target * epsilon).eqv currentRateMargin := by
      exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv target epsilon)
        (Q'.divPos_mul_eqv currentRateMargin target htarget)
    exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hEq)
  have htarget_floor : target ≤ currentRateFloorAt S j := by
    unfold currentRateFloorAt
    exact Q'.le_divPos_of_mul_le currentRateMargin (S.a j)
      (S.a_pos j) hmul
  have hUtarget : U ≤ target := by
    unfold target
    exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg U 1 (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv U 1))
  exact ⟨j, Q'.le_trans' _ _ _ hUtarget htarget_floor⟩

/- A smaller positive spacing gives a larger dimensionful rate for the SAME
   dimensionless transfer mass.  This is a genuine trajectory-comparison
   lemma; it does not supply the missing spacing family or a uniform floor. -/
theorem currentPhysicalRate_mono_spacing {A B : CurrentSpacing}
    (hAB : A.a ≤ B.a) :
    CReal.leEv (currentPhysicalRate B) (currentPhysicalRate A) := by
  have hrecip : spacingReciprocal B ≤ spacingReciprocal A :=
    spacingReciprocal_antitone hAB
  have hrecipC :
      CReal.leEv (CReal.ofQ' (spacingReciprocal B))
        (CReal.ofQ' (spacingReciprocal A)) := by
    exact CReal.leEv_ofQ'_of_approx_ge (fun _ => hrecip)
  change CReal.leEv
    (CReal.mul currentTransferMass
      (CReal.ofQ' (spacingReciprocal B)))
    (CReal.mul currentTransferMass
      (CReal.ofQ' (spacingReciprocal A)))
  exact CReal.leEv_mul_nonneg_left currentTransferMass_nonnegative hrecipC

/-! ## 5. Exact log pin after calibration -/

/-- Calibration preserves the exact logarithmic meaning of the current mass:
the physical rate is the constructive `-log(currentRate)` multiplied by
`1/a`. -/
theorem currentPhysicalRate_log_pin (A : CurrentSpacing) :
    CReal.Equiv (currentPhysicalRate A)
      (CReal.mul
        (CReal.neg (CReal.log (CReal.ofQ' currentRate)
          currentTransferLogReduction))
        (CReal.ofQ' (spacingReciprocal A))) := by
  exact CReal.mul_congr_left currentTransferMass_log_pin

end YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.spacingReciprocal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.spacingReciprocal_pos
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.spacingReciprocal_antitone
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentPhysicalRate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.spacingReciprocal_posEv
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentPhysicalRate_posEv
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentTransferMass_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentPhysicalRate_mono_spacing
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentRateMargin
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentRateMargin_pos
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentTransferMass_margin_floor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.CurrentSpacingSchedule
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentRateFloorAt
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentRateFloor_cofinal
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentPhysicalRate_log_pin
