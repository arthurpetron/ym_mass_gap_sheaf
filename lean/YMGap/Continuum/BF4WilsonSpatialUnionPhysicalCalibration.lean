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
import YMGap.Continuum.PhysicalSeparatorLogRate

namespace YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum.TuranPositivity
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

/-! ## 4. Exact log pin after calibration -/

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
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.currentPhysicalRate_log_pin
