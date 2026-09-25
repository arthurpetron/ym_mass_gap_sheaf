/-
# The fixed-spacing branch arrow in the presheaf topos

The nontriviality and gap branches meet on the same completed `UnionCompletion`.
The nontriviality side supplies a nonzero vacuum-orthogonal probe with a
positive two-step response.  The gap side consumes the *same* orthogonality
fact to obtain the strict two-step form bound.  This file makes that typed
implication a natural transformation between constant presheaves on the scale
site.

This is a genuine branch arrow in `Type^(ScaleCat.op)`: every scale has the
same proof-relevant fiber, and refinement maps are identities because the
carrier is already the common completed union.  It is not a sheaf-gluing
theorem, a canonical OS/GNS identification, or a spacing/continuum result.
The missing changing-spacing comparison therefore remains explicit.
-/

import YMGap.Categorical.Core
import YMGap.Categorical.ScaleSheaf
import YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
import YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
import YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
import YMGap.Continuum.FiniteSizeGeometricSum
import YMGap.Continuum.QuaternionHaarCharacterInterval
import YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap
import YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration

namespace YMGap.Continuum.BF4WilsonBranchSheafNaturalTransformation

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Categorical
open YMGap.Categorical.ScaleSheaf
open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef
  (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
  (completed_twoStep_form_gap)
open YMGap.Continuum.BF4WilsonSpatialUnionResponseLower
  (unitExcitation_even_lower)
open YMGap.Continuum.BF4WilsonSpatialUnionNormalizedExcitation
  (rayleighFloor unitExcitation unitExcitation_orthogonal)
open YMGap.Continuum.BF4WilsonSpatialUnionResolventResponse
  (unitExcitation_ne_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
  (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate
  (existingNome_entropyRate)
open YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap
  (currentRate currentTransferMass currentTransferMass_pos
    currentTransferLogReduction currentTransferMass_log_pin)
open YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration
  (CurrentSpacing currentPhysicalRate currentPhysicalRate_posEv
    currentPhysicalRate_log_pin)


local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate
local notation "V" => UnionCompletion nome_pos nome_lt_one hsmall hd hs
local notation "B" => completedInner nome_pos nome_lt_one hsmall hd hs
local notation "T" => completedTime nome_pos nome_lt_one hsmall hd hs
local notation "U" => completedUnit nome_pos nome_lt_one hsmall hd hs
local notation "Z" => completedZero nome_pos nome_lt_one hsmall hd hs

/-! ## The two branch fibers -/

/-- A nontriviality-side section at the current fixed spacing.  The response
floor and nonzero field are retained; the vacuum-orthogonality field is the
typed datum that permits passage to the gap branch. -/
structure NontrivialityFiber : Type 2 where
  probe : V
  probe_ne_zero : probe ≠ Z
  probe_vacuum_orthogonal : B probe U = RCzero
  probe_response_floor :
    RCle (Quotient.mk crealSetoid (ofQ' rayleighFloor))
      (B probe (T 2 probe))

/-- A gap-side section on the same completed carrier.  Its strict form bound
is the EVERY-centered-state consumer, specialized to this section's probe. -/
structure GapFiber : Type 2 where
  probe : V
  probe_vacuum_orthogonal : B probe U = RCzero
  probe_strict_two_step :
    RCle (B probe (T 2 probe))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (B probe probe))

/-- A gap-side section enriched with the constructive dimensionless transfer
mass.  The mass is the exact positive `-log(currentRate)` of the fixed
two-step rate; no lattice-spacing conversion is included. -/
structure DimensionlessMassFiber : Type 2 where
  probe : V
  probe_vacuum_orthogonal : B probe U = RCzero
  probe_strict_two_step :
    RCle (B probe (T 2 probe))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (B probe probe))
  transfer_mass : CReal
  transfer_mass_positive : CReal.IsPositive transfer_mass
  transfer_mass_log_pin : CReal.Equiv transfer_mass
      (CReal.neg (CReal.log (CReal.ofQ' currentRate)
        currentTransferLogReduction))

/-- A fixed-spacing physical-rate section on the same completed carrier.  The
spacing is an explicit witness, and `physical_rate_exact` prevents this fiber
from silently changing the rate.  This is a per-spacing calibration arrow,
not a uniform continuum family. -/
structure SpacingCalibratedMassFiber (A : CurrentSpacing) : Type 2 where
  probe : V
  probe_vacuum_orthogonal : B probe U = RCzero
  probe_strict_two_step :
    RCle (B probe (T 2 probe))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (B probe probe))
  physical_rate : CReal
  physical_rate_exact : physical_rate = currentPhysicalRate A
  physical_rate_posEv : PosEv physical_rate
  physical_rate_log_pin : CReal.Equiv physical_rate
      (CReal.mul
        (CReal.neg (CReal.log (CReal.ofQ' currentRate)
          currentTransferLogReduction))
        (CReal.ofQ'
          (YMGap.Continuum.BF4WilsonSpatialUnionPhysicalCalibration.spacingReciprocal A)))

/-! ## The branch compiler -/

/-- The shared-carrier branch compiler.  It keeps the probe and its
orthogonality proof, and derives the strict gap from the existing completed
gap theorem.  The positive response is not used to fake an EVERY-state gap;
it remains visible in the source fiber as an independent nontriviality datum.
-/
def NontrivialityFiber.toGap (e : NontrivialityFiber) : GapFiber where
  probe := e.probe
  probe_vacuum_orthogonal := e.probe_vacuum_orthogonal
  probe_strict_two_step :=
    completed_twoStep_form_gap nome_pos nome_lt_one hsmall hd hs e.probe
      e.probe_vacuum_orthogonal

/-- The gap-to-mass compiler retains the same probe and strict estimate and
adds only the already checked fixed-spacing logarithmic certificate. -/
def GapFiber.toDimensionlessMass (g : GapFiber) : DimensionlessMassFiber where
  probe := g.probe
  probe_vacuum_orthogonal := g.probe_vacuum_orthogonal
  probe_strict_two_step := g.probe_strict_two_step
  transfer_mass := currentTransferMass
  transfer_mass_positive := currentTransferMass_pos
  transfer_mass_log_pin := currentTransferMass_log_pin

/-- The dimensionless certificate feeds the exact fixed-spacing physical-rate
calibration while preserving the same probe and completed carrier. -/
def DimensionlessMassFiber.toSpacingCalibratedMass
    (A : CurrentSpacing) (m : DimensionlessMassFiber) :
    SpacingCalibratedMassFiber A where
  probe := m.probe
  probe_vacuum_orthogonal := m.probe_vacuum_orthogonal
  probe_strict_two_step := m.probe_strict_two_step
  physical_rate := currentPhysicalRate A
  physical_rate_exact := rfl
  physical_rate_posEv := currentPhysicalRate_posEv A
  physical_rate_log_pin := currentPhysicalRate_log_pin A

/-- The concrete current Wilson probe inhabits the nontriviality fiber. -/
def currentNontriviality : NontrivialityFiber where
  probe := unitExcitation
  probe_ne_zero := unitExcitation_ne_zero
  probe_vacuum_orthogonal := unitExcitation_orthogonal
  probe_response_floor := by
    exact unitExcitation_even_lower 1

/-- The corresponding fixed-spacing gap section, obtained by the branch
compiler rather than by a new carrier or a new analytic estimate. -/
def currentGap : GapFiber := currentNontriviality.toGap

/-! ## Presheaves and the natural transformation -/

/-- Constant presheaf of nontriviality sections on the scale site. -/
def nontrivialityPresheaf : Presheaf ScaleCat TypeCat where
  obj := fun _ => NontrivialityFiber
  map := fun _ => fun e => e
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Constant presheaf of gap sections on the scale site. -/
def gapPresheaf : Presheaf ScaleCat TypeCat where
  obj := fun _ => GapFiber
  map := fun _ => fun g => g
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Constant presheaf of dimensionless fixed-spacing mass sections. -/
def dimensionlessMassPresheaf : Presheaf ScaleCat TypeCat where
  obj := fun _ => DimensionlessMassFiber
  map := fun _ => fun m => m
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Constant presheaf of exact fixed-spacing physical-rate sections.  The
spacing witness is fixed externally; changing-spacing comparison remains an
explicit later obligation. -/
def spacingCalibratedMassPresheaf (A : CurrentSpacing) :
    Presheaf ScaleCat TypeCat where
  obj := fun _ => SpacingCalibratedMassFiber A
  map := fun _ => fun e => e
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The branch arrow in the presheaf topos `Type^(ScaleCat.op)`.  Naturality
states that scale refinement and branch compilation commute; both are the
identity on the already-common completed carrier. -/
def nontrivialityToGap : NatTrans nontrivialityPresheaf gapPresheaf where
  app := fun _ => NontrivialityFiber.toGap
  naturality := fun _ => rfl

/-- The second branch arrow in the presheaf topos: a completed gap section
feeds the constructive dimensionless logarithmic mass section. -/
def gapToDimensionlessMass : NatTrans gapPresheaf dimensionlessMassPresheaf where
  app := fun _ => GapFiber.toDimensionlessMass
  naturality := fun _ => rfl

/-- The fixed-spacing calibration arrow in the presheaf topos. -/
def dimensionlessMassToSpacingCalibratedMass (A : CurrentSpacing) :
    NatTrans dimensionlessMassPresheaf (spacingCalibratedMassPresheaf A) where
  app := fun _ => DimensionlessMassFiber.toSpacingCalibratedMass A
  naturality := fun _ => rfl

/-- The contracted branch chain in the presheaf topos. -/
def nontrivialityToDimensionlessMass :
    NatTrans nontrivialityPresheaf dimensionlessMassPresheaf :=
  YMGap.Categorical.natTransComp nontrivialityToGap gapToDimensionlessMass

/-- Paste the gap branch through the dimensionless mass and into the explicit
physical-rate fiber. -/
def gapToSpacingCalibratedMass (A : CurrentSpacing) :
    NatTrans gapPresheaf (spacingCalibratedMassPresheaf A) :=
  YMGap.Categorical.natTransComp gapToDimensionlessMass
    (dimensionlessMassToSpacingCalibratedMass A)

/-- The full checked nontriviality -> gap -> calibrated-rate chain. -/
def nontrivialityToSpacingCalibratedMass (A : CurrentSpacing) :
    NatTrans nontrivialityPresheaf (spacingCalibratedMassPresheaf A) :=
  YMGap.Categorical.natTransComp nontrivialityToGap
    (gapToSpacingCalibratedMass A)

theorem branch_arrow_preserves_probe (n : Nat) (e : NontrivialityFiber) :
    (nontrivialityToGap.app n e).probe = e.probe := rfl

theorem branch_arrow_preserves_orthogonality
    (n : Nat) (e : NontrivialityFiber) :
    (nontrivialityToGap.app n e).probe_vacuum_orthogonal =
      e.probe_vacuum_orthogonal := rfl

theorem gap_mass_arrow_preserves_probe (n : Nat) (g : GapFiber) :
    (gapToDimensionlessMass.app n g).probe = g.probe := rfl

theorem gap_mass_arrow_preserves_rate (n : Nat) (g : GapFiber) :
    (gapToDimensionlessMass.app n g).transfer_mass = currentTransferMass := rfl

theorem calibration_arrow_preserves_probe
    (A : CurrentSpacing) (n : Nat) (m : DimensionlessMassFiber) :
    ((dimensionlessMassToSpacingCalibratedMass A).app n m).probe = m.probe := rfl

theorem calibration_arrow_exposes_exact_rate
    (A : CurrentSpacing) (n : Nat) (m : DimensionlessMassFiber) :
    ((dimensionlessMassToSpacingCalibratedMass A).app n m).physical_rate =
      currentPhysicalRate A := rfl

theorem calibration_arrow_preserves_rate_pin
    (A : CurrentSpacing) (n : Nat) (m : DimensionlessMassFiber) :
    ((dimensionlessMassToSpacingCalibratedMass A).app n m).physical_rate_log_pin =
      currentPhysicalRate_log_pin A := rfl

theorem branch_chain_preserves_probe (n : Nat) (e : NontrivialityFiber) :
    (nontrivialityToDimensionlessMass.app n e).probe = e.probe := by
  change (GapFiber.toDimensionlessMass (NontrivialityFiber.toGap e)).probe = e.probe
  rfl

theorem currentGap_strict_two_step :
    RCle (B currentGap.probe (T 2 currentGap.probe))
      (RCmul (Quotient.mk crealSetoid (ofQ' (twoStepRate nome hd)))
        (B currentGap.probe currentGap.probe)) :=
  currentGap.probe_strict_two_step

#print axioms NontrivialityFiber.toGap
#print axioms currentNontriviality
#print axioms currentGap
#print axioms nontrivialityPresheaf
#print axioms gapPresheaf
#print axioms dimensionlessMassPresheaf
#print axioms SpacingCalibratedMassFiber
#print axioms spacingCalibratedMassPresheaf
#print axioms nontrivialityToGap
#print axioms gapToDimensionlessMass
#print axioms nontrivialityToDimensionlessMass
#print axioms DimensionlessMassFiber.toSpacingCalibratedMass
#print axioms dimensionlessMassToSpacingCalibratedMass
#print axioms gapToSpacingCalibratedMass
#print axioms nontrivialityToSpacingCalibratedMass
#print axioms branch_arrow_preserves_probe
#print axioms branch_arrow_preserves_orthogonality
#print axioms gap_mass_arrow_preserves_probe
#print axioms gap_mass_arrow_preserves_rate
#print axioms calibration_arrow_preserves_probe
#print axioms calibration_arrow_exposes_exact_rate
#print axioms calibration_arrow_preserves_rate_pin
#print axioms branch_chain_preserves_probe
#print axioms currentGap_strict_two_step

end YMGap.Continuum.BF4WilsonBranchSheafNaturalTransformation
