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

namespace YMGap.Continuum.BF4WilsonBranchSheafNaturalTransformation

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Categorical
open YMGap.Categorical.ScaleSheaf
open YMGap.Constructive
open YMGap.Constructive.CReal
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

/-- The branch arrow in the presheaf topos `Type^(ScaleCat.op)`.  Naturality
states that scale refinement and branch compilation commute; both are the
identity on the already-common completed carrier. -/
def nontrivialityToGap : NatTrans nontrivialityPresheaf gapPresheaf where
  app := fun _ => NontrivialityFiber.toGap
  naturality := fun _ => rfl

theorem branch_arrow_preserves_probe (n : Nat) (e : NontrivialityFiber) :
    (nontrivialityToGap.app n e).probe = e.probe := rfl

theorem branch_arrow_preserves_orthogonality
    (n : Nat) (e : NontrivialityFiber) :
    (nontrivialityToGap.app n e).probe_vacuum_orthogonal =
      e.probe_vacuum_orthogonal := rfl

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
#print axioms nontrivialityToGap
#print axioms branch_arrow_preserves_probe
#print axioms branch_arrow_preserves_orthogonality
#print axioms currentGap_strict_two_step

end YMGap.Continuum.BF4WilsonBranchSheafNaturalTransformation
