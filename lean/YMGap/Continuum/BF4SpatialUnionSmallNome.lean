/-
# A closed small-nome instance of the actual spatial union sector

At the already certified nome 1/1024, all analytic guards are supplied by
existing proofs. The actual completed form and physical time have a nonzero
unit-orthogonal plaquette excitation and the universal two-step bound below.
This is one discrete small-nome instance, not a continuum or all-nome claim.
-/

import YMGap.Continuum.BF4SpatialUnionUnitComplement
import YMGap.Continuum.BF4SpatialUnionExcitation
import YMGap.Continuum.BF4ExactSlabSummableCoreRate

namespace YMGap.Continuum.BF4SpatialUnionSmallNome

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4SpatialUnion (zeroStage)
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4SpatialUnionUnitComplement
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate

abbrev Completion := UnionCompletion nome_pos nome_lt_one hsmall hd hs
abbrev Sector := UnitComplement nome_pos nome_lt_one hsmall hd hs

def pairing : Completion → Completion → RC :=
  completedInner nome_pos nome_lt_one hsmall hd hs

def unit : Completion := completedUnit nome_pos nome_lt_one hsmall hd hs

def time (n : Nat) : Sector → Sector :=
  unitComplementTime nome_pos nome_lt_one hsmall hd hs n

def rate : Q' := twoStepRate nome hd

theorem rate_positive : (0 : Q') < rate := twoStepRate_positive nome_pos hd
theorem rate_lt_one : rate < (1 : Q') := twoStepRate_lt_one nome_pos hd hs

/-- Computed Type-valued witness in the actual completed unit complement. -/
def excitation : Sector :=
  ⟨BF4SpatialUnionExcitation.excitation nome_pos nome_lt_one hsmall hd hs,
    BF4SpatialUnionExcitation.excitation_orthogonal nome_pos nome_lt_one hsmall hd hs⟩

theorem excitation_ne_zero :
    excitation.val ≠ embedStage nome_pos nome_lt_one hsmall hd hs zeroStage :=
  BF4SpatialUnionExcitation.excitation_ne_zero nome_pos nome_lt_one hsmall hd hs

theorem excitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio nome)))
      (pairing excitation.val excitation.val) :=
  BF4SpatialUnionExcitation.excitation_norm_floor nome_pos nome_lt_one hsmall hd hs

/-- The bound quantifies over the whole actual unit complement, not just the witness. -/
theorem twoStep_gap (x : Sector) :
    RCle (pairing x.val (time 2 x).val)
      (RCmul (Quotient.mk crealSetoid (ofQ' rate)) (pairing x.val x.val)) :=
  unitComplement_twoStep_form_gap nome_pos nome_lt_one hsmall hd hs x

#print axioms Completion
#print axioms Sector
#print axioms pairing
#print axioms unit
#print axioms time
#print axioms rate
#print axioms rate_positive
#print axioms rate_lt_one
#print axioms excitation
#print axioms excitation_ne_zero
#print axioms excitation_norm_floor
#print axioms twoStep_gap

end YMGap.Continuum.BF4SpatialUnionSmallNome
