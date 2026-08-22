/-
# Cofinal finite-prefix rates characterize BF4 cross-carrier uniformity

The constructed prefix rates are monotone located maxima.  Therefore one need
not bound every prefix directly: it is enough to bound them by one strict
rational rate along any constructively cofinal schedule.  Every individual
base then lies below a selected prefix and inherits the same rate.

This module packages that weakest schedule-shaped input and compiles it to the
all-carrier constructed-rate bound, the cofinal moving-centered vacuum-sector
gap, and the Bishop-real limit inequality.  Conversely, an all-carrier rate
bound gives the cofinal-prefix certificate on the identity schedule.

No inhabitant of either infinitary uniformity certificate is asserted.  No
vacuum-sector completion, thermodynamic limit, continuum QFT, or Clay result is
claimed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorConstructedCofinalRateBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFinitePrefixUniformGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledConstructedUniformCRealGap

/-- One strict rational ceiling on the constructed finite-prefix rates along
a constructively cofinal schedule of prefix bounds. -/
structure FixedNomeCofinalFinitePrefixRateCeiling
    (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (q : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ q
  rate_lt_one : q < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ request : Nat, request ≤ anchor request
  prefixRate_le : ∀ request : Nat,
    constructedFinitePrefixRate hw0 hw1 half (anchor request) ≤ q

namespace FixedNomeCofinalFinitePrefixRateCeiling

/-- Cofinal control of the located prefix maxima gives a common upper bound on
every constructed fixed-base rate. -/
def toUniformConstructedVacuumSectorRateBound
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeCofinalFinitePrefixRateCeiling
      w hw0 hw1 half q) :
    FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  constructedRate_le := by
    intro base
    exact Q'.le_trans' _ _ _
      (constructedFixedBaseRate_le_finitePrefixRate
        hw0 hw1 half base (family.anchor base) (family.anchor_ge base))
      (family.prefixRate_le base)

/-- Hence a cofinal strict ceiling on prefix maxima gives the existing cofinal
moving-centered vacuum-sector gap certificate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeCofinalFinitePrefixRateCeiling
      w hw0 hw1 half q) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q :=
  family.toUniformConstructedVacuumSectorRateBound.toVacuumSectorCenteredStrictGap

/-- The same cofinal prefix ceiling controls every fixed carrier's
same-object moving-centered Bishop-real limits. -/
theorem centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (family : FixedNomeCofinalFinitePrefixRateCeiling
      w hw0 hw1 half q)
    (base : Nat) (coefficient : Nat → Q') :
    CReal.leEv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (CReal.mul
        (CReal.ofQ' q)
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 base half coefficient)) :=
  family.toUniformConstructedVacuumSectorRateBound.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half base coefficient

end FixedNomeCofinalFinitePrefixRateCeiling

namespace FixedNomeUniformConstructedVacuumSectorRateBound

/-- Conversely, an all-base constructed-rate bound controls every located
prefix maximum, so the identity schedule is already cofinal. -/
def toCofinalFinitePrefixRateCeiling
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat} {q : Q'}
    (family : FixedNomeUniformConstructedVacuumSectorRateBound
      w hw0 hw1 half q) :
    FixedNomeCofinalFinitePrefixRateCeiling
      w hw0 hw1 half q where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := fun request => request
  anchor_ge := fun request => Nat.le_refl request
  prefixRate_le := by
    intro request
    exact Q'.runningMax_le_of_le (fun base => family.constructedRate_le base)
      request

end FixedNomeUniformConstructedVacuumSectorRateBound

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge.FixedNomeCofinalFinitePrefixRateCeiling.toUniformConstructedVacuumSectorRateBound
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge.FixedNomeCofinalFinitePrefixRateCeiling.toVacuumSectorCenteredStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge.FixedNomeCofinalFinitePrefixRateCeiling.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCofinalPrefixRateBridge.FixedNomeUniformConstructedVacuumSectorRateBound.toCofinalFinitePrefixRateCeiling
