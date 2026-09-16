/-
# The stationary sector is exactly the constructed unit-projection image

Centering commutes with the SAME physical time. A stationary centered
vector is zero by the already proved strict complement bound. Thus every
stationary vector equals its constructed unit projection, and conversely.
Its RC unit coefficient determines it uniquely. No representative of that
quotient scalar is extracted as Type-valued data.

These are fixed-spacing, small-nome statements on the existing spatial
presentation completion, not a continuum vacuum uniqueness, physical
Hamiltonian, full observable-algebra, or all-coupling result.
-/

import YMGap.Continuum.BF4SpatialUnionCentered

namespace YMGap.Continuum.BF4SpatialUnionStationary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionGeometry
open YMGap.Continuum.BF4SpatialUnionLinear
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionUnitProjection
open YMGap.Continuum.BF4SpatialUnionUnitComplement
open YMGap.Continuum.BF4SpatialUnionCentered
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "P" => unitProjection hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

/-- The existing strict bound removes the entire stationary centered part. -/
theorem fixed_twoStep_iff (x : V) : T 2 x = x ↔ P x = x := by
  constructor
  · intro h
    have hf : T 2 (center hw0 hw1 hsmall hd hs x) = center hw0 hw1 hsmall hd hs x := by
      rw [completedTime_center, h]
    have hz := fixed_twoStep_complement_eq_zero hw0 hw1 hsmall hd hs
      (centeredState hw0 hw1 hsmall hd hs x) hf
    have hdcp := center_decomposition hw0 hw1 hsmall hd hs x
    change center hw0 hw1 hsmall hd hs x = completedZero hw0 hw1 hsmall hd hs at hz
    rw [hz, completedZero_add] at hdcp
    exact hdcp
  · intro h
    rw [← h]
    exact time_unitProjection hw0 hw1 hsmall hd hs 2 x

theorem fixed_oneStep_iff (x : V) : T 1 x = x ↔ P x = x := by
  constructor
  · intro h
    apply (fixed_twoStep_iff hw0 hw1 hsmall hd hs x).mp
    change T (1+1) x = x
    rw [completedTime_add, h, h]
  · intro h
    rw [← h]
    exact time_unitProjection hw0 hw1 hsmall hd hs 1 x

theorem fixed_all_time_iff (x : V) : (∀ n, T n x = x) ↔ P x = x := by
  constructor
  · intro h
    exact (fixed_oneStep_iff hw0 hw1 hsmall hd hs x).mp (h 1)
  · intro h n
    rw [← h]
    exact time_unitProjection hw0 hw1 hsmall hd hs n x

/-- Equality of the actual quotient coefficients suffices; no scalar choice. -/
theorem stationary_coefficient_unique (x y : V)
    (hx : T 2 x = x) (hy : T 2 y = y) (hcoef : B x U = B y U) : x = y := by
  have hpx := (fixed_twoStep_iff hw0 hw1 hsmall hd hs x).mp hx
  have hpy := (fixed_twoStep_iff hw0 hw1 hsmall hd hs y).mp hy
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  calc
    B x z = B (P x) z := congrArg (fun t => B t z) hpx.symm
    _ = RCmul (B x U) (B U z) := unitProjection_pairing hw0 hw1 hsmall hd hs x z
    _ = RCmul (B y U) (B U z) := congrArg (fun a => RCmul a (B U z)) hcoef
    _ = B (P y) z := (unitProjection_pairing hw0 hw1 hsmall hd hs y z).symm
    _ = B y z := congrArg (fun t => B t z) hpy

/-- Overlap with the unit is one; this is not merely norm-one normalization. -/
theorem stationary_unit_overlap_one (x : V) (hx : T 2 x = x)
    (hcoef : B x U = Quotient.mk crealSetoid cone) : x = U :=
  stationary_coefficient_unique hw0 hw1 hsmall hd hs x U hx
    (completedUnit_fixed hw0 hw1 hsmall hd hs 2)
    (hcoef.trans (completedUnit_norm_one hw0 hw1 hsmall hd hs).symm)

end YMGap.Continuum.BF4SpatialUnionStationary

#print axioms YMGap.Continuum.BF4SpatialUnionStationary.fixed_twoStep_iff
#print axioms YMGap.Continuum.BF4SpatialUnionStationary.fixed_oneStep_iff
#print axioms YMGap.Continuum.BF4SpatialUnionStationary.fixed_all_time_iff
#print axioms YMGap.Continuum.BF4SpatialUnionStationary.stationary_coefficient_unique
#print axioms YMGap.Continuum.BF4SpatialUnionStationary.stationary_unit_overlap_one
