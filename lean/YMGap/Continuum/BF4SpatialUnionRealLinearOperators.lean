/-
# Real homogeneity of the ORIGINAL union projection and reduced inverse

The actual pairing separates vectors. Its real-scalar homogeneity and each
existing operator's self-adjointness therefore prove real homogeneity without
new continuity assumptions or reconstruction of any operator. The old unit
projection is pinned to the new scalar action using its ORIGINAL computed
unit coefficient and modulus.

Scalars carry CReal and explicit QCauchy data. No modulus is selected for an
arbitrary legacy quotient real; full Hilbert/OS/QFT remains open.
-/

import YMGap.Continuum.BF4SpatialUnionRealScalarAlgebra
import YMGap.Continuum.BF4SpatialUnionResolventBound

namespace YMGap.Continuum.BF4SpatialUnionRealLinearOperators

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
open YMGap.Continuum.BF4SpatialUnionBilinear
open YMGap.Continuum.BF4SpatialUnionCompletedRealScalar
open YMGap.Continuum.BF4SpatialUnionRealScalarAlgebra
open YMGap.Continuum.BF4SpatialUnionUnitProjection
open YMGap.Continuum.BF4SpatialUnionCentered
open YMGap.Continuum.BF4SpatialUnionResolvent
open YMGap.Continuum.BF4SpatialUnionResolventBound
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "S" => completedRealSmul hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "P" => unitProjection hw0 hw1 hsmall hd hs
local notation "C" => center hw0 hw1 hsmall hd hs
local notation "R" => resolvent hw0 hw1 hsmall hd hs
local notation "F" => defect hw0 hw1 hsmall hd hs

private theorem selfAdjoint_realSmul (f : V → V)
    (hf : ∀ x y, B (f x) y = B x (f y))
    (s : CReal) (cs : QCauchy s.approx) (x : V) : f (S s cs x) = S s cs (f x) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [hf, completedInner_realSmul_left, completedInner_realSmul_left, hf]

/-- The earlier specialized scalar-unit construction is the same vector. -/
theorem scalarUnitCauchy_eq_realSmul (s : CReal) (cs : QCauchy s.approx) :
    Quotient.mk (D).completionSetoid (scalarUnitCauchy hw0 hw1 hsmall hd hs s cs) = S s cs U := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [scalarUnitCauchy_pairing, completedInner_realSmul_left]

/-- The exact original coefficient and its modulus are retained, not selected. -/
theorem unitProjection_mk_as_realSmul (X : (D).Cauchy) :
    P (Quotient.mk (D).completionSetoid X) =
      S (unitCoefficient hw0 hw1 hsmall hd hs X)
        (unitCoefficientCauchy hw0 hw1 hsmall hd hs X) U := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [unitProjection_pairing, completedInner_realSmul_left, unitCoefficient_pin]

theorem unitProjection_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    P (S s cs x) = S s cs (P x) :=
  selfAdjoint_realSmul hw0 hw1 hsmall hd hs P
    (unitProjection_selfAdjoint hw0 hw1 hsmall hd hs) s cs x

theorem center_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    C (S s cs x) = S s cs (C x) :=
  selfAdjoint_realSmul hw0 hw1 hsmall hd hs C
    (center_selfAdjoint hw0 hw1 hsmall hd hs) s cs x

theorem defect_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    F (S s cs x) = S s cs (F x) := by
  unfold defect
  rw [completedTime_realSmul, completedRealSmul_sub]

theorem resolvent_realSmul (s : CReal) (cs : QCauchy s.approx) (x : V) :
    R (S s cs x) = S s cs (R x) :=
  selfAdjoint_realSmul hw0 hw1 hsmall hd hs R
    (resolvent_selfAdjoint hw0 hw1 hsmall hd hs) s cs x

end YMGap.Continuum.BF4SpatialUnionRealLinearOperators

#print axioms YMGap.Continuum.BF4SpatialUnionRealLinearOperators.scalarUnitCauchy_eq_realSmul
#print axioms YMGap.Continuum.BF4SpatialUnionRealLinearOperators.unitProjection_mk_as_realSmul
#print axioms YMGap.Continuum.BF4SpatialUnionRealLinearOperators.unitProjection_realSmul
#print axioms YMGap.Continuum.BF4SpatialUnionRealLinearOperators.center_realSmul
#print axioms YMGap.Continuum.BF4SpatialUnionRealLinearOperators.defect_realSmul
#print axioms YMGap.Continuum.BF4SpatialUnionRealLinearOperators.resolvent_realSmul
