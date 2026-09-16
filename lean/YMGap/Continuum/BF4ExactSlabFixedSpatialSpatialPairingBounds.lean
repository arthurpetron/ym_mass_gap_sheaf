/-
# Computed norm ceilings on the actual spatial Cauchy carrier

The actual spatial-pairing approximation modulus gives a rational ceiling
for each anchor diagonal. No growing-width presentation cap is used. The
unconditional joint anchor inequality passes through the proved spatial
limit, so every supplied spatial Cauchy representative has its own computed
eventual ceiling 2+2*C_anchor. No uniform bound on all presentations of the
representative is assumed, and finite-width nullity is never inferred.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth recenter)
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarCauchy
  (scalarCeiling scalarCeiling_nonnegative scalar_approx_le_ceiling)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "P" => spatialPairing hw0 hw1 base hsmall hd hs hb
local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb

attribute [local irreducible] spatialPairing

/-- A computed scalar ceiling from the actual spatial pairing's modulus. -/
def diagonalCeiling (x : PhysicalSpan base) : Q' :=
  scalarCeiling (P x x) (spatialPairingCauchy hw0 hw1 base hsmall hd hs hb x x)

theorem diagonalCeiling_nonnegative (x : PhysicalSpan base) :
    (0 : Q') ≤ diagonalCeiling hw0 hw1 base hsmall hd hs hb x :=
  scalarCeiling_nonnegative _ _

theorem diagonal_le_ceiling (x : PhysicalSpan base) :
    leEv (P x x) (ofQ' (diagonalCeiling hw0 hw1 base hsmall hd hs hb x)) := by
  let c := spatialPairingCauchy hw0 hw1 base hsmall hd hs hb x x
  intro epsilon he
  refine ⟨c.M 1, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (Q'.le_trans' _ _ _ (scalar_approx_le_ceiling (P x x) c n hn)
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he)))

def normBase (X : (D).Cauchy) : Nat := X.modulus 1

def normCeiling (X : (D).Cauchy) : Q' :=
  (1+1) +
    (diagonalCeiling hw0 hw1 base hsmall hd hs hb (X.seq (normBase hw0 hw1 base hsmall hd hs hb X)) +
      diagonalCeiling hw0 hw1 base hsmall hd hs hb (X.seq (normBase hw0 hw1 base hsmall hd hs hb X)))

theorem normCeiling_nonnegative (X : (D).Cauchy) :
    (0 : Q') ≤ normCeiling hw0 hw1 base hsmall hd hs hb X :=
  Q'.zero_le_add _ _ (by decide)
    (Q'.zero_le_add _ _ (diagonalCeiling_nonnegative hw0 hw1 base hsmall hd hs hb _)
      (diagonalCeiling_nonnegative hw0 hw1 base hsmall hd hs hb _))

/-- Only an unconditional form inequality is passed through the spatial limit. -/
theorem diagonal_anchor_bound (x anchor : PhysicalSpan base) :
    leEv (P x x)
      (add (add (spatialDistSq hw0 hw1 base hsmall hd hs hb x anchor)
          (spatialDistSq hw0 hw1 base hsmall hd hs hb x anchor))
        (add (P anchor anchor) (P anchor anchor))) :=
  leEv_of_convergesTo_le (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x x)
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x anchor)
        (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x anchor))
      (TrigAddCReal.convergesTo_add (spatialPairing_converges hw0 hw1 base hsmall hd hs hb anchor anchor)
        (spatialPairing_converges hw0 hw1 base hsmall hd hs hb anchor anchor)))
    (fun r => BF4ExactSlabFixedSpatialJointPairingBounds.diagonal_anchor_bound
      hw0 hw1 (paddedWidth base r) (recenter r x) (recenter r anchor))

private theorem four_bound {A B : CReal} {a b : Q'}
    (hA : leEv A (ofQ' a)) (hB : leEv B (ofQ' b)) :
    leEv (add (add A A) (add B B)) (ofQ' ((a+a)+(b+b))) := by
  have h := leEv_add (leEv_add hA hA) (leEv_add hB hB)
  rw [ofQ'_add, ofQ'_add, ofQ'_add] at h
  exact h

/-- A rational ceiling computed from this representative and its anchor. -/
theorem diagonal_le_normCeiling (X : (D).Cauchy)
    (n : Nat) (hn : normBase hw0 hw1 base hsmall hd hs hb X ≤ n) :
    leEv (P (X.seq n) (X.seq n)) (ofQ' (normCeiling hw0 hw1 base hsmall hd hs hb X)) := by
  let anchor := X.seq (normBase hw0 hw1 base hsmall hd hs hb X)
  have hdist : leEv (spatialDistSq hw0 hw1 base hsmall hd hs hb (X.seq n) anchor) (ofQ' 1) :=
    X.isCauchy 1 (by decide) n (normBase hw0 hw1 base hsmall hd hs hb X) hn (Nat.le_refl _)
  exact leEv_trans (diagonal_anchor_bound hw0 hw1 base hsmall hd hs hb (X.seq n) anchor)
    (four_bound hdist (diagonal_le_ceiling hw0 hw1 base hsmall hd hs hb anchor))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds.diagonalCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds.diagonalCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds.diagonal_le_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds.normBase
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds.normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds.normCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds.diagonal_anchor_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds.diagonal_le_normCeiling
