/-
# Computed norm ceilings for the actual joint reflected Cauchy carrier

The old presentation cap and unconditional anchor inequality pass through
the proved cutoff limit. Each Cauchy representative of the joint seminorm
then supplies its own anchor at modulus one and the explicit eventual
ceiling 2+2*C_anchor. No bound on all its presentation coefficients is
assumed, and no fixed-cutoff Cauchy carrier is identified with this one.
Nome and spatial width remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialPairingBounds
  (diagonalCeiling diagonalCeiling_nonnegative)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width

attribute [local irreducible] jointPairing

/-- The same computed finite-presentation cap survives cutoff removal. -/
theorem diagonal_le_ceiling (x : PhysicalSpan width) :
    leEv (jointPairing hw0 hw1 width x x) (ofQ' (diagonalCeiling width x)) :=
  leEv_of_convergesTo_le (pairing_converges_jointPairing hw0 hw1 width x x)
    (convergesTo_const (ofQ' (diagonalCeiling width x)))
    (fun stage => BF4ExactSlabFixedSpatialPairingBounds.diagonal_le_ceiling
      hw0 hw1 width stage x)

def normBase (X : (D).Cauchy) : Nat := X.modulus 1

def normCeiling (X : (D).Cauchy) : Q' :=
  (1+1) +
    (diagonalCeiling width (X.seq (normBase hw0 hw1 width X)) +
      diagonalCeiling width (X.seq (normBase hw0 hw1 width X)))

theorem normCeiling_nonnegative (X : (D).Cauchy) :
    (0 : Q') ≤ normCeiling hw0 hw1 width X :=
  Q'.zero_le_add _ _ (by decide)
    (Q'.zero_le_add _ _ (diagonalCeiling_nonnegative width _)
      (diagonalCeiling_nonnegative width _))

/-- The unconditional original anchor inequality passes to the joint form.
This does not transfer a stage-dependent small-distance hypothesis. -/
theorem diagonal_anchor_bound (x anchor : PhysicalSpan width) :
    leEv (jointPairing hw0 hw1 width x x)
      (add (add (jointDistSq hw0 hw1 width x anchor)
          (jointDistSq hw0 hw1 width x anchor))
        (add (jointPairing hw0 hw1 width anchor anchor)
          (jointPairing hw0 hw1 width anchor anchor))) :=
  leEv_of_convergesTo_le (pairing_converges_jointPairing hw0 hw1 width x x)
    (TrigAddCReal.convergesTo_add
      (TrigAddCReal.convergesTo_add (distSq_converges_joint hw0 hw1 width x anchor)
        (distSq_converges_joint hw0 hw1 width x anchor))
      (TrigAddCReal.convergesTo_add (pairing_converges_jointPairing hw0 hw1 width anchor anchor)
        (pairing_converges_jointPairing hw0 hw1 width anchor anchor)))
    (fun stage => BF4ExactSlabFixedSpatialPairingBounds.diagonal_anchor_bound
      hw0 hw1 width stage x anchor)

private theorem four_bound {A B : CReal} {a b : Q'}
    (hA : leEv A (ofQ' a)) (hB : leEv B (ofQ' b)) :
    leEv (add (add A A) (add B B)) (ofQ' ((a+a)+(b+b))) := by
  have h := leEv_add (leEv_add hA hA) (leEv_add hB hB)
  rw [ofQ'_add, ofQ'_add, ofQ'_add] at h
  exact h

/-- A common eventual diagonal ceiling computed from this supplied joint
Cauchy stream, not from a uniformly bounded presentation of it. -/
theorem diagonal_le_normCeiling (X : (D).Cauchy)
    (n : Nat) (hn : normBase hw0 hw1 width X ≤ n) :
    leEv (jointPairing hw0 hw1 width (X.seq n) (X.seq n))
      (ofQ' (normCeiling hw0 hw1 width X)) := by
  let anchor := X.seq (normBase hw0 hw1 width X)
  have hdist : leEv (jointDistSq hw0 hw1 width (X.seq n) anchor) (ofQ' 1) :=
    X.isCauchy 1 (by decide) n (normBase hw0 hw1 width X) hn (Nat.le_refl _)
  exact leEv_trans (diagonal_anchor_bound hw0 hw1 width (X.seq n) anchor)
    (four_bound hdist (diagonal_le_ceiling hw0 hw1 width anchor))

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds.diagonal_le_ceiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds.normBase
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds.normCeiling
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds.normCeiling_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds.diagonal_anchor_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingBounds.diagonal_le_normCeiling
