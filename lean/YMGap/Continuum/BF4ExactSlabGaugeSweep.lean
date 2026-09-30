/-
# Gauge-polynomial witnesses for the ORIGINAL sweep and coupled recurrence

The singleton block projection equals the existing star projection on the
same full-action completion. Consequently the actual scheduled sweep, its
balanced product and affine map preserve explicit gauge-polynomial Cauchy
representatives. Both components of the existing coupled recurrence inherit
these witnesses, at every order and rational affine coefficient.

This uses the existing common-auxiliary vertex-tag Invariant predicate.
It does not construct an arbitrary completed gauge action, supply a strict
bound, or identify this ordinary conditional dynamics with OS transfer.
-/

import YMGap.Continuum.BF4ExactSlabGaugeRepresentedCompletion
import YMGap.Continuum.BF4ExactSlabBlockSingletonProjection
import YMGap.Continuum.GNSRepresentedSectorRecurrence
import YMGap.Continuum.BF4ExactSlabSweepChebyshev

namespace YMGap.Continuum.BF4ExactSlabGaugeSweep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabConditionalSweep
open YMGap.Continuum.BF4ExactSlabEightLayerCone
open YMGap.Continuum.BF4ExactSlabGaugeRepresentedCompletion

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)

local notation "F" => fullData hw0 hw1 K extent hK
local notation "P" => projections hw0 hw1 K extent hK
local notation "W" => Witness hw0 hw1 K extent hK

/-- The operator already used by the original single-link sweep. -/
def link (i : PhysicalLink extent) {x : GNSCompletionSpace F} (a : W x) :
    W ((P).op i x) := by
  have hi : ∀ j, j ∈ [i.val] → j ∈ boundaryCompleteSlabLinks extent := by
    intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    exact i.property
  exact (block hw0 hw1 K extent hK [i.val] hi a).transport
    (BF4ExactSlabBlockSingletonProjection.conditionalProjection_singleton
      hw0 hw1 K extent hK i.val i.property x)

/-- Actual successive states, with arbitrary order and repeated links. -/
def sweep : (links : List (PhysicalLink extent)) →
    {x : GNSCompletionSpace F} → W x → W ((P).sweep links x)
  | [], _, a => a
  | i :: rest, _, a => sweep rest (link hw0 hw1 K extent hK i a)

/-- Forward sweep followed by its actual reversed schedule. -/
def balanced (links : List (PhysicalLink extent))
    {x : GNSCompletionSpace F} (a : W x) : W ((P).balanced links x) :=
  sweep hw0 hw1 K extent hK links.reverse (sweep hw0 hw1 K extent hK links a)

/-- No restriction on c and no contraction hypothesis are needed for closure. -/
def affine (c : Q') {x : GNSCompletionSpace F} (a : W x) :
    W (BF4ExactSlabSweepChebyshev.affine hw0 hw1 K extent hK c x) :=
  sub hw0 hw1 K extent hK
    (scale hw0 hw1 K extent hK c (balanced hw0 hw1 K extent hK (schedule extent) a)) a

/-- Witnesses for BOTH components of the existing auxiliary energy state. -/
def coupled (c : Q') {x : GNSCompletionSpace F} (a : W x) (n : Nat) :
    W (BF4ExactSlabSweepChebyshev.coupled hw0 hw1 K extent hK c x n).1 ×
      W (BF4ExactSlabSweepChebyshev.coupled hw0 hw1 K extent hK c x n).2 :=
  GNSRepresentedSectorRecurrence.state_representatives F
    (GaugePolynomial hw0 hw1 K extent hK)
    (polynomial_zero hw0 hw1 K extent hK)
    (polynomial_add hw0 hw1 K extent hK)
    (polynomial_neg hw0 hw1 K extent hK)
    (BF4ExactSlabSweepChebyshev.affine hw0 hw1 K extent hK c)
    (fun _ h => affine hw0 hw1 K extent hK c h) a n

#print axioms link
#print axioms sweep
#print axioms balanced
#print axioms affine
#print axioms coupled

end YMGap.Continuum.BF4ExactSlabGaugeSweep
